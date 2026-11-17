(*  Title:      monomorphize.ML
    Monomorphisation of code equations as a refinement step.

    For a polymorphic constant c and a type instantiation of some of its type variables,
    [monomorphize] introduces a new constant c' == c at the instantiated type, derives the
    code equations of c' from the (preprocessed) code equations of c by type instantiation
    and folding of the definition, simplifies their right-hand sides with a user-supplied
    simpset (which resolves the type class dictionaries of the instance), declares them as
    code equations of c', and finally registers the [code_unfold] rule c = c' at the
    instantiated type, so that all code equations mentioning c at that type call c' instead.

    Everything is derived by the inference kernel from the definition c' == c and the
    existing code equations; no new axioms are involved.
*)

signature MONOMORPHIZE =
sig
  (* tyinst: instantiations of the constant's type variables, in order of their first
     occurrence in its type; NONE keeps a type variable *)
  type spec = {const: string, name: string, tyinst: typ option list}
  val monomorphize: spec list -> thm list -> theory -> theory
  val monomorphize_cmd: (string * string * string list) list -> string list -> theory -> theory
  val box: spec list -> theory -> theory
  val box_cmd: (string * string * string list) list -> theory -> theory
end

structure Monomorphize : MONOMORPHIZE =
struct

type spec = {const: string, name: string, tyinst: typ option list}

fun dest_eqn (Const (@{const_name Pure.eq}, _) $ lhs $ rhs) = (lhs, rhs)
  | dest_eqn (Const (@{const_name Trueprop}, _) $ (Const (@{const_name HOL.eq}, _) $ lhs $ rhs)) =
      (lhs, rhs)
  | dest_eqn t = raise TERM ("dest_eqn", [t]);

(* conversion on the right-hand side of a (Pure or HOL) equation *)
fun rhs_conv conv ct =
  (case Thm.term_of ct of
    Const (@{const_name Pure.eq}, _) $ _ $ _ => Conv.arg_conv conv ct
  | Const (@{const_name Trueprop}, _) $ _ => Conv.arg_conv (Conv.arg_conv conv) ct
  | _ => raise CTERM ("rhs_conv", [ct]));

fun find_const c t =
  (case Term.fold_aterms (fn u as Const (d, _) => if d = c then cons u else I | _ => I) t [] of
    Const (_, T) :: _ => SOME T
  | _ => NONE);

(* the constant's declared type, with the given type variables instantiated *)
fun instantiated_type thy c tyinst =
  let
    val ctxt = Proof_Context.init_global thy;
    val T = Sign.the_const_type thy c
      |> Term.map_atyps (fn TVar ((a, _), S) => TFree (a, S) | U => U);
    val tfrees = rev (Term.add_tfreesT T []);
    val _ = if length tyinst > length tfrees then
      error ("monomorphize: too many type instantiations for " ^ quote c ^ " :: " ^
        Syntax.string_of_typ ctxt T) else ();
    val inst = map_filter I (map2 (fn (v, S) => fn U_opt =>
      (case U_opt of
        NONE => NONE
      | SOME U =>
          if Sign.of_sort thy (U, S) then SOME (v, U)
          else error ("monomorphize: type " ^ Syntax.string_of_typ ctxt U ^
            " is not of sort " ^ Syntax.string_of_sort ctxt S ^ " (required by " ^ quote c ^ ")")))
      (take (length tyinst) tfrees) tyinst);
  in
    Term.map_type_tfree (fn (v, S) => the_default (TFree (v, S)) (AList.lookup (op =) inst v)) T
  end;

fun monomorphize1 eqngr simps ({const = c_raw, name, tyinst} : spec) thy =
  let
    val ctxt0 = Proof_Context.init_global thy;
    val c = Code.read_const ctxt0 c_raw;
    val T' = instantiated_type thy c tyinst;
    val _ = writeln ("monomorphize: " ^ name ^ " = " ^ c ^ " :: " ^ Syntax.string_of_typ ctxt0 T');
    val b = Binding.name name;

    (* definition c' == c *)
    val (lhs, thy) = Sign.declare_const_global ((b, T'), NoSyn) thy;
    val (def, thy) =
      Global_Theory.add_def (Thm.def_binding b, Logic.mk_equals (lhs, Const (c, T'))) thy;
    val ctxt = Proof_Context.init_global thy;
    val def' = Axclass.overload ctxt def;
    val (c_ov, T_target) =
      (case Thm.term_of (Thm.rhs_of def') of
        Const (d, U) => (d, U)
      | t => raise TERM ("monomorphize: unexpected definition", [t]));
    val is_abs = Code.is_abstr thy c;
    val _ = if is_abs then
      error ("monomorphize: " ^ quote c ^ " constructs values of an abstract type; " ^
        "its code equation cannot be specialised") else ();
    val cert = Code_Preproc.cert eqngr c;
    val eqns = Code.equations_of_cert thy cert |> snd |> these
      |> map_filter (fn (_, (SOME thm, proper)) => SOME (thm, proper) | _ => NONE);
    val _ = if null eqns then error ("monomorphize: no code equations for " ^ quote c) else ();
    val simp_ctxt = put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps simps;

    fun instantiate thm =
      let
        val thm = Axclass.overload ctxt thm;
        val (l, _) = dest_eqn (Thm.prop_of thm);
        val Tc = (case find_const c_ov l of
            SOME Tc => Tc
          | NONE => raise THM ("monomorphize: head constant not found", 0, [thm]));
        val tyenv = Sign.typ_match thy (Tc, T_target) Vartab.empty
          handle Type.TYPE_MATCH =>
            error ("monomorphize: code equation of " ^ quote c ^ " at incompatible type\n" ^
              Syntax.string_of_typ (Config.put show_sorts true ctxt) Tc ^ "\nvs.\n" ^
              Syntax.string_of_typ (Config.put show_sorts true ctxt) T_target ^ "\n" ^
              Thm.string_of_thm ctxt thm);
        val instT = TVars.build (Vartab.fold (fn (xi, (S, U)) =>
          TVars.add ((xi, S), Thm.ctyp_of ctxt U)) tyenv);
      in
        Thm.instantiate (instT, Vars.empty) thm
        |> Local_Defs.fold ctxt [def']
        |> Conv.fconv_rule (rhs_conv (Simplifier.rewrite simp_ctxt))
        |> Drule.zero_var_indexes
      end;
    val eqns' = map (apfst instantiate) eqns;
    (* A function into an abstract type has its code equations stated through the type's
       projection, as proj (c x) = ..., and the code generator takes them by a different door. *)
    val n_const =
      (case Thm.term_of (Thm.lhs_of def') of
        Const (d, _) => d
      | t => raise TERM ("monomorphize: unexpected definition", [t]));
    fun is_abstract_eqn thm =
      (case Term.head_of (fst (dest_eqn (Thm.prop_of thm))) of
        Const (d, _) => d <> n_const
      | _ => true);
    val thy =
      if exists (is_abstract_eqn o fst) eqns'
      then fold (Code.declare_abstract_eqn_global o fst) eqns' thy
      else Code.declare_eqns_global eqns' thy;
    val (_, thy) = Global_Theory.add_thmss
      [((Binding.suffix_name "_code" b, map fst eqns'), [])] thy;
    (* redirect applied occurrences of c at the instantiated type to c'; the applied form
       leaves occurrences of c as an argument (e.g. as a locale parameter) untouched *)
    val unfold =
      (case try dest_funT T_target of
        SOME (argT, _) =>
          let
            val x = Free ("x", argT);
            val lhs' = Thm.term_of (Thm.lhs_of def');
            val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (Const (c_ov, T_target) $ x, lhs' $ x));
          in
            Goal.prove ctxt ["x"] [] goal (fn {context = ctxt', ...} =>
              simp_tac (put_simpset HOL_basic_ss ctxt' |> Simplifier.add_simps [def']) 1)
            |> Drule.zero_var_indexes
          end
      | NONE => Thm.symmetric def');
    val (_, thy) = Global_Theory.add_thmss
      [((Binding.suffix_name "_unfold" b, [unfold]), [])] thy;
    val thy = Code_Preproc.map_pre (fn ctxt => ctxt |> Simplifier.add_simps [unfold]) thy;
  in thy end;

fun monomorphize specs simps thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val consts = map (Code.read_const ctxt o #const) specs;
    val {eqngr, ...} = Code_Preproc.obtain false {ctxt = ctxt, consts = consts, terms = []};
  in fold (monomorphize1 eqngr simps) specs thy end;

fun read_specs thy raw_specs =
  let val ctxt = Proof_Context.init_global thy in
    raw_specs |> map (fn (c, name, tyinst) =>
      {const = c, name = name,
       tyinst = map (fn "_" => NONE | s => SOME (Syntax.read_typ ctxt s)) tyinst})
  end;

fun monomorphize_cmd raw_specs raw_simps thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val simps = maps (Proof_Context.get_thms ctxt) raw_simps;
  in monomorphize (read_specs thy raw_specs) simps thy end;


(* Boxing: c_v = Box (c :: T) for a closed type T.

   The generated code for the nullary constant c_v is a value (not eta-expanded), so the
   type class dictionaries of c at T are constructed once, when the module is initialised.
   The rule c x = unbox c_v x redirects all applied occurrences of c at type T. *)

fun box1 ({const = c_raw, name, tyinst} : spec) thy =
  let
    val ctxt0 = Proof_Context.init_global thy;
    val c = Code.read_const ctxt0 c_raw;
    val T = instantiated_type thy c tyinst;
    val _ = if null (Term.add_tfreesT T []) then ()
      else error ("box: type of " ^ quote name ^ " is not closed: " ^ Syntax.string_of_typ ctxt0 T);
    val _ = writeln ("box: " ^ name ^ " = " ^ c ^ " :: " ^ Syntax.string_of_typ ctxt0 T);
    val b = Binding.name name;
    val boxedT = Type (@{type_name boxed}, [T]);
    val (lhs, thy) = Sign.declare_const_global ((b, boxedT), NoSyn) thy;
    val rhs = Const (@{const_name Box}, T --> boxedT) $ Const (c, T);
    val (def, thy) = Global_Theory.add_def (Thm.def_binding b, Logic.mk_equals (lhs, rhs)) thy;
    val ctxt = Proof_Context.init_global thy;
    val def' = Axclass.overload ctxt def;
    val c_ov = (case Thm.term_of (Thm.rhs_of def') of
        _ $ (t as Const _) => t
      | t => raise TERM ("box: unexpected definition", [t]));
    val (argT, _) = dest_funT T handle TYPE _ =>
      error ("box: " ^ quote name ^ " does not have a function type");
    val x = Free ("x", argT);
    val unbox = Const (@{const_name unbox}, boxedT --> T);
    val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (c_ov $ x, unbox $ lhs $ x));
    val unfold = Goal.prove ctxt ["x"] [] goal (fn {context = ctxt', ...} =>
        simp_tac (put_simpset HOL_basic_ss ctxt' |> Simplifier.add_simps [def', @{thm boxed.sel}]) 1)
      |> Drule.zero_var_indexes;
    val thy = Code.declare_eqns_global [(def' RS @{thm meta_eq_to_obj_eq}, true)] thy;
    val (_, thy) = Global_Theory.add_thmss [((Binding.suffix_name "_unfold" b, [unfold]), [])] thy;
    val thy = Code_Preproc.map_pre (fn ctxt => ctxt |> Simplifier.add_simps [unfold]) thy;
  in thy end;

fun box specs thy = fold box1 specs thy;

fun box_cmd raw_specs thy = box (read_specs thy raw_specs) thy;

end;

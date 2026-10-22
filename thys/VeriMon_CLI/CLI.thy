(*<*)
theory CLI
  imports "MFODL_Frontend.Surface_Conversion" CLI_Output "MFODL_Parser.MFODL_Parser"
    "Monitor_Exec.Log_Monitor"
begin
(*>*)

section \<open>Verified monitor with MonPoly's command line\<close>

text \<open>The verified parts composed into the program @{text verimon}: the driver only reads the files
  that @{text cli_main} asks for, prints what it says, and runs the loop over the log.\<close>

subsection \<open>Signature of the monitor\<close>

text \<open>The monitor has no type of regular expressions: a formula with a predicate with such an
  argument is refused, and the other such arguments are read as strings.\<close>

fun ty_of_sty :: "sty \<Rightarrow> ty" where
  "ty_of_sty SInt = TInt"
| "ty_of_sty SStr = TString"
| "ty_of_sty SFloat = TFloat"
| "ty_of_sty SRegexp = TString"

definition lsig_of :: "schema \<Rightarrow> tysym Formula.formula \<Rightarrow> string + lsig" where
  "lsig_of S \<phi> = (let used = map fst (free_preds \<phi>) in
     if (\<exists>(p, fs) \<in> set S. str8_of_string p \<in> set used \<and> SRegexp \<in> set (map snd fs))
     then Inl (unsupported ''Regular expressions constants are not supported'')
     else Inr (map (\<lambda>(p, fs). (str8_of_string p, map (ty_of_sty \<circ> snd) fs)) S))"

subsection \<open>Types of the free variables\<close>

definition str_of_ty :: "ty \<Rightarrow> string" where
  "str_of_ty t = (case t of TInt \<Rightarrow> ''int'' | TString \<Rightarrow> ''string'' | TFloat \<Rightarrow> ''float'')"

text \<open>@{text "-sigout"}: the free variables with the types that the type checker infers.\<close>

definition sigout_text :: "string list \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> string" where
  "sigout_text vs f = concat (between '', '' (map (\<lambda>(i, v). v @ '':'' @ str_of_ty (convert_tysym (f (TAny i))))
     (zip [0..<length vs] vs))) @ nl"

definition fv_text :: "string list \<Rightarrow> string" where
  "fv_text vs = ''The sequence of free variables is: ('' @ concat (between '','' vs) @ '')'' @ nl"

subsection \<open>MonPoly's checks of the input formula\<close>

text \<open>MonPoly checks the intervals, the bounds of future operators and the declarations on the input
  formula; the checks of @{text LET} and aggregations are left to the conversion and the type checker.\<close>

fun bnd_ok :: "bound \<Rightarrow> bool" where
  "bnd_ok (OBnd a) = (0 \<le> a)"
| "bnd_ok (CBnd a) = (0 \<le> a)"
| "bnd_ok BInf = True"

fun lb_ub_ok :: "bound \<Rightarrow> bound \<Rightarrow> bool" where
  "lb_ub_ok BInf _ = False"
| "lb_ub_ok (CBnd a) (CBnd b) = (a \<le> b)"
| "lb_ub_ok (CBnd a) (OBnd b) = (a < b)"
| "lb_ub_ok (OBnd a) (CBnd b) = (a < b)"
| "lb_ub_ok (OBnd a) (OBnd b) = (a < b)"
| "lb_ub_ok _ BInf = True"

definition intv_ok :: "interval \<Rightarrow> bool" where
  "intv_ok i = (case i of (l, u) \<Rightarrow> bnd_ok l \<and> bnd_ok u \<and> lb_ub_ok l u)"

fun intervals_ok :: "formula \<Rightarrow> bool"
and intervals_ok_r :: "regex \<Rightarrow> bool" where
  "intervals_ok (FNeg f) = intervals_ok f"
| "intervals_ok (FExists _ f) = intervals_ok f"
| "intervals_ok (FForAll _ f) = intervals_ok f"
| "intervals_ok (FAggreg _ _ _ _ f) = intervals_ok f"
| "intervals_ok (FAnd f g) = (intervals_ok f \<and> intervals_ok g)"
| "intervals_ok (FOr f g) = (intervals_ok f \<and> intervals_ok g)"
| "intervals_ok (FImplies f g) = (intervals_ok f \<and> intervals_ok g)"
| "intervals_ok (FEquiv f g) = (intervals_ok f \<and> intervals_ok g)"
| "intervals_ok (FLet _ f g) = (intervals_ok f \<and> intervals_ok g)"
| "intervals_ok (FLetPast _ f g) = (intervals_ok f \<and> intervals_ok g)"
| "intervals_ok (FFrz _ f g) = (intervals_ok f \<and> intervals_ok g)"
| "intervals_ok (FEventually i f) = (intv_ok i \<and> intervals_ok f)"
| "intervals_ok (FAlways i f) = (intv_ok i \<and> intervals_ok f)"
| "intervals_ok (FPrev i f) = (intv_ok i \<and> intervals_ok f)"
| "intervals_ok (FNext i f) = (intv_ok i \<and> intervals_ok f)"
| "intervals_ok (FOnce i f) = (intv_ok i \<and> intervals_ok f)"
| "intervals_ok (FPastAlways i f) = (intv_ok i \<and> intervals_ok f)"
| "intervals_ok (FSince i f g) = (intv_ok i \<and> intervals_ok f \<and> intervals_ok g)"
| "intervals_ok (FTrigger i f g) = (intv_ok i \<and> intervals_ok f \<and> intervals_ok g)"
| "intervals_ok (FUntil i f g) = (intv_ok i \<and> intervals_ok f \<and> intervals_ok g)"
| "intervals_ok (FRelease i f g) = (intv_ok i \<and> intervals_ok f \<and> intervals_ok g)"
| "intervals_ok (FFrex i r) = (intv_ok i \<and> intervals_ok_r r)"
| "intervals_ok (FPrex i r) = (intv_ok i \<and> intervals_ok_r r)"
| "intervals_ok _ = True"
| "intervals_ok_r (RTest f) = intervals_ok f"
| "intervals_ok_r (RConcat r s) = (intervals_ok_r r \<and> intervals_ok_r s)"
| "intervals_ok_r (RPlus r s) = (intervals_ok_r r \<and> intervals_ok_r s)"
| "intervals_ok_r (RStar r) = intervals_ok_r r"
| "intervals_ok_r (RSkip _) = True"

definition ub_ok :: "interval \<Rightarrow> bool" where
  "ub_ok i = (snd i \<noteq> BInf)"

fun bounds_ok :: "formula \<Rightarrow> bool"
and bounds_ok_r :: "regex \<Rightarrow> bool" where
  "bounds_ok (FNeg f) = bounds_ok f"
| "bounds_ok (FExists _ f) = bounds_ok f"
| "bounds_ok (FForAll _ f) = bounds_ok f"
| "bounds_ok (FAggreg _ _ _ _ f) = bounds_ok f"
| "bounds_ok (FPrev _ f) = bounds_ok f"
| "bounds_ok (FNext _ f) = bounds_ok f"
| "bounds_ok (FOnce _ f) = bounds_ok f"
| "bounds_ok (FPastAlways _ f) = bounds_ok f"
| "bounds_ok (FPrex _ r) = bounds_ok_r r"
| "bounds_ok (FAnd f g) = (bounds_ok f \<and> bounds_ok g)"
| "bounds_ok (FOr f g) = (bounds_ok f \<and> bounds_ok g)"
| "bounds_ok (FImplies f g) = (bounds_ok f \<and> bounds_ok g)"
| "bounds_ok (FEquiv f g) = (bounds_ok f \<and> bounds_ok g)"
| "bounds_ok (FSince _ f g) = (bounds_ok f \<and> bounds_ok g)"
| "bounds_ok (FTrigger _ f g) = (bounds_ok f \<and> bounds_ok g)"
| "bounds_ok (FLet _ f g) = (bounds_ok f \<and> bounds_ok g)"
| "bounds_ok (FLetPast _ f g) = (bounds_ok f \<and> bounds_ok g)"
| "bounds_ok (FFrz _ f g) = (bounds_ok f \<and> bounds_ok g)"
| "bounds_ok (FEventually i f) = (ub_ok i \<and> bounds_ok f)"
| "bounds_ok (FAlways i f) = (ub_ok i \<and> bounds_ok f)"
| "bounds_ok (FFrex i r) = (ub_ok i \<and> bounds_ok_r r)"
| "bounds_ok (FUntil i f g) = (ub_ok i \<and> bounds_ok f \<and> bounds_ok g)"
| "bounds_ok (FRelease i f g) = (ub_ok i \<and> bounds_ok f \<and> bounds_ok g)"
| "bounds_ok _ = True"
| "bounds_ok_r (RTest f) = bounds_ok f"
| "bounds_ok_r (RConcat r s) = (bounds_ok_r r \<and> bounds_ok_r s)"
| "bounds_ok_r (RPlus r s) = (bounds_ok_r r \<and> bounds_ok_r s)"
| "bounds_ok_r (RStar r) = bounds_ok_r r"
| "bounds_ok_r (RSkip _) = True"

text \<open>The first predicate, in the order of MonPoly's type checker, that is neither declared nor bound.\<close>

definition oelse :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "oelse x y = (case x of None \<Rightarrow> y | Some _ \<Rightarrow> x)"

fun unknown_pred :: "(string \<times> nat) list \<Rightarrow> formula \<Rightarrow> (string \<times> nat) option"
and unknown_pred_r :: "(string \<times> nat) list \<Rightarrow> regex \<Rightarrow> (string \<times> nat) option" where
  "unknown_pred K (FPred (p, ts)) = (if (p, length ts) \<in> set K then None else Some (p, length ts))"
| "unknown_pred K (FLet (p, ts) f g) = oelse (unknown_pred K f) (unknown_pred ((p, length ts) # K) g)"
| "unknown_pred K (FLetPast (p, ts) f g) =
     oelse (unknown_pred ((p, length ts) # K) f) (unknown_pred ((p, length ts) # K) g)"
| "unknown_pred K (FFrz (p, ts) f g) = oelse (unknown_pred K f) (unknown_pred ((p, length ts) # K) g)"
| "unknown_pred K (FNeg f) = unknown_pred K f"
| "unknown_pred K (FExists _ f) = unknown_pred K f"
| "unknown_pred K (FForAll _ f) = unknown_pred K f"
| "unknown_pred K (FAggreg _ _ _ _ f) = unknown_pred K f"
| "unknown_pred K (FPrev _ f) = unknown_pred K f"
| "unknown_pred K (FNext _ f) = unknown_pred K f"
| "unknown_pred K (FEventually _ f) = unknown_pred K f"
| "unknown_pred K (FOnce _ f) = unknown_pred K f"
| "unknown_pred K (FAlways _ f) = unknown_pred K f"
| "unknown_pred K (FPastAlways _ f) = unknown_pred K f"
| "unknown_pred K (FAnd f g) = oelse (unknown_pred K f) (unknown_pred K g)"
| "unknown_pred K (FOr f g) = oelse (unknown_pred K f) (unknown_pred K g)"
| "unknown_pred K (FImplies f g) = oelse (unknown_pred K f) (unknown_pred K g)"
| "unknown_pred K (FEquiv f g) = oelse (unknown_pred K f) (unknown_pred K g)"
| "unknown_pred K (FSince _ f g) = oelse (unknown_pred K f) (unknown_pred K g)"
| "unknown_pred K (FTrigger _ f g) = oelse (unknown_pred K f) (unknown_pred K g)"
| "unknown_pred K (FUntil _ f g) = oelse (unknown_pred K f) (unknown_pred K g)"
| "unknown_pred K (FRelease _ f g) = oelse (unknown_pred K f) (unknown_pred K g)"
| "unknown_pred K (FFrex _ r) = unknown_pred_r K r"
| "unknown_pred K (FPrex _ r) = unknown_pred_r K r"
| "unknown_pred K _ = None"
| "unknown_pred_r K (RTest f) = unknown_pred K f"
| "unknown_pred_r K (RConcat r s) = oelse (unknown_pred_r K r) (unknown_pred_r K s)"
| "unknown_pred_r K (RPlus r s) = oelse (unknown_pred_r K r) (unknown_pred_r K s)"
| "unknown_pred_r K (RStar r) = unknown_pred_r K r"
| "unknown_pred_r K (RSkip _) = None"

definition input_error :: "schema \<Rightarrow> formula \<Rightarrow> string option" where
  "input_error S \<psi> = (if \<not> intervals_ok \<psi>
     then Some ''[Rewriting.check_wff] The formula contains a negative or empty interval''
     else if \<not> bounds_ok \<psi>
     then Some ''[Rewriting.check_wff] The formula contains an unbounded future temporal operator. It is hence not monitorable.''
     else map_option (\<lambda>(p, n). ''[Rewriting.check_syntax] unknown predicate '' @ p @ ''/'' @ dec_nat n @
       '' in input formula'') (unknown_pred (map (\<lambda>(p, fs). (p, length fs)) S) \<psi>))"

subsection \<open>Main program\<close>

text \<open>What the driver does next: exit with two texts and a code, print the version, read a file, or
  run the monitor on the log.\<close>

type_synonym otext = "string8 list"

definition otxt :: "string \<Rightarrow> otext" where
  "otxt s = [str8_of_string s]"

datatype step = Done otext otext nat | Version | NeedFile bytes "bytes \<Rightarrow> step"
  | Run otext config vconf vstate "nat option" nat lsig

text \<open>MonPoly adds the last time point only for formulas with future operators.\<close>

fun is_future :: "formula \<Rightarrow> bool"
and is_future_r :: "regex \<Rightarrow> bool" where
  "is_future (FNeg f) = is_future f"
| "is_future (FExists _ f) = is_future f"
| "is_future (FForAll _ f) = is_future f"
| "is_future (FAggreg _ _ _ _ f) = is_future f"
| "is_future (FPrev _ f) = is_future f"
| "is_future (FOnce _ f) = is_future f"
| "is_future (FPastAlways _ f) = is_future f"
| "is_future (FPrex _ r) = is_future_r r"
| "is_future (FAnd f g) = (is_future f \<or> is_future g)"
| "is_future (FOr f g) = (is_future f \<or> is_future g)"
| "is_future (FImplies f g) = (is_future f \<or> is_future g)"
| "is_future (FEquiv f g) = (is_future f \<or> is_future g)"
| "is_future (FSince _ f g) = (is_future f \<or> is_future g)"
| "is_future (FTrigger _ f g) = (is_future f \<or> is_future g)"
| "is_future (FLet _ f g) = (is_future f \<or> is_future g)"
| "is_future (FLetPast _ f g) = (is_future f \<or> is_future g)"
| "is_future (FFrz _ f g) = (is_future f \<or> is_future g)"
| "is_future (FNext _ _) = True"
| "is_future (FEventually _ _) = True"
| "is_future (FAlways _ _) = True"
| "is_future (FUntil _ _ _) = True"
| "is_future (FRelease _ _ _) = True"
| "is_future (FFrex _ _) = True"
| "is_future _ = False"
| "is_future_r (RTest f) = is_future f"
| "is_future_r (RConcat r s) = (is_future_r r \<or> is_future_r s)"
| "is_future_r (RPlus r s) = (is_future_r r \<or> is_future_r s)"
| "is_future_r (RStar r) = is_future_r r"
| "is_future_r (RSkip _) = False"

definition input_formula :: "config \<Rightarrow> formula \<Rightarrow> formula" where
  "input_formula conf \<psi> = (if c_negate conf then FNeg \<psi> else \<psi>)"

definition prep_msg :: "String.literal \<Rightarrow> otext" where
  "prep_msg e = [S8 STR ''Fatal error: exception Failure(\"Error during the verified preparation of the formula: '',
     string8_literal e, S8 STR ''\")'', S8 STR ''\<newline>'']"

text \<open>Converts the formula and starts the monitor, or reports why it cannot start, as MonPoly's
  front end does.\<close>

definition start_monitor :: "config \<Rightarrow> (bytes \<Rightarrow> double option) \<Rightarrow> formula \<Rightarrow> schema \<Rightarrow> step" where
  "start_monitor conf pf \<psi> S = (case input_error S \<psi> of
     Some e \<Rightarrow> Done [] (otxt (fatal_failure e @ nl)) 2
   | None \<Rightarrow> (case conv_formula pf (c_rw conf) \<psi> of
     Inl msg \<Rightarrow> Done [] (otxt (msg @ nl)) 2
   | Inr \<phi> \<Rightarrow> (case lsig_of S \<phi> of
       Inl msg \<Rightarrow> Done [] (otxt (msg @ nl)) 2
     | Inr L \<Rightarrow> (let vs = out_vars \<psi>; info = c_verbose conf \<or> c_check conf in
       (case check (lsig_tsig L) TAny \<phi> of
         Inl e \<Rightarrow> Done [] (prep_msg e) 2
       | Inr f \<Rightarrow>
         (case vinit (c_index conf) (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> of
           Inl VI_WF \<Rightarrow> Done [] (prep_msg STR ''the formula is not well-formed'') 2
         | Inl (VI_FRAGMENT n) \<Rightarrow> Done [] (otxt (fatal_failure ''the formula is outside the verified dense fragment'' @ nl)) 2
         | Inl (VI_PREPARE e) \<Rightarrow>
             let msg = (if info then otxt (fv_text vs) @ [if c_rw conf
                   then S8 STR ''The analyzed formula is NOT monitorable: ''
                   else S8 STR ''The formula is NOT monitorable: '',
                 string8_literal e, S8 STR ''\<newline>'']
               else otxt (''The formula is NOT monitorable. Use the -check or -verbose flags.'' @ nl)) in
             if c_sigout conf then Done (otxt (sigout_text vs f)) msg 0 else Done [] msg 0
         | Inr (cf, z) \<Rightarrow>
             let msg = otxt ((if info then fv_text vs else []) @
               (if c_rw conf then (if c_check conf then ''The analyzed formula is monitorable.'' @ nl else [])
                else if info then ''The formula is monitorable.'' @ nl else [])) in
             if c_sigout conf then Done (otxt (sigout_text vs f)) msg 0
             else if c_check conf then Done [] msg 0
             else Run msg conf cf z (if c_newlastts conf \<and> is_future \<psi> then Some ts_max else None) (length vs) L))))))"

definition cli_main :: "bytes \<Rightarrow> bytes list \<Rightarrow> (bytes \<Rightarrow> double option) \<Rightarrow> step" where
  "cli_main prog args pf = (case parse_command (string_of_bytes prog) (map string_of_bytes args) of
     CExit out e c \<Rightarrow> Done (otxt out) (otxt e) c
   | CRun conf \<Rightarrow>
       if c_version conf then Version
       else if c_formula conf = [] then Done [] (otxt (usage_string @ nl)) 2
       else NeedFile (bytes_of_string (c_formula conf)) (\<lambda>ftext.
         case parse_formula (string_of_bytes ftext) of
           None \<Rightarrow> Done [] (otxt (''[Main.main] Failed to parse formula file'' @ nl @
             fatal_failure ''[Main.main] the verified parser rejects the formula'' @ nl)) 2
         | Some \<psi>0 \<Rightarrow> let \<psi> = input_formula conf \<psi>0 in
             if c_sig conf = [] then Done [] (otxt (usage_string @ nl)) 2
             else NeedFile (bytes_of_string (c_sig conf)) (\<lambda>stext.
               case read_sig (string_of_bytes stext) of
                 Inl e \<Rightarrow> Done [] (otxt (sig_error_msg e @ nl)) 2
               | Inr S \<Rightarrow> start_monitor conf pf \<psi> S)))"

(*<*)
end
(*>*)

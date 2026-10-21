(*<*)
theory CLI
  imports Formula_Conv CLI_Output "MFODL_Parser.MFODL_Parser"
    "MFODL_Monitor_Exec.Log_Monitor_Online"
begin
(*>*)

section \<open>The verified monitor with MonPoly's command line\<close>

text \<open>
  This theory composes the verified parts into the monitor that the program @{text verimon}
  runs, with MonPoly's command line (theory @{theory VeriMon_CLI.CLI_Options}):

  \<^enum> the arguments are parsed (@{const parse_command});
  \<^enum> the formula file is parsed by the verified parser (@{const parse_formula}, session
    @{text MFODL_Parser}), and negated with @{text "-negate"};
  \<^enum> the signature file is read (@{const read_sig}, theory @{theory VeriMon_CLI.Signature});
  \<^enum> the formula is converted into the monitor's (@{const conv_formula}, theory
    @{theory VeriMon_CLI.Formula_Conv}), and the signature into the monitor's (@{text lsig_of});
  \<^enum> the monitor is started (@{const vinit}, theory @{theory MFODL_Monitor_Exec.Log_Monitor}),
    which type checks the formula and prepares it as VeriMon does;
  \<^enum> the log is read in chunks (@{const vfeed_chunk} and @{const vfinish}), and the verdicts are
    printed as MonPoly prints them (theory @{theory VeriMon_CLI.CLI_Output}).

  The decisions, and the order in which MonPoly's front end takes them, are those of
  @{text cli_main}: the driver only reads the files it asks for (@{text NeedFile}), prints what
  it says, and runs the loop over the log. The driver also locates the errors in the log and
  reports them, as for @{text "monpoly -verified"}.

  @{text verimon_correct} states the correctness of the whole: if @{text cli_main} starts the
  monitor on the contents of the formula and signature files, then the formula file is derived by
  the grammar of formulas from a formula @{text \<psi>}, the signature file by the grammar of
  signatures from a signature @{text S}, and for every log that denotes a prefix @{text \<pi>}, the
  monitor reports no error and its verdicts are exactly the satisfactions on @{text \<pi>} of the
  conversion of @{text \<psi>} (negated with @{text "-negate"}), as the semantics of MFODL defines
  them. @{text verimon_correct_online} states the same online, for the chunks of the log read so
  far and for each further chunk, as the driver runs the monitor.
\<close>

subsection \<open>The monitor's signature\<close>

text \<open>The signature as the monitor reads it (@{text Verified_adapter.lsig_of_schema}): the
  types of the arguments of each predicate. The monitor has no type of regular expressions: a
  formula with a predicate with such an argument is refused, and the arguments of the other such
  predicates are read as strings.\<close>

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

subsection \<open>Messages\<close>

definition str_of_ty :: "ty \<Rightarrow> string" where
  "str_of_ty t = (case t of TInt \<Rightarrow> ''int'' | TString \<Rightarrow> ''string'' | TFloat \<Rightarrow> ''float'')"

text \<open>@{text "-sigout"}: the free variables with their types (@{text Predicate.print_vartypes_list}),
  as the monitor's type checker infers them.\<close>

definition sigout_text :: "string list \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> string" where
  "sigout_text vs f = concat (between '', '' (map (\<lambda>(i, v). v @ '':'' @ str_of_ty (convert_tysym (f (TAny i))))
     (zip [0..<length vs] vs))) @ nl"

definition fv_text :: "string list \<Rightarrow> string" where
  "fv_text vs = ''The sequence of free variables is: ('' @ concat (between '','' vs) @ '')'' @ nl"

subsection \<open>MonPoly's checks of the input formula\<close>

text \<open>Before the conversion, MonPoly's front end checks the intervals and the bounds of the
  future operators (@{text Rewriting.check_wff}) and that the predicates are declared
  (@{text Rewriting.check_syntax}); the formula is that of the input, with its syntactic sugar.
  The checks of @{text LET} and of aggregations, whose messages print subformulas, are left to
  the conversion and to the verified type checker.\<close>

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

text \<open>The first predicate, in the order of MonPoly's type checker, that is neither declared nor
  bound by an enclosing @{text LET}, @{text LETPAST} (also in its definition) or @{text FRZ}.\<close>

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

subsection \<open>The main program\<close>

text \<open>What the driver does next: print the two texts (on standard output and on standard error)
  and exit with the code; print the version; read a file and continue with its contents; or print
  the text on standard error and run the monitor on the log, with the configuration, the
  monitor's configuration and state, the last time point to add at the end of the log, the number
  of free variables, and the signature.\<close>

type_synonym otext = "string8 list"

definition otxt :: "string \<Rightarrow> otext" where
  "otxt s = [str8_of_string s]"

datatype step = Done otext otext nat | Version | NeedFile bytes "bytes \<Rightarrow> step"
  | Run otext config vconf vstate "nat option" nat lsig

text \<open>MonPoly adds the last time point only for formulas with future operators
  (@{text Rewriting.is_future}).\<close>

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

text \<open>The formula of the input, negated with @{text "-negate"}.\<close>

definition input_formula :: "config \<Rightarrow> formula \<Rightarrow> formula" where
  "input_formula conf \<psi> = (if c_negate conf then FNeg \<psi> else \<psi>)"

text \<open>The message of a failure of the preparation, whose text is the type checker's.\<close>

definition prep_msg :: "String.literal \<Rightarrow> otext" where
  "prep_msg e = [S8 STR ''Fatal error: exception Failure(\"Error during the verified preparation of the formula: '',
     string8_literal e, S8 STR ''\")'', S8 STR ''\<newline>'']"

text \<open>After the signature is read: convert the formula and start the monitor, or report why it
  cannot start, as MonPoly's front end does. With @{text "-sigout"} the types of the free
  variables are printed; with @{text "-check"} whether the formula is monitorable (with
  @{text "-no_rw"}, also with @{text "-verbose"}, as MonPoly words it without rewriting).\<close>

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

text \<open>The main program, from the program name and the arguments.\<close>

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

subsection \<open>Correctness\<close>

text \<open>If the monitor starts on the contents of the two files, then they are a formula and a
  signature, and the monitor was started by @{const vinit} on the converted formula and the
  converted signature.\<close>

lemma cli_main_Run:
  assumes "cli_main prog args pf = NeedFile fn k1" "k1 ftext = NeedFile sn k2"
    and "k2 stext = Run msg conf cf z fin n L"
  obtains \<psi>0 S \<phi> f where "parse_formula (Rep_bytes ftext) = Some \<psi>0"
    and "read_sig (Rep_bytes stext) = Inr S"
    and "conv_formula pf (c_rw conf) (input_formula conf \<psi>0) = Inr \<phi>"
    and "lsig_of S \<phi> = Inr L"
    and "check (lsig_tsig L) TAny \<phi> = Inr f"
    and "vinit (c_index conf) (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> = Inr (cf, z)"
  using assms unfolding cli_main_def start_monitor_def Let_def
  by (auto split: command.splits if_splits option.splits sum.splits vinit_error.splits prod.splits)

text \<open>The main theorem: the monitor runs on the formula of the input and the signature, which
  satisfy the assumptions of @{locale verimon_log}. So for every log that denotes a prefix, the
  monitor reports no error and outputs the verdicts that the specification of the formula
  prescribes for the prefix (@{thm [source] verimon_log.vrun_log}, theory
  @{theory MFODL_Monitor_Exec.Log_Monitor_Online}), and an error on every log whose events of
  the formula's predicates denote no prefix (@{thm [source] verimon_log.vrun_filtered}).\<close>

theorem cli_run:
  assumes "cli_main prog args pf = NeedFile fn k1" "k1 ftext = NeedFile sn k2"
    and "k2 stext = Run msg conf cf z fin n L"
  obtains \<psi>0 S \<phi> where "parse_formula (Rep_bytes ftext) = Some \<psi>0"
    and "read_sig (Rep_bytes stext) = Inr S"
    and "conv_formula pf (c_rw conf) (input_formula conf \<psi>0) = Inr \<phi>"
    and "lsig_of S \<phi> = Inr L"
    and "vinit (c_index conf) (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> = Inr (cf, z)"
    and "verimon_log (c_rw conf) L \<phi>"
  using cli_main_Run[OF assms] vinit_verimon_log by metis

subsection \<open>End-to-end correctness\<close>

text \<open>The verdicts that the specification prescribes for a prefix @{text \<pi>}, for the formula
  @{text \<phi>} with the types @{text f} that the type checker infers for it and the signature
  @{text L}: the time points @{text i} up to the progress on @{text \<pi>}, with their timestamps,
  and the tuples @{text v} over the free variables of @{text \<phi>} such that @{text \<phi>} holds at
  @{text i} under @{text v} on every well-typed trace that extends @{text \<pi>}. The type annotations
  matter: an aggregation's decides, for example, whether a sum is an integer or a floating point
  sum.\<close>

definition verdict_spec :: "lsig \<Rightarrow> tysym Formula.formula \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> Formula.prefix \<Rightarrow>
    (nat \<times> nat \<times> event_data tuple) set" where
  "verdict_spec L \<phi> f \<pi> = {(i, pts \<pi> ! i, v) | i v. i < pprogress \<phi> \<pi> \<and> wf_tuple (Formula.fv_list \<phi>) v \<and>
     (\<forall>\<sigma>. wty_trace (lsig_lookup L) \<sigma> \<longrightarrow> prefix_of \<pi> \<sigma> \<longrightarrow>
       Formula.sat \<sigma> Map.empty (val (Formula.nfv \<phi>) (Formula.fv_list \<phi>) v) i
         (Formula.formula.map_formula (convert_tysym \<circ> f) \<phi>))}"

text \<open>The verdicts of the monitor's specification (@{text monitor_\<phi>.Mt}, theory
  @{theory MFODL_Monitor_Exec.Log_Monitor}) are those of @{const verdict_spec}.\<close>

context verimon_log
begin

interpretation monitor_\<phi>: future_bounded_mfodl "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>"
  "map_sig (convert_tysym o check_subst) (lsig_tsig S)" "convert_tysym o check_subst o TAny"
  using future_bounded_\<phi> by (auto simp: future_bounded_mfodl_def future_bounded_mfodl_axioms_def wty_mfodl_def)

lemma Mt_verdict_spec:
  assumes "check (lsig_tsig S) TAny \<phi> = Inr f"
  shows "monitor_\<phi>.Mt \<pi> = verdict_spec S \<phi> f \<pi>"
proof -
  have cs: "check_subst = f"
    using check_check_subst assms by simp
  have pp: "pprogress (Formula.formula.map_formula g \<phi>) = pprogress \<phi>" for g :: "tysym \<Rightarrow> ty"
    by (simp add: pprogress_def fun_eq_iff)
  show ?thesis
    unfolding monitor_\<phi>.Mt_def
    unfolding monitor_\<phi>.M_def
    unfolding monitor_\<phi>.traces_def
    unfolding map_sig_lsig
    unfolding cs
    by (auto simp: verdict_spec_def pp)
qed

end

text \<open>The correctness of the whole monitor, in terms of the specifications of its parts: if the
  program starts the monitor on the contents of the formula file and of the signature file, then

  \<^item> the formula file is lexed into a token sequence that the grammar of MonPoly's formulas
    derives (@{const mfodl_Formula}), and @{text \<psi>0} is the formula it denotes;
  \<^item> the signature file is lexed into a token sequence that the grammar of signatures derives
    (@{const sig_lang}), and @{text S} is the signature it denotes;
  \<^item> @{text \<phi>} is the conversion of @{text \<psi>0} (negated with @{text "-negate"}), @{text L} the
    signature of the monitor, and @{text f} the types that the type checker infers for
    @{text \<phi>};
  \<^item> the run on a log reports an error exactly when the log's events of the formula's predicates
    and of the predicates the signature does not declare (all events with
    @{text "-nofilterrel"}, @{const keep_spec}) denote no prefix; and
  \<^item> on a log that denotes a prefix @{text \<pi>}, its verdicts are exactly those that
    @{const verdict_spec} prescribes for @{text \<pi>}.

  The verdicts are those of @{const vrun}: the outputs of @{const vfeed_chunk} on the chunks of
  the log, however it is cut into chunks, and of @{const vfinish} at its end, which the driver
  prints with @{const verdict_out}.\<close>

theorem verimon_correct:
  assumes run: "cli_main prog args pf = NeedFile fn k1" "k1 ftext = NeedFile sn k2"
    "k2 stext = Run msg conf cf z fin n L"
  obtains w \<psi> \<psi>0 ds S \<phi> f where
    "lex (Rep_bytes ftext) = Some w" "mfodl_Formula w \<psi>" "postprocess \<psi> = Some \<psi>0"
    and "sig_lang (Rep_bytes stext) ds" "decls_schema ds base_schema = Inr S"
    and "conv_formula pf (c_rw conf) (input_formula conf \<psi>0) = Inr \<phi>"
    and "lsig_of S \<phi> = Inr L"
    and "check (lsig_tsig L) TAny \<phi> = Inr f"
    and "\<And>ss. has_verror (vrun cf fin z ss) \<longleftrightarrow>
      log_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L fin (concat (map Rep_bytes ss)) = None"
    and "\<And>ss \<pi>. log_prefix (\<lambda>_. True) (sf pf) L fin (concat (map Rep_bytes ss)) = Some \<pi> \<Longrightarrow>
      \<not> has_verror (vrun cf fin z ss) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (vrun cf fin z ss))) = verdict_spec L \<phi> f \<pi>"
proof -
  obtain \<psi>0 S \<phi> f where P: "parse_formula (Rep_bytes ftext) = Some \<psi>0"
    and R: "read_sig (Rep_bytes stext) = Inr S"
    and C: "conv_formula pf (c_rw conf) (input_formula conf \<psi>0) = Inr \<phi>"
    and Ls: "lsig_of S \<phi> = Inr L"
    and ch: "check (lsig_tsig L) TAny \<phi> = Inr f"
    and init: "vinit (c_index conf) (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> = Inr (cf, z)"
    using cli_main_Run[OF run] by metis
  obtain w \<psi> where W: "lex (Rep_bytes ftext) = Some w" "mfodl_Formula w \<psi>" "postprocess \<psi> = Some \<psi>0"
    using P unfolding parse_formula_Some_iff by blast
  obtain ds where D: "sig_lang (Rep_bytes stext) ds" "decls_schema ds base_schema = Inr S"
    using R unfolding read_sig_correct by blast
  interpret verimon_log "c_rw conf" L \<phi>
    using vinit_verimon_log[OF init] .
  have E: "has_verror (vrun cf fin z ss) \<longleftrightarrow>
      log_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L fin (concat (map Rep_bytes ss)) = None" for ss
    using vrun_filtered(1)[OF init] by blast
  have V: "\<not> has_verror (vrun cf fin z ss) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (vrun cf fin z ss))) = verdict_spec L \<phi> f \<pi>"
    if "log_prefix (\<lambda>_. True) (sf pf) L fin (concat (map Rep_bytes ss)) = Some \<pi>" for ss \<pi>
    using vrun_log[OF init that, unfolded Mt_verdict_spec[OF ch]] by blast
  show thesis
    using that[OF W D C Ls ch E V] .
qed

text \<open>The same online, as the driver runs the monitor: after the chunks @{text ss} read so far,

  \<^item> the outputs so far contain an error exactly when the bytes read so far, restricted to the
    events the monitor keeps, denote no prefix (@{const stream_prefix}; the last time point read
    is held back until the next begins);
  \<^item> if the bytes read so far denote a prefix @{text \<pi>}, the outputs so far contain no error, and
    their verdicts are exactly those of @{const verdict_spec} for @{text \<pi>};
  \<^item> the outputs of a further chunk, after which the bytes denote @{text \<pi>'}, contain no error,
    and their verdicts are exactly those of @{text \<pi>'} that are not those of @{text \<pi>}, so that
    every verdict is output once, as soon as the bytes that determine it have been read;
  \<^item> the outputs at the end of the log are those of the prefix that the whole log denotes, with
    the last time point @{text fin}, that are not those of @{text \<pi>}; and
  \<^item> a chunk, or the end of the log, after which the bytes no longer denote a prefix outputs an
    error.\<close>

theorem verimon_correct_online:
  assumes run: "cli_main prog args pf = NeedFile fn k1" "k1 ftext = NeedFile sn k2"
    "k2 stext = Run msg conf cf z fin n L"
  obtains w \<psi> \<psi>0 ds S \<phi> f where
    "lex (Rep_bytes ftext) = Some w" "mfodl_Formula w \<psi>" "postprocess \<psi> = Some \<psi>0"
    and "sig_lang (Rep_bytes stext) ds" "decls_schema ds base_schema = Inr S"
    and "conv_formula pf (c_rw conf) (input_formula conf \<psi>0) = Inr \<phi>"
    and "lsig_of S \<phi> = Inr L"
    and "check (lsig_tsig L) TAny \<phi> = Inr f"
    and "\<And>ss. has_verror (fst (vfeed_chunks cf ss z)) \<longleftrightarrow>
      stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) = None"
    and "\<And>ss \<pi>. stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi> \<Longrightarrow>
      \<not> has_verror (fst (vfeed_chunks cf ss z)) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunks cf ss z)))) = verdict_spec L \<phi> f \<pi>"
    and "\<And>ss c \<pi> \<pi>'. stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi> \<Longrightarrow>
      stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss) @ Rep_bytes c) = Some \<pi>' \<Longrightarrow>
      \<pi> \<le> \<pi>' \<and> \<not> has_verror (fst (vfeed_chunk cf c (snd (vfeed_chunks cf ss z)))) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunk cf c (snd (vfeed_chunks cf ss z)))))) =
        verdict_spec L \<phi> f \<pi>' - verdict_spec L \<phi> f \<pi>"
    and "\<And>ss \<pi> \<pi>'. stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi> \<Longrightarrow>
      log_prefix (\<lambda>_. True) (sf pf) L fin (concat (map Rep_bytes ss)) = Some \<pi>' \<Longrightarrow>
      \<not> has_verror (vfinish cf fin (snd (vfeed_chunks cf ss z))) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (vfinish cf fin (snd (vfeed_chunks cf ss z))))) =
        verdict_spec L \<phi> f \<pi>' - verdict_spec L \<phi> f \<pi>"
    and "\<And>ss c. stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) \<noteq> None \<Longrightarrow>
      stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss) @ Rep_bytes c) = None \<Longrightarrow>
      has_verror (fst (vfeed_chunk cf c (snd (vfeed_chunks cf ss z))))"
    and "\<And>ss. stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) \<noteq> None \<Longrightarrow>
      log_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L fin (concat (map Rep_bytes ss)) = None \<Longrightarrow>
      has_verror (vfinish cf fin (snd (vfeed_chunks cf ss z)))"
proof -
  obtain \<psi>0 S \<phi> f where P: "parse_formula (Rep_bytes ftext) = Some \<psi>0"
    and R: "read_sig (Rep_bytes stext) = Inr S"
    and C: "conv_formula pf (c_rw conf) (input_formula conf \<psi>0) = Inr \<phi>"
    and Ls: "lsig_of S \<phi> = Inr L"
    and ch: "check (lsig_tsig L) TAny \<phi> = Inr f"
    and init: "vinit (c_index conf) (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> = Inr (cf, z)"
    using cli_main_Run[OF run] by metis
  obtain w \<psi> where W: "lex (Rep_bytes ftext) = Some w" "mfodl_Formula w \<psi>" "postprocess \<psi> = Some \<psi>0"
    using P unfolding parse_formula_Some_iff by blast
  obtain ds where D: "sig_lang (Rep_bytes stext) ds" "decls_schema ds base_schema = Inr S"
    using R unfolding read_sig_correct by blast
  interpret verimon_log "c_rw conf" L \<phi>
    using vinit_verimon_log[OF init] .
  note M = Mt_verdict_spec[OF ch]
  note wf0 = wf_vstate_vinit[OF init]
  obtain ust0 where init': "vinit (c_index conf) (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> = Inr (cf, (einit, ust0, 0))"
    using wf0 unfolding wf_vstate_def by blast
  have p0: "stream_prefix (\<lambda>_. True) (sf pf) L [] = Some pnil"
    by (simp add: stream_prefix_def prefix_of_items_Nil)
  have E: "has_verror (fst (vfeed_chunks cf ss z)) \<longleftrightarrow>
      stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) = None" for ss
    using vfeed_chunks_online(1)[OF init, of ss] by (simp add: stream_prefix_def) (metis not_None_eq)
  have V: "\<not> has_verror (fst (vfeed_chunks cf ss z)) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunks cf ss z)))) = verdict_spec L \<phi> f \<pi>"
    if p: "stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi>" for ss \<pi>
  proof -
    obtain outs z' where v: "vfeed_chunks cf ss z = (outs, z')"
      by (cases "vfeed_chunks cf ss z")
    have p': "stream_prefix (\<lambda>_. True) (sf pf) L ([] @ concat (map Rep_bytes ss)) = Some \<pi>"
      using p by simp
    note O = vfeed_chunks_online_log[OF wf0 v p0 p']
    show ?thesis
      using O(1,4)[unfolded Mt_pnil[OF init'], unfolded M] by (simp add: v)
  qed
  have wfss: "wf_vstate (c_mw conf) (c_filter conf) pf cf (concat (map Rep_bytes ss))
      (pmap_\<Gamma> (\<lambda>D. D \<inter> {e. keep_spec (c_filter conf) \<phi> L (Rep_string8 (fst e))}) \<pi>)
      (snd (vfeed_chunks cf ss z))"
    if p: "stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi>" for ss \<pi>
  proof -
    obtain outs z' where v: "vfeed_chunks cf ss z = (outs, z')"
      by (cases "vfeed_chunks cf ss z")
    have p': "stream_prefix (\<lambda>_. True) (sf pf) L ([] @ concat (map Rep_bytes ss)) = Some \<pi>"
      using p by simp
    show ?thesis
      using vfeed_chunks_online_log(3)[OF wf0 v p0 p'] by (simp add: v)
  qed
  have Ch: "\<pi> \<le> \<pi>' \<and> \<not> has_verror (fst (vfeed_chunk cf c (snd (vfeed_chunks cf ss z)))) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (fst (vfeed_chunk cf c (snd (vfeed_chunks cf ss z)))))) =
        verdict_spec L \<phi> f \<pi>' - verdict_spec L \<phi> f \<pi>"
    if p: "stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi>"
      and p': "stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss) @ Rep_bytes c) = Some \<pi>'"
    for ss c \<pi> \<pi>'
  proof -
    obtain outs z' where s: "vfeed_chunk cf c (snd (vfeed_chunks cf ss z)) = (outs, z')"
      by (cases "vfeed_chunk cf c (snd (vfeed_chunks cf ss z))")
    note O = vfeed_chunk_online_log[OF wfss[OF p] s p p']
    show ?thesis
      using O(1,2,4)[unfolded M] by (simp add: s)
  qed
  have Fi: "\<not> has_verror (vfinish cf fin (snd (vfeed_chunks cf ss z))) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (vfinish cf fin (snd (vfeed_chunks cf ss z))))) =
        verdict_spec L \<phi> f \<pi>' - verdict_spec L \<phi> f \<pi>"
    if p: "stream_prefix (\<lambda>_. True) (sf pf) L (concat (map Rep_bytes ss)) = Some \<pi>"
      and p': "log_prefix (\<lambda>_. True) (sf pf) L fin (concat (map Rep_bytes ss)) = Some \<pi>'"
    for ss \<pi> \<pi>'
    using vfinish_online_log[OF wfss[OF p] p p', unfolded M] by simp
  have wfk: "\<exists>\<pi>. wf_vstate (c_mw conf) (c_filter conf) pf cf (concat (map Rep_bytes ss)) \<pi>
      (snd (vfeed_chunks cf ss z))"
    if p: "stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) \<noteq> None" for ss
  proof -
    obtain \<pi> where p': "stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L ([] @ concat (map Rep_bytes ss)) = Some \<pi>"
      using p by auto
    obtain outs z' where v: "vfeed_chunks cf ss z = (outs, z')"
      by (cases "vfeed_chunks cf ss z")
    show ?thesis
      using vfeed_chunks_online_step[OF wf0 v p'] by (auto simp: v)
  qed
  have ChE: "has_verror (fst (vfeed_chunk cf c (snd (vfeed_chunks cf ss z))))"
    if p: "stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) \<noteq> None"
      and p': "stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss) @ Rep_bytes c) = None"
    for ss c
  proof -
    obtain \<pi> where wf: "wf_vstate (c_mw conf) (c_filter conf) pf cf (concat (map Rep_bytes ss)) \<pi>
        (snd (vfeed_chunks cf ss z))"
      using wfk[OF p] by blast
    obtain outs z' where s: "vfeed_chunk cf c (snd (vfeed_chunks cf ss z)) = (outs, z')"
      by (cases "vfeed_chunk cf c (snd (vfeed_chunks cf ss z))")
    show ?thesis
      using vfeed_chunk_online(1)[OF wf s p'] by (simp add: s)
  qed
  have FiE: "has_verror (vfinish cf fin (snd (vfeed_chunks cf ss z)))"
    if p: "stream_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L (concat (map Rep_bytes ss)) \<noteq> None"
      and p': "log_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L fin (concat (map Rep_bytes ss)) = None"
    for ss
    using wfk[OF p] vfinish_online(1)[OF _ p'] by blast
  show thesis
    using that[OF W D C Ls ch E V Ch Fi ChE FiE] .
qed

(*<*)
end
(*>*)

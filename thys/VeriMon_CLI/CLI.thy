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
  them.
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
     if (\<exists>(p, fs) \<in> set S. str8_of_string p \<in> set used \<and> SRegexp \<in> snd ` set fs)
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
  variables are printed; with @{text "-check"} whether the formula is monitorable.\<close>

definition start_monitor :: "config \<Rightarrow> (bytes \<Rightarrow> double option) \<Rightarrow> formula \<Rightarrow> schema \<Rightarrow> step" where
  "start_monitor conf pf \<psi> S = (case conv_formula pf (c_rw conf) \<psi> of
     Inl msg \<Rightarrow> Done [] (otxt (msg @ nl)) 2
   | Inr \<phi> \<Rightarrow> (case lsig_of S \<phi> of
       Inl msg \<Rightarrow> Done [] (otxt (msg @ nl)) 2
     | Inr L \<Rightarrow> (let vs = out_vars \<psi>; info = c_verbose conf \<or> c_check conf in
       (case check (lsig_tsig L) TAny \<phi> of
         Inl e \<Rightarrow> Done [] (prep_msg e) 2
       | Inr f \<Rightarrow>
         (case vinit (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> of
           Inl VI_WF \<Rightarrow> Done [] (prep_msg STR ''the formula is not well-formed'') 2
         | Inl (VI_FRAGMENT n) \<Rightarrow> Done [] (otxt (fatal_failure ''the formula is outside the verified dense fragment'' @ nl)) 2
         | Inl (VI_PREPARE e) \<Rightarrow>
             let msg = (if info then otxt (fv_text vs) @ [S8 STR ''The analyzed formula is NOT monitorable: '',
                 string8_literal e, S8 STR ''\<newline>'']
               else otxt (''The formula is NOT monitorable. Use the -check or -verbose flags.'' @ nl)) in
             if c_sigout conf then Done (otxt (sigout_text vs f)) msg 0 else Done [] msg 0
         | Inr (cf, z) \<Rightarrow>
             let msg = otxt ((if info then fv_text vs else []) @
               (if c_check conf then ''The analyzed formula is monitorable.'' @ nl else [])) in
             if c_sigout conf then Done (otxt (sigout_text vs f)) msg 0
             else if c_check conf then Done [] msg 0
             else Run msg conf cf z (if c_newlastts conf \<and> is_future \<psi> then Some ts_max else None) (length vs) L)))))"

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
    and "vinit (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> = Inr (cf, z)"
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
    and "vinit (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> = Inr (cf, z)"
    and "verimon_log (c_rw conf) L \<phi>"
  using cli_main_Run[OF assms] vinit_verimon_log by metis

subsection \<open>End-to-end correctness\<close>

text \<open>The correctness of the whole monitor, in terms of the specifications of its parts: if the
  program starts the monitor on the contents of the formula file and of the signature file, then

  \<^enum> the formula file is lexed into a token sequence that the grammar of MonPoly's formulas
    derives (@{const mfodl_Formula}), and @{text \<psi>0} is the formula it denotes;
  \<^enum> the signature file is lexed into a token sequence that the grammar of signatures derives
    (@{const sig_lang}), and @{text S} is the signature it denotes;
  \<^enum> @{text \<phi>} is the conversion of @{text \<psi>0} (negated with @{text "-negate"}), @{text L} the
    signature of the monitor, and @{text f} the types that the type checker infers for
    @{text \<phi>};
  \<^enum> the run on a log reports an error exactly when the log's events of the formula's predicates
    and of the predicates the signature does not declare (all events with
    @{text "-nofilterrel"}, @{const keep_spec}) denote no prefix; and
  \<^enum> on a log that denotes a prefix @{text \<pi>}, its verdicts are exactly the time points
    @{text i} up to the progress on @{text \<pi>}, with their timestamps, and the tuples @{text v}
    over the free variables of @{text \<phi>} such that @{text \<phi>}, with the inferred types, holds at
    @{text i} under @{text v} on every well-typed trace that extends @{text \<pi>}.

  The verdicts are those of @{const vrun}, which the driver computes as the outputs of
  @{const vfeed_chunk} on the chunks of the log and of @{const vfinish} at its end, and prints
  with @{const verdict_out}.\<close>

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
      flatten_verdicts (vwiden \<phi> (vverdicts (vrun cf fin z ss))) =
        {(i, pts \<pi> ! i, v) | i v. i < pprogress \<phi> \<pi> \<and> wf_tuple (Formula.fv_list \<phi>) v \<and>
          (\<forall>\<sigma>. wty_trace (lsig_lookup L) \<sigma> \<longrightarrow> prefix_of \<pi> \<sigma> \<longrightarrow>
            Formula.sat \<sigma> Map.empty (val (Formula.nfv \<phi>) (Formula.fv_list \<phi>) v) i
              (Formula.formula.map_formula (convert_tysym \<circ> f) \<phi>))}"
proof -
  obtain \<psi>0 S \<phi> f where P: "parse_formula (Rep_bytes ftext) = Some \<psi>0"
    and R: "read_sig (Rep_bytes stext) = Inr S"
    and C: "conv_formula pf (c_rw conf) (input_formula conf \<psi>0) = Inr \<phi>"
    and Ls: "lsig_of S \<phi> = Inr L"
    and ch: "check (lsig_tsig L) TAny \<phi> = Inr f"
    and init: "vinit (c_mw conf) (c_rw conf) (c_filter conf) L pf \<phi> = Inr (cf, z)"
    using cli_main_Run[OF run] by metis
  obtain w \<psi> where W: "lex (Rep_bytes ftext) = Some w" "mfodl_Formula w \<psi>" "postprocess \<psi> = Some \<psi>0"
    using P unfolding parse_formula_Some_iff by blast
  obtain ds where D: "sig_lang (Rep_bytes stext) ds" "decls_schema ds base_schema = Inr S"
    using R unfolding read_sig_correct by blast
  interpret verimon_log "c_rw conf" L \<phi>
    using vinit_verimon_log[OF init] .
  have cs: "check_subst = f"
    using check_check_subst ch by simp
  have E: "has_verror (vrun cf fin z ss) \<longleftrightarrow>
      log_prefix (keep_spec (c_filter conf) \<phi> L) (sf pf) L fin (concat (map Rep_bytes ss)) = None" for ss
    using vrun_filtered(1)[OF init] by blast
  have V: "\<not> has_verror (vrun cf fin z ss) \<and>
      flatten_verdicts (vwiden \<phi> (vverdicts (vrun cf fin z ss))) =
        {(i, pts \<pi> ! i, v) | i v. i < pprogress \<phi> \<pi> \<and> wf_tuple (Formula.fv_list \<phi>) v \<and>
          (\<forall>\<sigma>. wty_trace (lsig_lookup L) \<sigma> \<longrightarrow> prefix_of \<pi> \<sigma> \<longrightarrow>
            Formula.sat \<sigma> Map.empty (val (Formula.nfv \<phi>) (Formula.fv_list \<phi>) v) i
              (Formula.formula.map_formula (convert_tysym \<circ> f) \<phi>))}"
    if "log_prefix (\<lambda>_. True) (sf pf) L fin (concat (map Rep_bytes ss)) = Some \<pi>" for ss \<pi>
  proof -
    have pp: "pprogress (Formula.formula.map_formula g \<phi>) = pprogress \<phi>" for g :: "tysym \<Rightarrow> ty"
      by (simp add: pprogress_def fun_eq_iff)
    interpret fb: future_bounded_mfodl "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>"
      "map_sig (convert_tysym o check_subst) (lsig_tsig L)" "convert_tysym o check_subst o TAny"
      using future_bounded_\<phi>
      by (auto simp: future_bounded_mfodl_def future_bounded_mfodl_axioms_def wty_mfodl_def)
    have X: "flatten_verdicts (vwiden \<phi> (vverdicts (vrun cf fin z ss))) = fb.Mt \<pi>"
      using vrun_log(2)[OF init that] by simp
    show ?thesis
      using vrun_log(1)[OF init that] X[unfolded fb.Mt_def, unfolded fb.M_def,
          unfolded fb.traces_def, unfolded map_sig_lsig, unfolded cs]
      by (auto simp: pp)
  qed
  show thesis
    using that[OF W D C Ls ch E V] .
qed

(*<*)
end
(*>*)

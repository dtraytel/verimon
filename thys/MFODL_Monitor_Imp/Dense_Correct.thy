(*<*)
theory Dense_Correct
  imports Dense_Eval "MFODL_Monitor_Devel.Correctness"
begin
(*>*)

section \<open>The dense monitor inherits the kernel's correctness theorems\<close>

subsection \<open>The trace's databases are well formed\<close>

lemma wf_db_mk_db:
  assumes f: "finite X"
  shows "wf_db (mk_db X)"
  unfolding wf_db_def
proof (intro allI impI)
  fix e ar and T :: "event_data table list"
  assume "Mapping.lookup (mk_db X) (e, ar) = Some T"
  then have T: "T = [map Some ` {ts. (e, ts) \<in> X \<and> ar = length ts}]"
    by (transfer fixing: e ar) (auto split: if_splits)
  have "{ts. (e, ts) \<in> X \<and> ar = length ts} \<subseteq> snd ` X" by force
  then have "finite {ts. (e, ts) \<in> X \<and> ar = length ts}"
    using f by (auto elim: finite_subset)
  then show "list_all (\<lambda>T. table ar {0..<ar} T \<and> finite T) T"
    unfolding T by (auto simp: table_def wf_tuple_def)
qed

text \<open>A prefix all of whose databases are finite -- what a log is.\<close>

lift_definition pfinite :: "Formula.prefix \<Rightarrow> bool" is "\<lambda>p. \<forall>x \<in> set p. finite (fst x)" .

subsection \<open>The concrete monitor is a @{locale verimon}\<close>

sublocale verimon_spec \<subseteq> dmon: verimon \<phi> SIG ENV
  valid_mmasaux "init_mmasaux :: _ \<Rightarrow> mmasaux" add_new_ts_mmasaux gc_join_mmasaux
    add_new_table_mmasaux result_mmasaux
  valid_muaux_dq "init_muaux_dq :: _ \<Rightarrow> muaux_dq" add_new_muaux_dq length_muaux_dq eval_muaux_dq
  valid_mmtaux init_mmtaux update_mmtaux result_mmtaux
  by unfold_locales


subsection \<open>The dense state machine\<close>

text \<open>
  The dense monitor's online interface mirrors the kernel's -- the record \<open>mstate\<close> and the
  function \<open>mstep\<close> -- field for field, with @{const deval} in place of @{const meval}.  The state
  additionally records the column list its verdicts are narrowed at.
\<close>

record dmstate =
  dmstate_i :: nat
  dmstate_j :: nat
  dmstate_m :: dformula
  dmstate_n :: nat
  dmstate_cs :: cols
  dmstate_t :: "ts list"

definition dmstep :: "database \<times> ts \<Rightarrow> dmstate \<Rightarrow>
    (nat \<times> ts \<times> event_data table) list \<times> dmstate" where
  "dmstep tdb st =
    (case deval (dmstate_j st + 1) [snd tdb] (fst tdb) (dmstate_m st) of
      (xs, m) \<Rightarrow> (List.enumerate (dmstate_i st) (zip (dmstate_t st @ [snd tdb]) xs),
        \<lparr> dmstate_i = dmstate_i st + length xs,
          dmstate_j = dmstate_j st + 1,
          dmstate_m = m,
          dmstate_n = dmstate_n st,
          dmstate_cs = dmstate_cs st,
          dmstate_t = drop (length xs) (dmstate_t st @ [snd tdb]) \<rparr>))"

primrec dmsteps0_stateless where
  "dmsteps0_stateless [] st = []"
| "dmsteps0_stateless (tdb # \<pi>) st =
    (let (V', st') = dmstep (apfst mk_db tdb) st in V' @ dmsteps0_stateless \<pi> st')"

lift_definition dmsteps_stateless :: "Formula.prefix \<Rightarrow> dmstate \<Rightarrow>
    (nat \<times> ts \<times> event_data table) list" is dmsteps0_stateless .

definition dmonitor :: "dmstate \<Rightarrow> Formula.prefix \<Rightarrow> (nat \<times> ts \<times> event_data table) list" where
  "dmonitor st \<pi> = dmsteps_stateless \<pi> st"


subsection \<open>The state relation\<close>

text \<open>
  Two states are related when their bookkeeping agrees and their formulas are related by
  @{const dsim} at the frame the state records, with the timestamp bound of @{const dsim} being
  the last timestamp the two have been fed.
\<close>

definition dmsim_state :: "nat \<Rightarrow> cols \<Rightarrow> ts \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) mstate \<Rightarrow>
    dmstate \<Rightarrow> bool" where
  "dmsim_state n cs tw st dst \<longleftrightarrow>
     dmstate_i dst = mstate_i st \<and> dmstate_j dst = mstate_j st \<and>
     dmstate_t dst = mstate_t st \<and> mstate_n st = n \<and> dmstate_n dst = n \<and>
     dmstate_cs dst = cs \<and> dsim n cs tw (dmstate_m dst) (mstate_m st)"

lemma enumerate_zip_map:
  "List.enumerate i (zip us (map f xs))
     = map (\<lambda>(k, u, X). (k, u, f X)) (List.enumerate i (zip us xs))"
  by (simp add: List.enumerate_eq_zip zip_map2 case_prod_beta)

subsection \<open>One step\<close>

lemma dmstep_mstep:
  assumes r: "dmsim_state n cs tw st dst" and w: "wf_db (fst tdb)" and le: "tw \<le> snd tdb"
  shows "fst (dmstep tdb dst)
       = map (\<lambda>(i, t, X). (i, t, dtabc n cs X)) (fst (mstep tdb st))
     \<and> dmsim_state n cs (snd tdb) (snd (mstep tdb st)) (snd (dmstep tdb dst))
     \<and> (\<forall>(i, t, X) \<in> set (fst (mstep tdb st)). table n (set cs) X)"
proof -
  have i: "dmstate_i dst = mstate_i st" and j: "dmstate_j dst = mstate_j st"
    and t: "dmstate_t dst = mstate_t st" and mn: "mstate_n st = n" and dn: "dmstate_n dst = n"
    and dcs: "dmstate_cs dst = cs" and sim: "dsim n cs tw (dmstate_m dst) (mstate_m st)"
    using r unfolding dmsim_state_def by auto
  obtain xs m where e: "meval (mstate_j st + 1) n [snd tdb] (fst tdb) (mstate_m st) = (xs, m)"
    by (cases "meval (mstate_j st + 1) n [snd tdb] (fst tdb) (mstate_m st)")
  obtain dm where d: "deval (mstate_j st + 1) [snd tdb] (fst tdb) (dmstate_m dst)
      = (map (dtabc n cs) xs, dm)"
    and sim': "dsim n cs (dnext tw [snd tdb]) dm m"
    using dsim_deval[OF sim w _ _ e] le by auto
  have tb: "list_all (ftable n (set cs)) xs"
    by (rule produces_tables[OF dsim_produces[OF sim] w e])
  have dnx: "dnext tw [snd tdb] = snd tdb" by (simp add: dnext_def)
  have E: "mstep tdb st = (List.enumerate (mstate_i st) (zip (mstate_t st @ [snd tdb]) xs),
      \<lparr> mstate_i = mstate_i st + length xs, mstate_j = mstate_j st + 1, mstate_m = m,
        mstate_n = n, mstate_t = drop (length xs) (mstate_t st @ [snd tdb]) \<rparr>)"
    unfolding default_maux.mstep_def using e mn by (simp del: drop_append)
  have D: "dmstep tdb dst = (List.enumerate (mstate_i st)
        (zip (mstate_t st @ [snd tdb]) (map (dtabc n cs) xs)),
      \<lparr> dmstate_i = mstate_i st + length xs, dmstate_j = mstate_j st + 1, dmstate_m = dm,
        dmstate_n = n, dmstate_cs = cs,
        dmstate_t = drop (length xs) (mstate_t st @ [snd tdb]) \<rparr>)"
    using d unfolding dmstep_def i j t dn dcs by simp
  show ?thesis
    unfolding E D fst_conv snd_conv
    using sim'[unfolded dnx] tb
    by (auto simp: dmsim_state_def enumerate_zip_map List.in_set_enumerate_eq list_all_iff
        set_zip)
qed


subsection \<open>The whole prefix\<close>

text \<open>
  The timestamp bound of @{const dsim} threads through the prefix: each step re-establishes it at
  the timestamp just consumed, and the prefix's own sortedness says the next one is no smaller.
  That is where the third input hypothesis of @{thm [source] dsim_deval} is discharged, once and
  for all.
\<close>

lemma dmsteps0_stateless_rel:
  "dmsim_state n cs tw st dst \<Longrightarrow> sorted (map snd \<pi>) \<Longrightarrow> (\<forall>x \<in> set \<pi>. tw \<le> snd x) \<Longrightarrow>
   (\<forall>x \<in> set \<pi>. finite (fst x)) \<Longrightarrow>
   dmsteps0_stateless \<pi> dst = map (\<lambda>(i, t, X). (i, t, dtabc n cs X)) (msteps0_stateless \<pi> st)
   \<and> (\<forall>(i, t, X) \<in> set (msteps0_stateless \<pi> st). table n (set cs) X)"
proof (induct \<pi> arbitrary: st dst tw)
  case Nil
  then show ?case by simp
next
  case (Cons tdb \<pi>)
  note IH = Cons(1) and r = Cons(2) and srt = Cons(3) and b = Cons(4) and fin = Cons(5)
  have w: "wf_db (fst (apfst mk_db tdb))" using fin by (simp add: wf_db_mk_db)
  have le: "tw \<le> snd (apfst mk_db tdb)" using b by simp
  have step: "fst (dmstep (apfst mk_db tdb) dst)
      = map (\<lambda>(i, t, X). (i, t, dtabc n cs X)) (fst (mstep (apfst mk_db tdb) st))"
    and r': "dmsim_state n cs (snd tdb) (snd (mstep (apfst mk_db tdb) st))
        (snd (dmstep (apfst mk_db tdb) dst))"
    and tb: "\<forall>(i, t, X) \<in> set (fst (mstep (apfst mk_db tdb) st)). table n (set cs) X"
    using dmstep_mstep[OF r w le] by simp_all
  have b': "\<forall>x \<in> set \<pi>. snd tdb \<le> snd x" using srt by simp
  have srt': "sorted (map snd \<pi>)" using srt by simp
  have fin': "\<forall>x \<in> set \<pi>. finite (fst x)" using fin by simp
  show ?case using IH[OF r' srt' b' fin'] step tb by (simp add: split_beta) blast
qed

lemma dmsteps_stateless_rel:
  assumes r: "dmsim_state n cs 0 st dst" and f: "pfinite \<pi>"
  shows "dmsteps_stateless \<pi> dst
       = map (\<lambda>(i, t, X). (i, t, dtabc n cs X)) (msteps_stateless \<pi> st)
     \<and> (\<forall>(i, t, X) \<in> set (msteps_stateless \<pi> st). table n (set cs) X)"
proof -
  have srt: "sorted (map snd (Rep_prefix \<pi>))" using Rep_prefix[of \<pi>] by simp
  have fin: "\<forall>x \<in> set (Rep_prefix \<pi>). finite (fst x)" using f by (simp add: pfinite.rep_eq)
  show ?thesis
    unfolding dmsteps_stateless.rep_eq default_maux.msteps_stateless.rep_eq
    by (rule dmsteps0_stateless_rel[OF r srt _ fin]) simp
qed

subsection \<open>The verdicts are the narrowing of the kernel's\<close>

theorem dmonitor_monitor:
  assumes "dmsim_state n cs 0 (minit_safe \<phi>) dst" and "pfinite \<pi>"
  shows "dmonitor dst \<pi> = map (\<lambda>(i, t, X). (i, t, dtabc n cs X)) (monitor \<phi> \<pi>)"
  using dmsteps_stateless_rel[OF assms]
  by (simp add: dmonitor_def default_maux.monitor_def)

text \<open>Widening the verdicts back recovers the kernel's exactly, because @{const dtabc} is a
  bijection on the tables of the frame (@{thm [source] dtabw_dtabc}) and the kernel's verdict
  tables live there.\<close>

lemma map_dtabw_dtabc:
  "sorted_wrt (<) cs \<Longrightarrow> \<forall>(i, t, X) \<in> set V. table n (set cs) X \<Longrightarrow>
   map (\<lambda>(i, t, X). (i, t, dtabw n cs X)) (map (\<lambda>(i, t, X). (i, t, dtabc n cs X)) V) = V"
  by (induct V) (auto simp: dtabw_dtabc)

theorem dmonitor_widen:
  assumes r: "dmsim_state n cs 0 (minit_safe \<phi>) dst" and s: "sorted_wrt (<) cs"
    and f: "pfinite \<pi>"
  shows "map (\<lambda>(i, t, X). (i, t, dtabw n cs X)) (dmonitor dst \<pi>) = monitor \<phi> \<pi>"
proof -
  have e: "dmonitor dst \<pi> = map (\<lambda>(i, t, X). (i, t, dtabc n cs X)) (monitor \<phi> \<pi>)"
    by (rule dmonitor_monitor[OF r f])
  have t: "\<forall>(i, t, X) \<in> set (monitor \<phi> \<pi>). table n (set cs) X"
    using dmsteps_stateless_rel[OF r f] by (simp add: default_maux.monitor_def)
  show ?thesis unfolding e by (rule map_dtabw_dtabc[OF s t])
qed


subsection \<open>The correctness theorems, transferred\<close>

text \<open>
  Nothing about the dense representation is left in these statements: they are the kernel's own
  collected results with @{const dmonitor} in place of the kernel's monitor and the verdict
  tables widened back.  The simulation is what carries them across, and the only thing it asks of
  the caller is a related initial state.
\<close>

context verimon_spec
begin

theorem dmonitor_mverdicts:
  assumes r: "dmsim_state n cs 0 (minit_safe \<phi>) dst" and s: "sorted_wrt (<) cs"
    and f: "pfinite \<pi>" and wty: "wty_prefix SIG \<pi>"
  shows "flatten_verdicts (map (\<lambda>(i, t, X). (i, t, dtabw n cs X)) (dmonitor dst \<pi>)) = Mt \<pi>"
  unfolding dmonitor_widen[OF r s f] Monitor_Impl.monitor_def
  by (rule dmon.monitor_mverdicts[OF wty])

theorem dmstep_mverdicts:
  assumes r: "dmsim_state n cs tw st dst" and s: "sorted_wrt (<) cs"
    and wf: "dmon.wf_mstate SIG ENV \<phi> \<pi> R st"
    and wtydb: "wty_db SIG (fst tdb)" and fin: "finite (fst tdb)"
    and le: "last_ts \<pi> \<le> snd tdb" and tle: "tw \<le> snd tdb"
    and restrict: "mem_restr R v"
  shows "(i, t, v) \<in> flatten_verdicts (map (\<lambda>(i, t, X). (i, t, dtabw n cs X))
        (fst (dmstep (apfst mk_db tdb) dst)))
     \<longleftrightarrow> (i, t, v) \<in> Mt (psnoc \<pi> tdb) - Mt \<pi>"
proof -
  have w: "wf_db (fst (apfst mk_db tdb))" using fin by (simp add: wf_db_mk_db)
  have tle': "tw \<le> snd (apfst mk_db tdb)" using tle by simp
  have step: "fst (dmstep (apfst mk_db tdb) dst)
      = map (\<lambda>(i, t, X). (i, t, dtabc n cs X)) (fst (mstep (apfst mk_db tdb) st))"
    and tb: "\<forall>(i, t, X) \<in> set (fst (mstep (apfst mk_db tdb) st)). table n (set cs) X"
    using dmstep_mstep[OF r w tle'] by simp_all
  have "map (\<lambda>(i, t, X). (i, t, dtabw n cs X)) (fst (dmstep (apfst mk_db tdb) dst))
      = fst (mstep (apfst mk_db tdb) st)"
    unfolding step by (rule map_dtabw_dtabc[OF s tb])
  then show ?thesis
    unfolding Monitor_Impl.mstep_def
    using dmon.mstep_mverdicts[OF wf wtydb le restrict] by simp
qed

end

(*<*)
end
(*>*)

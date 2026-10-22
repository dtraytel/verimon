(*<*)
theory Correct_Proof
  imports "Monitor_Exec.Correct" IEval_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



section \<open>The executable monitor inherits the kernel's correctness theorems\<close>

subsection \<open>The concrete monitor is a @{locale verimon}\<close>

sublocale verimon_spec \<subseteq> dmon: verimon \<phi> SIG ENV
  valid_mmasaux "init_mmasaux :: _ \<Rightarrow> mmasaux" add_new_ts_mmasaux gc_join_mmasaux
    add_new_table_mmasaux result_mmasaux
  valid_muaux_dq "init_muaux_dq :: _ \<Rightarrow> muaux_dq" add_new_muaux_dq length_muaux_dq eval_muaux_dq
  valid_mmtaux init_mmtaux update_mmtaux result_mmtaux bin_join mmulti_join
  by unfold_locales (simp_all del: bin_join.simps mmulti_join.simps add: bin_join_table mmulti_join_correct)


lemma eannotate_eq:
  "eannotate i tq vs acc = (i', tq', vs') \<Longrightarrow>
     i' = i + length vs \<and> Rep_mbuf_t tq' = drop (length vs) (Rep_mbuf_t tq) \<and>
     vs' = rev acc @ List.enumerate i (zip (Rep_mbuf_t tq) vs)"
proof (induct vs arbitrary: i tq acc i' tq' vs')
  case (Cons v vs)
  obtain a tq0 where h: "mbuf_t_cases tq = (a, tq0)" by (cases "mbuf_t_cases tq")
  show ?case
  proof (cases a)
    case None
    then show ?thesis using Cons(2) h by simp
  next
    case (Some t)
    have lt: "Rep_mbuf_t tq = t # Rep_mbuf_t tq0" using h Some by simp
    have step: "eannotate (i + 1) tq0 vs ((i, t, v) # acc) = (i', tq', vs')"
      using Cons(2) h Some by simp
    show ?thesis using Cons(1)[OF step] lt by simp
  qed
qed simp

lemma enumerate_zip_map:
  "List.enumerate i (zip us (map f xs))
     = map (\<lambda>(k, u, X). (k, u, f X)) (List.enumerate i (zip us xs))"
  by (simp add: List.enumerate_eq_zip zip_map2 case_prod_beta)

subsection \<open>One step\<close>

lemma emstep_mstep:
  assumes r: "emsim_state n ks cs tw st dst" and le: "tw \<le> snd tdb"
    and kg: "kgood n ks (mstate_j st + 1) [snd tdb] (fst tdb) (mstate_m st)"
  shows "fst (emstep tdb dst)
       = map (\<lambda>(i, t, X). (i, t, etabc ks cs X)) (fst (mstep tdb st))
     \<and> emsim_state n ks cs (snd tdb) (snd (mstep tdb st)) (snd (emstep tdb dst))
     \<and> (\<forall>(i, t, X) \<in> set (fst (mstep tdb st)). table ks X)"
proof -
  have i: "emstate_i dst = mstate_i st" and j: "emstate_j dst = mstate_j st"
    and t: "Rep_mbuf_t (emstate_t dst) = mstate_t st" and mn: "mstate_n st = n"
    and dn: "emstate_n dst = n"
    and dcs: "emstate_cs dst = cs" and sim: "esim n ks cs tw (eabs (emstate_m dst)) (mstate_m st)"
    using r unfolding emsim_state_def by auto
  obtain xs m where e: "meval (mstate_j st + 1) n [snd tdb] (fst tdb) (mstate_m st) = (xs, m)"
    by (cases "meval (mstate_j st + 1) n [snd tdb] (fst tdb) (mstate_m st)")
  obtain dm where d: "eeval (mstate_j st + 1) [snd tdb] (fst tdb) (eabs (emstate_m dst))
      = (map (etabc ks cs) xs, dm)"
    and sim': "esim n ks cs (enext tw [snd tdb]) dm m"
    using esim_deval[OF sim _ e] le kg by auto
  obtain ixs im where iev: "ieval [] (mstate_j st + 1) [snd tdb] (demb (fst tdb)) (emstate_m dst) = (ixs, im)"
    by (cases "ieval [] (mstate_j st + 1) [snd tdb] (demb (fst tdb)) (emstate_m dst)")
  have ixs: "map iset ixs = map (etabc ks cs) xs" and dm: "dm = eabs im"
    using ieval_eeval[OF iev] d by simp_all
  have tb: "list_all (ftable ks) xs"
    by (rule kgood_tables[OF kg e])
  have dnx: "enext tw [snd tdb] = snd tdb" by (simp add: enext_def)
  have E: "mstep tdb st = (List.enumerate (mstate_i st) (zip (mstate_t st @ [snd tdb]) xs),
      \<lparr> mstate_i = mstate_i st + length xs, mstate_j = mstate_j st + 1, mstate_m = m,
        mstate_n = n, mstate_t = drop (length xs) (mstate_t st @ [snd tdb]) \<rparr>)"
    unfolding default_maux.mstep_def using e mn by (simp del: drop_append)
  obtain i' tq vs where A: "eannotate (mstate_i st) (emstate_t dst @@ [snd tdb])
      (map (etabc ks cs) xs) [] = (i', tq, vs)"
    by (cases "eannotate (mstate_i st) (emstate_t dst @@ [snd tdb])
      (map (etabc ks cs) xs) []")
  have ie: "i' = mstate_i st + length xs"
    and te: "Rep_mbuf_t tq = drop (length xs) (mstate_t st @ [snd tdb])"
    and ve: "vs = List.enumerate (mstate_i st)
      (zip (mstate_t st @ [snd tdb]) (map (etabc ks cs) xs))"
    using eannotate_eq[OF A] by (simp_all add: mbuf_t_append.rep_eq t)
  have D: "emstep tdb dst = (vs,
      \<lparr> emstate_i = i', emstate_j = mstate_j st + 1, emstate_m = im,
        emstate_n = n, emstate_cs = cs, emstate_t = tq \<rparr>)"
    using iev ixs A unfolding emstep_def i j dn dcs by simp
  show ?thesis
    unfolding E D fst_conv snd_conv ie ve
    using sim'[unfolded dnx dm] tb te
    by (auto simp: emsim_state_def enumerate_zip_map List.in_set_enumerate_eq list_all_iff
        set_zip)
qed

lemma emsim_state_dframe: "emsim_state n ks cs tw st dst \<Longrightarrow> eframe ks cs"
  unfolding emsim_state_def by (auto dest: esim_dframe)


subsection \<open>The whole prefix\<close>

text \<open>
  The timestamp bound of @{const esim} is the last timestamp of the prefix read so far: each step
  re-establishes it at the timestamp just consumed, and the prefix's own sortedness says the next
  one is no smaller.  That is where the timestamp hypothesis of @{thm [source] esim_deval} is
  discharged, once and for all.  The kernel's invariant @{const kwf_mstate} threads through alongside: it
  makes every step a good call (@{thm [source] kgood_mstep}).
\<close>

lemma emsteps0_stateless_rel:
  "emsim_state n (Formula.fv_list \<phi>) cs (last_ts \<pi>0) st dst \<Longrightarrow> kwf_mstate S E \<phi> \<pi>0 R st \<Longrightarrow>
   sorted (map snd \<pi>) \<Longrightarrow> (\<forall>x \<in> set \<pi>. last_ts \<pi>0 \<le> snd x) \<Longrightarrow>
   (\<forall>x \<in> set \<pi>. finite (fst x) \<and> wty_db S (fst x)) \<Longrightarrow>
   emsteps0_stateless \<pi> dst = map (\<lambda>(i, t, X). (i, t, etabc (Formula.fv_list \<phi>) cs X)) (msteps0_stateless \<pi> st)
   \<and> (\<forall>(i, t, X) \<in> set (msteps0_stateless \<pi> st). table (Formula.fv_list \<phi>) X)"
proof (induct \<pi> arbitrary: st dst \<pi>0)
  case Nil
  then show ?case by simp
next
  case (Cons tdb \<pi>)
  note IH = Cons(1) and r = Cons(2) and wfm = Cons(3) and srt = Cons(4)
    and lt = Cons(5) and fin = Cons(6)
  have le': "last_ts \<pi>0 \<le> snd tdb" and ft: "finite (fst tdb)" and wtd: "wty_db S (fst tdb)"
    using lt fin by simp_all
  have le: "last_ts \<pi>0 \<le> snd (apfst mk_db tdb)" using le' by simp
  have mn: "mstate_n st = n" using r by (simp add: emsim_state_def)
  have kg: "kgood n (Formula.fv_list \<phi>) (mstate_j st + 1) [snd (apfst mk_db tdb)] (fst (apfst mk_db tdb))
      (mstate_m st)"
    using kgood_mstep[OF wfm wtd le' ft] mn by simp
  have step: "fst (emstep (apfst mk_db tdb) dst)
      = map (\<lambda>(i, t, X). (i, t, etabc (Formula.fv_list \<phi>) cs X)) (fst (mstep (apfst mk_db tdb) st))"
    and r': "emsim_state n (Formula.fv_list \<phi>) cs (snd tdb) (snd (mstep (apfst mk_db tdb) st))
        (snd (emstep (apfst mk_db tdb) dst))"
    and tb: "\<forall>(i, t, X) \<in> set (fst (mstep (apfst mk_db tdb) st)). table (Formula.fv_list \<phi>) X"
    using emstep_mstep[OF r le kg] by simp_all
  have wfm': "kwf_mstate S E \<phi> (psnoc \<pi>0 tdb) R (snd (mstep (apfst mk_db tdb) st))"
    by (rule kmaux_wf_mstate_mstep[OF wfm wtd le' ft])
  have b': "\<forall>x \<in> set \<pi>. snd tdb \<le> snd x" using srt by simp
  have lts: "last_ts (psnoc \<pi>0 tdb) = snd tdb"
    using le' by transfer (auto split: list.splits)
  have lt': "\<forall>x \<in> set \<pi>. last_ts (psnoc \<pi>0 tdb) \<le> snd x" using b' lts by simp
  have r'': "emsim_state n (Formula.fv_list \<phi>) cs (last_ts (psnoc \<pi>0 tdb))
      (snd (mstep (apfst mk_db tdb) st)) (snd (emstep (apfst mk_db tdb) dst))"
    using r' lts by simp
  have srt': "sorted (map snd \<pi>)" using srt by simp
  have fin': "\<forall>x \<in> set \<pi>. finite (fst x) \<and> wty_db S (fst x)" using fin by simp
  show ?case using IH[OF r'' wfm' srt' lt' fin'] step tb by (simp add: split_beta) blast
qed

lemma emsteps_stateless_rel:
  assumes r: "emsim_state n (Formula.fv_list \<phi>) cs 0 st dst"
    and wfm: "kwf_mstate S E \<phi> pnil R st" and f: "pfinite \<pi>" and wty: "wty_prefix S \<pi>"
  shows "emsteps_stateless \<pi> dst
       = map (\<lambda>(i, t, X). (i, t, etabc (Formula.fv_list \<phi>) cs X)) (msteps_stateless \<pi> st)
     \<and> (\<forall>(i, t, X) \<in> set (msteps_stateless \<pi> st). table (Formula.fv_list \<phi>) X)"
proof -
  have srt: "sorted (map snd (Rep_prefix \<pi>))" using Rep_prefix[of \<pi>] by simp
  have fin: "\<forall>x \<in> set (Rep_prefix \<pi>). finite (fst x) \<and> wty_db S (fst x)"
    using f wty by (simp add: pfinite.rep_eq wty_prefix.rep_eq)
  show ?thesis
    unfolding emsteps_stateless.rep_eq default_maux.msteps_stateless.rep_eq
    by (rule emsteps0_stateless_rel[OF _ wfm srt _ fin]) (use r in \<open>simp_all add: last_ts.rep_eq pnil.rep_eq\<close>)
qed

subsection \<open>The verdicts are the narrowing of the kernel's\<close>

lemma map_etabw_etabc:
  "eframe ks cs \<Longrightarrow> \<forall>(i, t, X) \<in> set V. table ks X \<Longrightarrow>
   map (\<lambda>(i, t, X). (i, t, etabw ks cs X)) (map (\<lambda>(i, t, X). (i, t, etabc ks cs X)) V) = V"
  by (induct V) (auto simp: etabw_dtabc)

context verimon_spec
begin

theorem emonitor_monitor:
  assumes r: "emsim_state n (Formula.fv_list \<phi>) cs 0 (minit_safe \<phi>) dst"
    and f: "pfinite \<pi>" and wty: "wty_prefix SIG \<pi>"
  shows "emonitor dst \<pi> = map (\<lambda>(i, t, X). (i, t, etabc (Formula.fv_list \<phi>) cs X)) (monitor \<phi> \<pi>)"
    and "\<forall>(i, t, X) \<in> set (monitor \<phi> \<pi>). table (Formula.fv_list \<phi>) X"
  using emsteps_stateless_rel[OF r kmaux_wf_mstate_minit_safe[OF well_typed monitorable] f wty]
  by (simp_all add: emonitor_def default_maux.monitor_def)

text \<open>Widening the verdicts back recovers the kernel's exactly, because @{const etabc} is a
  bijection on the tables of the frame (@{thm [source] etabw_dtabc}) and the kernel's verdict
  tables live there.\<close>

theorem emonitor_widen:
  assumes r: "emsim_state n (Formula.fv_list \<phi>) cs 0 (minit_safe \<phi>) dst"
    and f: "pfinite \<pi>" and wty: "wty_prefix SIG \<pi>"
  shows "map (\<lambda>(i, t, X). (i, t, etabw (Formula.fv_list \<phi>) cs X)) (emonitor dst \<pi>) = monitor \<phi> \<pi>"
  unfolding emonitor_monitor(1)[OF r f wty]
  by (rule map_etabw_etabc[OF emsim_state_dframe[OF r] emonitor_monitor(2)[OF r f wty]])

text \<open>
  Nothing about the executable representation is left in these statements: they are the kernel's own
  collected results with @{const emonitor} in place of the kernel's monitor and the verdict
  tables widened back.  The simulation is what carries them across, and the only thing it asks of
  the caller is a related initial state.
\<close>

theorem emonitor_mverdicts:
  assumes r: "emsim_state n (Formula.fv_list \<phi>) cs 0 (minit_safe \<phi>) dst"
    and f: "pfinite \<pi>" and wty: "wty_prefix SIG \<pi>"
  shows "flatten_verdicts (map (\<lambda>(i, t, X). (i, t, etabw (Formula.fv_list \<phi>) cs X)) (emonitor dst \<pi>)) = Mt \<pi>"
  unfolding emonitor_widen[OF r f wty] Monitor_Impl.monitor_def
  by (rule dmon.monitor_mverdicts[OF wty f])

theorem emstep_mverdicts:
  assumes r: "emsim_state n (Formula.fv_list \<phi>) cs (last_ts \<pi>) st dst"
    and wf: "dmon.wf_mstate SIG ENV \<phi> \<pi> R st"
    and wtydb: "wty_db SIG (fst tdb)" and fin: "finite (fst tdb)"
    and le: "last_ts \<pi> \<le> snd tdb"
    and restrict: "mem_restr R (Formula.fv_list \<phi>) v"
  shows "(i, t, v) \<in> flatten_verdicts (map (\<lambda>(i, t, X). (i, t, etabw (Formula.fv_list \<phi>) cs X))
        (fst (emstep (apfst mk_db tdb) dst)))
     \<longleftrightarrow> (i, t, v) \<in> Mt (psnoc \<pi> tdb) - Mt \<pi>"
proof -
  have tle': "last_ts \<pi> \<le> snd (apfst mk_db tdb)" using le by simp
  have mn: "mstate_n st = n" using r by (simp add: emsim_state_def)
  have kg: "kgood n (Formula.fv_list \<phi>) (mstate_j st + 1) [snd (apfst mk_db tdb)] (fst (apfst mk_db tdb))
      (mstate_m st)"
    using kgood_mstep[OF wf wtydb le fin] mn by simp
  have step: "fst (emstep (apfst mk_db tdb) dst)
      = map (\<lambda>(i, t, X). (i, t, etabc (Formula.fv_list \<phi>) cs X)) (fst (mstep (apfst mk_db tdb) st))"
    and tb: "\<forall>(i, t, X) \<in> set (fst (mstep (apfst mk_db tdb) st)). table (Formula.fv_list \<phi>) X"
    using emstep_mstep[OF r tle' kg] by simp_all
  have "map (\<lambda>(i, t, X). (i, t, etabw (Formula.fv_list \<phi>) cs X)) (fst (emstep (apfst mk_db tdb) dst))
      = fst (mstep (apfst mk_db tdb) st)"
    unfolding step by (rule map_etabw_etabc[OF emsim_state_dframe[OF r] tb])
  then show ?thesis
    unfolding Monitor_Impl.mstep_def
    using dmon.mstep_mverdicts[OF wf wtydb le restrict fin] by simp
qed

end

(*<*)
end
(*>*)

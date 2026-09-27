(*<*)
theory Dense_Let
  imports Dense_Match
begin
(*>*)

section \<open>Discharging @{const produces} for the recursive let and the freeze node\<close>

text \<open>
  The last two nodes both evaluate a subformula against databases they build themselves.  That
  costs nothing extra: @{const produces} quantifies over every well-formed database, so all that
  has to be shown is that the databases they build are well formed -- which they are, because
  the tables they store under the bound predicate are tables over the full frame, exactly what
  @{const wf_db} asks of a stored relation, and because emptying a database keeps it well formed.
\<close>

text \<open>
  The recursive let feeds the bound formula its own output until the fixpoint is reached or the
  step budget runs out.  Each round evaluates against a database in which the bound predicate
  holds the previous round's output and -- from the second round on -- everything else is empty,
  and at an empty batch of timestamps, so the bound the invariant carries does not move after
  the first round.  The guard that rejects a round in which the formula's size changed keeps the
  old state, which the invariant still covers because raising the bound is harmless.
\<close>

lemma letpast_meval0_ftable:
  "letpast_meval0 eval J i ys xs q ts db \<phi> = (zs, i', bo, \<phi>') \<Longrightarrow>
   snd q = m \<Longrightarrow>
   (\<And>ts' db' \<chi> zs' \<chi>' w. produces m {0..<m} w \<chi> \<Longrightarrow> wf_db db' \<Longrightarrow> sorted ts' \<Longrightarrow>
      (\<forall>t \<in> set ts'. w \<le> t) \<Longrightarrow> eval ts' db' \<chi> = (zs', \<chi>') \<Longrightarrow>
      list_all (ftable m {0..<m}) zs' \<and> produces m {0..<m} (dnext w ts') \<chi>') \<Longrightarrow>
   produces m {0..<m} v \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow> (\<forall>t \<in> set ts. v \<le> t) \<Longrightarrow>
   list_all (ftable m {0..<m}) ys \<Longrightarrow> list_all (ftable m {0..<m}) xs \<Longrightarrow>
   list_all (ftable m {0..<m}) zs \<and> (\<forall>y. bo = Some y \<longrightarrow> ftable m {0..<m} y) \<and>
     produces m {0..<m} (dnext v ts) \<phi>'"
proof (induct eval J i ys xs q ts db \<phi> arbitrary: zs i' bo \<phi>' v
    rule: letpast_meval0.induct)
  case (1 eval J i ys xs q ts db \<phi>)
  note IH = 1(1) and E = 1(2) and SQ = 1(3) and ST = 1(4) and P = 1(5) and W = 1(6)
    and S = 1(7) and B = 1(8) and LY = 1(9) and LX = 1(10)
  obtain ys' \<phi>2 where ev: "eval ts (Mapping.update q xs db) \<phi> = (ys', \<phi>2)"
    by (cases "eval ts (Mapping.update q xs db) \<phi>")
  have wu: "wf_db (Mapping.update q xs db)"
    by (rule wf_db_update'[OF W]) (use LX SQ in simp)
  have h: "list_all (ftable m {0..<m}) ys' \<and> produces m {0..<m} (dnext v ts) \<phi>2"
    by (rule ST[OF P wu S B ev])
  have ty: "list_all (ftable m {0..<m}) ys'" using h by simp
  have n2: "produces m {0..<m} (dnext v ts) \<phi>2" using h by simp
  show ?case
  proof (cases "size \<phi>2 \<noteq> size \<phi>")
    case True
    have "zs = [] \<and> bo = None \<and> \<phi>' = \<phi>"
      using E ev True by (simp add: letpast_meval0.simps)
    then show ?thesis using produces_mono[OF P dnext_ge[OF B]] by simp
  next
    case same: False
    show ?thesis
    proof (cases ys')
      case Nil
      have "zs = ys @ ys' \<and> bo = None \<and> \<phi>' = \<phi>2"
        using E ev same Nil by (simp add: letpast_meval0.simps)
      then show ?thesis using LY ty n2 by simp
    next
      case (Cons y r)
      show ?thesis
      proof (cases "J \<le> Suc (i + length xs)")
        case True
        have "zs = ys @ ys' \<and> bo = Some y \<and> \<phi>' = \<phi>2"
          using E ev same Cons True by (simp add: letpast_meval0.simps)
        then show ?thesis using LY ty n2 Cons by simp
      next
        case cont: False
        have e': "letpast_meval0 eval J (i + length xs) (ys @ ys') ys' q []
            (Mapping.map_values (\<lambda>_ _. []) db) \<phi>2 = (zs, i', bo, \<phi>')"
          using E ev same Cons cont by (simp add: letpast_meval0.simps)
        have "list_all (ftable m {0..<m}) zs \<and>
            (\<forall>y. bo = Some y \<longrightarrow> ftable m {0..<m} y) \<and>
            produces m {0..<m} (dnext (dnext v ts) []) \<phi>'"
          by (rule IH[OF ev[symmetric] refl same Cons cont e' SQ ST n2
              wf_db_map_values_empty]) (use LY ty in auto)
        then show ?thesis by (simp add: dnext_def)
      qed
    qed
  qed
qed

subsection \<open>The freeze node\<close>

lemma freeze_meval0_ftable:
  "freeze_meval0 eval k \<alpha>s = (ys, \<alpha>s') \<Longrightarrow>
   (\<And>\<alpha>. \<alpha> \<in> set \<alpha>s \<Longrightarrow> list_all (ftable n A) (fst (eval \<alpha>))) \<Longrightarrow>
   list_all (ftable n A) ys \<and> set \<alpha>s' \<subseteq> set \<alpha>s"
proof (induct eval k \<alpha>s arbitrary: ys \<alpha>s' rule: freeze_meval0.induct)
  case (1 eval k)
  then show ?case by simp
next
  case (2 eval k \<alpha> \<alpha>s)
  note IH = 2(1) and E = 2(2) and OPS = 2(3)
  obtain zs st where ev: "eval \<alpha> = (zs, st)" by (cases "eval \<alpha>")
  have tz: "list_all (ftable n A) zs" using OPS[of \<alpha>] ev by simp
  show ?case
  proof (cases "drop k zs")
    case Nil
    then show ?thesis using E ev by simp
  next
    case (Cons y r)
    obtain ws \<beta>s where e2: "freeze_meval0 eval (Suc k) \<alpha>s = (ws, \<beta>s)"
      by (cases "freeze_meval0 eval (Suc k) \<alpha>s")
    have "list_all (ftable n A) ws \<and> set \<beta>s \<subseteq> set \<alpha>s"
      by (rule IH[OF ev[symmetric] refl Cons e2]) (use OPS in auto)
    moreover have "ftable n A y" using tz Cons
      by (metis list.set_intros(1) list_all_iff set_drop_subset subsetD)
    moreover have "ys = y # ws" and "\<alpha>s' = \<beta>s" using E ev Cons e2 by auto
    ultimately show ?thesis by auto
  qed
qed

text \<open>
  The freeze node evaluates its body, and its replay base, against the database with the bound
  predicate empty; then the replay base once more per stored operand table, against a database
  in which the bound predicate holds that table over the window and everything else is empty;
  and finally the replay base against a database that moves the window forward with empty tables.
  Every one of those databases is well formed as soon as the stored tables are, so the body's own
  invariant applies to all of them; the states of the replays are discarded rather than threaded.
\<close>

lemma produces_MFrz:
  assumes p1: "produces m {0..<m} tw \<phi>" and p2: "produces n A tw \<psi>"
    and pa: "list_all (ftable m {0..<m}) \<alpha>s"
    and p3: "produces n A tw \<rho>" and pb: "list_all (ftable n A) rb"
    and p4: "lv \<noteq> None \<longrightarrow> produces n A tw \<rho>L"
  shows "produces n A tw (mformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po lv \<rho>L)"
proof (rule producesI[where X = "\<lambda>n' A' u \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<chi> \<eta> f0 f1 f2 as \<rho>' w' pR' tq' rb' lv' \<rho>L'.
       \<Phi> = mformula.MFrz p m \<chi> \<eta> f0 f1 f2 as \<rho>' w' pR' tq' rb' d po lv' \<rho>L' \<and>
       produces m {0..<m} u \<chi> \<and> produces n A u \<eta> \<and>
       list_all (ftable m {0..<m}) as \<and> produces n A u \<rho>' \<and> list_all (ftable n A) rb' \<and>
       (lv' \<noteq> None \<longrightarrow> produces n A u \<rho>L'))"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi> \<eta> f0 f1 f2 as \<rho>' w' pR' tq' rb' lv' \<rho>L'.
      mformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po lv \<rho>L =
        mformula.MFrz p m \<chi> \<eta> f0 f1 f2 as \<rho>' w' pR' tq' rb' d po lv' \<rho>L' \<and>
      produces m {0..<m} tw \<chi> \<and> produces n A tw \<eta> \<and>
      list_all (ftable m {0..<m}) as \<and> produces n A tw \<rho>' \<and> list_all (ftable n A) rb' \<and>
      (lv' \<noteq> None \<longrightarrow> produces n A tw \<rho>L'))"
    using p1 p2 pa p3 pb p4 by blast
next
  fix n' A' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and>
      (\<exists>\<chi> \<eta> f0 f1 f2 as \<rho>' w' pR' tq' rb' lv' \<rho>L'.
         \<Phi> = mformula.MFrz p m \<chi> \<eta> f0 f1 f2 as \<rho>' w' pR' tq' rb' d po lv' \<rho>L' \<and>
         produces m {0..<m} u \<chi> \<and> produces n A u \<eta> \<and>
         list_all (ftable m {0..<m}) as \<and> produces n A u \<rho>' \<and> list_all (ftable n A) rb' \<and>
         (lv' \<noteq> None \<longrightarrow> produces n A u \<rho>L'))"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>v \<in> set ts. u \<le> v"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> \<eta> f0 f1 f2 as \<rho>' w' pR' tq' rb' lv' \<rho>L' where
    Phi: "\<Phi> = mformula.MFrz p m \<chi> \<eta> f0 f1 f2 as \<rho>' w' pR' tq' rb' d po lv' \<rho>L'"
    and pc: "produces m {0..<m} u \<chi>" and pe: "produces n A u \<eta>"
    and la: "list_all (ftable m {0..<m}) as" and pr: "produces n A u \<rho>'"
    and lb: "list_all (ftable n A) rb'" and pL: "lv' \<noteq> None \<longrightarrow> produces n A u \<rho>L'" by blast
  let ?dbe = "Mapping.map_values (\<lambda>_ _. []) db"
  obtain bs \<chi>' where e1: "meval j m ts db \<chi> = (bs, \<chi>')" by (cases "meval j m ts db \<chi>")
  have tb: "list_all (ftable m {0..<m}) bs" by (rule produces_tables[OF pc w sts mts e1])
  have nc: "produces m {0..<m} (dnext u ts) \<chi>'" by (rule produces_next[OF pc w sts mts e1])
  have w0: "wf_db (Mapping.update (p, m) [] db)" by (rule wf_db_update[OF w]) simp
  obtain zs0 \<eta>' where e2: "meval j n ts (Mapping.update (p, m) [] db) \<eta> = (zs0, \<eta>')"
    by (cases "meval j n ts (Mapping.update (p, m) [] db) \<eta>")
  have tz0: "list_all (ftable n A) zs0" by (rule produces_tables[OF pe w0 sts mts e2])
  have ne: "produces n A (dnext u ts) \<eta>'" by (rule produces_next[OF pe w0 sts mts e2])
  obtain rs \<rho>1 where e4: "meval j n ts (Mapping.update (p, m) [] db) \<rho>' = (rs, \<rho>1)"
    by (cases "meval j n ts (Mapping.update (p, m) [] db) \<rho>'")
  have trs: "list_all (ftable n A) rs" by (rule produces_tables[OF pr w0 sts mts e4])
  have nr: "produces n A (dnext u ts) \<rho>1" by (rule produces_next[OF pr w0 sts mts e4])
  have wa: "wf_db (Mapping.update (p, m) (replicate k \<alpha>) ?dbe)" if "ftable m {0..<m} \<alpha>" for k \<alpha>
    by (rule wf_db_update[OF wf_db_map_values_empty]) (use that in \<open>simp add: list_all_iff\<close>)
  define zout where "zout = drop (f0 - f1) zs0"
  define as1 where "as1 = drop (f0 - f2 + length zout) (as @ bs)"
  define rb0 where "rb0 = pR' - length rb'"
  define c where "c = frz_cut po w' f2 (length bs) j"
  define ev where "ev = (\<lambda>\<alpha>. case meval j n [] (Mapping.update (p, m) (replicate c \<alpha>) ?dbe) \<rho>1 of
    (us, \<sigma>) \<Rightarrow> ((rb' @ rs) @ us, \<sigma>))"
  have tzout: "list_all (ftable n A) zout"
    using tz0 by (auto simp: zout_def list_all_iff dest: set_drop_subset[THEN subsetD])
  have las1: "list_all (ftable m {0..<m}) as1"
    using la tb by (auto simp: as1_def list_all_iff dest: set_drop_subset[THEN subsetD])
  have evt: "list_all (ftable n A) (fst (ev \<alpha>)) \<and> produces n A (dnext u ts) (snd (ev \<alpha>))"
    if a: "\<alpha> \<in> set as1" for \<alpha>
  proof -
    have ta: "ftable m {0..<m} \<alpha>" using a las1 by (simp add: list_all_iff)
    obtain cs st where ec: "meval j n [] (Mapping.update (p, m) (replicate c \<alpha>) ?dbe) \<rho>1 = (cs, st)"
      by (cases "meval j n [] (Mapping.update (p, m) (replicate c \<alpha>) ?dbe) \<rho>1")
    have "list_all (ftable n A) cs"
      by (rule produces_tables[OF nr wa[OF ta] _ _ ec]) simp_all
    moreover have "produces n A (dnext u ts) st"
      using produces_next[OF nr wa[OF ta] _ _ ec] by (simp add: dnext_def)
    ultimately show ?thesis using ec lb trs by (simp add: ev_def)
  qed
  define dbL where "dbL = Mapping.update (p, m) (replicate (length ts) (hd as1)) db"
  define lr where "lr = (case lv' of None \<Rightarrow> None | Some g \<Rightarrow>
    if zout = [] \<and> as1 \<noteq> [] then Some (g, meval j n ts dbL \<rho>L') else None)"
  have lrt: "list_all (ftable n A) us \<and> produces n A (dnext u ts) st" if "lr = Some (g, us, st)" for g us st
  proof -
    from that have lv: "lv' \<noteq> None" and cond: "as1 \<noteq> []" and eL: "meval j n ts dbL \<rho>L' = (us, st)"
      by (auto simp: lr_def split: option.splits if_splits)
    have wL: "wf_db dbL"
      unfolding dbL_def
      by (rule wf_db_update[OF w]) (use las1 cond in \<open>auto simp: list_all_iff dest: hd_in_set\<close>)
    show ?thesis
      using produces_step[OF pL[rule_format, OF lv] wL sts mts eL] by blast
  qed
  obtain ys as' lv1 where e3: "frz_live_step ev (f0 + length zout - rb0) as1 lr = (ys, as', lv1)"
    by (metis prod_cases3)
  have tys: "list_all (ftable n A) ys"
    unfolding list_all_iff
  proof
    fix x
    assume "x \<in> set ys"
    with frz_live_step_set[OF e3] have "x \<in> (\<Union>\<alpha> \<in> set as1. set (fst (ev \<alpha>))) \<or>
        (\<exists>g us st. lr = Some (g, us, st) \<and> x \<in> set us)"
      by (auto split: option.splits)
    then show "ftable n A x"
      using evt lrt by (fastforce simp: list_all_iff)
  qed
  have las': "list_all (ftable m {0..<m}) as'"
    using frz_live_step_sub[OF e3] las1 by (auto simp: list_all_iff)
  let ?lvp = "if po then None else lv1"
  have pL': "frz_keep_lv ?lvp \<rho>L' \<noteq> None \<longrightarrow> produces n A (dnext u ts) (frz_keep_st ?lvp \<rho>L')"
  proof
    assume "frz_keep_lv ?lvp \<rho>L' \<noteq> None"
    then obtain g st where lv1: "lv1 = Some (g, st)" and st: "frz_keep_st ?lvp \<rho>L' = st"
      by (auto simp: frz_keep_lv_def frz_keep_st_def split: if_splits option.splits)
    from frz_live_step_state[OF e3[unfolded lv1]]
    show "produces n A (dnext u ts) (frz_keep_st ?lvp \<rho>L')"
      unfolding st using evt lrt by fastforce
  qed
  define tq1 where "tq1 = (if d = \<infinity> then [] else tq' @ ts)"
  define a where "a = frz_adv d w' (f0 + length zout + length ys) j tq1"
  obtain rs2 \<rho>2 where e5: "meval j n [] (Mapping.update (p, m) (replicate a {}) ?dbe) \<rho>1 = (rs2, \<rho>2)"
    by (cases "meval j n [] (Mapping.update (p, m) (replicate a {}) ?dbe) \<rho>1")
  have trs2: "list_all (ftable n A) rs2"
    by (rule produces_tables[OF nr wa[of "{}"] _ _ e5]) (simp_all add: table_def)
  have nr2: "produces n A (dnext u ts) \<rho>2"
    using produces_next[OF nr wa[of "{}"] _ _ e5] by (simp add: dnext_def table_def)
  define rb2 where "rb2 = drop (min (f0 + length zout + length ys) (pR' + length rs + length rs2) - rb0)
    ((rb' @ rs) @ rs2)"
  have trb2: "list_all (ftable n A) rb2"
    using lb trs trs2 by (auto simp: rb2_def list_all_iff dest: set_drop_subset[THEN subsetD])
  have m: "meval j n ts db (mformula.MFrz p m \<chi> \<eta> f0 f1 f2 as \<rho>' w' pR' tq' rb' d po lv' \<rho>L')
      = (zout @ ys, mformula.MFrz p m \<chi>' \<eta>' (f0 + length zout + length ys)
          (f1 + length zs0) (f2 + length bs) as' \<rho>2 (w' + a) (pR' + length rs + length rs2)
          (drop a tq1) rb2 d po (frz_keep_lv ?lvp \<rho>L') (frz_keep_st ?lvp \<rho>L'))"
    using e1 e2 e3 e4 e5 unfolding zout_def as1_def ev_def rb0_def tq1_def a_def rb2_def c_def lr_def dbL_def
    by (simp add: Let_def add.assoc)
  have x: "xs = zout @ ys"
    and f: "\<Phi>' = mformula.MFrz p m \<chi>' \<eta>' (f0 + length zout + length ys)
          (f1 + length zs0) (f2 + length bs) as' \<rho>2 (w' + a) (pR' + length rs + length rs2)
          (drop a tq1) rb2 d po (frz_keep_lv ?lvp \<rho>L') (frz_keep_st ?lvp \<rho>L')"
    using e[unfolded Phi conjunct1[OF X] m] by simp_all
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and>
          (\<exists>\<chi> \<eta> f0 f1 f2 as \<rho>' w' pR' tq' rb' lv' \<rho>L'.
             \<Phi>' = mformula.MFrz p m \<chi> \<eta> f0 f1 f2 as \<rho>' w' pR' tq' rb' d po lv' \<rho>L' \<and>
             produces m {0..<m} (dnext u ts) \<chi> \<and> produces n A (dnext u ts) \<eta> \<and>
             list_all (ftable m {0..<m}) as \<and> produces n A (dnext u ts) \<rho>' \<and> list_all (ftable n A) rb' \<and>
             (lv' \<noteq> None \<longrightarrow> produces n A (dnext u ts) \<rho>L'))) \<or>
       produces n' A' (dnext u ts) \<Phi>')"
    using X tzout tys nc ne las' nr2 trb2 pL' by (auto simp: x f)
qed

subsection \<open>The recursive let node\<close>

lemma produces_MLetPast:
  assumes p1: "produces m {0..<m} tw \<phi>" and p2: "produces n A tw \<psi>"
    and bo: "\<forall>y. buf = Some y \<longrightarrow> ftable m {0..<m} y"
  shows "produces n A tw (mformula.MLetPast p m \<phi> \<psi> i buf)"
proof (rule producesI[where X = "\<lambda>n' A' u \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<chi> \<eta> k bo. \<Phi> = mformula.MLetPast p m \<chi> \<eta> k bo \<and>
       produces m {0..<m} u \<chi> \<and> produces n A u \<eta> \<and>
       (\<forall>y. bo = Some y \<longrightarrow> ftable m {0..<m} y))"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi> \<eta> k bo'. mformula.MLetPast p m \<phi> \<psi> i buf
      = mformula.MLetPast p m \<chi> \<eta> k bo' \<and>
      produces m {0..<m} tw \<chi> \<and> produces n A tw \<eta> \<and>
      (\<forall>y. bo' = Some y \<longrightarrow> ftable m {0..<m} y))"
    using p1 p2 bo by blast
next
  fix n' A' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and>
      (\<exists>\<chi> \<eta> k bo. \<Phi> = mformula.MLetPast p m \<chi> \<eta> k bo \<and>
         produces m {0..<m} u \<chi> \<and> produces n A u \<eta> \<and>
         (\<forall>y. bo = Some y \<longrightarrow> ftable m {0..<m} y))"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>v \<in> set ts. u \<le> v"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> \<eta> k bo where Phi: "\<Phi> = mformula.MLetPast p m \<chi> \<eta> k bo"
    and pc: "produces m {0..<m} u \<chi>" and pe: "produces n A u \<eta>"
    and lbo: "\<forall>y. bo = Some y \<longrightarrow> ftable m {0..<m} y" by blast
  obtain bs k' bo' \<chi>' where e1: "letpast_meval m j k []
      (list_of_option bo) (p, m) ts db \<chi> = (bs, k', bo', \<chi>')"
    by (cases "letpast_meval m j k [] (list_of_option bo) (p, m) ts db \<chi>") auto
  have e1': "letpast_meval0 (meval j m) j k [] (list_of_option bo) (p, m) ts db \<chi>
      = (bs, k', bo', \<chi>')" using e1 by (simp add: default_maux.letpast_meval_def)
  have ST: "\<And>ts' db' \<xi> zs' \<xi>' v. produces m {0..<m} v \<xi> \<Longrightarrow> wf_db db' \<Longrightarrow>
      sorted ts' \<Longrightarrow> (\<forall>t \<in> set ts'. v \<le> t) \<Longrightarrow> meval j m ts' db' \<xi> = (zs', \<xi>') \<Longrightarrow>
      list_all (ftable m {0..<m}) zs' \<and> produces m {0..<m} (dnext v ts') \<xi>'"
    by (rule produces_step)
  have lbl: "list_all (ftable m {0..<m}) (list_of_option bo)"
    using lbo by (cases bo) auto
  have lp: "list_all (ftable m {0..<m}) bs \<and>
      (\<forall>y. bo' = Some y \<longrightarrow> ftable m {0..<m} y) \<and>
      produces m {0..<m} (dnext u ts) \<chi>'"
    by (rule letpast_meval0_ftable[OF e1' _ ST pc w sts mts _ lbl]) simp_all
  have tb: "list_all (ftable m {0..<m}) bs" using lp by simp
  have w2: "wf_db (Mapping.update (p, m) bs db)" by (rule wf_db_update[OF w tb])
  obtain cs \<eta>' where e2: "meval j n ts (Mapping.update (p, m) bs db) \<eta> = (cs, \<eta>')"
    by (cases "meval j n ts (Mapping.update (p, m) bs db) \<eta>")
  have tc: "list_all (ftable n A) cs" by (rule produces_tables[OF pe w2 sts mts e2])
  have ne: "produces n A (dnext u ts) \<eta>'" by (rule produces_next[OF pe w2 sts mts e2])
  have x: "xs = cs" and f: "\<Phi>' = mformula.MLetPast p m \<chi>' \<eta>' k' bo'"
    using e X Phi e1 e2 by simp_all
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and>
          (\<exists>\<chi> \<eta> k bo. \<Phi>' = mformula.MLetPast p m \<chi> \<eta> k bo \<and>
             produces m {0..<m} (dnext u ts) \<chi> \<and> produces n A (dnext u ts) \<eta> \<and>
             (\<forall>y. bo = Some y \<longrightarrow> ftable m {0..<m} y))) \<or>
       produces n' A' (dnext u ts) \<Phi>')"
    using X tc ne lp by (auto simp: x f)
qed

(*<*)
end
(*>*)

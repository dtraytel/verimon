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
  The freeze node evaluates its body once against the database with the bound predicate empty,
  and then once more per stored operand table, each time against a database in which the bound
  predicate holds that table and everything else is empty.  Every one of those databases is well
  formed as soon as the stored tables are, so the body's own invariant applies to all of them,
  and the states the repeated evaluations produce are discarded rather than threaded.
\<close>

lemma produces_MFrz:
  assumes p1: "produces m {0..<m} tw \<phi>" and p2: "produces n A tw \<psi>"
    and pa: "list_all (ftable m {0..<m}) \<alpha>s"
  shows "produces n A tw (mformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s)"
proof (rule producesI[where X = "\<lambda>n' A' u \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<chi> \<eta> f0 f1 f2 as. \<Phi> = mformula.MFrz p m \<chi> \<eta> f0 f1 f2 as \<and>
       produces m {0..<m} u \<chi> \<and> produces n A u \<eta> \<and>
       list_all (ftable m {0..<m}) as)"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi> \<eta> f0 f1 f2 as.
      mformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s = mformula.MFrz p m \<chi> \<eta> f0 f1 f2 as \<and>
      produces m {0..<m} tw \<chi> \<and> produces n A tw \<eta> \<and>
      list_all (ftable m {0..<m}) as)"
    using p1 p2 pa by blast
next
  fix n' A' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and>
      (\<exists>\<chi> \<eta> f0 f1 f2 as. \<Phi> = mformula.MFrz p m \<chi> \<eta> f0 f1 f2 as \<and>
         produces m {0..<m} u \<chi> \<and> produces n A u \<eta> \<and>
         list_all (ftable m {0..<m}) as)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>v \<in> set ts. u \<le> v"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> \<eta> f0 f1 f2 as where Phi: "\<Phi> = mformula.MFrz p m \<chi> \<eta> f0 f1 f2 as"
    and pc: "produces m {0..<m} u \<chi>" and pe: "produces n A u \<eta>"
    and la: "list_all (ftable m {0..<m}) as" by blast
  obtain bs \<chi>' where e1: "meval j m ts db \<chi> = (bs, \<chi>')" by (cases "meval j m ts db \<chi>")
  have tb: "list_all (ftable m {0..<m}) bs" by (rule produces_tables[OF pc w sts mts e1])
  have nc: "produces m {0..<m} (dnext u ts) \<chi>'" by (rule produces_next[OF pc w sts mts e1])
  have w0: "wf_db (Mapping.update (p, m) [] db)" by (rule wf_db_update[OF w]) simp
  obtain zs0 \<eta>' where e2: "meval j n ts (Mapping.update (p, m) [] db) \<eta> = (zs0, \<eta>')"
    by (cases "meval j n ts (Mapping.update (p, m) [] db) \<eta>")
  have tz0: "list_all (ftable n A) zs0" by (rule produces_tables[OF pe w0 sts mts e2])
  have ne: "produces n A (dnext u ts) \<eta>'" by (rule produces_next[OF pe w0 sts mts e2])
  define zout where "zout = drop (f0 - f1) zs0"
  define as1 where "as1 = drop (f0 - f2 + length zout) (as @ bs)"
  define ev where "ev = (\<lambda>\<alpha>. meval j n [] (Mapping.update (p, m) (replicate j \<alpha>)
    (Mapping.map_values (\<lambda>_ _. []) db)) \<eta>')"
  have tzout: "list_all (ftable n A) zout"
    using tz0 by (auto simp: zout_def list_all_iff dest: set_drop_subset[THEN subsetD])
  have las1: "list_all (ftable m {0..<m}) as1"
    using la tb by (auto simp: as1_def list_all_iff dest: set_drop_subset[THEN subsetD])
  have evt: "\<And>\<alpha>. \<alpha> \<in> set as1 \<Longrightarrow> list_all (ftable n A) (fst (ev \<alpha>))"
  proof -
    fix \<alpha> assume a: "\<alpha> \<in> set as1"
    then have ta: "ftable m {0..<m} \<alpha>" using las1 by (simp add: list_all_iff)
    have wa: "wf_db (Mapping.update (p, m) (replicate j \<alpha>)
        (Mapping.map_values (\<lambda>_ _. []) db))"
      by (rule wf_db_update[OF wf_db_map_values_empty])
        (use ta in \<open>simp add: list_all_iff\<close>)
    obtain cs st where ec: "ev \<alpha> = (cs, st)" by (cases "ev \<alpha>")
    have "list_all (ftable n A) cs"
      by (rule produces_tables[OF ne wa _ _ ec[unfolded ev_def]]) simp_all
    then show "list_all (ftable n A) (fst (ev \<alpha>))" using ec by simp
  qed
  obtain ys as' where e3: "freeze_meval0 ev (f0 - (f1 + length zs0)) as1 = (ys, as')"
    by (cases "freeze_meval0 ev (f0 - (f1 + length zs0)) as1")
  have fz: "list_all (ftable n A) ys \<and> set as' \<subseteq> set as1"
    by (rule freeze_meval0_ftable[OF e3 evt])
  have tys: "list_all (ftable n A) ys" using fz by simp
  have las': "list_all (ftable m {0..<m}) as'"
    using fz las1 by (auto simp: list_all_iff)
  have m: "meval j n ts db (mformula.MFrz p m \<chi> \<eta> f0 f1 f2 as)
      = (zout @ ys, mformula.MFrz p m \<chi>' \<eta>' (f0 + length zout + length ys)
          (f1 + length zs0) (f2 + length bs) as')"
    using e1 e2 e3 unfolding zout_def as1_def ev_def by (simp add: Let_def)
  have x: "xs = zout @ ys"
    and f: "\<Phi>' = mformula.MFrz p m \<chi>' \<eta>' (f0 + length zout + length ys)
      (f1 + length zs0) (f2 + length bs) as'"
    using e[unfolded Phi conjunct1[OF X] m] by simp_all
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and>
          (\<exists>\<chi> \<eta> f0 f1 f2 as. \<Phi>' = mformula.MFrz p m \<chi> \<eta> f0 f1 f2 as \<and>
             produces m {0..<m} (dnext u ts) \<chi> \<and> produces n A (dnext u ts) \<eta> \<and>
             list_all (ftable m {0..<m}) as)) \<or>
       produces n' A' (dnext u ts) \<Phi>')"
    using X tzout tys nc ne las' by (auto simp: x f)
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

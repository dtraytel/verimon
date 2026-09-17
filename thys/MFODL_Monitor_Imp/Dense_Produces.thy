(*<*)
theory Dense_Produces
  imports Dense_Eval "MFODL_Monitor_Devel.Correctness"
begin
(*>*)

section \<open>Discharging @{const produces}\<close>

text \<open>
  @{const produces} is the one thing the simulation assumes about the kernel's evaluation, and it
  is discharged node by node: for every constructor of the kernel's formula, a lemma saying that
  if the operands produce finite tables over their columns then so does the node.  Each such
  lemma is a coinduction of its own, with an invariant that says only what that node needs, so the
  whole discharge is modular rather than one monolithic invariant over the kernel's language.
\<close>

subsection \<open>The coinduction, packaged\<close>

lemma ftable_empty_table[simp]: "ftable n A empty_table"
  by (simp add: empty_table_def table_def)



text \<open>@{thm [source] produces.coinduct} with the trivial equations of its conclusion already
  solved, so that each node's lemma only has to name its own invariant.\<close>

lemma producesI[case_names init step]:
  assumes init: "X n A tw \<phi>"
    and step: "\<And>m B u \<psi> j ts db xs \<psi>'. X m B u \<psi> \<Longrightarrow> wf_db db \<Longrightarrow>
        sorted ts \<Longrightarrow> (\<forall>t \<in> set ts. u \<le> t) \<Longrightarrow>
        meval j m ts db \<psi> = (xs, \<psi>') \<Longrightarrow>
        list_all (ftable m B) xs \<and>
          (X m B (dnext u ts) \<psi>' \<or> produces m B (dnext u ts) \<psi>')"
  shows "produces n A tw \<phi>"
  using init
proof (rule produces.coinduct)
  fix m B u \<psi>
  assume X: "X m B u \<psi>"
  have "\<forall>j ts db xs \<chi>. wf_db db \<longrightarrow> sorted ts \<longrightarrow>
      (\<forall>t \<in> set ts. u \<le> t) \<longrightarrow> meval j m ts db \<psi> = (xs, \<chi>) \<longrightarrow>
      list_all (ftable m B) xs \<and>
        (X m B (dnext u ts) \<chi> \<or> produces m B (dnext u ts) \<chi>)"
    using step[OF X] by blast
  then show "\<exists>u' m' \<psi>' B'. m = m' \<and> B = B' \<and> u = u' \<and> \<psi> = \<psi>' \<and>
      (\<forall>j ts db xs \<chi>. wf_db db \<longrightarrow> sorted ts \<longrightarrow>
         (\<forall>t \<in> set ts. u' \<le> t) \<longrightarrow> meval j m' ts db \<psi>' = (xs, \<chi>) \<longrightarrow>
         list_all (ftable m' B') xs \<and>
           (X m' B' (dnext u' ts) \<chi> \<or> produces m' B' (dnext u' ts) \<chi>))"
    by blast
qed

text \<open>A node that does not change under evaluation.\<close>

lemma produces_fix:
  assumes "\<And>j ts db xs \<phi>'. wf_db db \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
      list_all (ftable n A) xs \<and> \<phi>' = \<phi>"
  shows "produces n A tw \<phi>"
  by (rule producesI[where X = "\<lambda>m B u \<psi>. m = n \<and> B = A \<and> \<psi> = \<phi>"])
    (use assms in auto)

text \<open>
  A node with one operand whose output is the operand's, mapped pointwise.  This covers every
  unary node of the kernel's language, and the table-and-finiteness obligation is the only thing
  that changes from one to the next.
\<close>

lemma produces_unop:
  assumes step: "\<And>j ts db \<psi> ys \<psi>'. meval j m ts db \<psi> = (ys, \<psi>') \<Longrightarrow>
      meval j n ts db (C \<psi>) = (map g ys, C \<psi>')"
    and tab: "\<And>Y. table m B Y \<Longrightarrow> finite Y \<Longrightarrow> table n A (g Y) \<and> finite (g Y)"
    and p: "produces m B tw \<phi>"
  shows "produces n A tw (C \<phi>)"
proof (rule producesI[where
    X = "\<lambda>n' A' u \<psi>. n' = n \<and> A' = A \<and>
      (\<exists>\<chi>. \<psi> = C \<chi> \<and> produces m B u \<chi>)"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi>. C \<phi> = C \<chi> \<and> produces m B tw \<chi>)"
    using p by blast
next
  fix n' A' u \<psi> j ts db xs \<psi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>\<chi>. \<psi> = C \<chi> \<and> produces m B u \<chi>)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j n' ts db \<psi> = (xs, \<psi>')"
  from X obtain \<chi> where pc: "produces m B u \<chi>" and psi: "\<psi> = C \<chi>" by blast
  obtain ys \<chi>' where e': "meval j m ts db \<chi> = (ys, \<chi>')" by (cases "meval j m ts db \<chi>")
  have "meval j n ts db (C \<chi>) = (map g ys, C \<chi>')" by (rule step[OF e'])
  then have x: "xs = map g ys" and f: "\<psi>' = C \<chi>'" using e X psi by simp_all
  have t: "list_all (ftable m B) ys" by (rule produces_tables[OF pc w sts mts e'])
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and>
          (\<exists>\<chi>. \<psi>' = C \<chi> \<and> produces m B (dnext u ts) \<chi>)) \<or>
       produces n' A' (dnext u ts) \<psi>')"
    using X t produces_next[OF pc w sts mts e'] tab by (auto simp: x f list_all_iff)
qed

subsection \<open>Nodes whose output does not depend on the operand's tables\<close>

lemma produces_MRel:
  "table n A rel \<Longrightarrow> finite rel \<Longrightarrow> produces n A tw (mformula.MRel rel)"
proof (coinduction arbitrary: rel tw)
  case produces
  then show ?case by (auto simp: list_all_iff)
qed

lemma produces_MNeg: "produces n {} tw (mformula.MNeg \<phi>)"
proof (coinduction arbitrary: \<phi> tw)
  case produces
  then show ?case
    by (auto simp: list_all_iff unit_table_def empty_table_def table_def wf_tuple_def
        split: prod.splits)
qed


subsection \<open>The unary nodes\<close>

lemma produces_MAndRel:
  "produces n A tw \<phi> \<Longrightarrow> produces n A tw (mformula.MAndRel \<phi> conf)"
  by (rule produces_unop[where m = n and B = A and C = "\<lambda>\<psi>. mformula.MAndRel \<psi> conf"
      and g = "Set.filter (eval_constraint conf)"])
    (auto simp: table_def split: prod.splits)

lemma table_eval_assignment:
  "table n B Y \<Longrightarrow> fst conf < n \<Longrightarrow>
     table n (Set.insert (fst conf) B) (eval_assignment conf ` Y)"
  by (cases conf) (auto simp: table_def wf_tuple_def nth_list_update)

lemma produces_MAndAssign:
  assumes x: "fst conf < n" and p: "produces n B tw \<phi>"
  shows "produces n (Set.insert (fst conf) B) tw (mformula.MAndAssign \<phi> conf)"
  by (rule produces_unop[where m = n and B = B and C = "\<lambda>\<psi>. mformula.MAndAssign \<psi> conf"
      and g = "\<lambda>Y. eval_assignment conf ` Y", OF _ _ p])
    (use x in \<open>auto simp: table_eval_assignment split: prod.splits\<close>)

lemma produces_MExists:
  "produces (Suc n) B tw \<phi> \<Longrightarrow>
     produces n ((\<lambda>x. x - Suc 0) ` (B - {0})) tw (mformula.MExists \<phi>)"
  by (rule produces_unop[where m = "Suc n" and B = B and C = mformula.MExists
      and g = "\<lambda>Y. tl ` Y"])
    (auto simp: table_project split: prod.splits)


subsection \<open>The predicate and time nodes\<close>

lemma produces_MPred_Copy:
  assumes l: "length tms = n"
  shows "produces n {0..<n} tw (mformula.MPred e tms Copy)"
proof (rule produces_fix)
  fix j ts db xs \<phi>'
  assume w: "wf_db db" and m: "meval j n ts db (mformula.MPred e tms Copy) = (xs, \<phi>')"
  show "list_all (ftable n {0..<n}) xs \<and> \<phi>' = mformula.MPred e tms Copy"
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    then show ?thesis using m by (auto simp: list_all_iff table_def)
  next
    case (Some X)
    then show ?thesis using m w l
      by (auto simp: list_all_iff dest: wf_dbD wf_dbD_finite)
  qed
qed

lemma produces_MPred_Simple:
  assumes sp: "is_simple_pattern tms 0"
    and b: "\<forall>t \<in> set tms. \<forall>x \<in> Formula.fv_trm t. x < n"
  shows "produces n (\<Union>t \<in> set tms. Formula.fv_trm t) tw
      (mformula.MPred e tms Simple)"
proof (rule produces_fix)
  fix j ts db xs \<phi>'
  assume w: "wf_db db" and m: "meval j n ts db (mformula.MPred e tms Simple) = (xs, \<phi>')"
  show "list_all (ftable n (\<Union>t \<in> set tms. Formula.fv_trm t)) xs \<and>
      \<phi>' = mformula.MPred e tms Simple"
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    then show ?thesis using m by (auto simp: list_all_iff table_def)
  next
    case (Some X)
    have "\<And>T. T \<in> set X \<Longrightarrow>
        ftable n (\<Union>t \<in> set tms. Formula.fv_trm t) (simple_match n 0 tms ` T)"
    proof -
      fix T assume T: "T \<in> set X"
      have t: "table (length tms) {0..<length tms} T" by (rule wf_dbD[OF w Some T])
      have "\<And>y. y \<in> T \<Longrightarrow> wf_tuple n (\<Union>t \<in> set tms. Formula.fv_trm t) (simple_match n 0 tms y)"
        using t by (intro wf_tuple_simple_match[OF sp b])
          (auto simp: table_def wf_tuple_def in_set_conv_nth)
      then show "ftable n (\<Union>t \<in> set tms. Formula.fv_trm t) (simple_match n 0 tms ` T)"
        using wf_dbD_finite[OF w Some T] by (auto simp: table_def)
    qed
    then show ?thesis using m Some by (auto simp: list_all_iff)
  qed
qed

lemma produces_MPred_Match:
  "produces n (\<Union>t \<in> set tms. Formula.fv_trm t) tw (mformula.MPred e tms Match)"
proof (rule produces_fix)
  fix j ts db xs \<phi>'
  assume w: "wf_db db" and m: "meval j n ts db (mformula.MPred e tms Match) = (xs, \<phi>')"
  show "list_all (ftable n (\<Union>t \<in> set tms. Formula.fv_trm t)) xs \<and>
      \<phi>' = mformula.MPred e tms Match"
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    then show ?thesis using m by (auto simp: list_all_iff table_def)
  next
    case (Some X)
    have "\<And>T. T \<in> set X \<Longrightarrow> ftable n (\<Union>t \<in> set tms. Formula.fv_trm t)
        ((\<lambda>f. Table.tabulate f 0 n) ` Option.these (match tms ` T))"
    proof -
      fix T assume T: "T \<in> set X"
      have f: "finite T" by (rule wf_dbD_finite[OF w Some T])
      then have "finite (Option.these (match tms ` T))" by (simp add: finite_these)
      then show "ftable n (\<Union>t \<in> set tms. Formula.fv_trm t)
          ((\<lambda>f. Table.tabulate f 0 n) ` Option.these (match tms ` T))"
        by (auto simp: table_def in_these_eq intro: match_wf_tuple)
    qed
    then show ?thesis using m Some by (auto simp: list_all_iff)
  qed
qed

fun mtrm_cols :: "mtrm \<Rightarrow> nat set" where
  "mtrm_cols (MVar v) = {v}"
| "mtrm_cols (MConst c) = {}"

lemma ftable_eval_mtrm: "ftable n (mtrm_cols mt) (eval_mtrm n mt x)"
proof (cases mt)
  case (MVar v)
  have "table n {v} (singleton_table n v x)" by simp
  moreover have "finite (singleton_table n v x)" by (simp add: singleton_table_def)
  ultimately show ?thesis using MVar by simp
next
  case (MConst c)
  have "table n {} (unit_table n)" by simp
  moreover have "finite (unit_table n)" unfolding unit_table_def by simp
  ultimately show ?thesis using MConst by (auto simp: empty_table_def)
qed

lemma produces_MTP: "produces n (mtrm_cols mt) tw (mformula.MTP mt i)"
  by (rule producesI[where
      X = "\<lambda>m B u \<psi>. m = n \<and> B = mtrm_cols mt \<and>
        (\<exists>k. \<psi> = mformula.MTP mt k)"])
    (auto simp: list_all_iff ftable_eval_mtrm)

lemma produces_MTS: "produces n (mtrm_cols mt) tw (mformula.MTS mt)"
  by (rule produces_fix) (auto simp: list_all_iff ftable_eval_mtrm)


subsection \<open>The binary nodes with a buffer\<close>

lemma mbuf2_take_out:
  "mbuf2_take f (xs, ys) = (zs, buf') \<Longrightarrow>
     (\<And>a b. a \<in> set xs \<Longrightarrow> b \<in> set ys \<Longrightarrow> P (f a b)) \<Longrightarrow> list_all P zs"
proof (induct xs arbitrary: ys zs buf')
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  note IH = Cons(1) and e = Cons(2) and st = Cons(3)
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using e by simp
  next
    case (Cons y ys0)
    obtain ws bf where w: "mbuf2_take f (xs, ys0) = (ws, bf)"
      by (cases "mbuf2_take f (xs, ys0)")
    have z: "zs = f x y # ws" using e Cons w by simp
    have "list_all P ws" by (rule IH[OF w]) (use st Cons in simp)
    then show ?thesis using st Cons by (simp add: z)
  qed
qed

lemma produces_binop:
  assumes step: "\<And>j ts db \<chi> \<eta> bf as \<chi>' bs \<eta>' zs bf'.
      meval j n ts db \<chi> = (as, \<chi>') \<Longrightarrow> meval j n ts db \<eta> = (bs, \<eta>') \<Longrightarrow>
      mbuf2_take f (mbuf2_add as bs bf) = (zs, bf') \<Longrightarrow>
      meval j n ts db (C \<chi> \<eta> bf) = (zs, C \<chi>' \<eta>' bf')"
    and tab: "\<And>X Y. ftable n B1 X \<Longrightarrow> ftable n B2 Y \<Longrightarrow> ftable n A (f X Y)"
    and p1: "produces n B1 tw \<phi>" and p2: "produces n B2 tw \<psi>"
    and bf1: "list_all (ftable n B1) (fst buf)" and bf2: "list_all (ftable n B2) (snd buf)"
  shows "produces n A tw (C \<phi> \<psi> buf)"
proof (rule producesI[where X = "\<lambda>n' A' u \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<chi> \<eta> bf. \<Phi> = C \<chi> \<eta> bf \<and> produces n B1 u \<chi> \<and>
       produces n B2 u \<eta> \<and>
       list_all (ftable n B1) (fst bf) \<and> list_all (ftable n B2) (snd bf))"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi> \<eta> bf. C \<phi> \<psi> buf = C \<chi> \<eta> bf \<and>
      produces n B1 tw \<chi> \<and> produces n B2 tw \<eta> \<and>
      list_all (ftable n B1) (fst bf) \<and> list_all (ftable n B2) (snd bf))"
    using p1 p2 bf1 bf2 by blast
next
  fix n' A' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>\<chi> \<eta> bf. \<Phi> = C \<chi> \<eta> bf \<and> produces n B1 u \<chi> \<and>
      produces n B2 u \<eta> \<and> list_all (ftable n B1) (fst bf) \<and>
      list_all (ftable n B2) (snd bf))"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> \<eta> bf where Phi: "\<Phi> = C \<chi> \<eta> bf" and pc: "produces n B1 u \<chi>"
    and pe: "produces n B2 u \<eta>" and b1: "list_all (ftable n B1) (fst bf)"
    and b2: "list_all (ftable n B2) (snd bf)" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  obtain bs \<eta>' where e2: "meval j n ts db \<eta> = (bs, \<eta>')" by (cases "meval j n ts db \<eta>")
  obtain zs c1 c2 where e3: "mbuf2_take f (mbuf2_add as bs bf) = (zs, (c1, c2))"
    by (cases "mbuf2_take f (mbuf2_add as bs bf)") auto
  have "meval j n ts db (C \<chi> \<eta> bf) = (zs, C \<chi>' \<eta>' (c1, c2))" by (rule step[OF e1 e2 e3])
  then have x: "xs = zs" and f': "\<Phi>' = C \<chi>' \<eta>' (c1, c2)" using e X Phi by simp_all
  have ta: "list_all (ftable n B1) as" by (rule produces_tables[OF pc w sts mts e1])
  have tb: "list_all (ftable n B2) bs" by (rule produces_tables[OF pe w sts mts e2])
  have add: "mbuf2_add as bs bf = (fst bf @ as, snd bf @ bs)" by (cases bf) simp
  have la: "list_all (ftable n B1) (fst bf @ as)" using b1 ta by simp
  have lb: "list_all (ftable n B2) (snd bf @ bs)" using b2 tb by simp
  have e3': "mbuf2_take f (fst bf @ as, snd bf @ bs) = (zs, (c1, c2))"
    using e3 unfolding add by simp
  have tz: "list_all (ftable n A) zs"
    by (rule mbuf2_take_out[OF e3']) (use la lb tab in \<open>auto simp: list_all_iff\<close>)
  have sb: "set c1 \<subseteq> set (fst bf @ as) \<and> set c2 \<subseteq> set (snd bf @ bs)"
    by (rule mbuf2_take_sub[OF e3'])
  have lc1: "list_all (ftable n B1) c1" using sb la by (auto simp: list_all_iff)
  have lc2: "list_all (ftable n B2) c2" using sb lb by (auto simp: list_all_iff)
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and> (\<exists>\<chi> \<eta> bf. \<Phi>' = C \<chi> \<eta> bf \<and>
         produces n B1 (dnext u ts) \<chi> \<and> produces n B2 (dnext u ts) \<eta> \<and>
         list_all (ftable n B1) (fst bf) \<and> list_all (ftable n B2) (snd bf))) \<or>
       produces n' A' (dnext u ts) \<Phi>')"
    using X tz lc1 lc2 produces_next[OF pc w sts mts e1] produces_next[OF pe w sts mts e2]
    by (auto simp: x f')
qed

lemma produces_MOr:
  assumes p1: "produces n A tw \<phi>" and p2: "produces n A tw \<psi>"
    and bf1: "list_all (ftable n A) (fst buf)" and bf2: "list_all (ftable n A) (snd buf)"
  shows "produces n A tw (mformula.MOr \<phi> \<psi> buf)"
proof -
  have step: "\<And>j ts db \<chi> \<eta> bf as \<chi>' bs \<eta>' zs bf'.
      meval j n ts db \<chi> = (as, \<chi>') \<Longrightarrow> meval j n ts db \<eta> = (bs, \<eta>') \<Longrightarrow>
      mbuf2_take (\<lambda>X Y. X \<union> Y) (mbuf2_add as bs bf) = (zs, bf') \<Longrightarrow>
      meval j n ts db (mformula.MOr \<chi> \<eta> bf) = (zs, mformula.MOr \<chi>' \<eta>' bf')"
    by simp
  have tab: "\<And>X Y. ftable n A X \<Longrightarrow> ftable n A Y \<Longrightarrow> ftable n A (X \<union> Y)"
    by (auto simp: table_def)
  show ?thesis by (rule produces_binop[OF step tab p1 p2 bf1 bf2])
qed

lemma ftable_bin_join:
  fixes X Y :: "event_data table"
  assumes tX: "ftable n A1 X" and tY: "ftable n A2 Y"
    and sub: "\<not> pos \<Longrightarrow> A2 \<subseteq> A1" and A: "A = (if pos then A1 \<union> A2 else A1)"
  shows "ftable n A (bin_join n A1 X pos A2 Y)"
proof -
  have tj: "table n A (join X pos Y)"
    by (rule join_table[of n A1 X A2 Y pos A]) (use tX tY sub A in auto)
  have fj: "finite (join X pos Y)" by (rule finite_join) (use tX tY in auto)
  have bj: "bin_join n A1 X pos A2 Y = join X pos Y"
    by (rule bin_join_table) (use tX tY in auto)
  show ?thesis unfolding bj using tj fj by simp
qed

lemma produces_MAnd:
  assumes p1: "produces n A1 tw \<phi>" and p2: "produces n A2 tw \<psi>"
    and bf1: "list_all (ftable n A1) (fst buf)" and bf2: "list_all (ftable n A2) (snd buf)"
    and sub: "\<not> pos \<Longrightarrow> A2 \<subseteq> A1" and A: "A = (if pos then A1 \<union> A2 else A1)"
  shows "produces n A tw (mformula.MAnd A1 \<phi> pos A2 \<psi> buf)"
proof -
  have step: "\<And>j ts db \<chi> \<eta> bf as \<chi>' bs \<eta>' zs bf'.
      meval j n ts db \<chi> = (as, \<chi>') \<Longrightarrow> meval j n ts db \<eta> = (bs, \<eta>') \<Longrightarrow>
      mbuf2_take (\<lambda>X Y. bin_join n A1 X pos A2 Y) (mbuf2_add as bs bf) = (zs, bf') \<Longrightarrow>
      meval j n ts db (mformula.MAnd A1 \<chi> pos A2 \<eta> bf)
        = (zs, mformula.MAnd A1 \<chi>' pos A2 \<eta>' bf')"
    by (simp del: bin_join.simps)
  show ?thesis
    by (rule produces_binop[OF step ftable_bin_join[OF _ _ sub A] p1 p2 bf1 bf2])
qed

subsection \<open>The temporal shift nodes\<close>

lemma mprev_next_out:
  "mprev_next I xs ts = (zs, xs', ts') \<Longrightarrow> list_all P xs \<Longrightarrow> P empty_table \<Longrightarrow>
     list_all P zs \<and> list_all P xs'"
  by (induct I xs ts arbitrary: zs xs' ts' rule: mprev_next.induct)
    (auto split: prod.splits)

lemma produces_MPrev:
  assumes p: "produces n A tw \<phi>" and bf: "list_all (ftable n A) buf"
  shows "produces n A tw (mformula.MPrev I \<phi> first buf nts)"
proof (rule producesI[where X = "\<lambda>n' A' u \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<chi> b bs nt. \<Phi> = mformula.MPrev I \<chi> b bs nt \<and> produces n A u \<chi> \<and>
       list_all (ftable n A) bs)"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi> b bs nt. mformula.MPrev I \<phi> first buf nts
      = mformula.MPrev I \<chi> b bs nt \<and> produces n A tw \<chi> \<and> list_all (ftable n A) bs)"
    using p bf by blast
next
  fix n' A' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>\<chi> b bs nt. \<Phi> = mformula.MPrev I \<chi> b bs nt \<and>
      produces n A u \<chi> \<and> list_all (ftable n A) bs)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> b bs nt where Phi: "\<Phi> = mformula.MPrev I \<chi> b bs nt"
    and pc: "produces n A u \<chi>" and lb: "list_all (ftable n A) bs" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  have ta: "list_all (ftable n A) as" by (rule produces_tables[OF pc w sts mts e1])
  obtain ws bs' nt' where e2: "mprev_next I (bs @ as) (nt @ ts) = (ws, bs', nt')"
    by (cases "mprev_next I (bs @ as) (nt @ ts)") auto
  have out: "list_all (ftable n A) ws \<and> list_all (ftable n A) bs'"
    by (rule mprev_next_out[OF e2]) (use lb ta in \<open>auto simp: table_def\<close>)
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and> (\<exists>\<chi> b bs nt. \<Phi>' = mformula.MPrev I \<chi> b bs nt \<and>
         produces n A (dnext u ts) \<chi> \<and> list_all (ftable n A) bs)) \<or>
       produces n' A' (dnext u ts) \<Phi>')"
    using X e Phi e1 e2 out lb ta produces_next[OF pc w sts mts e1]
    by (auto simp: table_def split: if_splits)
qed

lemma produces_MNext:
  assumes p: "produces n A tw \<phi>"
  shows "produces n A tw (mformula.MNext I \<phi> first nts)"
proof (rule producesI[where X = "\<lambda>n' A' u \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<chi> b nt. \<Phi> = mformula.MNext I \<chi> b nt \<and> produces n A u \<chi>)"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi> b nt. mformula.MNext I \<phi> first nts
      = mformula.MNext I \<chi> b nt \<and> produces n A tw \<chi>)" using p by blast
next
  fix n' A' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and>
      (\<exists>\<chi> b nt. \<Phi> = mformula.MNext I \<chi> b nt \<and> produces n A u \<chi>)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> b nt where Phi: "\<Phi> = mformula.MNext I \<chi> b nt"
    and pc: "produces n A u \<chi>" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  have ta: "list_all (ftable n A) as" by (rule produces_tables[OF pc w sts mts e1])
  obtain cs b' where c: "(case (as, b) of (_ # as', True) \<Rightarrow> (as', False) | a \<Rightarrow> a) = (cs, b')"
    by (cases "(case (as, b) of (_ # as', True) \<Rightarrow> (as', False) | a \<Rightarrow> a)") auto
  have tc: "list_all (ftable n A) cs"
    using ta c by (cases as; cases b) auto
  obtain ws cs' nt' where e2: "mprev_next I cs (nt @ ts) = (ws, cs', nt')"
    by (cases "mprev_next I cs (nt @ ts)") auto
  have out: "list_all (ftable n A) ws \<and> list_all (ftable n A) cs'"
    by (rule mprev_next_out[OF e2]) (use tc in \<open>auto simp: table_def\<close>)
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and> (\<exists>\<chi> b nt. \<Phi>' = mformula.MNext I \<chi> b nt \<and>
          produces n A (dnext u ts) \<chi>)) \<or>
       produces n' A' (dnext u ts) \<Phi>')"
    using X e Phi e1 c e2 out produces_next[OF pc w sts mts e1] by auto
qed


subsection \<open>The aggregation node\<close>

lemma wf_tuple_insert_upd:
  "wf_tuple n B t \<Longrightarrow> y < n \<Longrightarrow> wf_tuple n (Set.insert y B) (t[y := Some v])"
  by (auto simp: wf_tuple_def nth_list_update)

lemma ftable_eval_agg:
  assumes t: "table (length tys + n) G rel" and fin: "finite rel"
    and y: "y < n" and sh: "\<forall>i \<in> G. length tys \<le> i"
    and g0: "g0 \<Longrightarrow> G = {}"
  shows "ftable n (Set.insert y ((\<lambda>i. i - length tys) ` G))
      (eval_agg n g0 y \<omega> tys trm rel)"
proof (cases "g0 \<and> rel = empty_table")
  case True
  then have G: "G = {}" using g0 by simp
  have "table n {y} (singleton_table n y (eval_agg_op \<omega> {}))" by simp
  moreover have "finite (singleton_table n y (eval_agg_op \<omega> {}))"
    by (simp add: singleton_table_def)
  ultimately show ?thesis using True by (simp add: eval_agg_def G)
next
  case False
  have w: "\<And>x. x \<in> rel \<Longrightarrow>
      wf_tuple n ((\<lambda>i. i - length tys) ` G) (drop (length tys) x)"
  proof -
    fix x assume x: "x \<in> rel"
    then have wx: "wf_tuple (length tys + n) G x" using t by (simp add: table_def)
    show "wf_tuple n ((\<lambda>i. i - length tys) ` G) (drop (length tys) x)"
      using wx sh by (fastforce simp: wf_tuple_def image_iff)
  qed
  show ?thesis
    unfolding eval_agg_def if_not_P[OF False]
    using fin w y by (auto simp: table_def Let_def intro!: wf_tuple_insert_upd)
qed

lemma produces_MAgg:
  assumes p: "produces (length (aggargs_tys args) + n) G tw \<phi>"
    and an: "aggargs_n args = n" and y: "aggargs_y args < n"
    and sh: "\<forall>i \<in> G. length (aggargs_tys args) \<le> i"
    and g0: "aggargs_g0 args \<Longrightarrow> G = {}"
  shows "produces n (Set.insert (aggargs_y args) ((\<lambda>i. i - length (aggargs_tys args)) ` G))
      tw (mformula.MAgg args \<phi>)"
proof -
  have step: "\<And>j ts db \<chi> ys \<chi>'.
      meval j (length (aggargs_tys args) + n) ts db \<chi> = (ys, \<chi>') \<Longrightarrow>
      meval j n ts db (mformula.MAgg args \<chi>) = (map (eval_aggargs args) ys, mformula.MAgg args \<chi>')"
    by simp
  have tab: "\<And>Y. table (length (aggargs_tys args) + n) G Y \<Longrightarrow> finite Y \<Longrightarrow>
      table n (Set.insert (aggargs_y args) ((\<lambda>i. i - length (aggargs_tys args)) ` G))
        (eval_aggargs args Y) \<and>
      finite (eval_aggargs args Y)"
    unfolding eval_aggargs_def an[symmetric]
    by (rule ftable_eval_agg[OF _ _ _ sh g0]) (use y an in auto)
  show ?thesis by (rule produces_unop[OF step tab p])
qed


subsection \<open>The multi-way conjunction\<close>

text \<open>
  The multi-way join's shape follows from the same fold that
  @{thm [source] dmulti_join_dtabc} uses: at well-formed operands it is the left-to-right fold of
  the positive tables followed by the anti-joins against the negative ones, and each step of both
  folds keeps the table over the accumulated columns and keeps it finite.
\<close>

lemma kands_pos_ftable:
  "list_all2 (\<lambda>A X. table n A X \<and> finite X) As Xs \<Longrightarrow> table n B T \<Longrightarrow> finite T \<Longrightarrow>
     table n (B \<union> \<Union>(set As)) (kands_pos T Xs) \<and> finite (kands_pos T Xs)"
proof (induct As arbitrary: Xs B T)
  case Nil
  then show ?case by simp
next
  case (Cons A As)
  from Cons.prems(1) obtain X Xs' where Xs: "Xs = X # Xs'"
    and hd: "table n A X" "finite X"
    and tl: "list_all2 (\<lambda>A X. table n A X \<and> finite X) As Xs'"
    by (cases Xs) auto
  have t: "table n (B \<union> A) (join T True X)"
    using Cons.prems(2) hd by (intro join_table[of n B T A X True]) auto
  have f: "finite (join T True X)" using Cons.prems(3) hd by (simp add: finite_join)
  show ?case using Cons.hyps[OF tl t f] by (simp add: Xs Un_assoc)
qed

lemma kands_neg_ftable:
  "list_all2 (\<lambda>A X. table n A X \<and> finite X) Bs Ys \<Longrightarrow> table n B T \<Longrightarrow> finite T \<Longrightarrow>
     (\<forall>A \<in> set Bs. A \<subseteq> B) \<Longrightarrow>
     table n B (kands_neg T Ys) \<and> finite (kands_neg T Ys)"
proof (induct Bs arbitrary: Ys T)
  case Nil
  then show ?case by simp
next
  case (Cons A Bs)
  from Cons.prems(1) obtain Y Ys' where Ys: "Ys = Y # Ys'"
    and hd: "table n A Y" "finite Y"
    and tl: "list_all2 (\<lambda>A X. table n A X \<and> finite X) Bs Ys'"
    by (cases Ys) auto
  have s: "A \<subseteq> B" using Cons.prems(4) by simp
  have t: "table n B (join T False Y)"
    using Cons.prems(2) hd s by (intro join_table[of n B T A Y False B]) auto
  have f: "finite (join T False Y)" using Cons.prems(3) hd by (simp add: finite_join)
  show ?case using Cons.hyps[OF tl t f] Cons.prems(4) by (simp add: Ys)
qed

lemma ftable_mmulti_join:
  assumes lp: "length As = length Xs" and ln: "length A_neg = length L_neg"
    and lpos: "list_all2 (\<lambda>A X. table n A X \<and> finite X \<and> wf_set n A) As Xs"
    and lneg: "list_all2 (\<lambda>A X. table n A X \<and> finite X \<and> wf_set n A) A_neg L_neg"
    and t0: "table n A0 X0" and f0: "finite X0" and w0: "wf_set n A0"
    and sub: "\<forall>B \<in> set A_neg. B \<subseteq> A0 \<union> \<Union>(set As)"
  shows "ftable n (A0 \<union> \<Union>(set As)) (mmulti_join n (A0 # As) A_neg ((X0 # Xs) @ L_neg))"
proof -
  let ?A = "A0 \<union> \<Union>(set As)"
  let ?K = "kands_pos X0 Xs"
  have lpos': "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) As Xs"
    by (rule list_all2_mono[OF lpos]) auto
  have lneg': "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_neg L_neg"
    by (rule list_all2_mono[OF lneg]) auto
  have lposf: "list_all2 (\<lambda>A X. table n A X \<and> finite X) As Xs"
    by (rule list_all2_mono[OF lpos]) auto
  have lnegf: "list_all2 (\<lambda>A X. table n A X \<and> finite X) A_neg L_neg"
    by (rule list_all2_mono[OF lneg]) auto
  have la': "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
      ((A0 # As) @ A_neg) ((X0 # Xs) @ L_neg)"
    using t0 w0 lpos' lneg' by (simp add: list_all2_appendI)
  have subU: "\<Union>(set A_neg) \<subseteq> \<Union>(set (A0 # As))" using sub by auto
  have tk: "table n ?A ?K" and fk: "finite ?K"
    using kands_pos_ftable[OF lposf t0 f0] by auto
  have wA: "wf_set n ?A"
  proof -
    have "\<And>i. i < length As \<Longrightarrow> wf_set n (As ! i)"
      using lpos by (auto dest: list_all2_nthD)
    then have "\<And>C. C \<in> set As \<Longrightarrow> wf_set n C" by (auto simp: in_set_conv_nth)
    then show ?thesis using w0 by (auto simp: wf_set_def)
  qed
  have eq1: "mmulti_join n (A0 # As) A_neg ((X0 # Xs) @ L_neg)
      = mmulti_join' (A0 # As) A_neg ((X0 # Xs) @ L_neg)"
    by (rule mmulti_join_eq_mmulti_join'[OF _ la' subU]) simp
  have eq2: "mmulti_join' (A0 # As) A_neg ((X0 # Xs) @ L_neg)
      = mmulti_join' [?A] A_neg (?K # L_neg)"
    by (rule mmulti_join'_fold_pos[OF lp la'])
  have eq3: "mmulti_join' [?A] A_neg (?K # L_neg) = kands_neg ?K L_neg"
  proof (rule mmulti_join'_fold_neg[OF ln])
    show "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) ([?A] @ A_neg) ([?K] @ L_neg)"
      using tk wA lneg' by (simp add: list_all2_appendI)
    show "\<forall>B \<in> set A_neg. B \<subseteq> ?A" by (rule sub)
  qed
  show ?thesis unfolding eq1 eq2 eq3
    using kands_neg_ftable[OF lnegf tk fk sub] by simp
qed

lemma mbufn_take_out:
  "mbufn_take f z buf = (w, buf') \<Longrightarrow> length Ss = length buf \<Longrightarrow>
   (\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i) \<Longrightarrow>
   (\<And>as u. length as = length Ss \<Longrightarrow> (\<forall>i < length Ss. as ! i \<in> Ss ! i) \<Longrightarrow> Q u \<Longrightarrow>
      Q (f as u)) \<Longrightarrow>
   Q z \<Longrightarrow>
   Q w \<and> length buf' = length buf \<and> (\<forall>i < length buf'. set (buf' ! i) \<subseteq> Ss ! i)"
proof (induct f z buf arbitrary: w buf' rule: mbufn_take.induct)
  case (1 f z buf)
  note IH = 1(1) and E = 1(2) and L = 1(3) and SUB = 1(4) and ST = 1(5) and QZ = 1(6)
  show ?case
  proof (cases "buf = [] \<or> [] \<in> set buf")
    case True
    then show ?thesis using E L SUB QZ by simp
  next
    case False
    then have ne: "\<And>i. i < length buf \<Longrightarrow> buf ! i \<noteq> []" by (auto simp: in_set_conv_nth)
    have las: "length (map hd buf) = length Ss" using L by simp
    have has: "\<forall>i < length Ss. map hd buf ! i \<in> Ss ! i"
    proof (intro allI impI)
      fix i assume i: "i < length Ss"
      then have ib: "i < length buf" using L by simp
      have "hd (buf ! i) \<in> set (buf ! i)" using ne[OF ib] by simp
      then show "map hd buf ! i \<in> Ss ! i" using SUB ib by auto
    qed
    have q: "Q (f (map hd buf) z)" by (rule ST[OF las has QZ])
    have lt: "length Ss = length (map tl buf)" using L by simp
    have st: "\<forall>i < length (map tl buf). set (map tl buf ! i) \<subseteq> Ss ! i"
      using SUB L by (auto dest: set_tl_sub[THEN subsetD])
    have e: "mbufn_take f (f (map hd buf) z) (map tl buf) = (w, buf')"
      using E False by simp
    show ?thesis using IH[OF False e lt st ST q] L by simp
  qed
qed

lemma ftable_mmulti_join':
  assumes lall: "list_all2 (\<lambda>C X. table n C X \<and> finite X \<and> wf_set n C)
      ((A0 # As) @ A_neg) L"
    and sub: "\<forall>B \<in> set A_neg. B \<subseteq> A0 \<union> \<Union>(set As)"
  shows "ftable n (A0 \<union> \<Union>(set As)) (mmulti_join n (A0 # As) A_neg L)"
proof -
  let ?Q = "\<lambda>C X. table n C X \<and> finite X \<and> wf_set n C"
  obtain X0 R where L0: "L = X0 # R" and h0: "?Q A0 X0"
    and rest: "list_all2 ?Q (As @ A_neg) R"
    using lall by (auto simp: list_all2_Cons1)
  obtain Xs N where R: "R = Xs @ N" and lXs: "length Xs = length As"
    and lpos: "list_all2 ?Q As Xs" and sn: "list_all2 ?Q A_neg N"
    using rest by (auto simp: list_all2_append1)
  have lN: "length A_neg = length N" by (rule list_all2_lengthD[OF sn])
  have t0: "table n A0 X0" and f0: "finite X0" and w0: "wf_set n A0"
    using h0 by simp_all
  have L: "L = (X0 # Xs) @ N" by (simp add: L0 R)
  show ?thesis unfolding L
    by (rule ftable_mmulti_join[OF lXs[symmetric] lN lpos sn t0 f0 w0 sub])
qed


lemma ftable_mmulti_join_nth:
  fixes as :: "event_data table list"
  assumes la: "length as = length ((A0 # As) @ A_neg)"
    and ha: "\<forall>i < length as. ftable n (((A0 # As) @ A_neg) ! i) (as ! i)"
    and wf: "\<forall>C \<in> set ((A0 # As) @ A_neg). wf_set n C"
    and sub: "\<forall>B \<in> set A_neg. B \<subseteq> A0 \<union> \<Union>(set As)"
  shows "ftable n (A0 \<union> \<Union>(set As)) (mmulti_join n (A0 # As) A_neg as)"
proof -
  have wfi: "\<And>i. i < length ((A0 # As) @ A_neg) \<Longrightarrow> wf_set n (((A0 # As) @ A_neg) ! i)"
    using wf by (meson nth_mem)
  show ?thesis
    by (rule ftable_mmulti_join'[OF _ sub])
      (use la ha wfi in \<open>auto simp: list_all2_conv_all_nth\<close>)
qed

lemma produces_MAnds:
  assumes lL: "length L = length ((A0 # As) @ A_neg)"
    and lb: "length buf = length ((A0 # As) @ A_neg)"
    and pL: "\<forall>i < length ((A0 # As) @ A_neg).
        produces n (((A0 # As) @ A_neg) ! i) tw (L ! i)"
    and pb: "\<forall>i < length ((A0 # As) @ A_neg).
        list_all (ftable n (((A0 # As) @ A_neg) ! i)) (buf ! i)"
    and wf: "\<forall>C \<in> set ((A0 # As) @ A_neg). wf_set n C"
    and sub: "\<forall>B \<in> set A_neg. B \<subseteq> A0 \<union> \<Union>(set As)"
    and A: "A = A0 \<union> \<Union>(set As)"
  shows "produces n A tw (mformula.MAnds (A0 # As) A_neg L buf)"
proof (rule producesI[where X = "\<lambda>n' A' u \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>M bf. \<Phi> = mformula.MAnds (A0 # As) A_neg M bf \<and>
       length M = length ((A0 # As) @ A_neg) \<and>
       length bf = length ((A0 # As) @ A_neg) \<and>
       (\<forall>i < length ((A0 # As) @ A_neg).
          produces n (((A0 # As) @ A_neg) ! i) u (M ! i)) \<and>
       (\<forall>i < length ((A0 # As) @ A_neg).
          list_all (ftable n (((A0 # As) @ A_neg) ! i)) (bf ! i)))"])
  show "n = n \<and> A = A \<and> (\<exists>M bf. mformula.MAnds (A0 # As) A_neg L buf
      = mformula.MAnds (A0 # As) A_neg M bf \<and>
      length M = length ((A0 # As) @ A_neg) \<and> length bf = length ((A0 # As) @ A_neg) \<and>
      (\<forall>i < length ((A0 # As) @ A_neg).
         produces n (((A0 # As) @ A_neg) ! i) tw (M ! i)) \<and>
      (\<forall>i < length ((A0 # As) @ A_neg).
         list_all (ftable n (((A0 # As) @ A_neg) ! i)) (bf ! i)))"
    using lL lb pL pb by blast
next
  fix n' A' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>M bf. \<Phi> = mformula.MAnds (A0 # As) A_neg M bf \<and>
      length M = length ((A0 # As) @ A_neg) \<and> length bf = length ((A0 # As) @ A_neg) \<and>
      (\<forall>i < length ((A0 # As) @ A_neg).
         produces n (((A0 # As) @ A_neg) ! i) u (M ! i)) \<and>
      (\<forall>i < length ((A0 # As) @ A_neg).
         list_all (ftable n (((A0 # As) @ A_neg) ! i)) (bf ! i)))"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  define Cs where "Cs = (A0 # As) @ A_neg"
  from X obtain M0 bf0 where Phi: "\<Phi> = mformula.MAnds (A0 # As) A_neg M0 bf0"
    and lM: "length M0 = length Cs" and lbf: "length bf0 = length Cs"
    and pM: "\<forall>i < length Cs. produces n (Cs ! i) u (M0 ! i)"
    and pbf: "\<forall>i < length Cs. list_all (ftable n (Cs ! i)) (bf0 ! i)"
    unfolding Cs_def by blast
  define R where "R = map (meval j n ts db) M0"
  define bf1 where "bf1 = mbufn_add (map fst R) bf0"
  define Ss :: "event_data table set list" where "Ss = map (\<lambda>C. {X. ftable n C X}) Cs"
  define f :: "event_data table list \<Rightarrow> event_data table list \<Rightarrow> event_data table list"
    where "f = (\<lambda>as zs. zs @ [mmulti_join n (A0 # As) A_neg as])"
  have lR: "length R = length Cs" using lM by (simp add: R_def)
  have lb1: "length bf1 = length Cs" using lbf lR by (simp add: bf1_def)
  have lSs: "length Ss = length Cs" by (simp add: Ss_def)
  have tR: "\<And>i. i < length Cs \<Longrightarrow> list_all (ftable n (Cs ! i)) (fst (R ! i))"
  proof -
    fix i assume i: "i < length Cs"
    obtain as \<chi>' where ei: "meval j n ts db (M0 ! i) = (as, \<chi>')"
      by (cases "meval j n ts db (M0 ! i)")
    have "list_all (ftable n (Cs ! i)) as"
      by (rule produces_tables[OF _ w sts mts ei]) (use pM i in blast)
    then show "list_all (ftable n (Cs ! i)) (fst (R ! i))"
      using ei i lM by (simp add: R_def)
  qed
  have nR: "\<And>i. i < length Cs \<Longrightarrow> produces n (Cs ! i) (dnext u ts) (snd (R ! i))"
  proof -
    fix i assume i: "i < length Cs"
    obtain as \<chi>' where ei: "meval j n ts db (M0 ! i) = (as, \<chi>')"
      by (cases "meval j n ts db (M0 ! i)")
    have "produces n (Cs ! i) (dnext u ts) \<chi>'"
      by (rule produces_next[OF _ w sts mts ei]) (use pM i in blast)
    then show "produces n (Cs ! i) (dnext u ts) (snd (R ! i))"
      using ei i lM by (simp add: R_def)
  qed
  have sub1: "\<forall>i < length bf1. set (bf1 ! i) \<subseteq> Ss ! i"
  proof (intro allI impI)
    fix i assume i: "i < length bf1"
    then have ic: "i < length Cs" using lb1 by simp
    have "bf1 ! i = bf0 ! i @ fst (R ! i)" using ic lbf lR by (simp add: bf1_def)
    then show "set (bf1 ! i) \<subseteq> Ss ! i"
      using pbf tR[OF ic] ic by (auto simp: Ss_def list_all_iff)
  qed
  have st: "\<And>as u. length as = length Ss \<Longrightarrow> (\<forall>i < length Ss. as ! i \<in> Ss ! i) \<Longrightarrow>
      list_all (ftable n A) u \<Longrightarrow> list_all (ftable n A) (f as u)"
  proof -
    fix as :: "event_data table list" and u :: "event_data table list"
    assume la: "length as = length Ss" and ha: "\<forall>i < length Ss. as ! i \<in> Ss ! i"
      and qu: "list_all (ftable n A) u"
    have ha': "\<forall>i < length Cs. ftable n (Cs ! i) (as ! i)"
    proof (intro allI impI)
      fix i assume i: "i < length Cs"
      then have "as ! i \<in> Ss ! i" using ha lSs by simp
      then show "ftable n (Cs ! i) (as ! i)" using i by (simp add: Ss_def)
    qed
    have lac: "length as = length ((A0 # As) @ A_neg)" using la lSs by (simp add: Cs_def)
    have hac: "\<forall>i < length as. ftable n (((A0 # As) @ A_neg) ! i) (as ! i)"
      using ha' la lSs by (simp add: Cs_def)
    have "ftable n A (mmulti_join n (A0 # As) A_neg as)"
      unfolding A by (rule ftable_mmulti_join_nth[OF lac hac wf sub])
    then show "list_all (ftable n A) (f as u)" using qu by (simp add: f_def)
  qed
  obtain zs bf2 where e2: "mbufn_take f [] bf1 = (zs, bf2)"
    by (cases "mbufn_take f [] bf1")
  have lSb: "length Ss = length bf1" using lSs lb1 by simp
  have qz: "list_all (ftable n A) []" by simp
  have out: "list_all (ftable n A) zs \<and> length bf2 = length bf1 \<and>
      (\<forall>i < length bf2. set (bf2 ! i) \<subseteq> Ss ! i)"
    by (rule mbufn_take_out[where Q = "list_all (ftable n A)" and f = f and Ss = Ss,
        OF e2 lSb sub1 st qz])
  have m: "meval j n ts db (mformula.MAnds (A0 # As) A_neg M0 bf0)
      = (zs, mformula.MAnds (A0 # As) A_neg (map snd R) bf2)"
    using e2 unfolding R_def bf1_def f_def
    by (simp add: Let_def del: mbufn_take.simps mmulti_join.simps)
  have x: "xs = zs" and f': "\<Phi>' = mformula.MAnds (A0 # As) A_neg (map snd R) bf2"
    using e X Phi m by simp_all
  have pM': "\<forall>i < length Cs. produces n (Cs ! i) (dnext u ts) (map snd R ! i)"
    using nR lR by simp
  have pbf': "\<forall>i < length Cs. list_all (ftable n (Cs ! i)) (bf2 ! i)"
    using out lb1 by (auto simp: Ss_def list_all_iff subset_eq)
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and> (\<exists>M bf. \<Phi>' = mformula.MAnds (A0 # As) A_neg M bf \<and>
         length M = length ((A0 # As) @ A_neg) \<and>
         length bf = length ((A0 # As) @ A_neg) \<and>
         (\<forall>i < length ((A0 # As) @ A_neg).
            produces n (((A0 # As) @ A_neg) ! i) (dnext u ts) (M ! i)) \<and>
         (\<forall>i < length ((A0 # As) @ A_neg).
            list_all (ftable n (((A0 # As) @ A_neg) ! i)) (bf ! i)))) \<or>
       produces n' A' (dnext u ts) \<Phi>')"
    using X out pM' pbf' lM lb1 lR by (auto simp: x f' Cs_def)
qed

subsection \<open>The Since node\<close>

text \<open>
  The Since node's invariant is the verified structure's own: it is valid for an abstract
  auxiliary list whose tables are finite tables over the node's columns, at a current timestamp
  that the buffer's timestamps -- and every timestamp still to come -- are at or after.  This is
  the wide half of @{const dsince_rel}; the node needs nothing of the dense half in order to
  produce well-formed tables.
\<close>

lemma ftable_foldr_Un:
  "\<forall>(t, rel) \<in> set aux. ftable n R rel \<Longrightarrow>
     ftable n R (foldr (\<union>) [rel. (t, rel) \<leftarrow> aux, P t] {})"
  by (induct aux) (auto simp: table_def split: if_splits)

lemma fauxlist_join:
  assumes sub: "L \<subseteq> R" and r1: "ftable n L rel1"
  shows "\<forall>(t, rel) \<in> set aux. ftable n R rel \<Longrightarrow>
    \<forall>(t, rel) \<in> set (map (\<lambda>(t, rel). (t, join rel pos rel1)) aux). ftable n R rel"
proof (induct aux)
  case (Cons p aux)
  obtain v rel where p: "p = (v, rel)" by (cases p)
  have t: "ftable n R rel" using Cons.prems p by simp
  have tj: "table n R (join rel pos rel1)"
    by (rule join_table[of n R rel L rel1 pos R]) (use t r1 sub in auto)
  have fj: "finite (join rel pos rel1)" using t r1 by (simp add: finite_join)
  show ?case using Cons.hyps Cons.prems tj fj p by simp
qed simp

lemma fauxlist_add_new_table:
  assumes a: "\<forall>(t, rel) \<in> set aux. ftable n R rel" and r2: "ftable n R rel2"
  shows "\<forall>(t, rel) \<in> set (case aux of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # aux).
         ftable n R rel"
  using assms by (cases aux) (auto simp: table_def)

definition saux_inv :: "args \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> ts \<Rightarrow>
    event_data mbuf2S \<Rightarrow> mmasaux \<Rightarrow> bool" where
  "saux_inv args n L R u buf aux \<longleftrightarrow>
     (\<exists>cur auxlist. valid_mmasaux args cur aux auxlist \<and> cur \<le> u \<and>
        (\<forall>(t, rel) \<in> set auxlist. ftable n R rel) \<and>
        (case buf of (xs, ys, tss, sk) \<Rightarrow>
           list_all (ftable n L) xs \<and> list_all (ftable n R) ys \<and>
           sorted tss \<and> (\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> u)))"

lemma saux_invI:
  "valid_mmasaux args cur aux auxlist \<Longrightarrow> cur \<le> u \<Longrightarrow>
   (\<forall>(t, rel) \<in> set auxlist. ftable n R rel) \<Longrightarrow>
   list_all (ftable n L) xs \<Longrightarrow> list_all (ftable n R) ys \<Longrightarrow>
   sorted tss \<Longrightarrow> \<forall>t \<in> set tss. cur \<le> t \<and> t \<le> u \<Longrightarrow>
   saux_inv args n L R u (xs, ys, tss, sk) aux"
  unfolding saux_inv_def by (auto simp del: valid_mmasaux.simps)

lemma saux_invE:
  assumes "saux_inv args n L R u (xs, ys, tss, sk) aux"
  obtains cur auxlist where "valid_mmasaux args cur aux auxlist" and "cur \<le> u"
    and "\<forall>(t, rel) \<in> set auxlist. ftable n R rel"
    and "list_all (ftable n L) xs" and "list_all (ftable n R) ys"
    and "sorted tss" and "\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> u"
  using assms unfolding saux_inv_def by (auto simp del: valid_mmasaux.simps)

lemma ftable_result_mmasaux:
  assumes v: "valid_mmasaux args cur aux auxlist"
    and w: "\<forall>(t, rel) \<in> set auxlist. ftable n R rel"
    and agg: "args_agg args = None"
  shows "ftable n R (result_mmasaux args aux)"
  using default_mmasaux.valid_result_msaux[OF v] agg ftable_foldr_Un[OF w]
  by (simp add: eval_args_agg_def)

text \<open>A fresh batch enters the buffer at or after the bound, which becomes the batch's last
  timestamp.\<close>

lemma saux_inv_add:
  assumes r: "saux_inv args n L R u buf aux"
    and lx: "list_all (ftable n L) xs" and ly: "list_all (ftable n R) ys"
    and s: "sorted ts" and b: "\<forall>t \<in> set ts. u \<le> t"
  shows "saux_inv args n L R (dnext u ts) (mbuf2S_add xs ys ts buf) aux"
proof (cases buf)
  case (fields us vs tss sk)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist" and cu: "cur \<le> u"
    and wa: "\<forall>(t, rel) \<in> set auxlist. ftable n R rel"
    and lu: "list_all (ftable n L) us" and lv: "list_all (ftable n R) vs"
    and st: "sorted tss" and ct: "\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> u"
    using r unfolding fields by (rule saux_invE)
  have "sorted (tss @ ts)" using st s ct b
    by (fastforce simp: sorted_append intro: order_trans)
  moreover have "\<forall>t \<in> set (tss @ ts). cur \<le> t \<and> t \<le> dnext u ts"
    using ct b cu dnext_ge[OF b] dnext_bound[OF s] by fastforce
  ultimately show ?thesis unfolding fields
    using saux_invI[OF vw order_trans[OF cu dnext_ge[OF b]] wa,
      where xs = "us @ xs" and ys = "vs @ ys" and tss = "tss @ ts" and sk = sk] lu lx lv ly
    by simp
qed

text \<open>
  One firing of @{const meval_since} keeps the invariant and only ever appends results of the
  structure, which by @{thm [source] ftable_result_mmasaux} are tables over the node's columns.
  The induction is the kernel's own recursion, the same one
  @{thm [source] eval_since_rel} follows.
\<close>

lemma eval_since_ftable:
  fixes args :: args
  assumes agg: "args_agg args = None" and an: "args_n args = n"
    and aL: "args_L args = L" and aR: "args_R args = R" and sub: "L \<subseteq> R"
  shows "meval_since args rs buf aux = (zs, buf', aux') \<Longrightarrow>
    saux_inv args n L R u buf aux \<Longrightarrow> list_all (ftable n R) rs \<Longrightarrow>
    list_all (ftable n R) zs \<and> saux_inv args n L R u buf' aux'"
proof (induction rs buf aux arbitrary: zs buf' aux'
    taking: args rule: default_maux.eval_since.induct)
  case (1 rs x xs t tss skew aux)
  note E = 1(1) and R = 1(2) and Q = 1(3)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist" and cu: "cur \<le> u"
    and wa: "\<forall>(t, rel) \<in> set auxlist. ftable n R rel"
    and lx: "list_all (ftable n L) (x # xs)"
    and st: "sorted (t # tss)" and ct: "\<forall>v \<in> set (t # tss). cur \<le> v \<and> v \<le> u"
    using R by (rule saux_invE)
  have tx: "ftable n L x" using lx by simp
  have ctu: "cur \<le> t" using ct by simp
  show ?case
  proof (cases "skew \<or> memL (args_ivl args) 0")
    case True
    show ?thesis using E R Q True by (auto simp: list_all_iff)
  next
    case False
    let ?wa = "gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)"
    let ?al = "map (\<lambda>(v, rel). (v, join rel (args_pos args) x))
        (filter (\<lambda>(v, rel). memR (args_ivl args) (t - v)) auxlist)"
    have vw': "valid_mmasaux args t ?wa ?al"
      by (rule default_mmasaux.valid_join_msaux
          [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu]]) (use tx an aL in simp)
    have wa': "\<forall>(v, rel) \<in> set ?al. ftable n R rel"
      by (rule fauxlist_join[OF sub tx]) (use wa in auto)
    have EW: "meval_since args rs (x # xs, [], t # tss, skew) aux
        = (rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa)"
      using False by (simp add: Let_def)
    have EE: "(rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa) = (zs, buf', aux')"
      by (rule trans[OF EW[symmetric] E])
    have tr: "ftable n R (result_mmasaux args ?wa)"
      by (rule ftable_result_mmasaux[OF vw' wa' agg])
    have R': "saux_inv args n L R u (xs, [], tss, True) ?wa"
      by (rule saux_invI[OF vw' _ wa']) (use lx st ct in auto)
    show ?thesis using EE Q tr R' by auto
  qed
next
  case (2 rs xs y ys tss aux)
  note IH = 2(1) and E = 2(2) and R = 2(3) and Q = 2(4)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist" and cu: "cur \<le> u"
    and wa: "\<forall>(t, rel) \<in> set auxlist. ftable n R rel"
    and lx: "list_all (ftable n L) xs" and ly: "list_all (ftable n R) (y # ys)"
    and st: "sorted tss" and ct: "\<forall>v \<in> set tss. cur \<le> v \<and> v \<le> u"
    using R by (rule saux_invE)
  have ty: "ftable n R y" using ly by simp
  let ?al = "case auxlist of [] \<Rightarrow> [(cur, y)]
      | ((v, w) # r) \<Rightarrow> if v = cur then (v, w \<union> y) # r else (cur, y) # auxlist"
  have vw': "valid_mmasaux args cur (add_new_table_mmasaux args y aux) ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vw]) (use ty an aR in simp)
  have wa': "\<forall>(v, rel) \<in> set ?al. ftable n R rel"
    by (rule fauxlist_add_new_table[OF wa ty])
  have E': "meval_since args rs (xs, ys, tss, False) (add_new_table_mmasaux args y aux)
      = (zs, buf', aux')" using E by simp
  have R': "saux_inv args n L R u (xs, ys, tss, False) (add_new_table_mmasaux args y aux)"
    by (rule saux_invI[OF vw' cu wa']) (use lx ly st ct in auto)
  show ?case by (rule IH[OF E' R' Q])
next
  case (3 rs x xs y ys t tss aux)
  note IH = 3(1) and E = 3(2) and R = 3(3) and Q = 3(4)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist" and cu: "cur \<le> u"
    and wa: "\<forall>(v, rel) \<in> set auxlist. ftable n R rel"
    and lx: "list_all (ftable n L) (x # xs)" and ly: "list_all (ftable n R) (y # ys)"
    and st: "sorted (t # tss)" and ct: "\<forall>v \<in> set (t # tss). cur \<le> v \<and> v \<le> u"
    using R by (rule saux_invE)
  have tx: "ftable n L x" using lx by simp
  have ty: "ftable n R y" using ly by simp
  have ctu: "cur \<le> t" using ct by simp
  let ?jl = "map (\<lambda>(v, rel). (v, join rel (args_pos args) x))
      (filter (\<lambda>(v, rel). memR (args_ivl args) (t - v)) auxlist)"
  let ?al = "case ?jl of [] \<Rightarrow> [(t, y)]
      | ((v, w) # r) \<Rightarrow> if v = t then (v, w \<union> y) # r else (t, y) # ?jl"
  let ?wa = "add_new_table_mmasaux args y
      (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux))"
  have vwj: "valid_mmasaux args t (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)) ?jl"
    by (rule default_mmasaux.valid_join_msaux
        [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu]]) (use tx an aL in simp)
  have wj: "\<forall>(v, rel) \<in> set ?jl. ftable n R rel"
    by (rule fauxlist_join[OF sub tx]) (use wa in auto)
  have vw': "valid_mmasaux args t ?wa ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vwj]) (use ty an aR in simp)
  have wa': "\<forall>(v, rel) \<in> set ?al. ftable n R rel"
    by (rule fauxlist_add_new_table[OF wj ty])
  have tr: "ftable n R (result_mmasaux args ?wa)"
    by (rule ftable_result_mmasaux[OF vw' wa' agg])
  have E': "meval_since args (result_mmasaux args ?wa # rs) (xs, ys, tss, False) ?wa
      = (zs, buf', aux')" using E by (simp add: Let_def)
  have R': "saux_inv args n L R u (xs, ys, tss, False) ?wa"
    by (rule saux_invI[OF vw' _ wa']) (use lx ly st ct in auto)
  have Q': "list_all (ftable n R) (result_mmasaux args ?wa # rs)" using tr Q by simp
  show ?case by (rule IH[OF refl E' R' Q'])
qed auto

lemma produces_MSince:
  fixes args :: args
  assumes p1: "produces n L tw \<phi>" and p2: "produces n R tw \<psi>"
    and r: "saux_inv args n L R tw buf aux"
    and agg: "args_agg args = None" and an: "args_n args = n"
    and aL: "args_L args = L" and aR: "args_R args = R" and sub: "L \<subseteq> R"
  shows "produces n R tw (mformula.MSince args \<phi> \<psi> buf aux)"
proof (rule producesI[where X = "\<lambda>n' A' u \<Phi>. n' = n \<and> A' = R \<and>
    (\<exists>\<chi> \<eta> bf ax. \<Phi> = mformula.MSince args \<chi> \<eta> bf ax \<and>
       produces n L u \<chi> \<and> produces n R u \<eta> \<and> saux_inv args n L R u bf ax)"])
  show "n = n \<and> R = R \<and> (\<exists>\<chi> \<eta> bf ax. mformula.MSince args \<phi> \<psi> buf aux
      = mformula.MSince args \<chi> \<eta> bf ax \<and> produces n L tw \<chi> \<and> produces n R tw \<eta> \<and>
      saux_inv args n L R tw bf ax)"
    using p1 p2 r by blast
next
  fix n' A' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = R \<and> (\<exists>\<chi> \<eta> bf ax. \<Phi> = mformula.MSince args \<chi> \<eta> bf ax \<and>
      produces n L u \<chi> \<and> produces n R u \<eta> \<and> saux_inv args n L R u bf ax)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> \<eta> bf ax where Phi: "\<Phi> = mformula.MSince args \<chi> \<eta> bf ax"
    and pc: "produces n L u \<chi>" and pe: "produces n R u \<eta>"
    and inv: "saux_inv args n L R u bf ax" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  obtain bs \<eta>' where e2: "meval j n ts db \<eta> = (bs, \<eta>')" by (cases "meval j n ts db \<eta>")
  obtain zs bf' ax' where e3: "meval_since args [] (mbuf2S_add as bs ts bf) ax = (zs, bf', ax')"
    by (cases "meval_since args [] (mbuf2S_add as bs ts bf) ax")
  have x: "xs = zs" and f: "\<Phi>' = mformula.MSince args \<chi>' \<eta>' bf' ax'"
    using e X Phi e1 e2 e3 an by simp_all
  have ta: "list_all (ftable n L) as" by (rule produces_tables[OF pc w sts mts e1])
  have tb: "list_all (ftable n R) bs" by (rule produces_tables[OF pe w sts mts e2])
  have add: "saux_inv args n L R (dnext u ts) (mbuf2S_add as bs ts bf) ax"
    by (rule saux_inv_add[OF inv ta tb sts mts])
  have step: "list_all (ftable n R) zs \<and> saux_inv args n L R (dnext u ts) bf' ax'"
    by (rule eval_since_ftable[OF agg an aL aR sub e3 add]) simp
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = R \<and>
          (\<exists>\<chi> \<eta> bf ax. \<Phi>' = mformula.MSince args \<chi> \<eta> bf ax \<and>
             produces n L (dnext u ts) \<chi> \<and> produces n R (dnext u ts) \<eta> \<and>
             saux_inv args n L R (dnext u ts) bf ax)) \<or>
       produces n' A' (dnext u ts) \<Phi>')"
    using X step produces_next[OF pc w sts mts e1] produces_next[OF pe w sts mts e2]
    by (auto simp: x f)
qed

subsection \<open>The Until node\<close>

text \<open>
  The Until node's invariant is again the wide half of the relation
  @{theory MFODL_Monitor_Imp.Dense_Eval} carries: the verified structure is valid for an abstract
  auxiliary list whose two table components are finite tables over the operands' columns.  The
  structure is stepped from inside a buffer traversal, so the traversal gets its own invariant
  lemma first.
\<close>

lemma mbuf2t_take_inv:
  "(\<And>a b v w z. a \<in> set xs \<Longrightarrow> b \<in> set ys \<Longrightarrow> Q w z \<Longrightarrow> w \<le> v \<Longrightarrow>
      Q v (f a b v z)) \<Longrightarrow>
   Q u0 z \<Longrightarrow> u0 \<le> t0 \<Longrightarrow> sorted ts \<Longrightarrow> (\<forall>v \<in> set ts. u0 \<le> v) \<Longrightarrow>
   mbuf2t_take f z (xs, ys) t0 ts = (w, (xs', ys'), nt, ts') \<Longrightarrow>
   (\<exists>v. Q v w \<and> v \<le> nt \<and> (\<forall>u \<in> set ts'. v \<le> u)) \<and> sorted ts' \<and>
     (nt = t0 \<or> nt \<in> set ts) \<and> set ts' \<subseteq> set ts"
proof (induct xs arbitrary: ys z u0 t0 ts w xs' ys' nt ts')
  case Nil
  note r = Nil(2) and le = Nil(3) and s = Nil(4) and mb = Nil(5) and P = Nil(6)
  have w: "w = z" and ts': "ts' = ts"
    and nt: "nt = (case ts of [] \<Rightarrow> t0 | v # _ \<Rightarrow> v)"
    using P by (auto split: list.splits)
  have "u0 \<le> nt" using le mb unfolding nt by (cases ts) auto
  then show ?case using r s mb unfolding w ts' nt by (cases ts) auto
next
  case (Cons x xs)
  note step = Cons(2) and r = Cons(3) and le = Cons(4) and s = Cons(5)
    and mb = Cons(6) and P = Cons(7) and IH = Cons(1)
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using P r le s mb by (auto split: list.splits)
  next
    case (Cons y ys0)
    show ?thesis
    proof (cases ts)
      case Nil
      then show ?thesis using P r le s mb \<open>ys = y # ys0\<close> by (auto split: list.splits)
    next
      case (Cons v ts0)
      have e: "mbuf2t_take f (f x y v z) (xs, ys0) v ts0 = (w, (xs', ys'), nt, ts')"
        using P \<open>ys = y # ys0\<close> Cons by simp
      have rt: "Q v (f x y v z)"
        using step[of x y u0 z v] r mb Cons \<open>ys = y # ys0\<close> by simp
      have s0: "sorted ts0" using s Cons by simp
      have mb0: "\<forall>u \<in> set ts0. v \<le> u" using s Cons by simp
      have "(\<exists>u. Q u w \<and> u \<le> nt \<and> (\<forall>u' \<in> set ts'. u \<le> u')) \<and> sorted ts' \<and>
          (nt = v \<or> nt \<in> set ts0) \<and> set ts' \<subseteq> set ts0"
        by (rule IH[OF _ rt order_refl s0 mb0 e]) (use step \<open>ys = y # ys0\<close> in auto)
      then show ?thesis using Cons by auto
    qed
  qed
qed

lemma fauxlist3_update_until:
  assumes wf: "\<forall>(t, a1, a2) \<in> set aux. ftable n L a1 \<and> ftable n R a2"
    and sub: "L \<subseteq> R" and t1: "ftable n L rel1" and t2: "ftable n R rel2"
  shows "\<forall>(t, a1, a2) \<in> set (update_until args rel1 rel2 nt aux).
      ftable n L a1 \<and> ftable n R a2"
proof safe
  have w: "\<And>t b1 b2. (t, b1, b2) \<in> set aux \<Longrightarrow> ftable n L b1 \<and> ftable n R b2"
    using wf by auto
  fix t a1 a2 assume m: "(t, a1, a2) \<in> set (update_until args rel1 rel2 nt aux)"
  show "table n L a1"
    using m t1 t2 by (auto simp: update_until_def dest!: w intro: table_join_same table_Un)
  show "finite a1"
    using m t1 t2 by (auto simp: update_until_def finite_join dest!: w)
  show "table n R a2"
    using m t1 t2 sub
    by (auto simp: update_until_def dest!: w intro!: table_Un intro: table_join_sub)
  show "finite a2"
    using m t1 t2 by (auto simp: update_until_def finite_join empty_table_def dest!: w)
qed

definition uaux_inv :: "args \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> ts \<Rightarrow> muaux_dq \<Rightarrow> bool" where
  "uaux_inv args n L R cur aux \<longleftrightarrow>
     (\<exists>auxlist. valid_muaux_dq args cur aux auxlist \<and>
        (\<forall>(t, a1, a2) \<in> set auxlist. ftable n L a1 \<and> ftable n R a2))"

lemma uaux_inv_step:
  assumes v: "uaux_inv args n L R u aux"
    and sub: "L \<subseteq> R" and an: "args_n args = n" and aL: "args_L args = L"
    and aR: "args_R args = R"
    and t1: "ftable n L a" and t2: "ftable n R b" and ut: "u \<le> t"
  shows "uaux_inv args n L R t (add_new_muaux_dq args a b t aux)"
proof -
  obtain auxlist where vw: "valid_muaux_dq args u aux auxlist"
    and wf: "\<forall>(v, a1, a2) \<in> set auxlist. ftable n L a1 \<and> ftable n R a2"
    using v unfolding uaux_inv_def by blast
  have "valid_muaux_dq args t (add_new_muaux_dq args a b t aux)
      (update_until args a b t auxlist)"
    by (rule valid_add_new_muaux_dq[OF vw _ _ ut]) (use t1 t2 an aL aR in simp_all)
  moreover have "\<forall>(v, a1, a2) \<in> set (update_until args a b t auxlist).
      ftable n L a1 \<and> ftable n R a2"
    by (rule fauxlist3_update_until[OF wf sub t1 t2])
  ultimately show ?thesis unfolding uaux_inv_def by blast
qed

lemma eval_until_ftable:
  "eval_until I nt auxlist = (res, auxlist') \<Longrightarrow>
   (\<forall>(t, a1, a2) \<in> set auxlist. ftable n L a1 \<and> ftable n R a2) \<Longrightarrow>
   list_all (ftable n R) res \<and>
     (\<forall>(t, a1, a2) \<in> set auxlist'. ftable n L a1 \<and> ftable n R a2)"
  by (induct I nt auxlist arbitrary: res auxlist' rule: eval_until.induct)
    (auto split: if_splits prod.splits)

lemma uaux_inv_eval:
  assumes v: "uaux_inv args n L R cur aux" and nt: "cur \<le> nt"
    and agg: "args_agg args = None"
    and we: "eval_muaux_dq args nt aux = (zs, aux')"
  shows "list_all (ftable n R) zs \<and> uaux_inv args n L R cur aux'"
proof -
  obtain auxlist where vw: "valid_muaux_dq args cur aux auxlist"
    and wf: "\<forall>(t, a1, a2) \<in> set auxlist. ftable n L a1 \<and> ftable n R a2"
    using v unfolding uaux_inv_def by blast
  obtain res auxlist' where eu: "eval_until (args_ivl args) nt auxlist = (res, auxlist')"
    by (cases "eval_until (args_ivl args) nt auxlist")
  have w: "valid_muaux_dq args cur aux' auxlist' \<and> zs = map (eval_args_agg args) res"
    by (rule valid_eval_muaux_dq[OF vw nt we eu])
  have u: "list_all (ftable n R) res \<and>
      (\<forall>(t, a1, a2) \<in> set auxlist'. ftable n L a1 \<and> ftable n R a2)"
    by (rule eval_until_ftable[OF eu wf])
  show ?thesis using w u agg unfolding uaux_inv_def
    by (auto simp: eval_args_agg_def list_all_iff)
qed

definition until_inv :: "args \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow>
    muaux_dq \<Rightarrow> event_data mbuf2 \<Rightarrow> ts list \<Rightarrow> bool" where
  "until_inv args n L R u t aux buf nts \<longleftrightarrow>
     (\<exists>cur. uaux_inv args n L R cur aux \<and> cur \<le> t \<and> t \<le> u \<and>
        list_all (ftable n L) (fst buf) \<and> list_all (ftable n R) (snd buf) \<and>
        sorted nts \<and> (\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> u))"

text \<open>
  One firing of the Until node: the buffer traversal steps the structure at each timestamp it
  consumes, and one evaluation at the timestamp the traversal reports yields the node's output.
\<close>

lemma until_step_ftable:
  fixes args :: args
  assumes sub: "L \<subseteq> R" and agg: "args_agg args = None" and an: "args_n args = n"
    and aL: "args_L args = L" and aR: "args_R args = R"
    and rel: "until_inv args n L R u t aux buf nts"
    and ta: "list_all (ftable n L) as" and tb: "list_all (ftable n R) bs"
    and s: "sorted tss" and bnd: "\<forall>v \<in> set tss. u \<le> v"
    and we: "mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add as bs buf) t (nts @ tss)
      = (aux1, buf1, nt, nts1)"
    and wev: "eval_muaux_dq args nt aux1 = (zs, aux2)"
  shows "list_all (ftable n R) zs \<and> until_inv args n L R (dnext u tss) nt aux2 buf1 nts1"
proof -
  obtain cur where vr: "uaux_inv args n L R cur aux" and ct: "cur \<le> t" and ttw: "t \<le> u"
    and lu: "list_all (ftable n L) (fst buf)"
    and lv: "list_all (ftable n R) (snd buf)"
    and sn: "sorted nts" and cn: "\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> u"
    using rel unfolding until_inv_def by blast
  obtain b1 b2 where bfs: "buf1 = (b1, b2)" by (cases buf1)
  define us where "us = fst buf @ as"
  define vs where "vs = snd buf @ bs"
  have ma: "mbuf2_add as bs buf = (us, vs)" by (cases buf) (simp add: us_def vs_def)
  have lus: "list_all (ftable n L) us" using lu ta by (simp add: us_def)
  have lvs: "list_all (ftable n R) vs" using lv tb by (simp add: vs_def)
  have step: "\<And>a b v w z. a \<in> set us \<Longrightarrow> b \<in> set vs \<Longrightarrow>
      uaux_inv args n L R w z \<Longrightarrow> w \<le> v \<Longrightarrow>
      uaux_inv args n L R v (add_new_muaux_dq args a b v z)"
    using lus lvs by (intro uaux_inv_step[OF _ sub an aL aR]) (auto simp: list_all_iff)
  have sts: "sorted (nts @ tss)"
    using sn s cn bnd by (fastforce simp: sorted_append intro: order_trans)
  have cts: "\<forall>v \<in> set (nts @ tss). cur \<le> v" using cn bnd ct ttw by fastforce
  have tdn: "t \<le> dnext u tss" using ttw dnext_ge[OF bnd] by simp
  have bound: "\<forall>v \<in> set (nts @ tss). v \<le> dnext u tss"
    using cn dnext_ge[OF bnd] dnext_bound[OF s] by fastforce
  have we': "mbuf2t_take (add_new_muaux_dq args) aux (us, vs) t (nts @ tss)
      = (aux1, (b1, b2), nt, nts1)" using we unfolding ma bfs by simp
  have Rr: "(\<exists>v. uaux_inv args n L R v aux1 \<and> v \<le> nt \<and> (\<forall>w \<in> set nts1. v \<le> w)) \<and>
      sorted nts1 \<and> (nt = t \<or> nt \<in> set (nts @ tss)) \<and> set nts1 \<subseteq> set (nts @ tss)"
    by (rule mbuf2t_take_inv[OF step vr ct sts cts we'])
  obtain v where vu: "uaux_inv args n L R v aux1" and unt: "v \<le> nt"
    and un: "\<forall>w \<in> set nts1. v \<le> w" using Rr by blast
  have sn1: "sorted nts1" and sub1: "set nts1 \<subseteq> set (nts @ tss)" using Rr by blast+
  have ntdn: "nt \<le> dnext u tss" using Rr tdn bound by blast
  have ev: "list_all (ftable n R) zs \<and> uaux_inv args n L R v aux2"
    by (rule uaux_inv_eval[OF vu unt agg wev])
  have sb: "set b1 \<subseteq> set us \<and> set b2 \<subseteq> set vs" by (rule mbuf2t_take_sub[OF we'])
  have lb1: "list_all (ftable n L) b1" using sb lus by (auto simp: list_all_iff)
  have lb2: "list_all (ftable n R) b2" using sb lvs by (auto simp: list_all_iff)
  have "uaux_inv args n L R v aux2 \<and> v \<le> nt \<and> nt \<le> dnext u tss \<and>
      list_all (ftable n L) (fst buf1) \<and> list_all (ftable n R) (snd buf1) \<and>
      sorted nts1 \<and> (\<forall>w \<in> set nts1. v \<le> w \<and> w \<le> dnext u tss)"
    using ev unt ntdn lb1 lb2 sn1 un sub1 bound bfs by auto
  then have "until_inv args n L R (dnext u tss) nt aux2 buf1 nts1"
    unfolding until_inv_def by blast
  then show ?thesis using ev by simp
qed

lemma produces_MUntil:
  fixes args :: args
  assumes p1: "produces n L tw \<phi>" and p2: "produces n R tw \<psi>"
    and r: "until_inv args n L R tw t aux buf nts"
    and agg: "args_agg args = None" and an: "args_n args = n"
    and aL: "args_L args = L" and aR: "args_R args = R" and sub: "L \<subseteq> R"
  shows "produces n R tw (mformula.MUntil args \<phi> \<psi> buf nts t aux)"
proof (rule producesI[where X = "\<lambda>n' A' u \<Phi>. n' = n \<and> A' = R \<and>
    (\<exists>\<chi> \<eta> bf ns tt ax. \<Phi> = mformula.MUntil args \<chi> \<eta> bf ns tt ax \<and>
       produces n L u \<chi> \<and> produces n R u \<eta> \<and>
       until_inv args n L R u tt ax bf ns)"])
  show "n = n \<and> R = R \<and> (\<exists>\<chi> \<eta> bf ns tt ax.
      mformula.MUntil args \<phi> \<psi> buf nts t aux = mformula.MUntil args \<chi> \<eta> bf ns tt ax \<and>
      produces n L tw \<chi> \<and> produces n R tw \<eta> \<and> until_inv args n L R tw tt ax bf ns)"
    using p1 p2 r by blast
next
  fix n' A' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = R \<and> (\<exists>\<chi> \<eta> bf ns tt ax.
      \<Phi> = mformula.MUntil args \<chi> \<eta> bf ns tt ax \<and>
      produces n L u \<chi> \<and> produces n R u \<eta> \<and> until_inv args n L R u tt ax bf ns)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>v \<in> set ts. u \<le> v"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> \<eta> bf ns tt ax where Phi: "\<Phi> = mformula.MUntil args \<chi> \<eta> bf ns tt ax"
    and pc: "produces n L u \<chi>" and pe: "produces n R u \<eta>"
    and inv: "until_inv args n L R u tt ax bf ns" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  obtain bs \<eta>' where e2: "meval j n ts db \<eta> = (bs, \<eta>')" by (cases "meval j n ts db \<eta>")
  obtain ax1 bf1 nt ns1 where e3:
    "mbuf2t_take (add_new_muaux_dq args) ax (mbuf2_add as bs bf) tt (ns @ ts)
       = (ax1, bf1, nt, ns1)"
    by (cases "mbuf2t_take (add_new_muaux_dq args) ax (mbuf2_add as bs bf) tt (ns @ ts)")
      auto
  obtain zs ax2 where e4: "eval_muaux_dq args nt ax1 = (zs, ax2)"
    by (cases "eval_muaux_dq args nt ax1")
  have x: "xs = zs" and f: "\<Phi>' = mformula.MUntil args \<chi>' \<eta>' bf1 ns1 nt ax2"
    using e X Phi e1 e2 e3 e4 an by simp_all
  have ta: "list_all (ftable n L) as" by (rule produces_tables[OF pc w sts mts e1])
  have tb: "list_all (ftable n R) bs" by (rule produces_tables[OF pe w sts mts e2])
  have step: "list_all (ftable n R) zs \<and>
      until_inv args n L R (dnext u ts) nt ax2 bf1 ns1"
    by (rule until_step_ftable[OF sub agg an aL aR inv ta tb sts mts e3 e4])
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = R \<and>
          (\<exists>\<chi> \<eta> bf ns tt ax. \<Phi>' = mformula.MUntil args \<chi> \<eta> bf ns tt ax \<and>
             produces n L (dnext u ts) \<chi> \<and> produces n R (dnext u ts) \<eta> \<and>
             until_inv args n L R (dnext u ts) tt ax bf ns)) \<or>
       produces n' A' (dnext u ts) \<Phi>')"
    using X step produces_next[OF pc w sts mts e1] produces_next[OF pe w sts mts e2]
    by (auto simp: x f)
qed

subsection \<open>The let node\<close>

text \<open>
  A let node evaluates its body against a database extended by the bound predicate.  Since
  @{const produces} quantifies over every well-formed database, the body's own invariant applies
  to the extended one as soon as the extension is well formed -- which it is, because the
  definition evaluates the bound formula at the full frame @{term "{0..<m}"}, exactly the shape
  @{const wf_db} asks of a stored relation of arity @{term m}.
\<close>

lemma wf_db_update:
  "wf_db db \<Longrightarrow> list_all (ftable m {0..<m}) xs \<Longrightarrow>
     wf_db (Mapping.update (p, m) xs db)"
  by (auto simp: wf_db_def lookup_update' split: if_splits)

lemma produces_MLet:
  assumes p1: "produces m {0..<m} tw \<phi>" and p2: "produces n A tw \<psi>"
  shows "produces n A tw (mformula.MLet p m \<phi> \<psi>)"
proof (rule producesI[where X = "\<lambda>n' A' u \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<chi> \<eta>. \<Phi> = mformula.MLet p m \<chi> \<eta> \<and>
       produces m {0..<m} u \<chi> \<and> produces n A u \<eta>)"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi> \<eta>. mformula.MLet p m \<phi> \<psi> = mformula.MLet p m \<chi> \<eta> \<and>
      produces m {0..<m} tw \<chi> \<and> produces n A tw \<eta>)" using p1 p2 by blast
next
  fix n' A' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>\<chi> \<eta>. \<Phi> = mformula.MLet p m \<chi> \<eta> \<and>
      produces m {0..<m} u \<chi> \<and> produces n A u \<eta>)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> \<eta> where Phi: "\<Phi> = mformula.MLet p m \<chi> \<eta>"
    and pc: "produces m {0..<m} u \<chi>" and pe: "produces n A u \<eta>" by blast
  obtain as \<chi>' where e1: "meval j m ts db \<chi> = (as, \<chi>')" by (cases "meval j m ts db \<chi>")
  have ta: "list_all (ftable m {0..<m}) as" by (rule produces_tables[OF pc w sts mts e1])
  have w2: "wf_db (Mapping.update (p, m) as db)" by (rule wf_db_update[OF w ta])
  obtain bs \<eta>' where e2: "meval j n ts (Mapping.update (p, m) as db) \<eta> = (bs, \<eta>')"
    by (cases "meval j n ts (Mapping.update (p, m) as db) \<eta>")
  have tb: "list_all (ftable n A) bs" by (rule produces_tables[OF pe w2 sts mts e2])
  have x: "xs = bs" and f: "\<Phi>' = mformula.MLet p m \<chi>' \<eta>'"
    using e X Phi e1 e2 by simp_all
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and> (\<exists>\<chi> \<eta>. \<Phi>' = mformula.MLet p m \<chi> \<eta> \<and>
          produces m {0..<m} (dnext u ts) \<chi> \<and> produces n A (dnext u ts) \<eta>)) \<or>
       produces n' A' (dnext u ts) \<Phi>')"
    using X tb produces_next[OF pc w sts mts e1] produces_next[OF pe w2 sts mts e2]
    by (auto simp: x f)
qed

(*<*)
end
(*>*)

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
  assumes init: "X n A \<phi>"
    and step: "\<And>m B \<psi> j ts db xs \<psi>'. X m B \<psi> \<Longrightarrow> wf_db db \<Longrightarrow>
        meval j m ts db \<psi> = (xs, \<psi>') \<Longrightarrow>
        list_all (ftable m B) xs \<and> (X m B \<psi>' \<or> produces m B \<psi>')"
  shows "produces n A \<phi>"
  using init
proof (rule produces.coinduct)
  fix m B \<psi>
  assume X: "X m B \<psi>"
  have "\<forall>j ts db xs \<chi>. wf_db db \<longrightarrow> meval j m ts db \<psi> = (xs, \<chi>) \<longrightarrow>
      list_all (ftable m B) xs \<and> (X m B \<chi> \<or> produces m B \<chi>)"
    using step[OF X] by blast
  then show "\<exists>m' \<psi>' B'. m = m' \<and> B = B' \<and> \<psi> = \<psi>' \<and>
      (\<forall>j ts db xs \<chi>. wf_db db \<longrightarrow> meval j m' ts db \<psi>' = (xs, \<chi>) \<longrightarrow>
         list_all (ftable m' B') xs \<and> (X m' B' \<chi> \<or> produces m' B' \<chi>))"
    by blast
qed

text \<open>A node that does not change under evaluation.\<close>

lemma produces_fix:
  assumes "\<And>j ts db xs \<phi>'. wf_db db \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
      list_all (ftable n A) xs \<and> \<phi>' = \<phi>"
  shows "produces n A \<phi>"
  by (rule producesI[where X = "\<lambda>m B \<psi>. m = n \<and> B = A \<and> \<psi> = \<phi>"]) (use assms in auto)

text \<open>
  A node with one operand whose output is the operand's, mapped pointwise.  This covers every
  unary node of the kernel's language, and the table-and-finiteness obligation is the only thing
  that changes from one to the next.
\<close>

lemma produces_unop:
  assumes step: "\<And>j ts db \<psi> ys \<psi>'. meval j m ts db \<psi> = (ys, \<psi>') \<Longrightarrow>
      meval j n ts db (C \<psi>) = (map g ys, C \<psi>')"
    and tab: "\<And>Y. table m B Y \<Longrightarrow> finite Y \<Longrightarrow> table n A (g Y) \<and> finite (g Y)"
    and p: "produces m B \<phi>"
  shows "produces n A (C \<phi>)"
proof (rule producesI[where
    X = "\<lambda>n' A' \<psi>. n' = n \<and> A' = A \<and> (\<exists>\<chi>. \<psi> = C \<chi> \<and> produces m B \<chi>)"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi>. C \<phi> = C \<chi> \<and> produces m B \<chi>)" using p by blast
next
  fix n' A' \<psi> j ts db xs \<psi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>\<chi>. \<psi> = C \<chi> \<and> produces m B \<chi>)"
    and w: "wf_db db" and e: "meval j n' ts db \<psi> = (xs, \<psi>')"
  from X obtain \<chi> where pc: "produces m B \<chi>" and psi: "\<psi> = C \<chi>" by blast
  obtain ys \<chi>' where e': "meval j m ts db \<chi> = (ys, \<chi>')" by (cases "meval j m ts db \<chi>")
  have "meval j n ts db (C \<chi>) = (map g ys, C \<chi>')" by (rule step[OF e'])
  then have x: "xs = map g ys" and f: "\<psi>' = C \<chi>'" using e X psi by simp_all
  have t: "list_all (ftable m B) ys" by (rule produces_tables[OF pc w e'])
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and> (\<exists>\<chi>. \<psi>' = C \<chi> \<and> produces m B \<chi>)) \<or> produces n' A' \<psi>')"
    using X t produces_next[OF pc w e'] tab by (auto simp: x f list_all_iff)
qed

subsection \<open>Nodes whose output does not depend on the operand's tables\<close>

lemma produces_MRel: "table n A rel \<Longrightarrow> finite rel \<Longrightarrow> produces n A (mformula.MRel rel)"
proof (coinduction arbitrary: rel)
  case produces
  then show ?case by (auto simp: list_all_iff)
qed

lemma produces_MNeg: "produces n {} (mformula.MNeg \<phi>)"
proof (coinduction arbitrary: \<phi>)
  case produces
  then show ?case
    by (auto simp: list_all_iff unit_table_def empty_table_def table_def wf_tuple_def
        split: prod.splits)
qed


subsection \<open>The unary nodes\<close>

lemma produces_MAndRel:
  "produces n A \<phi> \<Longrightarrow> produces n A (mformula.MAndRel \<phi> conf)"
  by (rule produces_unop[where m = n and B = A and C = "\<lambda>\<psi>. mformula.MAndRel \<psi> conf"
      and g = "Set.filter (eval_constraint conf)"])
    (auto simp: table_def split: prod.splits)

lemma table_eval_assignment:
  "table n B Y \<Longrightarrow> fst conf < n \<Longrightarrow>
     table n (Set.insert (fst conf) B) (eval_assignment conf ` Y)"
  by (cases conf) (auto simp: table_def wf_tuple_def nth_list_update)

lemma produces_MAndAssign:
  assumes x: "fst conf < n" and p: "produces n B \<phi>"
  shows "produces n (Set.insert (fst conf) B) (mformula.MAndAssign \<phi> conf)"
  by (rule produces_unop[where m = n and B = B and C = "\<lambda>\<psi>. mformula.MAndAssign \<psi> conf"
      and g = "\<lambda>Y. eval_assignment conf ` Y", OF _ _ p])
    (use x in \<open>auto simp: table_eval_assignment split: prod.splits\<close>)

lemma produces_MExists:
  "produces (Suc n) B \<phi> \<Longrightarrow>
     produces n ((\<lambda>x. x - Suc 0) ` (B - {0})) (mformula.MExists \<phi>)"
  by (rule produces_unop[where m = "Suc n" and B = B and C = mformula.MExists
      and g = "\<lambda>Y. tl ` Y"])
    (auto simp: table_project split: prod.splits)


subsection \<open>The predicate and time nodes\<close>

lemma produces_MPred_Copy:
  assumes l: "length tms = n"
  shows "produces n {0..<n} (mformula.MPred e tms Copy)"
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
  shows "produces n (\<Union>t \<in> set tms. Formula.fv_trm t) (mformula.MPred e tms Simple)"
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
  "produces n (\<Union>t \<in> set tms. Formula.fv_trm t) (mformula.MPred e tms Match)"
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

lemma produces_MTP: "produces n (mtrm_cols mt) (mformula.MTP mt i)"
  by (rule producesI[where
      X = "\<lambda>m B \<psi>. m = n \<and> B = mtrm_cols mt \<and> (\<exists>k. \<psi> = mformula.MTP mt k)"])
    (auto simp: list_all_iff ftable_eval_mtrm)

lemma produces_MTS: "produces n (mtrm_cols mt) (mformula.MTS mt)"
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
    and p1: "produces n B1 \<phi>" and p2: "produces n B2 \<psi>"
    and bf1: "list_all (ftable n B1) (fst buf)" and bf2: "list_all (ftable n B2) (snd buf)"
  shows "produces n A (C \<phi> \<psi> buf)"
proof (rule producesI[where X = "\<lambda>n' A' \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<chi> \<eta> bf. \<Phi> = C \<chi> \<eta> bf \<and> produces n B1 \<chi> \<and> produces n B2 \<eta> \<and>
       list_all (ftable n B1) (fst bf) \<and> list_all (ftable n B2) (snd bf))"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi> \<eta> bf. C \<phi> \<psi> buf = C \<chi> \<eta> bf \<and> produces n B1 \<chi> \<and>
      produces n B2 \<eta> \<and> list_all (ftable n B1) (fst bf) \<and> list_all (ftable n B2) (snd bf))"
    using p1 p2 bf1 bf2 by blast
next
  fix n' A' \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>\<chi> \<eta> bf. \<Phi> = C \<chi> \<eta> bf \<and> produces n B1 \<chi> \<and>
      produces n B2 \<eta> \<and> list_all (ftable n B1) (fst bf) \<and> list_all (ftable n B2) (snd bf))"
    and w: "wf_db db" and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> \<eta> bf where Phi: "\<Phi> = C \<chi> \<eta> bf" and pc: "produces n B1 \<chi>"
    and pe: "produces n B2 \<eta>" and b1: "list_all (ftable n B1) (fst bf)"
    and b2: "list_all (ftable n B2) (snd bf)" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  obtain bs \<eta>' where e2: "meval j n ts db \<eta> = (bs, \<eta>')" by (cases "meval j n ts db \<eta>")
  obtain zs c1 c2 where e3: "mbuf2_take f (mbuf2_add as bs bf) = (zs, (c1, c2))"
    by (cases "mbuf2_take f (mbuf2_add as bs bf)") auto
  have "meval j n ts db (C \<chi> \<eta> bf) = (zs, C \<chi>' \<eta>' (c1, c2))" by (rule step[OF e1 e2 e3])
  then have x: "xs = zs" and f': "\<Phi>' = C \<chi>' \<eta>' (c1, c2)" using e X Phi by simp_all
  have ta: "list_all (ftable n B1) as" by (rule produces_tables[OF pc w e1])
  have tb: "list_all (ftable n B2) bs" by (rule produces_tables[OF pe w e2])
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
      ((n' = n \<and> A' = A \<and> (\<exists>\<chi> \<eta> bf. \<Phi>' = C \<chi> \<eta> bf \<and> produces n B1 \<chi> \<and> produces n B2 \<eta> \<and>
         list_all (ftable n B1) (fst bf) \<and> list_all (ftable n B2) (snd bf))) \<or>
       produces n' A' \<Phi>')"
    using X tz lc1 lc2 produces_next[OF pc w e1] produces_next[OF pe w e2]
    by (auto simp: x f')
qed

lemma produces_MOr:
  assumes p1: "produces n A \<phi>" and p2: "produces n A \<psi>"
    and bf1: "list_all (ftable n A) (fst buf)" and bf2: "list_all (ftable n A) (snd buf)"
  shows "produces n A (mformula.MOr \<phi> \<psi> buf)"
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
  assumes p1: "produces n A1 \<phi>" and p2: "produces n A2 \<psi>"
    and bf1: "list_all (ftable n A1) (fst buf)" and bf2: "list_all (ftable n A2) (snd buf)"
    and sub: "\<not> pos \<Longrightarrow> A2 \<subseteq> A1" and A: "A = (if pos then A1 \<union> A2 else A1)"
  shows "produces n A (mformula.MAnd A1 \<phi> pos A2 \<psi> buf)"
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
  assumes p: "produces n A \<phi>" and bf: "list_all (ftable n A) buf"
  shows "produces n A (mformula.MPrev I \<phi> first buf nts)"
proof (rule producesI[where X = "\<lambda>n' A' \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<chi> b bs nt. \<Phi> = mformula.MPrev I \<chi> b bs nt \<and> produces n A \<chi> \<and>
       list_all (ftable n A) bs)"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi> b bs nt. mformula.MPrev I \<phi> first buf nts
      = mformula.MPrev I \<chi> b bs nt \<and> produces n A \<chi> \<and> list_all (ftable n A) bs)"
    using p bf by blast
next
  fix n' A' \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>\<chi> b bs nt. \<Phi> = mformula.MPrev I \<chi> b bs nt \<and>
      produces n A \<chi> \<and> list_all (ftable n A) bs)"
    and w: "wf_db db" and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> b bs nt where Phi: "\<Phi> = mformula.MPrev I \<chi> b bs nt"
    and pc: "produces n A \<chi>" and lb: "list_all (ftable n A) bs" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  have ta: "list_all (ftable n A) as" by (rule produces_tables[OF pc w e1])
  obtain ws bs' nt' where e2: "mprev_next I (bs @ as) (nt @ ts) = (ws, bs', nt')"
    by (cases "mprev_next I (bs @ as) (nt @ ts)") auto
  have out: "list_all (ftable n A) ws \<and> list_all (ftable n A) bs'"
    by (rule mprev_next_out[OF e2]) (use lb ta in \<open>auto simp: table_def\<close>)
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and> (\<exists>\<chi> b bs nt. \<Phi>' = mformula.MPrev I \<chi> b bs nt \<and>
         produces n A \<chi> \<and> list_all (ftable n A) bs)) \<or> produces n' A' \<Phi>')"
    using X e Phi e1 e2 out lb ta produces_next[OF pc w e1]
    by (auto simp: table_def split: if_splits)
qed

lemma produces_MNext:
  assumes p: "produces n A \<phi>"
  shows "produces n A (mformula.MNext I \<phi> first nts)"
proof (rule producesI[where X = "\<lambda>n' A' \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<chi> b nt. \<Phi> = mformula.MNext I \<chi> b nt \<and> produces n A \<chi>)"])
  show "n = n \<and> A = A \<and> (\<exists>\<chi> b nt. mformula.MNext I \<phi> first nts
      = mformula.MNext I \<chi> b nt \<and> produces n A \<chi>)" using p by blast
next
  fix n' A' \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and> (\<exists>\<chi> b nt. \<Phi> = mformula.MNext I \<chi> b nt \<and> produces n A \<chi>)"
    and w: "wf_db db" and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> b nt where Phi: "\<Phi> = mformula.MNext I \<chi> b nt" and pc: "produces n A \<chi>"
    by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  have ta: "list_all (ftable n A) as" by (rule produces_tables[OF pc w e1])
  obtain cs b' where c: "(case (as, b) of (_ # as', True) \<Rightarrow> (as', False) | a \<Rightarrow> a) = (cs, b')"
    by (cases "(case (as, b) of (_ # as', True) \<Rightarrow> (as', False) | a \<Rightarrow> a)") auto
  have tc: "list_all (ftable n A) cs"
    using ta c by (cases as; cases b) auto
  obtain ws cs' nt' where e2: "mprev_next I cs (nt @ ts) = (ws, cs', nt')"
    by (cases "mprev_next I cs (nt @ ts)") auto
  have out: "list_all (ftable n A) ws \<and> list_all (ftable n A) cs'"
    by (rule mprev_next_out[OF e2]) (use tc in \<open>auto simp: table_def\<close>)
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and> (\<exists>\<chi> b nt. \<Phi>' = mformula.MNext I \<chi> b nt \<and> produces n A \<chi>)) \<or>
       produces n' A' \<Phi>')"
    using X e Phi e1 c e2 out produces_next[OF pc w e1] by auto
qed

(*<*)
end
(*>*)

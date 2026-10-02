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
  A table over a column list @{term ks} is one whose tuples have the length of @{term ks}, so
  most of the obligations are about lengths and finiteness.
\<close>

subsection \<open>The coinduction, packaged\<close>

lemma ftable_empty_table[simp]: "ftable ks empty_table"
  by (simp add: empty_table_def table_def)

lemma ftable_unit_table[simp]: "ftable [] unit_table"
  by (simp add: unit_table_def table_def)

text \<open>@{thm [source] produces.coinduct} with the trivial equations of its conclusion already
  solved, so that each node's lemma only has to name its own invariant.\<close>

lemma producesI[case_names init step]:
  assumes init: "X n ks tw \<phi>"
    and step: "\<And>m B u \<psi> j ts db xs \<psi>'. X m B u \<psi> \<Longrightarrow> wf_db db \<Longrightarrow>
        sorted ts \<Longrightarrow> (\<forall>t \<in> set ts. u \<le> t) \<Longrightarrow>
        meval j m ts db \<psi> = (xs, \<psi>') \<Longrightarrow>
        list_all (ftable B) xs \<and>
          (X m B (dnext u ts) \<psi>' \<or> produces m B (dnext u ts) \<psi>')"
  shows "produces n ks tw \<phi>"
  using init
proof (rule produces.coinduct)
  fix m B u \<psi>
  assume X: "X m B u \<psi>"
  have "\<forall>j ts db xs \<chi>. wf_db db \<longrightarrow> sorted ts \<longrightarrow>
      (\<forall>t \<in> set ts. u \<le> t) \<longrightarrow> meval j m ts db \<psi> = (xs, \<chi>) \<longrightarrow>
      list_all (ftable B) xs \<and>
        (X m B (dnext u ts) \<chi> \<or> produces m B (dnext u ts) \<chi>)"
    using step[OF X] by blast
  then show "\<exists>tw' n' \<phi>' ks'. m = n' \<and> B = ks' \<and> u = tw' \<and> \<psi> = \<phi>' \<and>
      (\<forall>j ts db xs \<chi>. wf_db db \<longrightarrow> sorted ts \<longrightarrow>
         (\<forall>t \<in> set ts. tw' \<le> t) \<longrightarrow> meval j n' ts db \<phi>' = (xs, \<chi>) \<longrightarrow>
         list_all (ftable ks') xs \<and>
           (X n' ks' (dnext tw' ts) \<chi> \<or> produces n' ks' (dnext tw' ts) \<chi>))"
    by blast
qed

text \<open>Raising the bound only weakens what the invariant promises about the batches to come.\<close>

lemma produces_mono:
  assumes p: "produces n ks u \<phi>" and le: "u \<le> u'"
  shows "produces n ks u' \<phi>"
proof (rule producesI[where X = "\<lambda>n'' B w \<psi>. n'' = n \<and> B = ks \<and>
    (\<exists>v. v \<le> w \<and> produces n ks v \<psi>)"])
  show "n = n \<and> ks = ks \<and> (\<exists>v. v \<le> u' \<and> produces n ks v \<phi>)" using p le by blast
next
  fix n'' B w \<psi> j ts db xs \<psi>'
  assume X: "n'' = n \<and> B = ks \<and> (\<exists>v. v \<le> w \<and> produces n ks v \<psi>)"
    and wf: "wf_db db" and s: "sorted ts" and b: "\<forall>t \<in> set ts. w \<le> t"
    and e: "meval j n'' ts db \<psi> = (xs, \<psi>')"
  from X obtain v where vw: "v \<le> w" and pv: "produces n ks v \<psi>" by blast
  have b': "\<forall>t \<in> set ts. v \<le> t" using b vw by force
  have e': "meval j n ts db \<psi> = (xs, \<psi>')" using e X by simp
  have t: "list_all (ftable ks) xs" by (rule produces_tables[OF pv wf s b' e'])
  have n': "produces n ks (dnext v ts) \<psi>'" by (rule produces_next[OF pv wf s b' e'])
  have "dnext v ts \<le> dnext w ts" using vw by (cases ts) (auto simp: dnext_def)
  then show "list_all (ftable B) xs \<and>
      ((n'' = n \<and> B = ks \<and> (\<exists>v. v \<le> dnext w ts \<and> produces n ks v \<psi>')) \<or>
       produces n'' B (dnext w ts) \<psi>')"
    using X t n' by blast
qed

text \<open>A node that does not change under evaluation.\<close>

lemma produces_fix:
  assumes "\<And>j ts db xs \<phi>'. wf_db db \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
      list_all (ftable ks) xs \<and> \<phi>' = \<phi>"
  shows "produces n ks tw \<phi>"
  by (rule producesI[where X = "\<lambda>m B u \<psi>. m = n \<and> B = ks \<and> \<psi> = \<phi>"])
    (use assms in auto)

text \<open>
  A node with one operand whose output is the operand's, mapped pointwise.  This covers every
  unary node of the kernel's language, and the table-and-finiteness obligation is the only thing
  that changes from one to the next.
\<close>

lemma produces_unop:
  assumes step: "\<And>j ts db \<psi> ys \<psi>'. meval j m ts db \<psi> = (ys, \<psi>') \<Longrightarrow>
      meval j n ts db (C \<psi>) = (map g ys, C \<psi>')"
    and tab: "\<And>Y. ftable B Y \<Longrightarrow> ftable ks (g Y)"
    and p: "produces m B tw \<phi>"
  shows "produces n ks tw (C \<phi>)"
proof (rule producesI[where
    X = "\<lambda>n' ks' u \<psi>. n' = n \<and> ks' = ks \<and> (\<exists>\<chi>. \<psi> = C \<chi> \<and> produces m B u \<chi>)"])
  show "n = n \<and> ks = ks \<and> (\<exists>\<chi>. C \<phi> = C \<chi> \<and> produces m B tw \<chi>)"
    using p by blast
next
  fix n' ks' u \<psi> j ts db xs \<psi>'
  assume X: "n' = n \<and> ks' = ks \<and> (\<exists>\<chi>. \<psi> = C \<chi> \<and> produces m B u \<chi>)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j n' ts db \<psi> = (xs, \<psi>')"
  from X obtain \<chi> where pc: "produces m B u \<chi>" and psi: "\<psi> = C \<chi>" by blast
  obtain ys \<chi>' where e': "meval j m ts db \<chi> = (ys, \<chi>')" by (cases "meval j m ts db \<chi>")
  have "meval j n ts db (C \<chi>) = (map g ys, C \<chi>')" by (rule step[OF e'])
  then have x: "xs = map g ys" and f: "\<psi>' = C \<chi>'" using e X psi by simp_all
  have t: "list_all (ftable B) ys" by (rule produces_tables[OF pc w sts mts e'])
  show "list_all (ftable ks') xs \<and>
      ((n' = n \<and> ks' = ks \<and> (\<exists>\<chi>. \<psi>' = C \<chi> \<and> produces m B (dnext u ts) \<chi>)) \<or>
       produces n' ks' (dnext u ts) \<psi>')"
    using X t produces_next[OF pc w sts mts e'] tab by (auto simp: x f list_all_iff)
qed

subsection \<open>Nodes whose output does not depend on the operand's tables\<close>

lemma produces_MRel: "ftable ks rel \<Longrightarrow> produces n ks tw (MRel rel)"
  by (rule produces_fix) (auto simp: list_all_iff)

lemma produces_MNeg: "produces n [] tw (MNeg \<phi>)"
proof (coinduction arbitrary: \<phi> tw)
  case produces
  then show ?case
    by (auto simp: list_all_iff split: prod.splits)
qed

subsection \<open>The unary nodes\<close>

lemma produces_MAndRel:
  "produces n ks tw \<phi> \<Longrightarrow> produces n ks tw (MAndRel cs \<phi> conf)"
  by (rule produces_unop[where m = n and B = ks and C = "\<lambda>\<psi>. MAndRel cs \<psi> conf"
      and g = "Set.filter (eval_constraint cs conf)"])
    (auto simp: table_def split: prod.splits)

lemma ftable_eval_assignment:
  "ftable ks Y \<Longrightarrow> ftable (ks @ [fst conf]) (eval_assignment cs conf ` Y)"
  by (cases conf) (auto simp: table_def wf_tuple_def)

lemma produces_MAndAssign:
  "produces n ks tw \<phi> \<Longrightarrow> produces n (ks @ [fst conf]) tw (MAndAssign cs \<phi> conf)"
  by (rule produces_unop[where m = n and B = ks and C = "\<lambda>\<psi>. MAndAssign cs \<psi> conf"
      and g = "\<lambda>Y. eval_assignment cs conf ` Y"])
    (auto simp: ftable_eval_assignment split: prod.splits)

lemma ftable_ex_proj: "finite Y \<Longrightarrow> ftable (ex_cols cs) (ex_proj cs ` Y)"
  by (auto simp: table_def wf_tuple_def ex_proj_def ex_cols_def)

lemma produces_MExists:
  "produces (Suc n) kks tw \<phi> \<Longrightarrow> produces n (ex_cols cs) tw (MExists cs \<phi>)"
  by (rule produces_unop[where m = "Suc n" and B = kks and C = "MExists cs"
      and g = "\<lambda>Y. ex_proj cs ` Y"])
    (auto simp: ftable_ex_proj split: prod.splits)

subsection \<open>The predicate and time nodes\<close>

text \<open>In copy and simple mode the node passes the database's tables on, which are over the
  positions of the predicate's arguments.\<close>

lemma produces_MPred_db:
  assumes l: "length ks = length tms" and md: "mode \<noteq> Match"
  shows "produces n ks tw (MPred e tms mode)"
proof (rule produces_fix)
  fix j ts db xs \<phi>'
  assume w: "wf_db db" and m: "meval j n ts db (MPred e tms mode) = (xs, \<phi>')"
  show "list_all (ftable ks) xs \<and> \<phi>' = MPred e tms mode"
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    then show ?thesis using m by (auto simp: list_all_iff table_def)
  next
    case (Some X)
    have "list_all (\<lambda>T. table [0..<length tms] T \<and> finite T) X"
      using wf_dbD[OF w Some] wf_dbD_finite[OF w Some] by (auto simp: list_all_iff)
    then have "list_all (ftable ks) X"
      using l by (auto simp: list_all_iff table_def wf_tuple_def)
    then show ?thesis using m Some md by (cases mode) auto
  qed
qed

lemma produces_MPred_Copy:
  "length tms = length ks \<Longrightarrow> produces n ks tw (MPred e tms Copy)"
  by (rule produces_MPred_db) simp_all

lemma length_smp_cols: "is_simple_pattern tms m \<Longrightarrow> length (smp_cols tms) = length tms"
  by (induct tms m rule: is_simple_pattern.induct) auto

lemma produces_MPred_Simple:
  "is_simple_pattern tms 0 \<Longrightarrow> produces n (smp_cols tms) tw (MPred e tms Simple)"
  by (rule produces_MPred_db) (simp_all add: length_smp_cols)

lemma produces_MPred_Match: "produces n (pred_cols tms) tw (MPred e tms Match)"
proof (rule produces_fix)
  fix j ts db xs \<phi>'
  assume w: "wf_db db" and m: "meval j n ts db (MPred e tms Match) = (xs, \<phi>')"
  show "list_all (ftable (pred_cols tms)) xs \<and> \<phi>' = MPred e tms Match"
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    then show ?thesis using m by (auto simp: list_all_iff table_def)
  next
    case (Some X)
    have "\<And>T. T \<in> set X \<Longrightarrow>
        ftable (pred_cols tms) (tabulate_match (pred_cols tms) ` Option.these (match tms ` T))"
      using wf_dbD_finite[OF w Some]
      by (auto simp: table_def wf_tuple_def tabulate_match_def Option.these_def)
    then show ?thesis using m Some by (auto simp: list_all_iff)
  qed
qed

lemma ftable_eval_mtrm: "ftable (mtrm_dcols mt) (eval_mtrm mt x)"
  by (cases mt)
    (auto simp: mtrm_dcols_def singleton_table_def unit_table_def table_def wf_tuple_def)

lemma produces_MTP: "produces n (mtrm_dcols mt) tw (MTP mt i)"
  by (rule producesI[where
      X = "\<lambda>m B u \<psi>. m = n \<and> B = mtrm_dcols mt \<and> (\<exists>k. \<psi> = MTP mt k)"])
    (auto simp: list_all_iff ftable_eval_mtrm)

lemma produces_MTS: "produces n (mtrm_dcols mt) tw (MTS mt)"
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
    and tab: "\<And>X Y. ftable B1 X \<Longrightarrow> ftable B2 Y \<Longrightarrow> ftable ks (f X Y)"
    and p1: "produces n B1 tw \<phi>" and p2: "produces n B2 tw \<psi>"
    and bf1: "list_all (ftable B1) (fst buf)" and bf2: "list_all (ftable B2) (snd buf)"
  shows "produces n ks tw (C \<phi> \<psi> buf)"
proof (rule producesI[where X = "\<lambda>n' ks' u \<Phi>. n' = n \<and> ks' = ks \<and>
    (\<exists>\<chi> \<eta> bf. \<Phi> = C \<chi> \<eta> bf \<and> produces n B1 u \<chi> \<and> produces n B2 u \<eta> \<and>
       list_all (ftable B1) (fst bf) \<and> list_all (ftable B2) (snd bf))"])
  show "n = n \<and> ks = ks \<and> (\<exists>\<chi> \<eta> bf. C \<phi> \<psi> buf = C \<chi> \<eta> bf \<and>
      produces n B1 tw \<chi> \<and> produces n B2 tw \<eta> \<and>
      list_all (ftable B1) (fst bf) \<and> list_all (ftable B2) (snd bf))"
    using p1 p2 bf1 bf2 by blast
next
  fix n' ks' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> ks' = ks \<and> (\<exists>\<chi> \<eta> bf. \<Phi> = C \<chi> \<eta> bf \<and> produces n B1 u \<chi> \<and>
      produces n B2 u \<eta> \<and> list_all (ftable B1) (fst bf) \<and> list_all (ftable B2) (snd bf))"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> \<eta> bf where Phi: "\<Phi> = C \<chi> \<eta> bf" and pc: "produces n B1 u \<chi>"
    and pe: "produces n B2 u \<eta>" and b1: "list_all (ftable B1) (fst bf)"
    and b2: "list_all (ftable B2) (snd bf)" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  obtain bs \<eta>' where e2: "meval j n ts db \<eta> = (bs, \<eta>')" by (cases "meval j n ts db \<eta>")
  obtain zs c1 c2 where e3: "mbuf2_take f (mbuf2_add as bs bf) = (zs, (c1, c2))"
    by (cases "mbuf2_take f (mbuf2_add as bs bf)") auto
  have "meval j n ts db (C \<chi> \<eta> bf) = (zs, C \<chi>' \<eta>' (c1, c2))" by (rule step[OF e1 e2 e3])
  then have x: "xs = zs" and f': "\<Phi>' = C \<chi>' \<eta>' (c1, c2)" using e X Phi by simp_all
  have ta: "list_all (ftable B1) as" by (rule produces_tables[OF pc w sts mts e1])
  have tb: "list_all (ftable B2) bs" by (rule produces_tables[OF pe w sts mts e2])
  have add: "mbuf2_add as bs bf = (fst bf @ as, snd bf @ bs)" by (cases bf) simp
  have la: "list_all (ftable B1) (fst bf @ as)" using b1 ta by simp
  have lb: "list_all (ftable B2) (snd bf @ bs)" using b2 tb by simp
  have e3': "mbuf2_take f (fst bf @ as, snd bf @ bs) = (zs, (c1, c2))"
    using e3 unfolding add by simp
  have tz: "list_all (ftable ks) zs"
    by (rule mbuf2_take_out[OF e3']) (use la lb tab in \<open>auto simp: list_all_iff\<close>)
  have sb: "set c1 \<subseteq> set (fst bf @ as) \<and> set c2 \<subseteq> set (snd bf @ bs)"
    by (rule mbuf2_take_sub[OF e3'])
  have lc1: "list_all (ftable B1) c1" using sb la by (auto simp: list_all_iff)
  have lc2: "list_all (ftable B2) c2" using sb lb by (auto simp: list_all_iff)
  show "list_all (ftable ks') xs \<and>
      ((n' = n \<and> ks' = ks \<and> (\<exists>\<chi> \<eta> bf. \<Phi>' = C \<chi> \<eta> bf \<and>
         produces n B1 (dnext u ts) \<chi> \<and> produces n B2 (dnext u ts) \<eta> \<and>
         list_all (ftable B1) (fst bf) \<and> list_all (ftable B2) (snd bf))) \<or>
       produces n' ks' (dnext u ts) \<Phi>')"
    using X tz lc1 lc2 produces_next[OF pc w sts mts e1] produces_next[OF pe w sts mts e2]
    by (auto simp: x f')
qed

lemma ftable_reorder: "ftable k2 Y \<Longrightarrow> ftable ks (reorder ks k2 Y)"
  by (auto simp: reorder_def table_def wf_tuple_def)

lemma produces_MOr:
  assumes p1: "produces n ks tw \<phi>" and p2: "produces n k2 tw \<psi>"
    and bf1: "list_all (ftable ks) (fst buf)" and bf2: "list_all (ftable k2) (snd buf)"
  shows "produces n ks tw (MOr ks \<phi> k2 \<psi> buf)"
proof -
  have step: "\<And>j ts db \<chi> \<eta> bf as \<chi>' bs \<eta>' zs bf'.
      meval j n ts db \<chi> = (as, \<chi>') \<Longrightarrow> meval j n ts db \<eta> = (bs, \<eta>') \<Longrightarrow>
      mbuf2_take (\<lambda>X Y. X \<union> reorder ks k2 Y) (mbuf2_add as bs bf) = (zs, bf') \<Longrightarrow>
      meval j n ts db (MOr ks \<chi> k2 \<eta> bf) = (zs, MOr ks \<chi>' k2 \<eta>' bf')"
    by simp
  have tab: "\<And>X Y :: event_data table. ftable ks X \<Longrightarrow> ftable k2 Y \<Longrightarrow>
      ftable ks (X \<union> reorder ks k2 Y)"
    using ftable_reorder by (metis table_Un finite_UnI)
  show ?thesis by (rule produces_binop[OF step tab p1 p2 bf1 bf2])
qed

lemma ftable_bin_join:
  fixes X Y :: "event_data table"
  assumes tX: "ftable k1 X" and tY: "ftable k2 Y"
    and d1: "distinct k1" and d2: "distinct k2"
    and sub: "\<not> pos \<Longrightarrow> set k2 \<subseteq> set k1"
  shows "ftable (cols_union k1 k2) (bin_join k1 X pos k2 Y)"
proof -
  have tj: "table (cols_union k1 k2) (join k1 X pos k2 Y)"
    by (rule join_table) (use tX tY sub in auto)
  have fj: "finite (join k1 X pos k2 Y)" by (rule finite_join) (use tX tY in auto)
  have bj: "bin_join k1 X pos k2 Y = join k1 X pos k2 Y"
    by (rule bin_join_table) (use tX tY d1 d2 in auto)
  show ?thesis unfolding bj using tj fj by simp
qed

lemma produces_MAnd:
  assumes p1: "produces n k1 tw \<phi>" and p2: "produces n k2 tw \<psi>"
    and bf1: "list_all (ftable k1) (fst buf)" and bf2: "list_all (ftable k2) (snd buf)"
    and d1: "distinct k1" and d2: "distinct k2"
    and sub: "\<not> pos \<Longrightarrow> set k2 \<subseteq> set k1"
  shows "produces n (cols_union k1 k2) tw (MAnd k1 \<phi> pos k2 \<psi> buf)"
proof -
  have step: "\<And>j ts db \<chi> \<eta> bf as \<chi>' bs \<eta>' zs bf'.
      meval j n ts db \<chi> = (as, \<chi>') \<Longrightarrow> meval j n ts db \<eta> = (bs, \<eta>') \<Longrightarrow>
      mbuf2_take (\<lambda>X Y. bin_join k1 X pos k2 Y) (mbuf2_add as bs bf) = (zs, bf') \<Longrightarrow>
      meval j n ts db (MAnd k1 \<chi> pos k2 \<eta> bf) = (zs, MAnd k1 \<chi>' pos k2 \<eta>' bf')"
    by (simp del: bin_join.simps)
  show ?thesis
    by (rule produces_binop[OF step ftable_bin_join[OF _ _ d1 d2 sub] p1 p2 bf1 bf2])
qed

subsection \<open>The temporal shift nodes\<close>

lemma mprev_next_out:
  "mprev_next I xs ts = (zs, xs', ts') \<Longrightarrow> list_all P xs \<Longrightarrow> P empty_table \<Longrightarrow>
     list_all P zs \<and> list_all P xs'"
  by (induct I xs ts arbitrary: zs xs' ts' rule: mprev_next.induct)
    (auto split: prod.splits)

lemma produces_MPrev:
  assumes p: "produces n ks tw \<phi>" and bf: "list_all (ftable ks) buf"
  shows "produces n ks tw (MPrev I \<phi> first buf nts)"
proof (rule producesI[where X = "\<lambda>n' ks' u \<Phi>. n' = n \<and> ks' = ks \<and>
    (\<exists>\<chi> b bs nt. \<Phi> = MPrev I \<chi> b bs nt \<and> produces n ks u \<chi> \<and> list_all (ftable ks) bs)"])
  show "n = n \<and> ks = ks \<and> (\<exists>\<chi> b bs nt. MPrev I \<phi> first buf nts = MPrev I \<chi> b bs nt \<and>
      produces n ks tw \<chi> \<and> list_all (ftable ks) bs)"
    using p bf by blast
next
  fix n' ks' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> ks' = ks \<and> (\<exists>\<chi> b bs nt. \<Phi> = MPrev I \<chi> b bs nt \<and>
      produces n ks u \<chi> \<and> list_all (ftable ks) bs)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> b bs nt where Phi: "\<Phi> = MPrev I \<chi> b bs nt"
    and pc: "produces n ks u \<chi>" and lb: "list_all (ftable ks) bs" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  have ta: "list_all (ftable ks) as" by (rule produces_tables[OF pc w sts mts e1])
  obtain ws bs' nt' where e2: "mprev_next I (bs @ as) (nt @ ts) = (ws, bs', nt')"
    by (cases "mprev_next I (bs @ as) (nt @ ts)") auto
  have out: "list_all (ftable ks) ws \<and> list_all (ftable ks) bs'"
    by (rule mprev_next_out[OF e2]) (use lb ta in auto)
  show "list_all (ftable ks') xs \<and>
      ((n' = n \<and> ks' = ks \<and> (\<exists>\<chi> b bs nt. \<Phi>' = MPrev I \<chi> b bs nt \<and>
         produces n ks (dnext u ts) \<chi> \<and> list_all (ftable ks) bs)) \<or>
       produces n' ks' (dnext u ts) \<Phi>')"
    using X e Phi e1 e2 out lb ta produces_next[OF pc w sts mts e1]
    by (auto split: if_splits)
qed

lemma produces_MNext:
  assumes p: "produces n ks tw \<phi>"
  shows "produces n ks tw (MNext I \<phi> first nts)"
proof (rule producesI[where X = "\<lambda>n' ks' u \<Phi>. n' = n \<and> ks' = ks \<and>
    (\<exists>\<chi> b nt. \<Phi> = MNext I \<chi> b nt \<and> produces n ks u \<chi>)"])
  show "n = n \<and> ks = ks \<and> (\<exists>\<chi> b nt. MNext I \<phi> first nts = MNext I \<chi> b nt \<and>
      produces n ks tw \<chi>)" using p by blast
next
  fix n' ks' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> ks' = ks \<and> (\<exists>\<chi> b nt. \<Phi> = MNext I \<chi> b nt \<and> produces n ks u \<chi>)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> b nt where Phi: "\<Phi> = MNext I \<chi> b nt"
    and pc: "produces n ks u \<chi>" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  have ta: "list_all (ftable ks) as" by (rule produces_tables[OF pc w sts mts e1])
  obtain cs b' where c: "(case (as, b) of (_ # as', True) \<Rightarrow> (as', False) | a \<Rightarrow> a) = (cs, b')"
    by (cases "(case (as, b) of (_ # as', True) \<Rightarrow> (as', False) | a \<Rightarrow> a)") auto
  have tc: "list_all (ftable ks) cs"
    using ta c by (cases as; cases b) auto
  obtain ws cs' nt' where e2: "mprev_next I cs (nt @ ts) = (ws, cs', nt')"
    by (cases "mprev_next I cs (nt @ ts)") auto
  have out: "list_all (ftable ks) ws \<and> list_all (ftable ks) cs'"
    by (rule mprev_next_out[OF e2]) (use tc in auto)
  show "list_all (ftable ks') xs \<and>
      ((n' = n \<and> ks' = ks \<and> (\<exists>\<chi> b nt. \<Phi>' = MNext I \<chi> b nt \<and>
          produces n ks (dnext u ts) \<chi>)) \<or>
       produces n' ks' (dnext u ts) \<Phi>')"
    using X e Phi e1 c e2 out produces_next[OF pc w sts mts e1] by auto
qed

subsection \<open>The aggregation node\<close>

text \<open>
  The node groups by the operand's columns above the aggregation's own @{term "length tys"}
  bound columns, shifted down, and puts the result column in front.  Without group columns
  (@{term g0}) an empty operand yields the aggregate of the empty multiset, a single one-column
  tuple, so the group columns must then be empty indeed.
\<close>

lemma ftable_eval_agg:
  assumes fin: "finite rel" and g0: "g0 \<Longrightarrow> shift_cols (length tys) cs = []"
  shows "ftable (y # shift_cols (length tys) cs) (eval_agg cs g0 \<omega> tys f rel)"
proof (cases "g0 \<and> rel = empty_table")
  case True
  then show ?thesis using g0
    by (simp add: eval_agg_def singleton_table_def table_def wf_tuple_def)
next
  case False
  then show ?thesis using fin
    unfolding eval_agg_def if_not_P[OF False]
    by (auto simp: table_def wf_tuple_def Let_def agg_key_def shift_cols_def)
qed

lemma produces_MAgg:
  assumes p: "produces (length (aggargs_tys args) + n) k0 tw \<phi>"
    and g0: "aggargs_g0 args \<Longrightarrow> shift_cols (length (aggargs_tys args)) (aggargs_cols args) = []"
  shows "produces n (y # shift_cols (length (aggargs_tys args)) (aggargs_cols args))
      tw (MAgg args \<phi>)"
  by (rule produces_unop[where m = "length (aggargs_tys args) + n" and B = k0
      and C = "MAgg args" and g = "eval_aggargs args", OF _ _ p])
    (use g0 in \<open>auto simp: eval_aggargs_def intro!: ftable_eval_agg split: prod.splits\<close>)

subsection \<open>The multi-way conjunction\<close>

text \<open>
  The multi-way join's shape follows from @{thm [source] mmulti_join_kands}: at well-formed
  operands it is the left-to-right fold of the positive tables followed by the anti-joins against
  the negative ones, brought into the node's column order.  The anti-joins only remove tuples.
\<close>

lemma kands_neg_subset: "kands_neg acc t us \<subseteq> t"
  by (induct us arbitrary: t) (fastforce simp: join_False_code)+

lemma ftable_mmulti_join:
  fixes T :: "event_data table"
  assumes acc: "distinct k0" "ftable k0 T"
    and pos: "\<forall>(k, u) \<in> set (zip kss Us). distinct k \<and> ftable k u" "length kss = length Us"
    and neg: "\<forall>(k, u) \<in> set (zip nkss Vs). distinct k \<and> ftable k u \<and> set k \<subseteq> set (kands_cols k0 kss)"
      "length nkss = length Vs"
    and cs: "distinct ks" "set ks = set (kands_cols k0 kss)"
  shows "ftable ks (mmulti_join ks (k0 # kss) nkss ((T # Us) @ Vs))"
proof -
  have eq: "mmulti_join ks (k0 # kss) nkss ((T # Us) @ Vs)
      = restrict ks (kands_cols k0 kss) `
          kands_neg (kands_cols k0 kss) (kands_pos k0 T (zip kss Us)) (zip nkss Vs)"
    by (rule mmulti_join_kands) (use acc pos neg cs in auto)
  have "finite (kands_pos k0 T (zip kss Us))"
    by (rule finite_kands_pos) (use acc pos in auto)
  then have "finite (kands_neg (kands_cols k0 kss) (kands_pos k0 T (zip kss Us)) (zip nkss Vs))"
    by (rule finite_subset[OF kands_neg_subset])
  then show ?thesis unfolding eq by (auto simp: table_def wf_tuple_def)
qed

lemma ftable_mmulti_join_nth:
  fixes as :: "event_data table list" and k0 :: cols and kss nkss :: "cols list"
  defines "Ks \<equiv> (k0 # kss) @ nkss"
  assumes la: "length as = length Ks"
    and ha: "\<forall>i < length as. distinct (Ks ! i) \<and> ftable (Ks ! i) (as ! i)"
    and sub: "\<forall>k \<in> set nkss. set k \<subseteq> set (kands_cols k0 kss)"
    and cs: "distinct ks" "set ks = set (kands_cols k0 kss)"
  shows "ftable ks (mmulti_join ks (k0 # kss) nkss as)"
proof -
  obtain T R where as: "as = T # R" using la by (cases as) (auto simp: Ks_def)
  define Us where "Us = take (length kss) R"
  define Vs where "Vs = drop (length kss) R"
  have lR: "length R = length kss + length nkss" using la as by (simp add: Ks_def)
  have R: "as = (T # Us) @ Vs" by (simp add: as Us_def Vs_def)
  have lU: "length kss = length Us" and lV: "length nkss = length Vs"
    using lR by (simp_all add: Us_def Vs_def)
  have h0: "distinct k0 \<and> ftable k0 T" using ha[rule_format, of 0] by (simp add: as Ks_def)
  have hU: "\<And>i. i < length kss \<Longrightarrow> distinct (kss ! i) \<and> ftable (kss ! i) (Us ! i)"
  proof -
    fix i assume i: "i < length kss"
    have "distinct (Ks ! Suc i) \<and> ftable (Ks ! Suc i) (as ! Suc i)"
      using ha[rule_format, of "Suc i"] i lR as by simp
    then show "distinct (kss ! i) \<and> ftable (kss ! i) (Us ! i)"
      using i by (simp add: Ks_def as Us_def nth_append)
  qed
  have hV: "\<And>i. i < length nkss \<Longrightarrow> distinct (nkss ! i) \<and> ftable (nkss ! i) (Vs ! i)"
  proof -
    fix i assume i: "i < length nkss"
    have "distinct (Ks ! Suc (length kss + i)) \<and>
        ftable (Ks ! Suc (length kss + i)) (as ! Suc (length kss + i))"
      using ha[rule_format, of "Suc (length kss + i)"] i lR as by simp
    then show "distinct (nkss ! i) \<and> ftable (nkss ! i) (Vs ! i)"
      using i lR by (simp add: Ks_def as Vs_def nth_append)
  qed
  show ?thesis unfolding R
  proof (rule ftable_mmulti_join[OF _ _ _ lU _ lV cs])
    show "\<forall>(k, u) \<in> set (zip kss Us). distinct k \<and> ftable k u"
      using hU lU by (auto simp: set_zip)
    show "\<forall>(k, u) \<in> set (zip nkss Vs). distinct k \<and> ftable k u \<and> set k \<subseteq> set (kands_cols k0 kss)"
      using hV lV sub by (auto simp: set_zip)
  qed (use h0 in auto)
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
    proof (intro allI impI)
      fix i assume "i < length (map tl buf)"
      then have i: "i < length buf" by simp
      show "set (map tl buf ! i) \<subseteq> Ss ! i"
        using SUB[rule_format, OF i] i by (cases "buf ! i") auto
    qed
    have e: "mbufn_take f (f (map hd buf) z) (map tl buf) = (w, buf')"
      using E False by simp
    show ?thesis using IH[OF False e lt st ST q] L by simp
  qed
qed

lemma produces_MAnds:
  fixes k0 :: cols and kss nkss :: "cols list"
  defines "Ks \<equiv> (k0 # kss) @ nkss"
  assumes lL: "length L = length Ks" and lb: "length buf = length Ks"
    and pL: "\<forall>i < length Ks. produces n (Ks ! i) tw (L ! i)"
    and pb: "\<forall>i < length Ks. list_all (ftable (Ks ! i)) (buf ! i)"
    and dK: "\<forall>k \<in> set Ks. distinct k"
    and sub: "\<forall>k \<in> set nkss. set k \<subseteq> set (kands_cols k0 kss)"
    and cs: "distinct ks" "set ks = set (kands_cols k0 kss)"
  shows "produces n ks tw (MAnds ks (k0 # kss) nkss L buf)"
proof (rule producesI[where X = "\<lambda>n' ks' u \<Phi>. n' = n \<and> ks' = ks \<and>
    (\<exists>M bf. \<Phi> = MAnds ks (k0 # kss) nkss M bf \<and> length M = length Ks \<and> length bf = length Ks \<and>
       (\<forall>i < length Ks. produces n (Ks ! i) u (M ! i)) \<and>
       (\<forall>i < length Ks. list_all (ftable (Ks ! i)) (bf ! i)))"])
  show "n = n \<and> ks = ks \<and> (\<exists>M bf. MAnds ks (k0 # kss) nkss L buf = MAnds ks (k0 # kss) nkss M bf \<and>
      length M = length Ks \<and> length bf = length Ks \<and>
      (\<forall>i < length Ks. produces n (Ks ! i) tw (M ! i)) \<and>
      (\<forall>i < length Ks. list_all (ftable (Ks ! i)) (bf ! i)))"
    using lL lb pL pb by blast
next
  fix n' ks' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> ks' = ks \<and> (\<exists>M bf. \<Phi> = MAnds ks (k0 # kss) nkss M bf \<and>
      length M = length Ks \<and> length bf = length Ks \<and>
      (\<forall>i < length Ks. produces n (Ks ! i) u (M ! i)) \<and>
      (\<forall>i < length Ks. list_all (ftable (Ks ! i)) (bf ! i)))"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain M0 bf0 where Phi: "\<Phi> = MAnds ks (k0 # kss) nkss M0 bf0"
    and lM: "length M0 = length Ks" and lbf: "length bf0 = length Ks"
    and pM: "\<forall>i < length Ks. produces n (Ks ! i) u (M0 ! i)"
    and pbf: "\<forall>i < length Ks. list_all (ftable (Ks ! i)) (bf0 ! i)"
    by blast
  define R where "R = map (meval j n ts db) M0"
  define bf1 where "bf1 = mbufn_add (map fst R) bf0"
  define Ss :: "event_data table set list" where "Ss = map (\<lambda>k. {X. ftable k X}) Ks"
  define f :: "event_data table list \<Rightarrow> event_data table list \<Rightarrow> event_data table list"
    where "f = (\<lambda>as zs. zs @ [mmulti_join ks (k0 # kss) nkss as])"
  have lR: "length R = length Ks" using lM by (simp add: R_def)
  have lb1: "length bf1 = length Ks" using lbf lR by (simp add: bf1_def)
  have lSs: "length Ss = length Ks" by (simp add: Ss_def)
  have tR: "\<And>i. i < length Ks \<Longrightarrow> list_all (ftable (Ks ! i)) (fst (R ! i))"
  proof -
    fix i assume i: "i < length Ks"
    obtain as \<chi>' where ei: "meval j n ts db (M0 ! i) = (as, \<chi>')"
      by (cases "meval j n ts db (M0 ! i)")
    have "list_all (ftable (Ks ! i)) as"
      by (rule produces_tables[OF _ w sts mts ei]) (use pM i in blast)
    then show "list_all (ftable (Ks ! i)) (fst (R ! i))"
      using ei i lM by (simp add: R_def)
  qed
  have nR: "\<And>i. i < length Ks \<Longrightarrow> produces n (Ks ! i) (dnext u ts) (snd (R ! i))"
  proof -
    fix i assume i: "i < length Ks"
    obtain as \<chi>' where ei: "meval j n ts db (M0 ! i) = (as, \<chi>')"
      by (cases "meval j n ts db (M0 ! i)")
    have "produces n (Ks ! i) (dnext u ts) \<chi>'"
      by (rule produces_next[OF _ w sts mts ei]) (use pM i in blast)
    then show "produces n (Ks ! i) (dnext u ts) (snd (R ! i))"
      using ei i lM by (simp add: R_def)
  qed
  have sub1: "\<forall>i < length bf1. set (bf1 ! i) \<subseteq> Ss ! i"
  proof (intro allI impI)
    fix i assume i: "i < length bf1"
    then have ic: "i < length Ks" using lb1 by simp
    have "bf1 ! i = bf0 ! i @ fst (R ! i)" using ic lbf lR by (simp add: bf1_def)
    then show "set (bf1 ! i) \<subseteq> Ss ! i"
      using pbf tR[OF ic] ic by (auto simp: Ss_def list_all_iff)
  qed
  have st: "\<And>as u. length as = length Ss \<Longrightarrow> (\<forall>i < length Ss. as ! i \<in> Ss ! i) \<Longrightarrow>
      list_all (ftable ks) u \<Longrightarrow> list_all (ftable ks) (f as u)"
  proof -
    fix as :: "event_data table list" and u :: "event_data table list"
    assume la: "length as = length Ss" and ha: "\<forall>i < length Ss. as ! i \<in> Ss ! i"
      and qu: "list_all (ftable ks) u"
    have lac: "length as = length Ks" using la lSs by simp
    have hac: "\<forall>i < length as. distinct (Ks ! i) \<and> ftable (Ks ! i) (as ! i)"
      using ha la lSs dK by (auto simp: Ss_def)
    have "ftable ks (mmulti_join ks (k0 # kss) nkss as)"
      by (rule ftable_mmulti_join_nth[OF lac[unfolded Ks_def] hac[unfolded Ks_def] sub cs])
    then show "list_all (ftable ks) (f as u)" using qu by (simp add: f_def)
  qed
  obtain zs bf2 where e2: "mbufn_take f [] bf1 = (zs, bf2)"
    by (cases "mbufn_take f [] bf1")
  have lSb: "length Ss = length bf1" using lSs lb1 by simp
  have qz: "list_all (ftable ks) []" by simp
  have out: "list_all (ftable ks) zs \<and> length bf2 = length bf1 \<and>
      (\<forall>i < length bf2. set (bf2 ! i) \<subseteq> Ss ! i)"
    by (rule mbufn_take_out[where Q = "list_all (ftable ks)" and f = f and Ss = Ss,
        OF e2 lSb sub1 st qz])
  have m: "meval j n ts db (MAnds ks (k0 # kss) nkss M0 bf0)
      = (zs, MAnds ks (k0 # kss) nkss (map snd R) bf2)"
    using e2 unfolding R_def bf1_def f_def
    by (simp add: Let_def del: mbufn_take.simps mmulti_join.simps)
  have x: "xs = zs" and f': "\<Phi>' = MAnds ks (k0 # kss) nkss (map snd R) bf2"
    using e X Phi m by simp_all
  have pM': "\<forall>i < length Ks. produces n (Ks ! i) (dnext u ts) (map snd R ! i)"
    using nR lR by simp
  have pbf': "\<forall>i < length Ks. list_all (ftable (Ks ! i)) (bf2 ! i)"
    using out lb1 by (auto simp: Ss_def list_all_iff subset_eq)
  show "list_all (ftable ks') xs \<and>
      ((n' = n \<and> ks' = ks \<and> (\<exists>M bf. \<Phi>' = MAnds ks (k0 # kss) nkss M bf \<and>
         length M = length Ks \<and> length bf = length Ks \<and>
         (\<forall>i < length Ks. produces n (Ks ! i) (dnext u ts) (M ! i)) \<and>
         (\<forall>i < length Ks. list_all (ftable (Ks ! i)) (bf ! i)))) \<or>
       produces n' ks' (dnext u ts) \<Phi>')"
    using X out pM' pbf' lM lb1 lR by (auto simp: x f')
qed

subsection \<open>The Since node\<close>

text \<open>
  The Since node's invariant is the verified structure's own: it is valid for an abstract
  auxiliary list whose tables are finite tables over the right operand's columns, at a current
  timestamp that the buffer's timestamps -- and every timestamp still to come -- are at or after.
  This is the wide half of @{const dsince_rel}; the node needs nothing of the dense half in order
  to produce well-formed tables.  The node's output is the structure's result passed through the
  optional aggregation, whose columns @{term ko} are a parameter here.
\<close>

lemma ftable_foldr_Un:
  "\<forall>(t, rel) \<in> set aux. ftable R rel \<Longrightarrow> ftable R (foldr (\<union>) [rel. (t, rel) \<leftarrow> aux, P t] {})"
  by (induct aux) (auto simp: table_def split: if_splits)

lemma fauxlist_join:
  assumes sub: "set kL \<subseteq> set kR" and r1: "ftable kL rel1"
  shows "\<forall>(t, rel) \<in> set aux. ftable kR rel \<Longrightarrow>
    \<forall>(t, rel) \<in> set (map (\<lambda>(t, rel). (t, join kR rel pos kL rel1)) aux). ftable kR rel"
proof (induct aux)
  case (Cons p aux)
  obtain v rel where p: "p = (v, rel)" by (cases p)
  have t: "ftable kR rel" using Cons.prems p by simp
  have tj: "table kR (join kR rel pos kL rel1)"
    by (rule join_table) (use t r1 sub in \<open>auto simp: cols_union_subset\<close>)
  have fj: "finite (join kR rel pos kL rel1)" using t r1 by (simp add: finite_join)
  show ?case using Cons.hyps Cons.prems tj fj p by simp
qed simp

lemma fauxlist_add_new_table:
  assumes a: "\<forall>(t, rel) \<in> set aux. ftable R rel" and r2: "ftable R rel2"
  shows "\<forall>(t, rel) \<in> set (case aux of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # aux).
         ftable R rel"
  using assms by (cases aux) (auto simp: table_def)

definition saux_inv :: "args \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> ts \<Rightarrow> event_data mbuf2S \<Rightarrow> mmasaux \<Rightarrow> bool" where
  "saux_inv args kL kR u buf aux \<longleftrightarrow>
     (\<exists>cur auxlist. valid_mmasaux args cur aux auxlist \<and> cur \<le> u \<and>
        (\<forall>(t, rel) \<in> set auxlist. ftable kR rel) \<and>
        (case buf of (xs, ys, tss, sk) \<Rightarrow>
           list_all (ftable kL) xs \<and> list_all (ftable kR) ys \<and>
           sorted tss \<and> (\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> u)))"

lemma saux_invI:
  "valid_mmasaux args cur aux auxlist \<Longrightarrow> cur \<le> u \<Longrightarrow>
   (\<forall>(t, rel) \<in> set auxlist. ftable kR rel) \<Longrightarrow>
   list_all (ftable kL) xs \<Longrightarrow> list_all (ftable kR) ys \<Longrightarrow>
   sorted tss \<Longrightarrow> \<forall>t \<in> set tss. cur \<le> t \<and> t \<le> u \<Longrightarrow>
   saux_inv args kL kR u (xs, ys, tss, sk) aux"
  unfolding saux_inv_def by (auto simp del: valid_mmasaux.simps)

lemma saux_invE:
  assumes "saux_inv args kL kR u (xs, ys, tss, sk) aux"
  obtains cur auxlist where "valid_mmasaux args cur aux auxlist" and "cur \<le> u"
    and "\<forall>(t, rel) \<in> set auxlist. ftable kR rel"
    and "list_all (ftable kL) xs" and "list_all (ftable kR) ys"
    and "sorted tss" and "\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> u"
  using assms unfolding saux_inv_def by (auto simp del: valid_mmasaux.simps)

lemma ftable_result_mmasaux:
  assumes v: "valid_mmasaux args cur aux auxlist"
    and w: "\<forall>(t, rel) \<in> set auxlist. ftable kR rel"
    and agg: "\<And>X. ftable kR X \<Longrightarrow> ftable ko (eval_args_agg args X)"
  shows "ftable ko (result_mmasaux args aux)"
  using default_mmasaux.valid_result_msaux[OF v] agg[OF ftable_foldr_Un[OF w]] by simp

text \<open>A fresh batch enters the buffer at or after the bound, which becomes the batch's last
  timestamp.\<close>

lemma saux_inv_add:
  assumes r: "saux_inv args kL kR u buf aux"
    and lx: "list_all (ftable kL) xs" and ly: "list_all (ftable kR) ys"
    and s: "sorted ts" and b: "\<forall>t \<in> set ts. u \<le> t"
  shows "saux_inv args kL kR (dnext u ts) (mbuf2S_add xs ys ts buf) aux"
proof (cases buf)
  case (fields us vs tss sk)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist" and cu: "cur \<le> u"
    and wa: "\<forall>(t, rel) \<in> set auxlist. ftable kR rel"
    and lu: "list_all (ftable kL) us" and lv: "list_all (ftable kR) vs"
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
  structure, which by @{thm [source] ftable_result_mmasaux} are tables over the output columns.
  The induction is the kernel's own recursion, the same one @{thm [source] eval_since_rel}
  follows.
\<close>

lemma eval_since_ftable:
  fixes args :: args
  assumes agg: "\<And>X. ftable kR X \<Longrightarrow> ftable ko (eval_args_agg args X)"
    and aL: "args_L args = kL" and aR: "args_R args = kR" and sub: "set kL \<subseteq> set kR"
  shows "meval_since args rs buf aux = (zs, buf', aux') \<Longrightarrow>
    saux_inv args kL kR u buf aux \<Longrightarrow> list_all (ftable ko) rs \<Longrightarrow>
    list_all (ftable ko) zs \<and> saux_inv args kL kR u buf' aux'"
proof (induction rs buf aux arbitrary: zs buf' aux'
    taking: args rule: default_maux.eval_since.induct)
  case (1 rs x xs t tss skew aux)
  note E = 1(1) and R = 1(2) and Q = 1(3)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist" and cu: "cur \<le> u"
    and wa: "\<forall>(t, rel) \<in> set auxlist. ftable kR rel"
    and lx: "list_all (ftable kL) (x # xs)"
    and st: "sorted (t # tss)" and ct: "\<forall>v \<in> set (t # tss). cur \<le> v \<and> v \<le> u"
    using R by (rule saux_invE)
  have tx: "ftable kL x" using lx by simp
  have ctu: "cur \<le> t" using ct by simp
  show ?case
  proof (cases "skew \<or> memL (args_ivl args) 0")
    case True
    show ?thesis using E R Q True by (auto simp: list_all_iff)
  next
    case False
    let ?wa = "gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)"
    let ?al = "map (\<lambda>(v, rel). (v, join kR rel (args_pos args) kL x))
        (filter (\<lambda>(v, rel). memR (args_ivl args) (t - v)) auxlist)"
    have vw': "valid_mmasaux args t ?wa ?al"
      using default_mmasaux.valid_join_msaux
          [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu], of x] tx aL aR by simp
    have wa': "\<forall>(v, rel) \<in> set ?al. ftable kR rel"
      by (rule fauxlist_join[OF sub tx]) (use wa in auto)
    have EW: "meval_since args rs (x # xs, [], t # tss, skew) aux
        = (rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa)"
      using False by (simp add: Let_def)
    have EE: "(rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa) = (zs, buf', aux')"
      by (rule trans[OF EW[symmetric] E])
    have tr: "ftable ko (result_mmasaux args ?wa)"
      by (rule ftable_result_mmasaux[OF vw' wa' agg])
    have R': "saux_inv args kL kR u (xs, [], tss, True) ?wa"
      by (rule saux_invI[OF vw' _ wa']) (use lx st ct in auto)
    show ?thesis using EE Q tr R' by auto
  qed
next
  case (2 rs xs y ys tss aux)
  note IH = 2(1) and E = 2(2) and R = 2(3) and Q = 2(4)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist" and cu: "cur \<le> u"
    and wa: "\<forall>(t, rel) \<in> set auxlist. ftable kR rel"
    and lx: "list_all (ftable kL) xs" and ly: "list_all (ftable kR) (y # ys)"
    and st: "sorted tss" and ct: "\<forall>v \<in> set tss. cur \<le> v \<and> v \<le> u"
    using R by (rule saux_invE)
  have ty: "ftable kR y" using ly by simp
  let ?al = "case auxlist of [] \<Rightarrow> [(cur, y)]
      | ((v, w) # r) \<Rightarrow> if v = cur then (v, w \<union> y) # r else (cur, y) # auxlist"
  have vw': "valid_mmasaux args cur (add_new_table_mmasaux args y aux) ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vw]) (use ty aR in simp)
  have wa': "\<forall>(v, rel) \<in> set ?al. ftable kR rel"
    by (rule fauxlist_add_new_table[OF wa ty])
  have E': "meval_since args rs (xs, ys, tss, False) (add_new_table_mmasaux args y aux)
      = (zs, buf', aux')" using E by simp
  have R': "saux_inv args kL kR u (xs, ys, tss, False) (add_new_table_mmasaux args y aux)"
    by (rule saux_invI[OF vw' cu wa']) (use lx ly st ct in auto)
  show ?case by (rule IH[OF E' R' Q])
next
  case (3 rs x xs y ys t tss aux)
  note IH = 3(1) and E = 3(2) and R = 3(3) and Q = 3(4)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist" and cu: "cur \<le> u"
    and wa: "\<forall>(v, rel) \<in> set auxlist. ftable kR rel"
    and lx: "list_all (ftable kL) (x # xs)" and ly: "list_all (ftable kR) (y # ys)"
    and st: "sorted (t # tss)" and ct: "\<forall>v \<in> set (t # tss). cur \<le> v \<and> v \<le> u"
    using R by (rule saux_invE)
  have tx: "ftable kL x" using lx by simp
  have ty: "ftable kR y" using ly by simp
  have ctu: "cur \<le> t" using ct by simp
  let ?jl = "map (\<lambda>(v, rel). (v, join kR rel (args_pos args) kL x))
      (filter (\<lambda>(v, rel). memR (args_ivl args) (t - v)) auxlist)"
  let ?al = "case ?jl of [] \<Rightarrow> [(t, y)]
      | ((v, w) # r) \<Rightarrow> if v = t then (v, w \<union> y) # r else (t, y) # ?jl"
  let ?wa = "add_new_table_mmasaux args y
      (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux))"
  have vwj: "valid_mmasaux args t (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)) ?jl"
    using default_mmasaux.valid_join_msaux
        [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu], of x] tx aL aR by simp
  have wj: "\<forall>(v, rel) \<in> set ?jl. ftable kR rel"
    by (rule fauxlist_join[OF sub tx]) (use wa in auto)
  have vw': "valid_mmasaux args t ?wa ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vwj]) (use ty aR in simp)
  have wa': "\<forall>(v, rel) \<in> set ?al. ftable kR rel"
    by (rule fauxlist_add_new_table[OF wj ty])
  have tr: "ftable ko (result_mmasaux args ?wa)"
    by (rule ftable_result_mmasaux[OF vw' wa' agg])
  have E': "meval_since args (result_mmasaux args ?wa # rs) (xs, ys, tss, False) ?wa
      = (zs, buf', aux')" using E by (simp add: Let_def)
  have R': "saux_inv args kL kR u (xs, ys, tss, False) ?wa"
    by (rule saux_invI[OF vw' _ wa']) (use lx ly st ct in auto)
  have Q': "list_all (ftable ko) (result_mmasaux args ?wa # rs)" using tr Q by simp
  show ?case by (rule IH[OF refl E' R' Q'])
qed auto

lemma produces_MSince:
  fixes args :: args
  assumes p1: "produces n kL tw \<phi>" and p2: "produces n kR tw \<psi>"
    and r: "saux_inv args kL kR tw buf aux"
    and agg: "\<And>X. ftable kR X \<Longrightarrow> ftable ko (eval_args_agg args X)"
    and an: "args_n args = n" and aL: "args_L args = kL" and aR: "args_R args = kR"
    and sub: "set kL \<subseteq> set kR"
  shows "produces m ko tw (MSince args \<phi> \<psi> buf aux)"
proof (rule producesI[where X = "\<lambda>m' ks' u \<Phi>. m' = m \<and> ks' = ko \<and>
    (\<exists>\<chi> \<eta> bf ax. \<Phi> = MSince args \<chi> \<eta> bf ax \<and>
       produces n kL u \<chi> \<and> produces n kR u \<eta> \<and> saux_inv args kL kR u bf ax)"])
  show "m = m \<and> ko = ko \<and> (\<exists>\<chi> \<eta> bf ax. MSince args \<phi> \<psi> buf aux = MSince args \<chi> \<eta> bf ax \<and>
      produces n kL tw \<chi> \<and> produces n kR tw \<eta> \<and> saux_inv args kL kR tw bf ax)"
    using p1 p2 r by blast
next
  fix m' ks' u \<Phi> j ts db xs \<Phi>'
  assume X: "m' = m \<and> ks' = ko \<and> (\<exists>\<chi> \<eta> bf ax. \<Phi> = MSince args \<chi> \<eta> bf ax \<and>
      produces n kL u \<chi> \<and> produces n kR u \<eta> \<and> saux_inv args kL kR u bf ax)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j m' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> \<eta> bf ax where Phi: "\<Phi> = MSince args \<chi> \<eta> bf ax"
    and pc: "produces n kL u \<chi>" and pe: "produces n kR u \<eta>"
    and inv: "saux_inv args kL kR u bf ax" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  obtain bs \<eta>' where e2: "meval j n ts db \<eta> = (bs, \<eta>')" by (cases "meval j n ts db \<eta>")
  obtain zs bf' ax' where e3: "meval_since args [] (mbuf2S_add as bs ts bf) ax = (zs, bf', ax')"
    by (cases "meval_since args [] (mbuf2S_add as bs ts bf) ax")
  have x: "xs = zs" and f: "\<Phi>' = MSince args \<chi>' \<eta>' bf' ax'"
    using e X Phi e1 e2 e3 an by simp_all
  have ta: "list_all (ftable kL) as" by (rule produces_tables[OF pc w sts mts e1])
  have tb: "list_all (ftable kR) bs" by (rule produces_tables[OF pe w sts mts e2])
  have add: "saux_inv args kL kR (dnext u ts) (mbuf2S_add as bs ts bf) ax"
    by (rule saux_inv_add[OF inv ta tb sts mts])
  have step: "list_all (ftable ko) zs \<and> saux_inv args kL kR (dnext u ts) bf' ax'"
    by (rule eval_since_ftable[OF _ aL aR sub e3 add]) (use agg in auto)
  show "list_all (ftable ks') xs \<and>
      ((m' = m \<and> ks' = ko \<and>
          (\<exists>\<chi> \<eta> bf ax. \<Phi>' = MSince args \<chi> \<eta> bf ax \<and>
             produces n kL (dnext u ts) \<chi> \<and> produces n kR (dnext u ts) \<eta> \<and>
             saux_inv args kL kR (dnext u ts) bf ax)) \<or>
       produces m' ks' (dnext u ts) \<Phi>')"
    using X step produces_next[OF pc w sts mts e1] produces_next[OF pe w sts mts e2]
    by (auto simp: x f)
qed

end

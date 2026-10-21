(*<*)
theory Correct_Un_Ops
  imports
    "MFODL_Monitor.Monitor" 
    Progress
begin
(*>*)


subsection \<open> Correctness of atoms and unary Operators \<close>


subsubsection \<open> Inequalities \<close>

fun formula_of_constraint :: "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow> ty Formula.formula" where
  "formula_of_constraint (t1, True, MEq, t2) = Formula.Eq t1 t2"
| "formula_of_constraint (t1, True, MLess, t2) = Formula.Less t1 t2"
| "formula_of_constraint (t1, True, MLessEq, t2) = Formula.LessEq t1 t2"
| "formula_of_constraint (t1, False, MEq, t2) = Formula.Neg (Formula.Eq t1 t2)"
| "formula_of_constraint (t1, False, MLess, t2) = Formula.Neg (Formula.Less t1 t2)"
| "formula_of_constraint (t1, False, MLessEq, t2) = Formula.Neg (Formula.LessEq t1 t2)"

lemma fv_formula_of_constraint: "fv (formula_of_constraint (t1, p, c, t2)) = fv_trm t1 \<union> fv_trm t2"
  by (induction "(t1, p, c, t2)" rule: formula_of_constraint.induct) simp_all

lemma progress_constraint: "progress \<sigma> P (formula_of_constraint c) j = j"
  by (induction rule: formula_of_constraint.induct) simp_all
lemma eval_constraint_sat_eq: "fv_trm t1 \<subseteq> set A \<Longrightarrow> fv_trm t2 \<subseteq> set A \<Longrightarrow>
  \<forall>i\<in>set A. i < n \<Longrightarrow> eval_constraint A (t1, p, c, t2) x =
    Formula.sat \<sigma> V (val n A x) i (formula_of_constraint (t1, p, c, t2))"
  by (induction "(t1, p, c, t2)" rule: formula_of_constraint.induct)
    (simp_all add: meval_trm_eval_trm)

lemma formula_of_constraint_neq_release_safe_bdd: 
  "formula_of_constraint (t1, b, op, t2) \<noteq> release_safe_bounded \<phi>' I \<psi>'"
  by (induction rule: formula_of_constraint.induct)
    (auto simp: release_safe_bounded_def)


subsubsection \<open> Predicates \<close>

lemma set_pred_cols[simp]: "set (pred_cols ts) = (\<Union>t\<in>set ts. Formula.fv_trm t)"
  by (simp add: pred_cols_def set_fold_cols_union)

lemma distinct_pred_cols[simp]: "distinct (pred_cols ts)"
  by (simp add: pred_cols_def distinct_fold_cols_union)

lemma pred_cols_Var: "distinct ys \<Longrightarrow> pred_cols (map Formula.Var ys) = ys"
proof -
  have "distinct (cs @ ys) \<Longrightarrow> fold (\<lambda>t cs. cols_union cs (Formula.fv_trm_list t)) (map Formula.Var ys) cs = cs @ ys"
    for cs
    by (induct ys arbitrary: cs) (simp_all add: cols_union_def)
  then show "distinct ys \<Longrightarrow> pred_cols (map Formula.Var ys) = ys"
    by (simp add: pred_cols_def)
qed

lemma is_simple_pattern_Var: "is_simple_pattern ts m \<Longrightarrow>
  \<exists>ys. ts = map Formula.Var ys \<and> sorted_wrt (<) ys \<and> (\<forall>y\<in>set ys. m \<le> y)"
proof (induction ts m rule: is_simple_pattern.induct)
  case (2 y ts x)
  then obtain ys where "ts = map Formula.Var ys" "sorted_wrt (<) ys" "\<forall>z\<in>set ys. Suc y \<le> z"
    by auto
  with 2(2) show ?case
    by (intro exI[of _ "y # ys"]) auto
qed auto

lemma is_copy_pattern_simple: "is_copy_pattern n ts \<Longrightarrow> is_simple_pattern ts 0"
proof -
  have "is_simple_pattern (map Formula.Var [m..<m + k]) m" for m k
    by (induct k arbitrary: m) (simp_all add: upt_conv_Cons del: upt_Suc, metis add_Suc)
  then show "is_copy_pattern n ts \<Longrightarrow> is_simple_pattern ts 0"
    unfolding is_copy_pattern_def using add_0 by metis
qed

text \<open>With a simple pattern, the arguments of a predicate are distinct variables in increasing
  order, which are its columns: its tuples are those of the event.\<close>

lemma qtable_simple_pattern_gen:
  assumes "is_simple_pattern ts 0" "\<forall>t\<in>set ts. \<forall>x\<in>Formula.fv_trm t. x < n"
    and sat: "\<And>v. Formula.sat \<sigma> V v i (Formula.Pred p ts) \<longleftrightarrow> map (Formula.eval_trm v) ts \<in> S"
    and len: "\<forall>x\<in>S. length x = length ts" and fin: "finite S"
  shows "qtable (pred_cols ts) (mem_restr UU (pred_cols ts))
    (\<lambda>v. Formula.sat \<sigma> V (val n (pred_cols ts) v) i (Formula.Pred p ts)) S"
proof -
  obtain ys where ts: "ts = map Formula.Var ys" "sorted_wrt (<) ys"
    using is_simple_pattern_Var[OF assms(1)] by blast
  then have ys: "distinct ys" "pred_cols ts = ys"
    by (simp_all add: strict_sorted_iff pred_cols_Var)
  have ys_n: "\<forall>y\<in>set ys. y < n"
    using assms(2) ts(1) by auto
  have eval: "map (Formula.eval_trm (val n ys v)) ts = v" if "wf_tuple ys v" for v
  proof -
    have "map (Formula.eval_trm (val n ys v)) ts = map (tup_get ys v) ys"
      using ys_n by (simp add: ts(1))
    also have "\<dots> = v"
      using restrict_idle[OF ys(1) that] by (simp add: restrict_def)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding ys(2) qtable_iff
  proof (intro conjI allI impI)
    show "table ys S"
      using len ts(1) by (auto simp: table_def wf_tuple_def)
    show "finite S"
      by (rule fin)
    fix v
    assume "mem_restr UU ys v"
    then have "wf_tuple ys v"
      by (rule mem_restr_wf_tuple)
    then show "v \<in> S \<longleftrightarrow> Formula.sat \<sigma> V (val n ys v) i (Formula.Pred p ts) \<and> wf_tuple ys v"
      using sat eval by simp
  qed
qed

lemma sat_Pred_iff:
  "V (p, length ts) = Some P \<Longrightarrow>
    Formula.sat \<sigma> V v i (Formula.Pred p ts) \<longleftrightarrow> map (Formula.eval_trm v) ts \<in> {v. length v = length ts \<and> P v i}"
  "V (p, length ts) = None \<Longrightarrow>
    Formula.sat \<sigma> V v i (Formula.Pred p ts) \<longleftrightarrow> map (Formula.eval_trm v) ts \<in> {v. (p, v) \<in> \<Gamma> \<sigma> i \<and> length v = length ts}"
  by simp_all

lemma qtable_simple_pattern:
  assumes "X = Formula.fv_list (Formula.Pred p ts)" and "\<forall>x\<in>fv (Formula.Pred p ts). x < n" 
    and "is_simple_pattern ts 0"
  shows "V (p, length ts) = Some P \<Longrightarrow> 
  R = {v. length v = length ts \<and> P v i} \<Longrightarrow> finite R \<Longrightarrow>
  qtable X (mem_restr UU X) (\<lambda>v. Formula.sat \<sigma> V (val n X v) i (Formula.Pred p ts)) R"
    and "V (p, length ts) = None \<Longrightarrow> 
  R = {v. (p, v) \<in> \<Gamma> \<sigma> i \<and> length v = length ts} \<Longrightarrow> finite R \<Longrightarrow>
  qtable X (mem_restr UU X) (\<lambda>v. Formula.sat \<sigma> V (val n X v) i (Formula.Pred p ts)) R"
proof -
  have *: "\<forall>t\<in>set ts. \<forall>x\<in>Formula.fv_trm t. x < n"
    using assms(2) by simp
  show "qtable X (mem_restr UU X) (\<lambda>v. Formula.sat \<sigma> V (val n X v) i (Formula.Pred p ts)) R"
    if "V (p, length ts) = Some P" "R = {v. length v = length ts \<and> P v i}" "finite R"
    unfolding assms(1) fv_list_Pred using that
    by (intro qtable_simple_pattern_gen[OF assms(3) *]) simp_all
  show "qtable X (mem_restr UU X) (\<lambda>v. Formula.sat \<sigma> V (val n X v) i (Formula.Pred p ts)) R"
    if "V (p, length ts) = None" "R = {v. (p, v) \<in> \<Gamma> \<sigma> i \<and> length v = length ts}" "finite R"
    unfolding assms(1) fv_list_Pred using that
    by (intro qtable_simple_pattern_gen[OF assms(3) *]) simp_all
qed
lemma qtable_copy_pattern:
  assumes "X = Formula.fv_list (Formula.Pred p ts)" and "\<forall>x\<in>fv (Formula.Pred p ts). x < n"
    and "is_copy_pattern n ts"
  shows "V (p, length ts) = Some P \<Longrightarrow> 
  R = {v. length v = length ts \<and> P v i} \<Longrightarrow> finite R \<Longrightarrow>
  qtable X (mem_restr UU X) (\<lambda>v. Formula.sat \<sigma> V (val n X v) i (Formula.Pred p ts)) R"
    and "V (p, length ts) = None \<Longrightarrow> 
  R = {v. (p, v) \<in> \<Gamma> \<sigma> i \<and> length v = length ts} \<Longrightarrow> finite R \<Longrightarrow>
  qtable X (mem_restr UU X) (\<lambda>v. Formula.sat \<sigma> V (val n X v) i (Formula.Pred p ts)) R"
  by (fact qtable_simple_pattern[OF assms(1,2) is_copy_pattern_simple[OF assms(3)]])+

lemma match_fvi_trm_None: "Some f = match ts xs \<Longrightarrow> \<forall>t\<in>set ts. x \<notin> Formula.fv_trm t \<Longrightarrow> f x = None"
  by (induction ts xs arbitrary: f rule: match.induct) (auto split: if_splits option.splits)

lemma match_fvi_trm_Some: "Some f = match ts xs \<Longrightarrow> t \<in> set ts \<Longrightarrow> x \<in> Formula.fv_trm t \<Longrightarrow> f x \<noteq> None"
  by (induction ts xs arbitrary: f rule: match.induct) (auto split: if_splits option.splits)

lemma match_eval_trm: "Some f = match ts xs \<Longrightarrow>
    (\<And>x. x \<in> (\<Union>t\<in>set ts. Formula.fv_trm t) \<Longrightarrow> f x = Some (env ! x)) \<Longrightarrow>
    map (Formula.eval_trm env) ts = xs"
proof (induction ts xs arbitrary: f rule: match.induct)
  case (2 x ts y ys)
  then show ?case
    by (auto split: if_splits)
next
  case (3 x ts y ys)
  from 3(2) obtain f0 where f0: "Some f0 = match ts ys"
    by (auto split: option.splits)
  have f: "f = (case f0 x of None \<Rightarrow> f0(x \<mapsto> y) | Some z \<Rightarrow> f0)" and xz: "\<forall>z. f0 x = Some z \<longrightarrow> y = z"
    using 3(2) f0[symmetric] by (auto split: option.splits if_splits)
  have "f0 z = Some (env ! z)" if "z \<in> (\<Union>t\<in>set ts. Formula.fv_trm t)" for z
  proof -
    have "f0 z \<noteq> None"
      using that match_fvi_trm_Some[OF f0] by blast
    then show ?thesis
      using 3(3)[of z] that f by (auto split: option.splits if_splits)
  qed
  then have "map (Formula.eval_trm env) ts = ys"
    by (rule 3(1)[OF f0])
  moreover have "env ! x = y"
    using 3(3)[of x] f xz by (auto split: option.splits)
  ultimately show ?case
    by simp
qed auto

lemma match_map_eval_trm: "\<forall>t\<in>set ts. trm.is_Var t \<or> trm.is_Const t \<Longrightarrow>
  \<exists>f. match ts (map (Formula.eval_trm env) ts) = Some f \<and>
    (\<forall>x. f x = (if x \<in> (\<Union>t\<in>set ts. Formula.fv_trm t) then Some (env ! x) else None))"
proof (induction ts)
  case (Cons t ts)
  then obtain f where f: "match ts (map (Formula.eval_trm env) ts) = Some f"
    "\<forall>x. f x = (if x \<in> (\<Union>t\<in>set ts. Formula.fv_trm t) then Some (env ! x) else None)"
    by auto
  from Cons(2) show ?case
  proof (cases t)
    case (Var x)
    show ?thesis
    proof (cases "x \<in> (\<Union>t\<in>set ts. Formula.fv_trm t)")
      case True
      with f Var show ?thesis
        by (intro exI[of _ f]) auto
    next
      case False
      with f Var show ?thesis
        by (intro exI[of _ "f(x \<mapsto> env ! x)"]) auto
    qed
  qed (use f in \<open>auto simp: trm.is_Var_def trm.is_Const_def\<close>)qed simp

lemma qtable_no_pattern_gen:
  assumes "\<forall>t\<in>set ts. \<forall>x\<in>Formula.fv_trm t. x < n" "\<forall>t\<in>set ts. trm.is_Var t \<or> trm.is_Const t"
    and sat: "\<And>v. Formula.sat \<sigma> V v i (Formula.Pred p ts) \<longleftrightarrow> map (Formula.eval_trm v) ts \<in> S"
    and fin: "finite S"
  shows "qtable (pred_cols ts) (mem_restr UU (pred_cols ts))
    (\<lambda>v. Formula.sat \<sigma> V (val n (pred_cols ts) v) i (Formula.Pred p ts))
    (tabulate_match (pred_cols ts) ` Option.these (match ts ` S))"
proof -
  let ?cs = "pred_cols ts"
  let ?R = "tabulate_match ?cs ` Option.these (match ts ` S)"
  have mem: "v \<in> ?R \<longleftrightarrow> (\<exists>f xs. xs \<in> S \<and> Some f = match ts xs \<and> v = tabulate_match ?cs f)" for v
    unfolding image_iff Bex_def in_these_eq by blast
  show ?thesis
    unfolding qtable_iff
  proof (intro conjI allI impI)
    show "table ?cs ?R"
      by (auto simp: table_def wf_tuple_def tabulate_match_def mem)
    show "finite ?R"
      using fin by (simp add: Option.these_def)
    fix v
    assume "mem_restr UU ?cs v"
    then have wf: "wf_tuple ?cs v"
      by (rule mem_restr_wf_tuple)
    let ?env = "val n ?cs v"
    show "v \<in> ?R \<longleftrightarrow> Formula.sat \<sigma> V ?env i (Formula.Pred p ts) \<and> wf_tuple ?cs v"
    proof
      assume "v \<in> ?R"
      then obtain f xs where "xs \<in> S" and f: "Some f = match ts xs"
        and v: "v = tabulate_match ?cs f"
        unfolding mem by blast
      have "f x = Some (?env ! x)" if x: "x \<in> (\<Union>t\<in>set ts. Formula.fv_trm t)" for x
      proof -
        have "x \<in> set ?cs" "x < n"
          using x assms(1) by auto
        moreover obtain y where "f x = Some y"
          using match_fvi_trm_Some[OF f] x by blast
        ultimately show ?thesis
          by (simp add: v tabulate_match_def tup_get_map_self)
      qed
      then have "map (Formula.eval_trm ?env) ts = xs"        by (rule match_eval_trm[OF f])
      with \<open>xs \<in> S\<close> wf show "Formula.sat \<sigma> V ?env i (Formula.Pred p ts) \<and> wf_tuple ?cs v"
        using sat by simp
    next
      assume "Formula.sat \<sigma> V ?env i (Formula.Pred p ts) \<and> wf_tuple ?cs v"
      then have "map (Formula.eval_trm ?env) ts \<in> S"
        using sat by simp
      moreover obtain f where f: "match ts (map (Formula.eval_trm ?env) ts) = Some f"
        "\<forall>x. f x = (if x \<in> (\<Union>t\<in>set ts. Formula.fv_trm t) then Some (?env ! x) else None)"
        using match_map_eval_trm[OF assms(2)] by blast
      moreover have "tabulate_match ?cs f = v"
      proof -
        have "tabulate_match ?cs f = map (tup_get ?cs v) ?cs"
          using f(2) assms(1) by (auto simp: tabulate_match_def)
        also have "\<dots> = v"
          using restrict_idle[OF distinct_pred_cols wf] by (simp add: restrict_def)
        finally show ?thesis .
      qed
      ultimately show "v \<in> ?R"
        unfolding mem by metis
    qed
  qed
qed

lemma qtable_no_pattern:
  assumes "X = Formula.fv_list (Formula.Pred p ts)" and "\<forall>x\<in>fv (Formula.Pred p ts). x < n"
    and "\<forall>t\<in>set ts. trm.is_Var t \<or> trm.is_Const t"
  shows "V (p, length ts) = Some P \<Longrightarrow> 
  R = tabulate_match X ` Option.these (match ts ` {v. length v = length ts \<and> P v i}) \<Longrightarrow>
  finite {v. length v = length ts \<and> P v i} \<Longrightarrow>
  qtable X (mem_restr UU X) (\<lambda>v. Formula.sat \<sigma> V (val n X v) i (Formula.Pred p ts)) R"
    and "V (p, length ts) = None \<Longrightarrow> 
  R = tabulate_match X ` Option.these (match ts ` {v. (p, v) \<in> \<Gamma> \<sigma> i \<and> length v = length ts}) \<Longrightarrow>
  finite {v. (p, v) \<in> \<Gamma> \<sigma> i \<and> length v = length ts} \<Longrightarrow>
  qtable X (mem_restr UU X) (\<lambda>v. Formula.sat \<sigma> V (val n X v) i (Formula.Pred p ts)) R"
proof -
  have *: "\<forall>t\<in>set ts. \<forall>x\<in>Formula.fv_trm t. x < n"
    using assms(2) by simp
  show "qtable X (mem_restr UU X) (\<lambda>v. Formula.sat \<sigma> V (val n X v) i (Formula.Pred p ts)) R"
    if "V (p, length ts) = Some P"
      "R = tabulate_match X ` Option.these (match ts ` {v. length v = length ts \<and> P v i})"
      "finite {v. length v = length ts \<and> P v i}"
    unfolding that(2) assms(1) fv_list_Pred using that(1,3)
    by (intro qtable_no_pattern_gen[OF * assms(3)]) simp
  show "qtable X (mem_restr UU X) (\<lambda>v. Formula.sat \<sigma> V (val n X v) i (Formula.Pred p ts)) R"
    if "V (p, length ts) = None"
      "R = tabulate_match X ` Option.these (match ts ` {v. (p, v) \<in> \<Gamma> \<sigma> i \<and> length v = length ts})"
      "finite {v. (p, v) \<in> \<Gamma> \<sigma> i \<and> length v = length ts}"
    unfolding that(2) assms(1) fv_list_Pred using that(1,3)
    by (intro qtable_no_pattern_gen[OF * assms(3)]) simp
qed

subsubsection \<open> Equalities \<close>

text \<open>The columns of an equation between a variable and a constant (or two constants).\<close>

lemma qtable_eq_relI: "\<forall>x\<in>fv_trm t1. x < n \<Longrightarrow> \<forall>x\<in>fv_trm t2. x < n \<Longrightarrow> is_simple_eq t1 t2 \<Longrightarrow>
  cs = cols_union (Formula.fv_trm_list t1) (Formula.fv_trm_list t2) \<Longrightarrow>
  qtable cs (mem_restr U cs)
    (\<lambda>v. Formula.eval_trm (val n cs v) t1 = Formula.eval_trm (val n cs v) t2) (eq_rel t1 t2)"
  by (cases t1; cases t2)
    (auto simp: is_simple_eq_def qtable_iff table_def cols_union_def singleton_table_def unit_table_def
      empty_table_def length_Suc_conv tup_get_Cons dest: mem_restr_wf_tuple)


subsubsection \<open> Existential \<close>

text \<open>The table of an existential quantifier: the projection drops the column of the bound
  variable @{term 0}.\<close>

lemma qtable_project_fv:
  assumes "distinct cs" "set cs = fv \<phi>" "\<forall>x\<in>fv \<phi>. x < Suc n"
    and "qtable cs (mem_restr (lift_envs R) cs) (\<lambda>v. Formula.sat \<sigma> V (val (Suc n) cs v) i \<phi>) X"
  shows "qtable (ex_cols cs) (mem_restr R (ex_cols cs))
    (\<lambda>v. Formula.sat \<sigma> V (val n (ex_cols cs) v) i (Formula.Exists t \<phi>)) (ex_proj cs ` X)"
proof (rule qtable_cong[OF qtable_project[OF assms(1,4)] refl])
  fix v
  assume "mem_restr R (ex_cols cs) v"
  then have wf: "wf_tuple (ex_cols cs) v"
    by (rule mem_restr_wf_tuple)
  have agree: "Formula.sat \<sigma> V (val (Suc n) cs x) i \<phi> \<longleftrightarrow> Formula.sat \<sigma> V (z # val n (ex_cols cs) v) i \<phi>"
    if "0 \<in> set cs \<Longrightarrow> tup_get cs x 0 = z" "\<And>c. c \<in> set cs \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> tup_get cs x c = tup_get (ex_cols cs) v (c - 1)"
    for x z
  proof (rule sat_fv_cong, intro ballI)
    fix c
    assume "c \<in> fv \<phi>"
    then show "val (Suc n) cs x ! c = (z # val n (ex_cols cs) v) ! c"
      using assms(2,3) that by (cases c) auto
  qed
  show "(\<exists>x. wf_tuple cs x \<and> ex_proj cs x = v \<and> Formula.sat \<sigma> V (val (Suc n) cs x) i \<phi>) \<longleftrightarrow>
    Formula.sat \<sigma> V (val n (ex_cols cs) v) i (Formula.Exists t \<phi>)"
  proof
    assume "\<exists>x. wf_tuple cs x \<and> ex_proj cs x = v \<and> Formula.sat \<sigma> V (val (Suc n) cs x) i \<phi>"
    then obtain x where x: "ex_proj cs x = v" "Formula.sat \<sigma> V (val (Suc n) cs x) i \<phi>"
      by blast
    have "Formula.sat \<sigma> V (tup_get cs x 0 # val n (ex_cols cs) v) i \<phi>"
      using x(2) tup_get_ex_proj[of _ cs x] by (subst agree[symmetric]) (auto simp: x(1)[symmetric])
    then show "Formula.sat \<sigma> V (val n (ex_cols cs) v) i (Formula.Exists t \<phi>)"
      by auto
  next
    assume "Formula.sat \<sigma> V (val n (ex_cols cs) v) i (Formula.Exists t \<phi>)"
    then obtain z where z: "Formula.sat \<sigma> V (z # val n (ex_cols cs) v) i \<phi>"
      by auto
    define x where "x = map (\<lambda>c. if c = 0 then z else tup_get (ex_cols cs) v (c - 1)) cs"
    have get: "tup_get cs x c = (if c = 0 then z else tup_get (ex_cols cs) v (c - 1))" if "c \<in> set cs" for c
      using that by (simp add: x_def tup_get_map_self)
    have "ex_proj cs x = map (tup_get (ex_cols cs) v) (ex_cols cs)"
      by (auto simp: ex_proj_def ex_cols_def restrict_def get)
    also have "\<dots> = v"
      using restrict_idle[OF distinct_ex_cols[OF assms(1)] wf] by (simp add: restrict_def)
    finally have "ex_proj cs x = v" .
    moreover have "Formula.sat \<sigma> V (val (Suc n) cs x) i \<phi>"
      using z by (subst agree) (simp_all add: get)
    ultimately show "\<exists>x. wf_tuple cs x \<and> ex_proj cs x = v \<and> Formula.sat \<sigma> V (val (Suc n) cs x) i \<phi>"
      by (intro exI[of _ x]) (simp add: wf_tuple_def x_def)  qed
qed

subsubsection \<open> Next and Previous \<close>

lemma mprev_next_NilE[elim!]: "mprev_next I xs ts = (ys, [], []) \<Longrightarrow>
  (xs = [] \<Longrightarrow> ts = [] \<Longrightarrow> ys = [] \<Longrightarrow> R) \<Longrightarrow> R"
  by (induct I xs ts arbitrary: ys rule: mprev_next.induct) (auto split: prod.splits)

lemma mprev: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow>
  list_all2 P [i..<j'] xs \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [i..<j] ts \<Longrightarrow> i \<le> j' \<Longrightarrow> i \<le> j \<Longrightarrow>
  list_all2 (\<lambda>i X. if mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) then P i X else X = empty_table)
    [i..<min j' (if i = j then j else j-1)] ys \<and>
  list_all2 P [min j' (if i = j then j else j-1)..<j'] xs' \<and>
  list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min j' (if i = j then j else j-1)..<j] ts'"
proof (induction I xs ts arbitrary: i ys xs' ts' rule: mprev_next.induct)
  case (1 I ts)
  then have "min j' (if i = j then j else j-1) = i" by auto
  with 1 show ?case by auto
next
  case (3 I v v' t)
  then have "min j' (j-1) = i" by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  with 3 show ?case by auto
next
  case (4 I x xs t t' ts)
  from 4(2) obtain ys0 where rec: "mprev_next I xs (t' # ts) = (ys0, xs', ts')"
    and ys: "ys = (if mem I (t' - t) then x else empty_table) # ys0"
    by (cases "mprev_next I xs (t' # ts)") auto
  from 4(3) have "i < j'" and Px: "P i x" and xs: "list_all2 P [Suc i..<j'] xs"
    by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  from 4(4) have "Suc i < j" and t: "t = \<tau> \<sigma> i" "t' = \<tau> \<sigma> (Suc i)"
    and ts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [Suc i..<j] (t' # ts)"
    by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  let ?m = "min j' (j - 1)"
  have m: "min j' (if i = j then j else j - 1) = ?m" "min j' (if Suc i = j then j else j - 1) = ?m"
    using \<open>Suc i < j\<close> by simp_all
  have upt: "[i..<?m] = i # [Suc i..<?m]"
    using \<open>i < j'\<close> \<open>Suc i < j\<close> by (intro upt_conv_Cons) simp
  have IH: "list_all2 (\<lambda>i X. if mem I (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) then P i X else X = empty_table)
      [Suc i..<?m] ys0 \<and> list_all2 P [?m..<j'] xs' \<and> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?m..<j] ts'"
    using 4(1)[OF rec xs ts Suc_leI[OF \<open>i < j'\<close>] less_imp_le[OF \<open>Suc i < j\<close>]]
    unfolding m .
  have hd: "if mem I (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) then P i (if mem I (t' - t) then x else empty_table)
    else (if mem I (t' - t) then x else empty_table) = empty_table"
    using Px by (simp add: t)
  show ?case
    unfolding m upt ys list_all2_Cons using hd IH by blast
qed (auto simp: gr0_conv_Suc)

lemma mnext: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow>
  list_all2 P [Suc i..<j'] xs \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [i..<j] ts \<Longrightarrow> Suc i \<le> j' \<Longrightarrow> i \<le> j \<Longrightarrow>
  list_all2 (\<lambda>i X. if mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) then P (Suc i) X else X = empty_table)
    [i..<min (j'-1) ((if i = j then j else j-1))] ys \<and>
  list_all2 P [Suc (min (j'-1) ((if i = j then j else j-1)))..<j'] xs' \<and>
  list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (j'-1) ((if i = j then j else j-1))..<j] ts'"
proof (induction I xs ts arbitrary: i ys xs' ts' rule: mprev_next.induct)
  case (1 I ts)
  then have "min (j' - 1) ((if i = j then j else j-1)) = i" by auto
  with 1 show ?case by auto
next
  case (3 I v v' t)
  then have "min (j' - 1) ((if i = j then j else j-1)) = i" by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  with 3 show ?case by auto
next
  case (4 I x xs t t' ts)
  from 4(2) obtain ys0 where rec: "mprev_next I xs (t' # ts) = (ys0, xs', ts')"
    and ys: "ys = (if mem I (t' - t) then x else empty_table) # ys0"
    by (cases "mprev_next I xs (t' # ts)") auto
  from 4(3) have "Suc i < j'" and Px: "P (Suc i) x" and xs: "list_all2 P [Suc (Suc i)..<j'] xs"
    by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  from 4(4) have "Suc i < j" and t: "t = \<tau> \<sigma> i" "t' = \<tau> \<sigma> (Suc i)"
    and ts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [Suc i..<j] (t' # ts)"
    by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  let ?m = "min (j' - 1) (j - 1)"
  have m: "min (j' - 1) (if i = j then j else j - 1) = ?m"
    "min (j' - 1) (if Suc i = j then j else j - 1) = ?m"
    using \<open>Suc i < j\<close> by simp_all
  have upt: "[i..<?m] = i # [Suc i..<?m]"
    using \<open>Suc i < j'\<close> \<open>Suc i < j\<close> by (intro upt_conv_Cons) (simp add: less_diff_conv)
  have IH: "list_all2 (\<lambda>i X. if mem I (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) then P (Suc i) X else X = empty_table)
      [Suc i..<?m] ys0 \<and> list_all2 P [Suc ?m..<j'] xs' \<and> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?m..<j] ts'"
    using 4(1)[OF rec xs ts Suc_leI[OF \<open>Suc i < j'\<close>] less_imp_le[OF \<open>Suc i < j\<close>]]
    unfolding m .
  have hd: "if mem I (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) then P (Suc i) (if mem I (t' - t) then x else empty_table)
    else (if mem I (t' - t) then x else empty_table) = empty_table"
    using Px by (simp add: t)
  show ?case
    unfolding m upt ys list_all2_Cons using hd IH by blast
qed auto

(*<*)
end
(*>*)
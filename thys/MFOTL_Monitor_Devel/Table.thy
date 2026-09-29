(*<*)
theory Table
  imports Main
begin
(*>*)

section \<open>Finite tables\<close>

text \<open>
  A table is a set of tuples over a list of \<^emph>\<open>columns\<close>: variable indices, one per field of
  the tuple, in the tuple's order.  A tuple holds the values of exactly those variables, so it is
  as long as its column list.  The columns are not stored with the table; they are a parameter of
  every statement about it, as the free variables of the formula a table evaluates are.

  Column lists are free of duplicates wherever it matters, and otherwise in any order.  The order
  the monitor uses is MonPoly's: the columns of a conjunction are those of its left operand
  followed by the new ones of its right operand (@{text cols_union}), so a join produces its
  output in the order the conjunction's own columns are listed, without reordering.
\<close>

type_synonym 'a tuple = "'a list"
type_synonym 'a table = "'a tuple set"


subsection \<open>Columns\<close>

text \<open>The union of two column lists in MonPoly's order: the first list, then the columns of the
  second that are new, in the second's order.\<close>

definition cols_union :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "cols_union xs ys = xs @ filter (\<lambda>y. y \<notin> set xs) ys"

lemma set_cols_union[simp]: "set (cols_union xs ys) = set xs \<union> set ys"
  by (auto simp: cols_union_def)

lemma distinct_cols_union[simp]: "distinct xs \<Longrightarrow> distinct ys \<Longrightarrow> distinct (cols_union xs ys)"
  by (auto simp: cols_union_def)

lemma cols_union_Nil[simp]: "cols_union [] ys = ys" "cols_union xs [] = xs"
  by (simp_all add: cols_union_def)

lemma cols_union_subset: "set ys \<subseteq> set xs \<Longrightarrow> cols_union xs ys = xs"
  by (auto simp: cols_union_def filter_empty_conv)

lemma cols_union_self[simp]: "cols_union xs xs = xs"
  by (simp add: cols_union_subset)


subsection \<open>Well-formed tuples and tables\<close>

definition wf_tuple :: "nat list \<Rightarrow> 'a tuple \<Rightarrow> bool" where
  "wf_tuple cs x \<longleftrightarrow> length x = length cs"

lemma wf_tuple_length: "wf_tuple cs x \<Longrightarrow> length x = length cs"
  by (simp add: wf_tuple_def)

lemma wf_tuple_Nil[simp]: "wf_tuple [] x \<longleftrightarrow> x = []" "wf_tuple cs [] \<longleftrightarrow> cs = []"
  by (auto simp: wf_tuple_def)

lemma wf_tuple_Cons[simp]: "wf_tuple (c # cs) x \<longleftrightarrow> (\<exists>a y. x = a # y \<and> wf_tuple cs y)"
  by (cases x) (auto simp: wf_tuple_def)

lemma wf_tuple_append: "wf_tuple cs x \<Longrightarrow> wf_tuple ds y \<Longrightarrow> wf_tuple (cs @ ds) (x @ y)"
  by (simp add: wf_tuple_def)

lemma wf_tuple_upt: "wf_tuple [0..<n] x \<longleftrightarrow> length x = n"
  by (simp add: wf_tuple_def)

definition table :: "nat list \<Rightarrow> 'a table \<Rightarrow> bool" where
  "table cs X \<longleftrightarrow> (\<forall>x\<in>X. wf_tuple cs x)"

lemma tableI: "(\<And>x. x \<in> X \<Longrightarrow> wf_tuple cs x) \<Longrightarrow> table cs X"
  unfolding table_def by auto

lemma tableD: "table cs X \<Longrightarrow> x \<in> X \<Longrightarrow> wf_tuple cs x"
  unfolding table_def by auto

lemma table_Un[simp]: "table cs X \<Longrightarrow> table cs Y \<Longrightarrow> table cs (X \<union> Y)"
  unfolding table_def by auto

lemma table_InterI: "\<R> \<noteq> {} \<Longrightarrow> \<forall>R\<in>\<R>. table cs R \<Longrightarrow> table cs (\<Inter> \<R>)"
  unfolding table_def by auto

lemma table_empty[simp]: "table cs {}"
  by (simp add: table_def)

lemma table_subset: "table cs X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> table cs Y"
  unfolding table_def by auto


subsection \<open>Reading a variable\<close>

text \<open>The value a tuple over @{term cs} gives variable @{term i}.  At a variable that is not a
  column it is @{term "the None"}, the unspecified value the previous representation read off a
  hole; only the values at the columns ever matter.\<close>

definition tup_get :: "nat list \<Rightarrow> 'a tuple \<Rightarrow> nat \<Rightarrow> 'a" where
  "tup_get cs x i = the (map_of (zip cs x) i)"

lemma tup_get_nth:
  "distinct cs \<Longrightarrow> wf_tuple cs x \<Longrightarrow> k < length cs \<Longrightarrow> tup_get cs x (cs ! k) = x ! k"
  by (simp add: tup_get_def wf_tuple_def map_of_zip_nth)

lemma tup_get_Cons: "tup_get (c # cs) (a # x) i = (if i = c then a else tup_get cs x i)"
  by (simp add: tup_get_def)

lemma tup_get_append:
  "wf_tuple cs x \<Longrightarrow> tup_get (cs @ ds) (x @ y) i = (if i \<in> set cs then tup_get cs x i else tup_get ds y i)"
  by (induct cs arbitrary: x) (auto simp: tup_get_Cons wf_tuple_def length_Suc_conv)

lemma tup_get_map:
  assumes "inj_on f (set cs)" "c \<in> set cs"
  shows "tup_get (map f cs) x (f c) = tup_get cs x c"
  using assms
proof (induct cs arbitrary: x)
  case (Cons d cs)
  show ?case
  proof (cases x)
    case Nil
    then show ?thesis by (simp add: tup_get_def)
  next
    case x: (Cons a y)
    show ?thesis
    proof (cases "c = d")
      case False
      with Cons.prems have "f c \<noteq> f d" "c \<in> set cs" "inj_on f (set cs)"
        by (auto simp: inj_on_def)
      with Cons.hyps show ?thesis
        by (simp add: x tup_get_Cons False)
    qed (simp add: x tup_get_Cons)
  qed
qed simp

lemma wf_tuple_cong:
  assumes "distinct cs" "wf_tuple cs v" "wf_tuple cs w" "\<forall>c\<in>set cs. tup_get cs v c = tup_get cs w c"
  shows "v = w"
proof (rule nth_equalityI)
  show "length v = length w"
    using assms(2,3) by (simp add: wf_tuple_def)
  fix k
  assume "k < length v"
  then have "k < length cs"
    using assms(2) by (simp add: wf_tuple_def)
  then show "v ! k = w ! k"
    using assms(4)[THEN bspec, of "cs ! k"] tup_get_nth[OF assms(1,2)] tup_get_nth[OF assms(1,3)]
    by simp
qed

text \<open>The valuation of the first @{term n} variables a tuple determines, for the semantics.\<close>

definition val :: "nat \<Rightarrow> nat list \<Rightarrow> 'a tuple \<Rightarrow> 'a list" where
  "val n cs x = map (tup_get cs x) [0..<n]"

lemma length_val[simp]: "length (val n cs x) = n"
  by (simp add: val_def)

lemma nth_val[simp]: "i < n \<Longrightarrow> val n cs x ! i = tup_get cs x i"
  by (simp add: val_def)


subsection \<open>Restriction\<close>

text \<open>The restriction of a tuple over @{term cs} to the columns @{term ds}, in the order of
  @{term ds}.  It projects when @{term ds} lists fewer columns and reorders when it lists the same
  ones in another order.\<close>

definition restrict :: "nat list \<Rightarrow> nat list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
  "restrict ds cs x = map (tup_get cs x) ds"

lemma length_restrict[simp]: "length (restrict ds cs x) = length ds"
  by (simp add: restrict_def)

lemma wf_tuple_restrict[simp]: "wf_tuple ds (restrict ds cs x)"
  by (simp add: wf_tuple_def)

lemma restrict_Nil[simp]: "restrict [] cs x = []"
  by (simp add: restrict_def)

lemma nth_restrict: "k < length ds \<Longrightarrow> restrict ds cs x ! k = tup_get cs x (ds ! k)"
  by (simp add: restrict_def)

lemma tup_get_restrict: "c \<in> set ds \<Longrightarrow> tup_get ds (restrict ds cs x) c = tup_get cs x c"
  by (simp add: restrict_def tup_get_def map_of_zip_map)

lemma restrict_idle: "distinct cs \<Longrightarrow> wf_tuple cs x \<Longrightarrow> restrict cs cs x = x"
  by (rule nth_equalityI) (simp_all add: wf_tuple_def nth_restrict tup_get_nth)

lemma restrict_restrict: "set es \<subseteq> set ds \<Longrightarrow> restrict es ds (restrict ds cs x) = restrict es cs x"
  unfolding restrict_def[of es] by (auto intro!: map_cong tup_get_restrict)

lemma restrict_cong:
  "(\<And>c. c \<in> set ds \<Longrightarrow> tup_get cs x c = tup_get cs' x' c) \<Longrightarrow> restrict ds cs x = restrict ds cs' x'"
  by (simp add: restrict_def)

lemma val_restrict: "i \<in> set ds \<Longrightarrow> i < n \<Longrightarrow> val n ds (restrict ds cs x) ! i = val n cs x ! i"
  by (simp add: tup_get_restrict)

lemma restrict_append:
  "wf_tuple cs x \<Longrightarrow> set ds \<subseteq> set cs \<Longrightarrow> restrict ds (cs @ cs') (x @ y) = restrict ds cs x"
  by (rule restrict_cong) (auto simp: tup_get_append)


subsection \<open>Empty, unit, and singleton tables\<close>

definition "empty_table = {}"

lemma in_empty_table[simp]: "\<not> x \<in> empty_table"
  unfolding empty_table_def by simp

lemma empty_table[simp]: "table cs empty_table"
  unfolding table_def empty_table_def by simp

text \<open>The unit table holds the one tuple over no columns.\<close>

definition "unit_table = {[]}"

lemma in_unit_table: "v \<in> unit_table \<longleftrightarrow> v = []"
  unfolding unit_table_def by simp

lemma unit_table[simp]: "table [] unit_table"
  unfolding table_def unit_table_def by simp

lemma empty_neq_unit_table[simp]: "empty_table \<noteq> unit_table"
  by (simp add: empty_table_def unit_table_def)

lemma union_empty_table_eq[simp]: "empty_table \<union> R = R" "R \<union> empty_table = R"
  by (simp_all add: empty_table_def)

lemma table_empty_vars_iff: "table [] R \<longleftrightarrow> R = empty_table \<or> R = unit_table"
  unfolding table_def empty_table_def unit_table_def by auto

lemmas table_empty_varsD = iffD1[OF table_empty_vars_iff]

primrec tabulate :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "tabulate f x 0 = []"
| "tabulate f x (Suc n) = f x # tabulate f (Suc x) n"

lemma tabulate_alt: "tabulate f x n = map f [x ..< x + n]"
  by (induct n arbitrary: x) (auto simp: not_le Suc_le_eq upt_rec)

lemma length_tabulate[simp]: "length (tabulate f x n) = n"
  by (induction n arbitrary: x) simp_all

lemma map_tabulate[simp]: "map f (tabulate g x n) = tabulate (\<lambda>x. f (g x)) x n"
  by (induction n arbitrary: x) simp_all

lemma nth_tabulate[simp]: "k < n \<Longrightarrow> tabulate f x n ! k = f (x + k)"
proof (induction n arbitrary: x k)
  case (Suc n)
  then show ?case by (cases k) simp_all
qed simp

definition "singleton_table x = {[x]}"

lemma singleton_table[simp]: "table [i] (singleton_table x)"
  unfolding table_def singleton_table_def by simp


subsection \<open>Join\<close>

subsubsection \<open>Joining tuples\<close>

text \<open>Two tuples join if they agree on their common columns; the joined tuple is over the union
  of their columns, in the order of @{const cols_union}.\<close>

fun join1 :: "nat list \<Rightarrow> nat list \<Rightarrow> 'a tuple \<times> 'a tuple \<Rightarrow> 'a tuple option" where
  "join1 cs ds (x, y) = (if \<forall>c \<in> set cs \<inter> set ds. tup_get cs x c = tup_get ds y c
     then Some (x @ restrict (filter (\<lambda>d. d \<notin> set cs) ds) ds y) else None)"

declare join1.simps[simp del]

lemma join1_Some_restrict:
  assumes "distinct cs" "distinct ds" "wf_tuple cs x" "wf_tuple ds y"
  shows "join1 cs ds (x, y) = Some z \<longleftrightarrow> wf_tuple (cols_union cs ds) z \<and>
    restrict cs (cols_union cs ds) z = x \<and> restrict ds (cols_union cs ds) z = y"
proof -
  let ?ds' = "filter (\<lambda>d. d \<notin> set cs) ds"
  have U: "cols_union cs ds = cs @ ?ds'"
    by (simp add: cols_union_def)
  have dU: "distinct (cs @ ?ds')"
    using assms(1,2) by auto
  show ?thesis
  proof
    assume "join1 cs ds (x, y) = Some z"
    then have agree: "\<forall>c \<in> set cs \<inter> set ds. tup_get cs x c = tup_get ds y c"
      and z: "z = x @ restrict ?ds' ds y"
      by (auto simp: join1.simps split: if_splits)
    have "restrict ds (cs @ ?ds') z = restrict ds ds y"
      unfolding z using agree
      by (intro restrict_cong) (auto simp: tup_get_append[OF assms(3)] tup_get_restrict)
    then show "wf_tuple (cols_union cs ds) z \<and>
      restrict cs (cols_union cs ds) z = x \<and> restrict ds (cols_union cs ds) z = y"
      using assms(3) restrict_append[OF assms(3) subset_refl] restrict_idle[OF assms(1,3)]
        restrict_idle[OF assms(2,4)]
      by (simp add: U z wf_tuple_def)
  next
    assume "wf_tuple (cols_union cs ds) z \<and>
      restrict cs (cols_union cs ds) z = x \<and> restrict ds (cols_union cs ds) z = y"
    then have wf: "wf_tuple (cs @ ?ds') z" and zx: "restrict cs (cs @ ?ds') z = x"
      and zy: "restrict ds (cs @ ?ds') z = y"
      by (simp_all add: U)
    have agree: "\<forall>c \<in> set cs \<inter> set ds. tup_get cs x c = tup_get ds y c"
      using zx zy tup_get_restrict[of _ cs "cs @ ?ds'" z] tup_get_restrict[of _ ds "cs @ ?ds'" z]
      by auto
    have "z = restrict (cs @ ?ds') (cs @ ?ds') z"
      using restrict_idle[OF dU wf] by simp
    also have "\<dots> = restrict cs (cs @ ?ds') z @ restrict ?ds' (cs @ ?ds') z"
      by (simp add: restrict_def)
    also have "restrict ?ds' (cs @ ?ds') z = restrict ?ds' ds y"
      unfolding zy[symmetric] by (subst restrict_restrict) auto
    finally have "z = x @ restrict ?ds' ds y"
      using zx by simp
    with agree show "join1 cs ds (x, y) = Some z"
      by (simp add: join1.simps)
  qed
qed

lemma join1_wf_tuple:
  "wf_tuple cs x \<Longrightarrow> wf_tuple ds y \<Longrightarrow> join1 cs ds (x, y) = Some z \<Longrightarrow> wf_tuple (cols_union cs ds) z"
  by (auto simp: join1.simps wf_tuple_def cols_union_def split: if_splits)

text \<open>When the second tuple's columns are among the first's, the two join exactly if the first
  restricts to the second, and then the joined tuple is the first.\<close>

lemma join1_sub:
  assumes "distinct cs" "distinct ds" "wf_tuple cs x" "wf_tuple ds y" "set ds \<subseteq> set cs"
  shows "join1 cs ds (x, y) = (if restrict ds cs x = y then Some x else None)"
proof -
  have U: "cols_union cs ds = cs"
    using assms(5) by (rule cols_union_subset)
  have iff: "join1 cs ds (x, y) = Some z \<longleftrightarrow> z = x \<and> restrict ds cs x = y" for z
    using join1_Some_restrict[OF assms(1-4), of z] restrict_idle[OF assms(1)] assms(3)
    by (auto simp: U)
  show ?thesis
  proof (cases "restrict ds cs x = y")
    case True
    then show ?thesis
      using iff[of x] by simp
  next
    case False
    then have "join1 cs ds (x, y) \<noteq> Some z" for z
      using iff[of z] by simp
    then have "join1 cs ds (x, y) = None"
      by (cases "join1 cs ds (x, y)") blast+
    with False show ?thesis
      by simp
  qed
qed


subsubsection \<open>Joining tables\<close>

text \<open>The join and, for @{term "pos = False"}, the antijoin, whose second operand's columns are
  among the first's.\<close>

definition join :: "nat list \<Rightarrow> 'a table \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "join cs A pos ds B = (if pos then Option.these (join1 cs ds ` (A \<times> B))
    else {a \<in> A. \<forall>b \<in> B. join1 cs ds (a, b) = None})"

lemma join_True_code[code]: "join cs A True ds B = (\<Union>a \<in> A. \<Union>b \<in> B. set_option (join1 cs ds (a, b)))"
  unfolding join_def by (force simp: Option.these_def image_iff)

lemma join_False_code[code]: "join cs A False ds B = {a \<in> A. \<forall>b \<in> B. join1 cs ds (a, b) = None}"
  unfolding join_def by simp

lemma join_restrict:
  assumes "distinct cs" "distinct ds" "table cs X" "table ds Y" "\<not> b \<Longrightarrow> set ds \<subseteq> set cs"
  shows "v \<in> join cs X b ds Y \<longleftrightarrow> wf_tuple (cols_union cs ds) v \<and>
    restrict cs (cols_union cs ds) v \<in> X \<and>
    (if b then restrict ds (cols_union cs ds) v \<in> Y else restrict ds (cols_union cs ds) v \<notin> Y)"
proof (cases b)
  case True
  have iff: "join1 cs ds (x, y) = Some v \<longleftrightarrow> wf_tuple (cols_union cs ds) v \<and>
      restrict cs (cols_union cs ds) v = x \<and> restrict ds (cols_union cs ds) v = y"
    if "x \<in> X" "y \<in> Y" for x y
    using join1_Some_restrict[OF assms(1,2) tableD[OF assms(3) that(1)] tableD[OF assms(4) that(2)]] .
  have "v \<in> join cs X b ds Y \<longleftrightarrow> (\<exists>x \<in> X. \<exists>y \<in> Y. join1 cs ds (x, y) = Some v)"
    using True by (auto simp: join_True_code)
  also have "\<dots> \<longleftrightarrow> (\<exists>x \<in> X. \<exists>y \<in> Y. wf_tuple (cols_union cs ds) v \<and>
      restrict cs (cols_union cs ds) v = x \<and> restrict ds (cols_union cs ds) v = y)"
    using iff by (simp cong: bex_cong)
  finally show ?thesis
    using True by auto
next
  case False
  then have sub: "set ds \<subseteq> set cs"
    by (rule assms(5))
  then have U: "cols_union cs ds = cs"
    by (rule cols_union_subset)
  have none: "join1 cs ds (v, y) = None \<longleftrightarrow> restrict ds cs v \<noteq> y" if "v \<in> X" "y \<in> Y" for y
    using join1_sub[OF assms(1,2) tableD[OF assms(3) that(1)] tableD[OF assms(4) that(2)] sub]
    by simp
  have "v \<in> join cs X b ds Y \<longleftrightarrow> v \<in> X \<and> (\<forall>y \<in> Y. restrict ds cs v \<noteq> y)"
    using False none by (auto simp: join_False_code)
  then show ?thesis
    using False restrict_idle[OF assms(1)] tableD[OF assms(3)]
    by (auto simp: U)
qed

lemmas join_restrict_table = join_restrict

lemma join_table:
  assumes "table cs X" "table ds Y" "\<not> b \<Longrightarrow> set ds \<subseteq> set cs" "cols_union cs ds = es"
  shows "table es (join cs X b ds Y)"
proof (cases b)
  case True
  show ?thesis
  proof (rule tableI)
    fix z
    assume "z \<in> join cs X b ds Y"
    then obtain x y where "x \<in> X" "y \<in> Y" "join1 cs ds (x, y) = Some z"
      using True by (auto simp: join_True_code)
    then show "wf_tuple es z"
      using assms(4) join1_wf_tuple tableD[OF assms(1)] tableD[OF assms(2)] by blast
  qed
next
  case False
  then have "es = cs"
    using assms(3,4) cols_union_subset by blast
  with False assms(1) show ?thesis
    by (auto simp: table_def join_False_code)
qed
lemma in_joinI:
  "distinct cs \<Longrightarrow> distinct ds \<Longrightarrow> table cs X \<Longrightarrow> table ds Y \<Longrightarrow> (\<not> b \<Longrightarrow> set ds \<subseteq> set cs) \<Longrightarrow>
    wf_tuple (cols_union cs ds) v \<Longrightarrow> restrict cs (cols_union cs ds) v \<in> X \<Longrightarrow>
    (b \<Longrightarrow> restrict ds (cols_union cs ds) v \<in> Y) \<Longrightarrow> (\<not> b \<Longrightarrow> restrict ds (cols_union cs ds) v \<notin> Y) \<Longrightarrow>
    v \<in> join cs X b ds Y"
  by (subst join_restrict) auto

lemma in_joinE:
  "v \<in> join cs X b ds Y \<Longrightarrow> distinct cs \<Longrightarrow> distinct ds \<Longrightarrow> table cs X \<Longrightarrow> table ds Y \<Longrightarrow>
    (\<not> b \<Longrightarrow> set ds \<subseteq> set cs) \<Longrightarrow>
    (wf_tuple (cols_union cs ds) v \<Longrightarrow> restrict cs (cols_union cs ds) v \<in> X \<Longrightarrow>
      (if b then restrict ds (cols_union cs ds) v \<in> Y else restrict ds (cols_union cs ds) v \<notin> Y) \<Longrightarrow> P) \<Longrightarrow> P"
  by (subst (asm) join_restrict) auto

lemma join_unit_table:
  "distinct cs \<Longrightarrow> table cs R \<Longrightarrow> join cs R True [] unit_table = R"
  "distinct cs \<Longrightarrow> table cs R \<Longrightarrow> join [] unit_table True cs R = R"
  by (auto simp: join_True_code unit_table_def join1.simps table_def restrict_idle)

lemma join_empty[simp]:
  "join cs R True ds {} = {}"
  "join cs {} True ds R = {}"
  by (auto simp: join_True_code)

lemma join_union_distrib:
  "join cs R1 True ds (R2 \<union> R3) = join cs R1 True ds R2 \<union> join cs R1 True ds R3"
  "join cs (R1 \<union> R2) True ds R3 = join cs R1 True ds R3 \<union> join cs R2 True ds R3"
  by (auto simp: join_True_code)

lemma join_Un_distrib:
  "join cs R True ds (\<Union>i\<in>\<I>. \<R> i) = (\<Union>i\<in>\<I>. join cs R True ds (\<R> i))"
  "join cs (\<Union>i\<in>\<I>. \<R> i) True ds R = (\<Union>i\<in>\<I>. join cs (\<R> i) True ds R)"
  by (auto simp: join_True_code)

lemma join_sub_tables_eq:
  assumes "distinct cs" "distinct ds" "table cs R1" "table ds R2" "set ds \<subseteq> set cs"
  shows "join cs R1 True ds R2 = {v \<in> R1. restrict ds cs v \<in> R2}"
proof -
  have R1: "wf_tuple cs v \<and> restrict cs cs v \<in> R1 \<longleftrightarrow> v \<in> R1" for v
    using tableD[OF assms(3), of v] restrict_idle[OF assms(1), of v] by auto
  show ?thesis
    using join_restrict[OF assms(1-4), where b=True] R1
    by (auto simp: cols_union_subset[OF assms(5)])
qed

lemma join_eq_interI:
  assumes "distinct cs" "table cs R1" "table cs R2"
  shows "join cs R1 True cs R2 = R1 \<inter> R2"
proof -
  have "restrict cs cs v = v" if "v \<in> R1" for v
    using restrict_idle[OF assms(1) tableD[OF assms(2) that]] .
  then show ?thesis
    by (subst join_sub_tables_eq[OF assms(1,1,2,3) subset_refl]) auto
qed

subsection \<open>Correctness predicate\<close>

text \<open>@{term "qtable cs P Q X"}: @{term X} is a table over @{term cs} and, among the tuples that
  satisfy @{term P}, holds exactly those that satisfy @{term Q}.\<close>

definition qtable :: "nat list \<Rightarrow> ('a tuple \<Rightarrow> bool) \<Rightarrow> ('a tuple \<Rightarrow> bool) \<Rightarrow> 'a table \<Rightarrow> bool" where
  "qtable cs P Q X \<longleftrightarrow> table cs X \<and> (\<forall>x. (x \<in> X \<and> P x \<longrightarrow> Q x) \<and> (wf_tuple cs x \<and> P x \<and> Q x \<longrightarrow> x \<in> X))"

lemma qtable_wf_tupleD: "qtable cs P Q X \<Longrightarrow> \<forall>x\<in>X. wf_tuple cs x"
  unfolding qtable_def using tableD by blast

lemma qtable_iff: "qtable cs P Q R \<longleftrightarrow> (table cs R \<and> (\<forall>v. P v \<longrightarrow> v \<in> R \<longleftrightarrow> (Q v \<and> wf_tuple cs v)))"
  by (auto simp: qtable_def table_def)

lemma qtable_cong: "qtable cs P Q X \<Longrightarrow> cs = ds \<Longrightarrow> (\<And>v. P v \<Longrightarrow> Q v \<longleftrightarrow> Q' v) \<Longrightarrow> qtable ds P Q' X"
  by (auto simp: qtable_def)

lemma qtable_cong_strong: "cs = ds \<Longrightarrow> (\<And>v. wf_tuple cs v \<Longrightarrow> P v \<Longrightarrow> Q v \<longleftrightarrow> Q' v) \<Longrightarrow>
  qtable cs P Q = qtable ds P Q'"
  unfolding qtable_iff fun_eq_iff by blast

lemma qtable_wf_tuple_cong: "qtable cs P Q X \<Longrightarrow> cs = ds \<Longrightarrow>
  (\<And>v. wf_tuple cs v \<Longrightarrow> P v \<Longrightarrow> Q v = Q' v) \<Longrightarrow> qtable ds P Q' X"
  using qtable_cong_strong[of cs ds P Q] by simp

lemma qtable_unique_pred:
  "qtable cs P Q1 R \<Longrightarrow> qtable cs P Q2 R \<Longrightarrow> (\<forall>v. P v \<longrightarrow> wf_tuple cs v \<longrightarrow> Q1 v = Q2 v)"
  by (auto simp: qtable_iff)

lemma qtable_singleton_table: "qtable [i] P (\<lambda>v. v = [x]) (singleton_table x)"
  unfolding qtable_def singleton_table_def table_def by auto

abbreviation wf_table where
  "wf_table cs Q X \<equiv> qtable cs (\<lambda>_. True) Q X"

lemma wf_table_iff: "wf_table cs Q X \<longleftrightarrow> (\<forall>x. x \<in> X \<longleftrightarrow> (Q x \<and> wf_tuple cs x))"
  unfolding qtable_def table_def by auto

lemma table_wf_table: "table cs X = wf_table cs (\<lambda>v. v \<in> X) X"
  unfolding table_def wf_table_iff by auto

lemma qtableI: "table cs X \<Longrightarrow>
  (\<And>x. x \<in> X \<Longrightarrow> wf_tuple cs x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow>
  (\<And>x. wf_tuple cs x \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> x \<in> X) \<Longrightarrow>
  qtable cs P Q X"
  unfolding qtable_def table_def by auto

lemma in_qtableI: "qtable cs P Q X \<Longrightarrow> wf_tuple cs x \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> x \<in> X"
  unfolding qtable_def by blast

lemma in_qtableE: "qtable cs P Q X \<Longrightarrow> x \<in> X \<Longrightarrow> P x \<Longrightarrow> (wf_tuple cs x \<Longrightarrow> Q x \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding qtable_def table_def by blast

lemma qtableD:
  assumes "qtable cs P Q R"
  shows "table cs R"
    and "P v \<Longrightarrow> v \<in> R \<Longrightarrow> Q v"
    and "P v \<Longrightarrow> v \<in> R \<Longrightarrow> wf_tuple cs v"
    and "P v \<Longrightarrow> Q v \<Longrightarrow> wf_tuple cs v \<Longrightarrow> v \<in> R"
  using assms unfolding qtable_iff by auto


subsubsection \<open>No columns\<close>

lemma qtable_empty_vars_iff:
  "qtable [] P Q R \<longleftrightarrow> (R = empty_table \<or> R = unit_table) \<and> (\<forall>v. P v \<longrightarrow> (v \<in> R) = (Q v \<and> v = []))"
  unfolding qtable_iff table_empty_vars_iff by auto

lemma qtable_empty_varsI:
  "(\<And>v. P v \<Longrightarrow> Q v \<Longrightarrow> v \<noteq> []) \<Longrightarrow> qtable [] P Q empty_table"
  "(\<And>v. P v \<Longrightarrow> (v = []) = Q v) \<Longrightarrow> qtable [] P Q unit_table"
  unfolding qtable_iff table_empty_vars_iff by (auto simp: unit_table_def)

lemmas qtable_empty_varsD =
  iffD1[OF qtable_empty_vars_iff, THEN conjunct1, rule_format]
  iffD1[OF qtable_empty_vars_iff, THEN conjunct2, rule_format]

lemma nullary_qtable_cases: "qtable [] P Q X \<Longrightarrow> (X = empty_table \<or> X = unit_table)"
  by (simp add: qtable_empty_vars_iff)

lemma qtable_empty_unit_table:
  "qtable [] R P empty_table \<Longrightarrow> qtable [] R (\<lambda>v. \<not> P v) unit_table"
  by (auto simp: qtable_iff unit_table_def table_empty_vars_iff)

lemma qtable_unit_empty_table:
  "qtable [] R P unit_table \<Longrightarrow> qtable [] R (\<lambda>v. \<not> P v) empty_table"
  by (auto simp: qtable_iff unit_table_def table_empty_vars_iff)

lemma qtable_nonempty_empty_table:
  "qtable [] R P X \<Longrightarrow> x \<in> X \<Longrightarrow> qtable [] R (\<lambda>v. \<not> P v) empty_table"
  by (frule qtable_empty_varsD(1)) (auto dest: qtable_unit_empty_table)


subsubsection \<open>Empty and unit table\<close>

lemma qtable_empty: "(\<And>x. wf_tuple cs x \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> False) \<Longrightarrow> qtable cs P Q empty_table"
  unfolding qtable_def table_def empty_table_def by auto

lemma qtable_empty_iff: "qtable cs P Q empty_table = (\<forall>x. wf_tuple cs x \<longrightarrow> P x \<longrightarrow> Q x \<longrightarrow> False)"
  unfolding qtable_def table_def empty_table_def by auto

lemma qtable_unit_iff: "qtable cs P Q unit_table \<longleftrightarrow> (cs = [] \<and> (P [] \<longrightarrow> Q []))"
  unfolding qtable_iff table_def unit_table_def by (cases cs) auto

lemma qtable_unitI: "(P [] \<Longrightarrow> Q []) \<Longrightarrow> cs = [] \<Longrightarrow> qtable cs P Q unit_table"
  by (simp add: qtable_unit_iff)

lemma qtable_unit_table: "(\<And>x. wf_tuple [] x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> qtable [] P Q unit_table"
  unfolding qtable_def table_def by (auto simp: in_unit_table)


subsubsection \<open>Union\<close>

lemma qtable_union_iff: "qtable cs P Q1 R1 \<Longrightarrow> qtable cs P Q2 R2 \<Longrightarrow>
  qtable cs P Q (R1 \<union> R2) \<longleftrightarrow> (\<forall>v. P v \<longrightarrow> wf_tuple cs v \<longrightarrow> Q v = (Q1 v \<or> Q2 v))"
  by (auto simp: qtable_iff)

lemma qtable_union: "qtable cs P Q1 X \<Longrightarrow> qtable cs P Q2 Y \<Longrightarrow>
  (\<And>x. wf_tuple cs x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 x \<or> Q2 x) \<Longrightarrow> qtable cs P Q (X \<union> Y)"
  unfolding qtable_def table_def by blast

lemma qtable_union_emptyI:
  "qtable cs P Q R \<Longrightarrow> qtable cs P Q (R \<union> empty_table)"
  "qtable cs P Q R \<Longrightarrow> qtable cs P Q (empty_table \<union> R)"
  by simp_all

lemma qtable_Union: "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> qtable cs P (Qi i) (Xi i)) \<Longrightarrow>
  (\<And>x. wf_tuple cs x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> (\<exists>i \<in> I. Qi i x)) \<Longrightarrow> qtable cs P Q (\<Union>i \<in> I. Xi i)"
proof (induct I arbitrary: Q rule: finite_induct)
  case (insert i F)
  then show ?case
    by (auto intro!: qtable_union[where ?Q1.0 = "Qi i" and ?Q2.0 = "\<lambda>x. \<exists>i\<in>F. Qi i x"])
qed (auto intro!: qtable_empty[unfolded empty_table_def])

lemma qtable_inter: "qtable cs P Q1 R1 \<Longrightarrow> qtable cs P Q2 R2 \<Longrightarrow>
  (\<And>x. wf_tuple cs x \<Longrightarrow> P x \<Longrightarrow> Q x = (Q1 x \<and> Q2 x)) \<Longrightarrow> qtable cs P Q (R1 \<inter> R2)"
  unfolding qtable_def table_def by blast

lemma qtable_filter:
  assumes "qtable cs P Q X" "\<And>x. wf_tuple cs x \<Longrightarrow> P x \<Longrightarrow> Q x \<and> R x \<longleftrightarrow> Q' x"
  shows "qtable cs P Q' (Set.filter R X)"
proof (rule qtableI)
  show "table cs (Set.filter R X)"
    using qtableD(1)[OF assms(1)] by (auto simp: table_def)
next
  fix x
  assume "x \<in> Set.filter R X" "wf_tuple cs x" "P x"
  with assms show "Q' x"
    by (auto elim!: in_qtableE)
next
  fix x
  assume "wf_tuple cs x" "P x" "Q' x"
  with assms show "x \<in> Set.filter R X"
    by (auto intro!: in_qtableI)
qed


subsubsection \<open>Reordering\<close>

text \<open>A table over @{term cs} read in the order of @{term ds}, a permutation of @{term cs}.\<close>

lemma qtable_reorder:
  assumes "qtable cs P Q X" "distinct cs" "distinct ds" "set ds = set cs"
    "\<And>v. wf_tuple ds v \<Longrightarrow> P' v \<Longrightarrow> P (restrict cs ds v)"
    "\<And>v. wf_tuple ds v \<Longrightarrow> P' v \<Longrightarrow> Q' v \<longleftrightarrow> Q (restrict cs ds v)"
  shows "qtable ds P' Q' (restrict ds cs ` X)"
proof (rule qtableI)
  have rt: "restrict cs ds (restrict ds cs x) = x" if "x \<in> X" for x
    using restrict_restrict[of cs ds cs x] assms(4) restrict_idle[OF assms(2) qtableD(1)[OF assms(1), THEN tableD, OF that]]
    by simp
  show "table ds (restrict ds cs ` X)"
    by (auto intro: tableI)
  show "Q' v" if "v \<in> restrict ds cs ` X" "wf_tuple ds v" "P' v" for v
  proof -
    from that(1) obtain x where x: "x \<in> X" "v = restrict ds cs x"
      by blast
    then have v: "restrict cs ds v = x"
      using rt by simp
    have "P x"
      using assms(5)[OF that(2,3)] v by simp
    then have "Q x"
      using x(1) assms(1) by (auto elim: in_qtableE)
    then show ?thesis
      using assms(6)[OF that(2,3)] v by simp  qed
  show "v \<in> restrict ds cs ` X" if "wf_tuple ds v" "P' v" "Q' v" for v
  proof -
    have "restrict cs ds v \<in> X"
      using assms(5,6)[OF that(1,2)] that(3) by (auto intro: in_qtableI[OF assms(1)])
    moreover have "restrict ds cs (restrict cs ds v) = v"
      using restrict_restrict[of ds cs ds v] assms(4) restrict_idle[OF assms(3) that(1)] by simp
    ultimately show ?thesis
      by (intro image_eqI[where x="restrict cs ds v"]) simp_all
  qed
qed


subsubsection \<open>Join\<close>

text \<open>The operands' restriction predicates are their own, at their own columns.\<close>

lemma qtable_join:
  assumes "qtable cs P1 Q1 X" "qtable ds P2 Q2 Y" "distinct cs" "distinct ds"
    "\<not> b \<Longrightarrow> set ds \<subseteq> set cs" "es = cols_union cs ds"
    "\<And>x. wf_tuple es x \<Longrightarrow> P x \<Longrightarrow> P1 (restrict cs es x) \<and> P2 (restrict ds es x)"
    "\<And>x. b \<Longrightarrow> wf_tuple es x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict cs es x) \<and> Q2 (restrict ds es x)"
    "\<And>x. \<not> b \<Longrightarrow> wf_tuple es x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict cs es x) \<and> \<not> Q2 (restrict ds es x)"
  shows "qtable es P Q (join cs X b ds Y)"
proof (rule qtableI)
  have tX: "table cs X" and tY: "table ds Y"
    using assms(1,2) by (simp_all add: qtableD(1))
  have jr: "x \<in> join cs X b ds Y \<longleftrightarrow> wf_tuple es x \<and> restrict cs es x \<in> X \<and>
    (if b then restrict ds es x \<in> Y else restrict ds es x \<notin> Y)" for x
    using join_restrict[OF assms(3,4) tX tY assms(5), where v=x] assms(6) by simp
  show "table es (join cs X b ds Y)"
    using join_table[OF tX tY assms(5) assms(6)[symmetric]] .
  show "Q x" if "x \<in> join cs X b ds Y" "wf_tuple es x" "P x" for x
  proof -
    have P12: "P1 (restrict cs es x)" "P2 (restrict ds es x)"
      using assms(7)[OF that(2,3)] by simp_all
    have mem: "restrict cs es x \<in> X" "if b then restrict ds es x \<in> Y else restrict ds es x \<notin> Y"
      using jr[of x] that(1) by simp_all
    have Q1: "Q1 (restrict cs es x)"
      using mem(1) P12(1) by (auto elim: in_qtableE[OF assms(1)])
    show ?thesis
    proof (cases b)
      case True
      then have "Q2 (restrict ds es x)"
        using mem(2) P12(2) by (auto elim: in_qtableE[OF assms(2)])
      with True Q1 show ?thesis
        using assms(8)[OF True that(2,3)] by simp
    next
      case False
      then have "\<not> Q2 (restrict ds es x)"
        using mem(2) P12(2) in_qtableI[OF assms(2), of "restrict ds es x"] by auto
      with False Q1 show ?thesis
        using assms(9)[OF False that(2,3)] by simp
    qed
  qed
  show "x \<in> join cs X b ds Y" if "wf_tuple es x" "P x" "Q x" for x
  proof -
    have P12: "P1 (restrict cs es x)" "P2 (restrict ds es x)"
      using assms(7)[OF that(1,2)] by simp_all
    show ?thesis
    proof (cases b)
      case True
      then have "Q1 (restrict cs es x)" "Q2 (restrict ds es x)"
        using assms(8)[OF True that(1,2)] that(3) by simp_all
      then have "restrict cs es x \<in> X" "restrict ds es x \<in> Y"
        using P12 by (auto intro: in_qtableI[OF assms(1)] in_qtableI[OF assms(2)])
      with True that(1) show ?thesis
        using jr[of x] by simp
    next
      case False
      then have "Q1 (restrict cs es x)" "\<not> Q2 (restrict ds es x)"
        using assms(9)[OF False that(1,2)] that(3) by simp_all
      then have "restrict cs es x \<in> X" "restrict ds es x \<notin> Y"
        using P12 by (auto intro: in_qtableI[OF assms(1)] elim: in_qtableE[OF assms(2)])
      with False that(1) show ?thesis
        using jr[of x] by simp
    qed
  qed
qed

lemma qtable_join_fixed:
  assumes "qtable cs P1 Q1 X" "qtable ds P2 Q2 Y" "distinct cs" "distinct ds"
    "\<not> b \<Longrightarrow> set ds \<subseteq> set cs" "es = cols_union cs ds"
    "\<And>x. wf_tuple es x \<Longrightarrow> P x \<Longrightarrow> P1 (restrict cs es x) \<and> P2 (restrict ds es x)"
  shows "qtable es P (\<lambda>x. Q1 (restrict cs es x) \<and>
    (if b then Q2 (restrict ds es x) else \<not> Q2 (restrict ds es x))) (join cs X b ds Y)"
  by (rule qtable_join[OF assms]) auto


subsubsection \<open>Assignment\<close>

text \<open>A new column appended to a table, its value computed from the tuple.\<close>

lemma qtable_assign:
  assumes "qtable cs P Q X" "cs' = cs @ [y]"
    "\<And>x'. wf_tuple cs' x' \<Longrightarrow> P' x' \<Longrightarrow> P (butlast x')"
    "\<And>x. wf_tuple cs x \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> Q' (x @ [f x])"
    "\<And>x'. wf_tuple cs' x' \<Longrightarrow> P' x' \<Longrightarrow> Q' x' \<Longrightarrow> Q (butlast x') \<and> last x' = f (butlast x')"
  shows "qtable cs' P' Q' ((\<lambda>x. x @ [f x]) ` X)"
proof (rule qtableI)
  show "table cs' ((\<lambda>x. x @ [f x]) ` X)"
    using qtableD(1)[OF assms(1)] assms(2) by (auto simp: table_def wf_tuple_def)
  show "Q' x'" if "x' \<in> (\<lambda>x. x @ [f x]) ` X" "wf_tuple cs' x'" "P' x'" for x'
  proof -
    from that(1) obtain x where x: "x \<in> X" "x' = x @ [f x]"
      by blast
    have "P x"
      using assms(3)[OF that(2,3)] x(2) by simp
    moreover have "wf_tuple cs x"
      using qtableD(1)[OF assms(1)] x(1) by (rule tableD)
    ultimately show ?thesis
      using x assms(1,4) by (auto elim: in_qtableE)
  qed
  show "x' \<in> (\<lambda>x. x @ [f x]) ` X" if "wf_tuple cs' x'" "P' x'" "Q' x'" for x'
  proof -
    have x': "x' = butlast x' @ [last x']"
      using that(1) assms(2) by (auto simp: wf_tuple_def intro!: append_butlast_last_id[symmetric])
    have "wf_tuple cs (butlast x')"
      using that(1) assms(2) by (simp add: wf_tuple_def)
    then have "butlast x' \<in> X"
      using assms(3,5)[OF that(1,2)] that(3) by (auto intro: in_qtableI[OF assms(1)])
    moreover have "x' = butlast x' @ [f (butlast x')]"
      using x' assms(5)[OF that] by simp
    ultimately show ?thesis
      by (intro image_eqI[where x="butlast x'"]) simp_all
  qed
qed


subsubsection \<open>Restriction to a set of valuations\<close>

text \<open>A tuple over @{term cs} agrees with some valuation in @{term A}.  This is what restricts
  the monitor's tables to the part of the valuation space a slice covers.\<close>

definition mem_restr :: "'a list set \<Rightarrow> nat list \<Rightarrow> 'a tuple \<Rightarrow> bool" where
  "mem_restr A cs x \<longleftrightarrow> (\<exists>y\<in>A. list_all2 (\<lambda>c a. c < length y \<and> y ! c = a) cs x)"

lemma mem_restr_iff:
  assumes "distinct cs"
  shows "mem_restr A cs x \<longleftrightarrow>
    wf_tuple cs x \<and> (\<exists>y\<in>A. \<forall>c\<in>set cs. c < length y \<and> y ! c = tup_get cs x c)"
proof -
  have "list_all2 (\<lambda>c a. c < length y \<and> y ! c = a) cs x \<longleftrightarrow>
    wf_tuple cs x \<and> (\<forall>c\<in>set cs. c < length y \<and> y ! c = tup_get cs x c)" for y
  proof
    assume "list_all2 (\<lambda>c a. c < length y \<and> y ! c = a) cs x"
    then have l: "length cs = length x" and a: "\<And>i. i < length cs \<Longrightarrow> cs ! i < length y \<and> y ! (cs ! i) = x ! i"
      by (simp_all add: list_all2_conv_all_nth)
    then show "wf_tuple cs x \<and> (\<forall>c\<in>set cs. c < length y \<and> y ! c = tup_get cs x c)"
      using tup_get_nth[OF assms, of x] by (auto simp: wf_tuple_def in_set_conv_nth)
  next
    assume a: "wf_tuple cs x \<and> (\<forall>c\<in>set cs. c < length y \<and> y ! c = tup_get cs x c)"
    have "cs ! i < length y \<and> y ! (cs ! i) = x ! i" if "i < length cs" for i
      using a[THEN conjunct2, rule_format, OF nth_mem[OF that]] tup_get_nth[OF assms _ that, of x] a
      by simp
    with a show "list_all2 (\<lambda>c a. c < length y \<and> y ! c = a) cs x"
      by (simp add: list_all2_conv_all_nth wf_tuple_def)
  qed  then show ?thesis
    unfolding mem_restr_def by auto
qed

lemma mem_restrI:
  "distinct cs \<Longrightarrow> y \<in> A \<Longrightarrow> wf_tuple cs x \<Longrightarrow> \<forall>c\<in>set cs. c < length y \<and> y ! c = tup_get cs x c \<Longrightarrow>
    mem_restr A cs x"
  by (auto simp: mem_restr_iff)

lemma mem_restrE:
  "mem_restr A cs x \<Longrightarrow> distinct cs \<Longrightarrow>
    (\<And>y. y \<in> A \<Longrightarrow> wf_tuple cs x \<Longrightarrow> \<forall>c\<in>set cs. c < length y \<and> y ! c = tup_get cs x c \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: mem_restr_iff)

lemma mem_restr_wf_tuple: "mem_restr A cs x \<Longrightarrow> wf_tuple cs x"
  by (auto simp: mem_restr_def wf_tuple_def dest: list_all2_lengthD)

lemma mem_restr_IntD: "mem_restr (A \<inter> B) cs v \<Longrightarrow> mem_restr A cs v \<and> mem_restr B cs v"
  unfolding mem_restr_def by auto

lemma mem_restr_Un_iff: "mem_restr (A \<union> B) cs x \<longleftrightarrow> mem_restr A cs x \<or> mem_restr B cs x"
  unfolding mem_restr_def by blast

lemma mem_restr_UNIV[simp]: "distinct cs \<Longrightarrow> wf_tuple cs x \<Longrightarrow> mem_restr UNIV cs x"
  by (rule mem_restrI[where y = "val (Suc (Max (insert 0 (set cs)))) cs x"])
    (auto simp: le_imp_less_Suc)

lemma restrict_mem_restr:
  "mem_restr A cs x \<Longrightarrow> distinct cs \<Longrightarrow> distinct ds \<Longrightarrow> set ds \<subseteq> set cs \<Longrightarrow>
    mem_restr A ds (restrict ds cs x)"
  by (auto simp: mem_restr_iff tup_get_restrict)

lemma qtable_mem_restr_UNIV:
  assumes "distinct cs"
  shows "qtable cs (mem_restr UNIV cs) Q R = wf_table cs Q R"
proof -
  have "mem_restr UNIV cs v \<longleftrightarrow> wf_tuple cs v" for v :: "'a tuple"
    using mem_restr_UNIV[OF assms, of v] mem_restr_wf_tuple[of UNIV cs v] by blast
  then show ?thesis
    unfolding qtable_iff table_def by blast
qed


subsubsection \<open>Projection\<close>

text \<open>An existential quantifier binds variable @{term 0} and shifts the others down by one.  The
  projection drops the column of variable @{term 0} and keeps the order of the others.\<close>

definition ex_cols :: "nat list \<Rightarrow> nat list" where
  "ex_cols cs = map (\<lambda>x. x - 1) (filter (\<lambda>x. x \<noteq> 0) cs)"

definition ex_proj :: "nat list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
  "ex_proj cs x = restrict (filter (\<lambda>x. x \<noteq> 0) cs) cs x"

lemma set_ex_cols: "set (ex_cols cs) = (\<lambda>x. x - 1) ` (set cs - {0})"
  by (auto simp: ex_cols_def)

lemma inj_on_minus_one: "inj_on (\<lambda>x. x - Suc 0) {x \<in> A. 0 < x}"
  by (auto intro!: inj_onI)

lemma distinct_ex_cols: "distinct cs \<Longrightarrow> distinct (ex_cols cs)"
  unfolding ex_cols_def by (auto simp: distinct_map inj_on_minus_one)
lemma wf_tuple_ex_proj[simp]: "wf_tuple (ex_cols cs) (ex_proj cs x)"
  by (simp add: ex_cols_def ex_proj_def wf_tuple_def)

lemma tup_get_ex_proj:
  assumes "c \<in> set cs" "c \<noteq> 0"
  shows "tup_get (ex_cols cs) (ex_proj cs x) (c - 1) = tup_get cs x c"
proof -
  have "tup_get (ex_cols cs) (ex_proj cs x) (c - 1) =
    tup_get (filter (\<lambda>x. x \<noteq> 0) cs) (ex_proj cs x) c"
    unfolding ex_cols_def using assms
    by (intro tup_get_map) (auto simp: inj_on_minus_one)
  also have "\<dots> = tup_get cs x c"
    unfolding ex_proj_def using assms by (simp add: tup_get_restrict)
  finally show ?thesis .
qed

definition lift_envs :: "'a list set \<Rightarrow> 'a list set" where
  "lift_envs R = (\<lambda>(a,b). a # b) ` (UNIV \<times> R)"

lemma lift_envs_mem_restr:
  assumes "distinct cs" "wf_tuple cs x" "mem_restr A (ex_cols cs) (ex_proj cs x)"
  shows "mem_restr (lift_envs A) cs x"
proof -
  obtain y where y: "y \<in> A" "\<forall>c\<in>set (ex_cols cs). c < length y \<and> y ! c = tup_get (ex_cols cs) (ex_proj cs x) c"
    using assms(3) distinct_ex_cols[OF assms(1)] by (auto elim: mem_restrE)
  have "\<forall>c\<in>set cs. c < length (tup_get cs x 0 # y) \<and> (tup_get cs x 0 # y) ! c = tup_get cs x c"
  proof
    fix c
    assume c: "c \<in> set cs"
    show "c < length (tup_get cs x 0 # y) \<and> (tup_get cs x 0 # y) ! c = tup_get cs x c"
    proof (cases c)
      case (Suc c')
      then have "c' \<in> set (ex_cols cs)"
        using c by (auto simp: set_ex_cols intro!: rev_image_eqI[of "Suc c'"])
      with y(2) tup_get_ex_proj[OF c, of x] Suc show ?thesis
        by auto
    qed simp
  qed
  with y(1) show ?thesis
    by (intro mem_restrI[OF assms(1) _ assms(2)]) (auto simp: lift_envs_def)
qed

lemma mem_restr_ex_proj:
  assumes "distinct cs" "mem_restr (lift_envs A) cs x"
  shows "mem_restr A (ex_cols cs) (ex_proj cs x)"
proof -
  obtain y where y: "y \<in> lift_envs A" "wf_tuple cs x" "\<forall>c\<in>set cs. c < length y \<and> y ! c = tup_get cs x c"
    using assms(2) by (auto elim: mem_restrE[OF _ assms(1)])
  then obtain a y' where y': "y = a # y'" "y' \<in> A"
    by (auto simp: lift_envs_def)
  have "\<forall>c\<in>set (ex_cols cs). c < length y' \<and> y' ! c = tup_get (ex_cols cs) (ex_proj cs x) c"
  proof
    fix c
    assume "c \<in> set (ex_cols cs)"
    then obtain d where d: "d \<in> set cs" "d \<noteq> 0" "c = d - 1"
      by (auto simp: set_ex_cols)
    then have c: "Suc c \<in> set cs"
      by (cases d) simp_all
    then show "c < length y' \<and> y' ! c = tup_get (ex_cols cs) (ex_proj cs x) c"
      using y(3)[rule_format, OF c] y'(1) tup_get_ex_proj[OF c, of x] by simp
  qed
  then show ?thesis
    by (rule mem_restrI[OF distinct_ex_cols[OF assms(1)] y'(2) wf_tuple_ex_proj])
qed

lemma qtable_project:
  assumes "distinct cs" "qtable cs (mem_restr (lift_envs R) cs) P X"
  shows "qtable (ex_cols cs) (mem_restr R (ex_cols cs))
    (\<lambda>v. \<exists>x. wf_tuple cs x \<and> ex_proj cs x = v \<and> P x) (ex_proj cs ` X)"
proof (rule qtableI)
  show "table (ex_cols cs) (ex_proj cs ` X)"
    by (auto intro: tableI)
next
  fix v
  assume "v \<in> ex_proj cs ` X" "mem_restr R (ex_cols cs) v"
  then obtain x where x: "x \<in> X" "ex_proj cs x = v"
    by blast
  have wf: "wf_tuple cs x"
    using qtableD(1)[OF assms(2)] x(1) by (rule tableD)
  have "P x"
    using x \<open>mem_restr R (ex_cols cs) v\<close>
    by (auto elim: in_qtableE[OF assms(2)] intro: lift_envs_mem_restr[OF assms(1) wf])
  with wf x(2) show "\<exists>x. wf_tuple cs x \<and> ex_proj cs x = v \<and> P x"
    by blast
next
  fix v
  assume "mem_restr R (ex_cols cs) v" "\<exists>x. wf_tuple cs x \<and> ex_proj cs x = v \<and> P x"
  then obtain x where x: "wf_tuple cs x" "ex_proj cs x = v" "P x"
    by blast
  then have "x \<in> X"
    using \<open>mem_restr R (ex_cols cs) v\<close>
    by (auto intro: in_qtableI[OF assms(2)] lift_envs_mem_restr[OF assms(1)])
  with x(2) show "v \<in> ex_proj cs ` X"
    by blast
qed

(*<*)
end
(*>*)

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
(*<*)
end
(*>*)

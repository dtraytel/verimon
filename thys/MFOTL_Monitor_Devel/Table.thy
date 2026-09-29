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

(*<*)
end
(*>*)

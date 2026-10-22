theory Tree_List
  imports Order_Statistic_Tree
  "Containers.Set_Impl"
begin

section \<open>Lists as order statistic trees\<close>

subsection \<open>Operations on tree lists\<close>

typedef 'a treelist = "UNIV :: 'a list set" ..
setup_lifting type_definition_treelist

lift_definition empty_treelist :: "'a treelist" is "[]" .
lift_definition insert_treelist :: "'a::linorder \<Rightarrow> 'a treelist \<Rightarrow> 'a treelist" is insort1 .
lift_definition get_treelist :: "'a::linorder treelist \<Rightarrow> nat \<Rightarrow> 'a" is "\<lambda>l n. (sort l) ! n" . 
lift_definition length_treelist :: "'a::linorder treelist \<Rightarrow> nat" is length .
lift_definition remove_treelist :: "'a::linorder \<Rightarrow> 'a treelist => 'a treelist" is del_list .
lift_definition mset_treelist :: "'a::linorder treelist \<Rightarrow> 'a multiset" is mset .
lift_definition unpack :: "'a::linorder treelist \<Rightarrow> 'a list" is id .
lift_definition set_treelist :: "'a::linorder treelist \<Rightarrow> 'a set" is set .
lift_definition sort_treelist :: "'a::linorder treelist \<Rightarrow> 'a treelist" is sort .
lift_definition sorted_treelist :: "'a::linorder treelist \<Rightarrow> bool" is sorted .

lemma mset_treelist_insert:
  "mset_treelist (insert_treelist i t) = {#i#} + mset_treelist t"
  by (simp add: Sorting.mset_insort1 insert_treelist.rep_eq mset_treelist.rep_eq)

lemma mset_treelist_empty:
  "mset_treelist empty_treelist = {#}"
  by (simp add: empty_treelist_def mset_treelist.abs_eq)

lemma treelist_length_eq:
  "length_treelist x = length (unpack (sort_treelist x))" by transfer auto

lemma insert_treelist_comm: "(insert_treelist a (insert_treelist b x)) = (insert_treelist b (insert_treelist a x))" 
  by(transfer) (simp add: insort_eq2 insort_left_comm)

lemma del_list_comm: "del_list x (del_list y xs) = del_list y (del_list x xs)"
  by(induction xs; auto)

lemma remove_comm: "remove_treelist x (remove_treelist y xs) = remove_treelist y (remove_treelist x xs)"
  by(transfer) (simp add:del_list_comm)

lemma remove_treelist_empty: "remove_treelist x empty_treelist = empty_treelist"
  by transfer simp

lemma sort_remove_eq:
  shows "sort_treelist (remove_treelist t l) = remove_treelist t (sort_treelist l)"
proof transfer
  fix t l
  show "sort (del_list (t :: 'a) l) = del_list t (sort l)"
    by(induction l; auto simp add: insort_del_inverse) (metis insort_del_comm sorted_sort)
qed

lemma insort_remove_comm:
  assumes "t \<in> set_treelist l"
  and "sorted_treelist l"
  shows "(insert_treelist t ^^ i) (remove_treelist t l) = remove_treelist t ((insert_treelist t ^^ i) l)"
  using assms
proof transfer
  fix t l i
  assume "(t :: 'a) \<in> set l" and "sorted l"
  then show "(insort1 t ^^ i) (del_list t l) = del_list t ((insort1 t ^^ i) l)"
  proof(induction l)
    case Nil
    then show ?case by auto
  next
    case (Cons a l)
    then show ?case by (metis funpow_swap1 insort_del_inverse insort_eq2 insort_remove1)
  qed
qed

lemma bulk_remove_in_set:
  assumes "(count \<circ> mset_treelist) l t \<ge> Suc i"
  shows "t \<in> set_treelist ((remove_treelist t ^^ i) l)"
  using assms unfolding comp_def
proof transfer
  fix i l t
  assume "Suc i \<le> count (mset l) (t :: 'a)"
  then show "t \<in> set ((del_list t ^^ i) l)"
  proof(induction i arbitrary: l)
  case 0
    then show ?case by auto
  next
    case (Suc i)
    have "i + 1 \<le> count (mset (del_list t l)) t" using Suc(2) mset_del_list[of t l] by auto
    then show ?case using Suc(1)[of "del_list t l"] by(simp add:funpow_swap1)
  qed
qed

lemma bulk_insert_in_set:
  assumes "t \<in> set_treelist l"
  shows "t \<in> set_treelist ((insert_treelist t ^^ i) l)"
  using assms by(induction i; transfer) (simp add: insort_eq set_insort_key)+

lemma sorted_bulk_insort:
  assumes "sorted_treelist l"
  shows "sorted_treelist ((insert_treelist t ^^ i) l)"
  using assms by(induction i; transfer) (simp add: Sorting.sorted_insort1)+

lemma sort_insert_remove:
  assumes "(count \<circ> mset_treelist) l t \<ge> i"
  shows "sort_treelist l = (insert_treelist t ^^ i) (sort_treelist ((remove_treelist t ^^ i) l))" 
  using assms
proof(induction i)
  case 0
  then show ?case by auto
next
  case (Suc i)
  let ?removed = "sort_treelist (((remove_treelist t ^^ i) l))"
  have "(remove1 t ^^ i) [] = []" by (induction i) auto
  then have simp1: "sort_treelist (((remove_treelist t ^^ Suc i) l)) = remove_treelist t (sort_treelist ((remove_treelist t ^^ i) l))" 
    using sort_remove_eq by(induction l) auto
  have in_set: "t \<in> set_treelist ?removed" using bulk_remove_in_set[OF Suc(2)]
    by transfer auto
  have sorted: "sorted_treelist ?removed" by(transfer) simp
  have *: "i \<le> (count \<circ> mset_treelist) l t" using Suc(2) by auto
  have "t \<in> set_treelist ((insert_treelist t ^^ i) ?removed)" using bulk_insert_in_set[of t] in_set by auto
  moreover have "sorted_treelist ((insert_treelist t ^^ i) ?removed)" using sorted_bulk_insort sorted by auto
  show ?case using Suc(1)[OF *] unfolding simp1 insort_remove_comm[OF in_set, OF sorted]
  proof transfer
    fix l t i
    assume "sort (l :: 'a list) = (Sorting.insort1 t ^^ i) (sort ((del_list t ^^ i) l))"
    then show "sort l = del_list t ((Sorting.insort1 t ^^ Suc i) (sort ((del_list t ^^ i) l)))"
      using insort_del_inverse[of t, unfolded insort_eq2[symmetric]] by auto
  qed
qed

lemma treelist_size_eq:
  "length_treelist x1 = size (mset_treelist x1)" by(transfer) simp

lemma treelist_empty: "length_treelist l = 0 \<Longrightarrow> set_treelist l = {}" by transfer auto

lemma treelist_del1: "length_treelist l = 1 \<Longrightarrow> x \<in> set_treelist l \<Longrightarrow> remove_treelist x l = empty_treelist"
  by(transfer) (metis Zero_not_Suc cancel_comm_monoid_add_class.diff_cancel insort_del_inverse insort_remove1 length_greater_0_conv length_remove1 less_nat_zero_code less_one sorted_iff_nth_Suc)

lemma treelist_del2: "length_treelist l > 1 \<Longrightarrow> remove_treelist x l \<noteq> empty_treelist" 
proof transfer
  fix l x
  assume "length (l::'a list) > 1"
  then show "del_list x l \<noteq> []" by (cases l) auto
qed

lemma mset_remove_treelist: 
  shows "mset_treelist (remove_treelist i l) = mset_treelist l - {#i#}"
  unfolding remove_treelist.rep_eq mset_treelist.rep_eq set_treelist.rep_eq mset_del_list by auto

lemma mset_remove_treelist_funpow:
  "mset_treelist ((remove_treelist t ^^ n) l) = mset_treelist l - replicate_mset n t"
  by (induction n) (simp_all add: mset_remove_treelist)

subsection \<open>Implementation by trees\<close>

lift_definition Collapse :: "'a::linorder wf_wbt \<Rightarrow> 'a treelist" is "inorder" .

code_datatype Collapse

derive (eq) ceq treelist

lemma empty_treelist_code[code]: "empty_treelist = Collapse empty_tree"
  by transfer simp

lemma insert_treelist_code[code]: "insert_treelist x (Collapse y) = Collapse (tree_insert x y)"
  by transfer (simp add: inorder_insert)

lemma get_treelist_code[code]: "get_treelist (Collapse y) n = tree_select y n"
  by transfer (simp add: sorted_sort_id valid_select_wbt)

lemma length_treelist_code[code]: "length_treelist (Collapse y) = tree_size y"
  by transfer simp

lemma remove_treelist_code[code]: "remove_treelist x (Collapse y) = Collapse (tree_remove x y)"
  by(transfer) (simp add: inorder_delete)

instantiation treelist :: (equal) equal begin
lift_definition equal_treelist :: "'a treelist \<Rightarrow> 'a treelist \<Rightarrow> bool" is "(=)" .
instance by (standard; transfer; auto)
end

lemma eq_treelist_code[code]: "equal_class.equal (Collapse y1) (Collapse y2) = (if y2 = empty_tree then (y1 = empty_tree) else (tree_inorder y1 = tree_inorder y2))"
proof -
  have eq: "equal_class.equal (Collapse y1) (Collapse y2) \<longleftrightarrow> tree_inorder y1 = tree_inorder y2"
    by transfer simp
  have "tree_inorder y1 = tree_inorder empty_tree \<longleftrightarrow> y1 = empty_tree"
    by transfer (auto elim: Tree2.inorder.elims)
  then show ?thesis
    by (simp add: eq)
qed

end

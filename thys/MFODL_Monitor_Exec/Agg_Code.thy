(*<*)
theory Agg_Code
  imports Mono_Sweep
begin
(*>*)

section \<open>The rank trees of the aggregations, in code\<close>

text \<open>
  The aggregation over a window keeps one order-statistic tree per group for MIN, MAX and MED
  (@{typ list_aux}, over @{typ "'a treelist"}, over @{typ "'a wf_wbt"}).  Its operations are
  refined here at the level of code equations, with the refinements proved against the
  equations they replace.  They are placed after
  @{theory MFODL_Monitor_Exec.Mono_Sweep} so that the theory lies on the import chain
  of the export rather than beside it: a side branch would bring back, at the merge, the code
  preprocessor rules that the theories in between delete.
\<close>

subsection \<open>Deletion that reads the stored sizes\<close>

text \<open>@{const Order_Statistic_Tree.combine} decides which side to take the new root from by
  comparing @{const size}, which walks both subtrees, although every node carries its size;
  and @{const split_min} and @{const del_max} test @{term "l = Leaf"}, an equality on trees,
  which is the only reason the tree operations need an @{class equal} dictionary besides the
  @{class linorder} one.  The copies below read the stored size and match on @{const Leaf}
  instead.  On a tree satisfying @{const wbt}, which every tree inside @{typ "'a wf_wbt"}
  does, they compute the same result.\<close>

text \<open>The subtrees are inspected with a @{text case} rather than by nested patterns: a nested
  pattern such as @{term "Node (Node l' x r') y r"} makes the generated code rebuild the inner
  node before it can pass it on, an allocation per level.\<close>

fun split_min_p :: "'a wbt \<Rightarrow> 'a \<times> 'a wbt" where
  "split_min_p (Node l (a, _) r) = (case l of
     Leaf \<Rightarrow> (a, r)
   | Node _ _ _ \<Rightarrow> let (x, l') = split_min_p l in (x, balanceL l' a r))"

fun del_max_p :: "'a wbt \<Rightarrow> 'a \<times> 'a wbt" where
  "del_max_p (Node l (a, _) r) = (case r of
     Leaf \<Rightarrow> (a, l)
   | Node _ _ _ \<Rightarrow> let (x, r') = del_max_p r in (x, balanceR l a r'))"

lemma split_min_p_eq: "t \<noteq> Leaf \<Longrightarrow> split_min_p t = split_min t"
  by (induction t rule: split_min_p.induct) (auto split: tree.split)

lemma del_max_p_eq: "t \<noteq> Leaf \<Longrightarrow> del_max_p t = del_max t"
  by (induction t rule: del_max_p.induct) (auto split: tree.split)

definition combine_p :: "'a wbt \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
  "combine_p l r = (case l of
     Leaf \<Rightarrow> r
   | Node _ _ _ \<Rightarrow> (case r of
       Leaf \<Rightarrow> l
     | Node _ _ _ \<Rightarrow>
         if size_wbt l > size_wbt r then
           let (lMax, l') = del_max_p l in balanceL l' lMax r
         else
           let (rMin, r') = split_min_p r in balanceR l rMin r'))"

lemma combine_p_eq: "wbt l \<Longrightarrow> wbt r \<Longrightarrow> combine_p l r = Order_Statistic_Tree.combine l r"
  by (cases l; cases r) (simp_all add: combine_p_def split_min_p_eq del_max_p_eq)

fun delete_p :: "'a::linorder \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
  "delete_p _ Leaf = Leaf"
| "delete_p x (Node l (a, _) r) =
    (case cmp x a of
       LT \<Rightarrow> balanceL (delete_p x l) a r
     | GT \<Rightarrow> balanceR l a (delete_p x r)
     | EQ \<Rightarrow> combine_p l r)"

lemma delete_p_eq: "wbt t \<Longrightarrow> delete_p x t = delete x t"
  by (induction x t rule: delete_p.induct) (simp_all add: combine_p_eq)

lemma tree_remove_code[code]: "Rep_wf_wbt (tree_remove x t) = delete_p x (Rep_wf_wbt t)"
  using Rep_wf_wbt[of t] by (simp add: tree_remove.rep_eq delete_p_eq)

subsection \<open>The extremes, read off the ends of the tree\<close>

text \<open>MIN and MAX ask for the element of rank 0 and of rank \<open>n - 1\<close>.  @{const select} finds
  them by comparing the rank with the stored size at every node on the way down; the leftmost
  and the rightmost node are reached without any arithmetic.\<close>

fun wbt_min :: "'a wbt \<Rightarrow> 'a" where
  "wbt_min Leaf = [] ! 0"
| "wbt_min (Node l (a, _) _) = (case l of Leaf \<Rightarrow> a | Node _ _ _ \<Rightarrow> wbt_min l)"

fun wbt_max :: "'a wbt \<Rightarrow> 'a" where
  "wbt_max Leaf = [] ! 0"
| "wbt_max (Node _ (a, _) r) = (case r of Leaf \<Rightarrow> a | Node _ _ _ \<Rightarrow> wbt_max r)"

lemma select_0: "wbt t \<Longrightarrow> select t 0 = wbt_min t"
proof (induction t)
  case (Node l x r)
  then show ?case by (cases x; cases l) auto
qed simp

lemma select_last: "wbt t \<Longrightarrow> select t (size_wbt t - 1) = wbt_max t"
proof (induction t)
  case (Node l x r)
  then show ?case by (cases x; cases r) auto
qed simp

lift_definition tree_min :: "'a::linorder wf_wbt \<Rightarrow> 'a" is wbt_min .
lift_definition tree_max :: "'a::linorder wf_wbt \<Rightarrow> 'a" is wbt_max .

lemma tree_select_0: "tree_select t 0 = tree_min t"
  by transfer (simp add: select_0)

lemma tree_select_last: "tree_select t (tree_size t - 1) = tree_max t"
  by transfer (metis select_last)

definition get_edata_min :: "list_aux \<Rightarrow> event_data" where
  "get_edata_min k = get_edata_list k 0"

definition get_edata_max :: "list_aux \<Rightarrow> event_data" where
  "get_edata_max k = get_edata_list k (get_length k - 1)"

lemma get_edata_min_code[code]:
  "get_edata_min (LInt (Collapse t)) = EInt (tree_min t)"
  "get_edata_min (LString (Collapse s)) = EString (tree_min s)"
  by (simp_all add: get_edata_min_def get_treelist_code tree_select_0)

lemma get_edata_max_code[code]:
  "get_edata_max (LInt (Collapse t)) = EInt (tree_max t)"
  "get_edata_max (LString (Collapse s)) = EString (tree_max s)"
  by (simp_all add: get_edata_max_def get_length_def get_treelist_code length_treelist_code
      tree_select_last[unfolded One_nat_def])

lemma get_edata_min_max_unfold[code_unfold]:
  "get_edata_list k 0 = get_edata_min k"
  "get_edata_list k (get_length k - 1) = get_edata_max k"
  by (simp_all add: get_edata_min_def get_edata_max_def)

subsection \<open>The tree operations at their two closed types\<close>

text \<open>@{theory MFODL_Monitor_Exec.Mono_Sweep} specialises the treelist operations at
  @{typ integer} and @{typ string8}, but their bodies still called the generic tree operations
  with a dictionary, and the generic @{const cmp} goes through the dictionary's @{text less} and
  @{text equal} at every node.  These are the tree operations' copies at the two types, and the
  @{typ nat} comparison of @{const select}.\<close>

setup \<open>mono
  [("cmp", "nat_cmp", ["nat"]),
   ("cmp", "int_cmp", ["integer"]),
   ("Order_Statistic_Tree.insert", "int_wbt_insert", ["integer"]),
   ("delete_p", "int_wbt_delete", ["integer"]),
   ("tree_insert", "int_tree_insert", ["integer"]),
   ("tree_remove", "int_tree_remove", ["integer"]),
   ("cmp", "s8_cmp", ["string8"]),
   ("Order_Statistic_Tree.insert", "s8_wbt_insert", ["string8"]),
   ("delete_p", "s8_wbt_delete", ["string8"]),
   ("tree_insert", "s8_tree_insert", ["string8"]),
   ("tree_remove", "s8_tree_remove", ["string8"])]
  dicts\<close>

subsection \<open>The result table, left as it is\<close>

text \<open>The result table of the aggregation is left as @{thm [source] ugmr_code} builds it, by
  inserting its rows one at a time.  Collecting the rows in a list, sorting them with the
  comparator merge sort @{const sort_c} and building the tree with @{const rbt_of_sorted_list}
  was proved and measured, and it does not pay: on @{text "CNT"} over a window of 50 it saves
  about as many instructions in the insertions as the sort, the sortedness check of
  @{const rbt_of_sorted_list} and the natural-number arithmetic of @{const rbtreeify} spend
  (0.7% of the run).\<close>

subsection \<open>The aggregation outside a window, through the window's structure\<close>

text \<open>An aggregation that is not over a window (@{const uagg}) clusters its operand's table by
  the group, clusters each group again by the aggregated value to count the multiplicities, and
  reads the aggregate off the multiset.  The window's structure (@{typ "'b gagg"}) keeps, per
  group, the count, the count and the sum, or the order-statistic tree of the values; built
  from scratch by inserting the table's tuples one at a time, it has the aggregate at hand.  The
  invariant of the window's aggregation says that the result read off it is
  @{const uagg}'s (@{thm [source] ag_res_inv}), when the tuples have one width that the
  aggregation's parameters fit (@{const eagg_ok}).  The code below checks that and falls back
  to @{const uagg}'s own equation, @{text uagg_gen}, otherwise, or when the structure cannot
  represent the aggregation.\<close>

definition uagg_gen :: "bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> Formula.trm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    event_data list set \<Rightarrow> event_data list set" where
  "uagg_gen = uagg"

lemma uagg_gen_code[code]:
  "uagg_gen g0 \<omega> f k pos rel =
     (if g0 \<and> Set.is_empty rel then {[eval_agg_op \<omega> {}]}
      else (let groups = cluster (Some \<circ> drop k) rel in
        (\<lambda>g. case Mapping.lookup groups g of
                None \<Rightarrow> g
              | Some G \<Rightarrow> take pos g @ eval_agg_op \<omega> (uagg_values f G) # drop pos g)
          ` Mapping.keys groups))"
  by (simp add: uagg_gen_def uagg_def)

lemma uagg_gins:
  assumes ok: "eagg_ok (g0, \<omega>, f, k, pos) w" and fX: "finite X" and w: "\<forall>t\<in>X. length t = w"
    and a: "gins k (umeval_trm f) (csl X) (ginit \<omega>) = Some a"
  shows "gres g0 \<omega> pos (\<lambda>x. x) a = uagg g0 \<omega> f k pos X"
proof -
  let ?p = "(g0, \<omega>, f, k, pos)"
  let ?cc = "(Mapping.empty, {}) :: cntset"
  have cr: "cnt_rep (\<lambda>_. 0) ?cc"
    by (simp add: cnt_rep_def)
  have inv: "ag_inv ?p w (cnt_add X ?cc) (ag_ins ?p w X ?cc (ag_init ?p w))"
    by (rule ag_inv_ins[OF cr fX ok w _ ag_inv_init]) simp
  have snd: "snd (cnt_add X ?cc) = X"
    using cnt_rep_snd_add[OF cr fX] by simp
  have ins: "ag_ins ?p w X ?cc (ag_init ?p w) = Some a"
    using a by (simp add: ag_ins_def ag_init_def)
  have "ag_res ?p w (cnt_add X ?cc) (Some a) = eagg_p ?p X"
    using ag_res_inv[OF inv ok] snd w ins by simp
  then show ?thesis
    by (simp add: ag_res_def id_def)
qed

definition uagg_g :: "bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> Formula.trm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    event_data list set \<Rightarrow> event_data list set" where
  "uagg_g = uagg"

lemma uagg_g_eq:
  "uagg_g g0 \<omega> f k pos X = (let xs = csl X in case xs of
       [] \<Rightarrow> uagg_gen g0 \<omega> f k pos X
     | t # _ \<Rightarrow> (let w = length t in
         if eagg_ok (g0, \<omega>, f, k, pos) w \<and> list_all (\<lambda>u. length u = w) xs
         then (case gins k (umeval_trm f) xs (ginit \<omega>) of
                 Some a \<Rightarrow> gres g0 \<omega> pos (\<lambda>x. x) a
               | None \<Rightarrow> uagg_gen g0 \<omega> f k pos X)
         else uagg_gen g0 \<omega> f k pos X))"
proof (cases "csl X")
  case (Cons t ts)
  then have fX: "finite X"
    using csl_infinite by fastforce
  then have s: "set (csl X) = X"
    by (rule set_csl_ed)
  show ?thesis
  proof (cases "eagg_ok (g0, \<omega>, f, k, pos) (length t) \<and> list_all (\<lambda>u. length u = length t) (csl X)")
    case True
    then have w: "\<forall>u\<in>X. length u = length t"
      using s by (simp add: list_all_iff)
    show ?thesis
    proof (cases "gins k (umeval_trm f) (csl X) (ginit \<omega>)")
      case (Some a)
      then show ?thesis
        using True uagg_gins[OF _ fX w Some] by (simp add: Let_def Cons uagg_g_def)
    qed (use True Cons in \<open>simp add: Let_def uagg_gen_def uagg_g_def\<close>)
  next
    case False
    then show ?thesis
      by (simp only: Cons Let_def list.case if_False uagg_gen_def uagg_g_def)
  qed
qed (simp add: uagg_gen_def uagg_g_def)

text \<open>An aggregation the structure cannot represent at all (@{const ginit}) goes straight to
  @{const uagg}'s own equation, without the checks.\<close>

lemma uagg_g_code[code]:
  "uagg_g g0 \<omega> f k pos X = (if Option.is_none (ginit \<omega> :: event_data gagg option) then uagg_gen g0 \<omega> f k pos X
     else (let xs = csl X in case xs of
       [] \<Rightarrow> uagg_gen g0 \<omega> f k pos X
     | t # _ \<Rightarrow> (let w = length t in
         if eagg_ok (g0, \<omega>, f, k, pos) w \<and> list_all (\<lambda>u. length u = w) xs
         then (case gins k (umeval_trm f) xs (ginit \<omega>) of
                 Some a \<Rightarrow> gres g0 \<omega> pos (\<lambda>x. x) a
               | None \<Rightarrow> uagg_gen g0 \<omega> f k pos X)
         else uagg_gen g0 \<omega> f k pos X)))"
  by (simp add: uagg_g_eq[symmetric]) (simp add: uagg_g_def uagg_gen_def)

(*<*)
end
(*>*)

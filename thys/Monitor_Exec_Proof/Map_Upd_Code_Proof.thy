(*<*)
theory Map_Upd_Code_Proof
  imports "Monitor_Exec.Map_Upd_Code" Agg_Code_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



context
  fixes c :: "'a comparator"
begin

lemma fst_rbt_comp_ins_lk: "fst (rbt_comp_ins_lk F k t) = rbt_comp_lookup c t k"
  by (induct F k t rule: rbt_comp_ins_lk.induct) (auto split: order.splits prod.splits option.splits)

lemma rbt_comp_ins_lk:
  "rbt_comp_ins_lk F k t = (rbt_comp_lookup c t k, case rbt_comp_lookup c t k of
     None \<Rightarrow> rbt_comp_ins c (\<lambda>_ _ nv. nv) k (F None) t
   | Some v \<Rightarrow> rbt_comp_map_entry c k (\<lambda>_. F (Some v)) t)"
proof (induct F k t rule: rbt_comp_ins_lk.induct)
  case (2 F k l x y r)
  then show ?case
    using fst_rbt_comp_ins_lk[of F k l] fst_rbt_comp_ins_lk[of F k r]
    by (auto split: order.splits prod.splits option.splits)
qed (auto split: order.splits prod.splits option.splits)

lemma rbt_comp_ins_lk2: "rbt_comp_ins_lk2 F k t =
    (case rbt_comp_ins_lk F k t of (ov, t') \<Rightarrow> (ov, F ov, t'))"
proof (induct F k t rule: rbt_comp_ins_lk2.induct)
  case (2 F k l x y r)
  then show ?case
    using fst_rbt_comp_ins_lk[of F k l] fst_rbt_comp_ins_lk[of F k r]
    by (auto simp: Let_def split: order.splits prod.splits option.splits)
qed (auto simp: Let_def split: order.splits prod.splits option.splits)

text \<open>A caller that does not read the old value needs no pair at every node: the insertion
  that combines the old value with the new one computes the same tree as the insertion of the
  value computed from the lookup, since both descend by the same comparisons.\<close>

lemma rbt_comp_ins_upd_w:
  "rbt_comp_ins c (\<lambda>_ y _. F (Some y)) k (F None) t =
    rbt_comp_ins c (\<lambda>_ _ nv. nv) k (F (rbt_comp_lookup c t k)) t"
proof (induct t)
  case (Branch col l x y r)
  then show ?case
    by (cases col) (auto split: order.splits)
qed simp

end

lemma paint_rbt_comp_ins: "RBT_Impl.paint RBT_Impl.B (rbt_comp_ins c (\<lambda>_ _ nv. nv) k v t) = rbt_comp_insert c k v t"
  by (simp add: rbt_comp_insert_def rbt_comp_insert_with_key_def)

lemma is_rbt_rbt_comp_map_entry:
  "ID CCOMPARE('a :: ccompare) = Some c \<Longrightarrow> ord.is_rbt (lt_of_comp c) (t :: ('a, 'b) rbt) \<Longrightarrow>
    ord.is_rbt (lt_of_comp c) (rbt_comp_map_entry c k f t)"
  by (simp add: rbt_comp_map_entry[OF ID_ccompare'] ord.rbt_map_entry_is_rbt)

lemma upd_w_eq: "upd_w k F t = RBT_Mapping2.insert k (F (RBT_Mapping2.lookup t k)) t"
  by transfer (simp add: rbt_comp_insert_with_key_def rbt_comp_ins_upd_w paint_rbt_comp_ins)

lemma upd_lk2_eq: "upd_lk2 k F t = (case upd_lk k F t of (ov, t') \<Rightarrow> (ov, F ov, t'))"
  by transfer (simp add: rbt_comp_ins_lk2 split: prod.splits option.splits)

lemma upd_lk_eq: "upd_lk k F t = (RBT_Mapping2.lookup t k, case RBT_Mapping2.lookup t k of
    None \<Rightarrow> RBT_Mapping2.insert k (F None) t
  | Some v \<Rightarrow> RBT_Mapping2.map_entry k (\<lambda>_. F (Some v)) t)"
  by transfer (simp add: rbt_comp_ins_lk paint_rbt_comp_ins split: option.splits)

lemma lookup_mrefresh: "Mapping.lookup (mrefresh v Y m) k =
  (if k \<in> Y then Some (case Mapping.lookup m k of None \<Rightarrow> v | Some w \<Rightarrow> w) else None)"
  by (auto simp: mrefresh_def lookup_mfilter_keys Mapping_lookup_upd_set keys_is_none_rep
      split: option.splits)

text \<open>A tuple of the right operand enters the deque's map at a time point only if the time
  stamp of that point lies in the interval's left end.  For an interval starting at 0, the common
  case, that is always so, and the test -- a walk of the time stamp deque to the point -- is
  dropped.\<close>

lemma de_gadd_new_dq_inz:
  "de_gadd_new_dq args msk rel1 rel2 nt aux =
    (let (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) =
       de_gshift_dq args nt aux;
     I = args_ivl args; pos = args_pos args; inz = memL I 0;
     new_tstp = (if inz then Inr tp else Inl nt);
     tstp_dq = dq_push nt tstp_dq;
     P = (if inz then (\<lambda>_. True) else (\<lambda>t. memL I (nt - dq_nth_s tstp_dq (t - (tp - len)) 0)));
     (tbl, a2_dq') = fold (de_guntil_elem_step_dq a1_map msk pos tp len inz P new_tstp)
       (csl rel2) ({}, a2_dq);
     tables = append_queue (tbl, new_tstp) tables;
     a2_dq = dq_push Mapping.empty a2_dq';
     a1_map = (if pos then mrefresh tp rel1 a1_map else upd_set a1_map (\<lambda>_. tp) rel1);
     tss = append_queue nt tss in
     (tp + 1, tss, tables, len + 1, result, a1_map, a2_dq, tstp_dq, dn))"
proof -
  have "(\<lambda>t. memL (args_ivl args) (nt - dq_nth_s d (t - k) 0)) = (\<lambda>_. True)"
    if "memL (args_ivl args) 0" for d k
    using that by auto
  then show ?thesis
    unfolding de_gadd_new_dq_def gadd_new_dq_code de_gshift_dq_def de_guntil_elem_step_dq_def
      mrefresh_def[symmetric]
    by (simp add: Let_def split: prod.splits)
qed

lemma guntil_elem_step_dq_True:
  "guntil_elem_step_dq a1_map msk pos tp len True (\<lambda>_. True) d as (tbl, a2) =
    (Set.insert as tbl, guntil_a2_step a1_map msk pos tp len d as a2)"
  by (simp add: guntil_elem_step_dq_def guntil_step_dq_def guntil_a2_step_def Let_def
      split: option.splits)

lemma fold_guntil_elem_step_dq_True:
  "fold (guntil_elem_step_dq a1_map msk pos tp len True (\<lambda>_. True) d) xs (tbl, a2) =
    (tbl \<union> set xs, fold (guntil_a2_step a1_map msk pos tp len d) xs a2)"
  by (induction xs arbitrary: tbl a2) (simp_all add: guntil_elem_step_dq_True)

lemma lookup_delete_if:
  "Mapping.lookup (Mapping.delete a m) k = (if a = k then None else Mapping.lookup m k)"
  by simp

lemma lookup_fold_mdel_if:
  "distinct xs \<Longrightarrow> Mapping.lookup (fold (mdel_if Q) xs m) k =
    (if k \<in> set xs \<and> (case Mapping.lookup m k of Some v \<Rightarrow> Q v | None \<Rightarrow> False) then None
     else Mapping.lookup m k)"
  by (induction xs arbitrary: m) (auto simp: mdel_if_def lookup_delete_if split: option.splits)

lemma fold_mdel_if:
  "distinct xs \<Longrightarrow> fold (mdel_if Q) xs m = mapping_delete_set m
    (Set.filter (\<lambda>x. case Mapping.lookup m x of Some v \<Rightarrow> Q v | None \<Rightarrow> False) (set xs))"
  by (rule mapping_eqI) (auto simp: lookup_fold_mdel_if delete_set_lookup split: option.splits)

context
  fixes c :: "'a comparator"
begin

lemma rbt_comp_del_lk:
  fixes a b t :: "('a, 'b) rbt"
  shows "rbt_comp_del_lk_from_left x a y s b = (rbt_comp_lookup c a x, rbt_comp_del_from_left c x a y s b)"
  "rbt_comp_del_lk_from_right x a y s b = (rbt_comp_lookup c b x, rbt_comp_del_from_right c x a y s b)"
  "rbt_comp_del_lk x t = (rbt_comp_lookup c t x, rbt_comp_del c x t)"
  by (induct x a y s b and x a y s b and x t
      rule: rbt_comp_del_lk_from_left_rbt_comp_del_lk_from_right_rbt_comp_del_lk.induct)
    (auto split: order.splits prod.splits)

end

lemma del_lk_eq: "del_lk k t = (RBT_Mapping2.lookup t k, RBT_Mapping2.delete k t)"
  by transfer (simp add: rbt_comp_del_lk rbt_comp_delete_def)

lemma gval_GRank: "gval \<omega> (GRank m ty) g = (case Mapping.lookup m g of None \<Rightarrow> None | Some l \<Rightarrow> rkval \<omega> l)"
  by (cases "fst \<omega>") (simp_all add: rkval_def split: option.splits)

lemma lookup_fold_mm_step:
  "Mapping.lookup (fold (mm_step ev op k) xs m) g
   = foldl (mm_acc ev op) (Mapping.lookup m g) (filter (\<lambda>t. drop k t = g) xs)"
  by (induct xs arbitrary: m) (simp_all add: mm_step_def mupdw_def mm_acc_def lookup_update')

lemma foldl_mm_acc_Some: "foldl (mm_acc ev op) (Some u) ts = Some (foldl op u (map ev ts))"
  by (induct ts arbitrary: u) (simp_all add: mm_acc_def)

lemma keys_fold_mm_step: "Mapping.keys (fold (mm_step ev op k) xs m) = Mapping.keys m \<union> drop k ` set xs"
  by (induct xs arbitrary: m) (auto simp: mm_step_def mupdw_def)

lemma foldl_max_Max: "foldl max u xs = Max (Set.insert u (set xs))" for u :: "'a :: linorder"
proof -
  have "foldl max u xs = fold max xs u"
    by (induct xs arbitrary: u) (simp_all add: max.commute)
  then show ?thesis
    by (simp add: Max.set_eq_fold[symmetric])
qed

lemma foldl_min_Min: "foldl min u xs = Min (Set.insert u (set xs))" for u :: "'a :: linorder"
proof -
  have "foldl min u xs = fold min xs u"
    by (induct xs arbitrary: u) (simp_all add: min.commute)
  then show ?thesis
    by (simp add: Min.set_eq_fold[symmetric])
qed

text \<open>The multiset of a finite, non-empty group's values lists each of its values at least once
  and nothing else, so its minimum and maximum are those of the values.\<close>

lemma set_csorted_list_of_set_mset:
  "finite (M :: (event_data \<times> enat) set) \<Longrightarrow> set (csorted_list_of_set M) = M"
proof -
  obtain c where c_def: "ID ccompare = Some (c :: (event_data \<times> enat) comparator)"
    by (simp add: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def
        split: if_splits option.splits)
  note c_class = comparator.linorder[OF ID_ccompare'[OF c_def]]
  assume "finite M"
  then show ?thesis
    using linorder.set_sorted_list_of_set[OF c_class] by (simp add: csorted_list_of_set_def c_def)
qed

lemma flatten_uagg_values:
  assumes "finite G" "G \<noteq> {}"
  shows "set (flatten_multiset (uagg_values f G)) = umeval_trm f ` G"
    and "finite_multiset (uagg_values f G)"
proof -
  let ?M = "uagg_values f G"
  let ?c = "\<lambda>v. card {x \<in> G. umeval_trm f x = v}"
  have M: "?M = (\<lambda>v. (v, enat (?c v))) ` umeval_trm f ` G"
    using assms(1) by (simp add: uagg_values ecard_def)
  have fM: "finite ?M"
    using assms(1) by (simp add: M)
  have pos: "0 < ?c (umeval_trm f x')" if "x' \<in> G" for x'
    using assms(1) that by (auto simp: card_gt_0_iff)
  have "set (flatten_multiset ?M) = {x. \<exists>c. (x, c) \<in> ?M \<and> the_enat c \<noteq> 0}"
    unfolding flatten_multiset_def set_concat set_map set_csorted_list_of_set_mset[OF fM]
    by (auto split: prod.splits)
  then show "set (flatten_multiset ?M) = umeval_trm f ` G"
    using pos by (auto simp: M image_iff)
  show "finite_multiset ?M"
    using fM by (auto simp: finite_multiset_def M)
qed

lemma foldl_max_ival: "\<forall>x \<in> set (u # xs). is_eint x \<Longrightarrow>
    foldl max u xs = EInt (foldl max (ival u) (map ival xs))"
  by (induct xs arbitrary: u) (auto simp: is_eint_def ival_def max_def split: event_data.splits)

lemma foldl_min_ival: "\<forall>x \<in> set (u # xs). is_eint x \<Longrightarrow>
    foldl min u xs = EInt (foldl min (ival u) (map ival xs))"
  by (induct xs arbitrary: u) (auto simp: is_eint_def ival_def min_def split: event_data.splits)

lemma eval_agg_op_uagg_values_Max_Min:
  assumes "finite G" "G \<noteq> {}" "\<forall>x \<in> G. is_eint (umeval_trm f x)"
  shows "eval_agg_op (Formula.Agg_Max, ty) (uagg_values f G) = EInt (Max (ival ` umeval_trm f ` G))"
    and "eval_agg_op (Formula.Agg_Min, ty) (uagg_values f G) = EInt (Min (ival ` umeval_trm f ` G))"
proof -
  note fl = flatten_uagg_values[OF assms(1,2), of f]
  obtain x xs where x: "flatten_multiset (uagg_values f G) = x # xs"
    using fl(1) assms(2) by (cases "flatten_multiset (uagg_values f G)") auto
  have s: "set (x # xs) = umeval_trm f ` G"
    using fl(1) x by simp
  then have i: "\<forall>y \<in> set (x # xs). is_eint y"
    using assms(3) by auto
  have "ival ` umeval_trm f ` G = Set.insert (ival x) (set (map ival xs))"
    using s by (metis image_insert list.set(2) set_map)
  then show "eval_agg_op (Formula.Agg_Max, ty) (uagg_values f G) = EInt (Max (ival ` umeval_trm f ` G))"
    and "eval_agg_op (Formula.Agg_Min, ty) (uagg_values f G) = EInt (Min (ival ` umeval_trm f ` G))"
    using fl x by (simp_all add: foldl_max_ival[OF i] foldl_min_ival[OF i] foldl_max_Max
        foldl_min_Min)
qed

lemma uagg_mm_gen:
  fixes F :: "integer set \<Rightarrow> integer"
  assumes fX: "finite X" and ne: "X \<noteq> {}" and i: "\<forall>x \<in> X. is_eint (umeval_trm f x)"
    and ev: "\<And>G. finite G \<Longrightarrow> G \<noteq> {} \<Longrightarrow> \<forall>x \<in> G. is_eint (umeval_trm f x) \<Longrightarrow>
      eval_agg_op \<omega> (uagg_values f G) = EInt (F (ival ` umeval_trm f ` G))"
    and op: "\<And>u xs. foldl op u xs = F (Set.insert u (set xs))"
  shows "uagg g0 \<omega> f k pos X = uagg_mm op f k pos (csl X)"
proof -
  let ?ev = "\<lambda>t. ival (umeval_trm f t)"
  let ?m = "fold (mm_step ?ev op k) (csl X) Mapping.empty"
  have s: "set (csl X) = X"
    by (rule set_csl_ed[OF fX])
  have keys: "Mapping.keys ?m = drop k ` X"
    by (simp add: keys_fold_mm_step s)
  have lk: "Mapping.lookup ?m g = Some (F (ival ` umeval_trm f ` Set.filter (\<lambda>x. drop k x = g) X))"
    if g: "g \<in> drop k ` X" for g
  proof -
    obtain t ts where tts: "filter (\<lambda>t. drop k t = g) (csl X) = t # ts"
      using g s by (cases "filter (\<lambda>t. drop k t = g) (csl X)") (auto simp: filter_empty_conv)
    have "set (t # ts) = Set.filter (\<lambda>x. drop k x = g) X"
      using tts[symmetric] s by auto
    then have "Set.insert (?ev t) (set (map ?ev ts)) = ival ` umeval_trm f ` Set.filter (\<lambda>x. drop k x = g) X"
      by (metis image_image image_insert list.set(2) set_map)
    then show ?thesis
      by (simp add: lookup_fold_mm_step tts mm_acc_def foldl_mm_acc_Some op)
  qed
  have evG: "eval_agg_op \<omega> (uagg_values f {a \<in> X. drop k a = drop k x})
      = EInt (F (ival ` umeval_trm f ` {a \<in> X. drop k a = drop k x}))" if "x \<in> X" for x
    using ev[of "{a \<in> X. drop k a = drop k x}"] fX i that by auto
  show ?thesis
    unfolding uagg_def uagg_mm_def ugmr_def gmr_def Let_def keys_cluster
    using ne by (auto simp: keys lk lookup_cluster_Some evG intro!: image_cong)
qed

lemma uagg_mm_Max_Min:
  assumes "finite X" "X \<noteq> {}" "\<forall>x \<in> X. is_eint (umeval_trm f x)"
  shows "uagg g0 (Formula.Agg_Max, ty) f k pos X = uagg_mm max f k pos (csl X)"
    and "uagg g0 (Formula.Agg_Min, ty) f k pos X = uagg_mm min f k pos (csl X)"
  by (rule uagg_mm_gen[OF assms eval_agg_op_uagg_values_Max_Min(1) foldl_max_Max]; assumption)
    (rule uagg_mm_gen[OF assms eval_agg_op_uagg_values_Max_Min(2) foldl_min_Min]; assumption)

end
(*>*)

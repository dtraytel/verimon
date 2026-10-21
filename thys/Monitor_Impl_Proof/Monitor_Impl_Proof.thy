(*<*)
theory Monitor_Impl_Proof
  imports "Monitor_Impl.Monitor_Impl" Optimized_Trigger_Proof Optimized_Agg_Temporal_Proof Optimized_Until_Deque_Proof
begin
(*>*)


lemma Rep_mbuf_t_cases[simp]:
  "mbuf_t_cases xs = (None, xs') \<Longrightarrow> Rep_mbuf_t xs = []"
  "mbuf_t_cases xs = (None, xs') \<Longrightarrow> Rep_mbuf_t xs' = []"
  "mbuf_t_cases xs = (Some x, xs') \<Longrightarrow> Rep_mbuf_t xs = x # Rep_mbuf_t xs'"
  subgoal by transfer (auto split: option.splits list.splits)
  subgoal by transfer (auto split: option.splits list.splits)
  subgoal by transfer (auto split: option.splits list.splits)
  done

lemma mbuf_t_cases_size[termination_simp]: "(Some x, xs') = mbuf_t_cases xs \<Longrightarrow> size xs' < size xs"
  by transfer (auto split: list.splits)

lemma meprev_next: "meprev_next I xs ts = (zs, xs', ts') \<Longrightarrow> mprev_next I (Rep_mbuf_t xs) (Rep_mbuf_t ts) =
  (zs, Rep_mbuf_t xs', Rep_mbuf_t ts')"
proof (induction I xs ts arbitrary: zs xs' ts' rule: meprev_next.induct)
  case (1 I xs ts)
  obtain xo xs'' where xs_def: "mbuf_t_cases xs = (xo, xs'')"
    by fastforce
  obtain to ts'' where ts_def: "mbuf_t_cases ts = (to, ts'')"
    by fastforce
  obtain to' ts''' where ts''_def: "mbuf_t_cases ts'' = (to', ts''')"
    by fastforce
  show ?case
    using 1
    by (cases xo; cases to; cases to')
       (auto simp: xs_def ts_def ts''_def mbuf_t_empty.rep_eq mbuf_t_Cons.rep_eq split: prod.splits)
qed

lemma mbuf2_add: "mbuf2_add xs ys (map_prod Rep_mbuf_t Rep_mbuf_t buf) 
  = map_prod Rep_mbuf_t Rep_mbuf_t (mebuf2_add xs ys buf)"
  by (cases buf) (auto simp: mbuf_t_append.rep_eq)

lemma mebuf2_take_aux: "mebuf2_take f (xs, ys) = (zs, (xs', ys')) \<Longrightarrow>
  mbuf2_take f (Rep_mbuf_t xs, Rep_mbuf_t ys) = (zs, (Rep_mbuf_t xs', Rep_mbuf_t ys'))"
proof (induction f "(xs, ys)" arbitrary: xs ys zs xs' ys' rule: mebuf2_take.induct)
  case (1 f xs ys)
  obtain x xs'' where xs_def: "mbuf_t_cases xs = (x, xs'')"
    by fastforce
  obtain y ys'' where ys_def: "mbuf_t_cases ys = (y, ys'')"
    by fastforce
  show ?case
    using 1 xs_def ys_def
    by (cases x; cases y) (auto simp: mbuf_t_Cons.rep_eq split: prod.splits)
qed

lemma mebuf2_take: "mebuf2_take f buf = (zs, buf') \<Longrightarrow>
  mbuf2_take f (map_prod Rep_mbuf_t Rep_mbuf_t buf) = (zs, (map_prod Rep_mbuf_t Rep_mbuf_t buf'))"
  using mebuf2_take_aux
  by (cases buf; cases buf') fastforce

lemma mebuf2t_take_aux: "mebuf2t_take f z (xs, ys) t ts = (zs, (xs', ys'), nt, ts') \<Longrightarrow>
  mbuf2t_take f z (Rep_mbuf_t xs, Rep_mbuf_t ys) t (Rep_mbuf_t ts) = (zs, (Rep_mbuf_t xs', Rep_mbuf_t ys'), nt, Rep_mbuf_t ts')"
proof (induction f z "(xs, ys)" t ts arbitrary: xs ys rule: mebuf2t_take.induct)
  case (1 f z xs ys t ts)
  obtain x xs'' where xs_def: "mbuf_t_cases xs = (x, xs'')"
    by fastforce
  obtain y ys'' where ys_def: "mbuf_t_cases ys = (y, ys'')"
    by fastforce
  obtain t ts'' where ts_def: "mbuf_t_cases ts = (t, ts'')"
    by fastforce
  show ?case
    using 1 xs_def ys_def ts_def
    by (cases x; cases y; cases t) (auto simp: mbuf_t_Cons.rep_eq split: prod.splits list.splits)
qed

lemma mebuf2t_take: "mebuf2t_take f z buf t ts = (zs, buf', nt, nts) \<Longrightarrow>
  mbuf2t_take f z (map_prod Rep_mbuf_t Rep_mbuf_t buf) t (Rep_mbuf_t ts) = (zs, (map_prod Rep_mbuf_t Rep_mbuf_t buf'), nt, Rep_mbuf_t nts)"
  using mebuf2t_take_aux
  by (cases buf; cases buf') fastforce

lemma mebuf2T_take_aux: "mebuf2T_take f z (xs, ys) ts = (zs, (xs', ys'), ts') \<Longrightarrow>
  mbuf2T_take f z (Rep_mbuf_t xs, Rep_mbuf_t ys) (Rep_mbuf_t ts) = (zs, (Rep_mbuf_t xs', Rep_mbuf_t ys'), Rep_mbuf_t ts')"
proof (induction f z "(xs, ys)" ts arbitrary: xs ys rule: mebuf2T_take.induct)
  case (1 f z xs ys ts)
  obtain x xs'' where xs_def: "mbuf_t_cases xs = (x, xs'')"
    by fastforce
  obtain y ys'' where ys_def: "mbuf_t_cases ys = (y, ys'')"
    by fastforce
  obtain t ts'' where ts_def: "mbuf_t_cases ts = (t, ts'')"
    by fastforce
  show ?case
    using 1 xs_def ys_def ts_def
    by (cases x; cases y; cases t) (auto simp: mbuf_t_Cons.rep_eq split: prod.splits list.splits)
qed

lemma mebuf2T_take: "mebuf2T_take f z buf ts = (zs, buf', nts) \<Longrightarrow>
  mbuf2T_take f z (map_prod Rep_mbuf_t Rep_mbuf_t buf) (Rep_mbuf_t ts) = (zs, (map_prod Rep_mbuf_t Rep_mbuf_t buf'), Rep_mbuf_t nts)"
  using mebuf2T_take_aux
  by (cases buf; cases buf') 
    fastforce

lemma mbufn_add: "mbufn_add xss (map Rep_mbuf_t buf) = map Rep_mbuf_t (mebufn_add xss buf)"
  by (auto simp: comp_def zip_map1 mbuf_t_append.rep_eq)

lemma size_snd_mbuf_t_cases: "\<not> mbuf_t_is_empty a \<Longrightarrow> size (snd (mbuf_t_cases a)) < size a"
  by transfer (auto split: list.splits)

lemma size_list_snd_mbuf_t_cases: assumes "buf \<noteq> []" "\<And>x. x \<in> set buf \<Longrightarrow> \<not> mbuf_t_is_empty x"
  shows "size_list (\<lambda>x. size (snd (mbuf_t_cases x))) buf < size_list size buf"
  using assms
proof (induction buf)
  case IH: (Cons a buf)
  show ?case
  proof (cases buf)
    case Nil
    show ?thesis
      using IH(3) size_snd_mbuf_t_cases
      by (auto simp: Nil)
  next
    case (Cons a' buf')
    have "size_list (\<lambda>x. size (snd (mbuf_t_cases x))) buf < size_list size buf"
      using IH(1,3)
      by (auto simp: Cons)
    then show ?thesis
      using IH(3) size_snd_mbuf_t_cases
      by force
  qed
qed auto

lemma mbuf_t_is_empty_in_set: "[] \<in> set (map Rep_mbuf_t buf) \<longleftrightarrow> (\<exists>x \<in> set buf. mbuf_t_is_empty x)"
  by transfer auto

lemma hd_Rep_mbuf_t:
  assumes "\<And>x. x \<in> set buf \<Longrightarrow> \<not> mbuf_t_is_empty x"
  shows "map (hd \<circ> Rep_mbuf_t) buf = map (the \<circ> fst \<circ> mbuf_t_cases) buf"
  using assms
  by transfer (auto split: list.splits)

lemma tl_Rep_mbuf_t:
  assumes "\<And>x. x \<in> set buf \<Longrightarrow> \<not> mbuf_t_is_empty x"
  shows "map (tl \<circ> Rep_mbuf_t) buf = map Rep_mbuf_t (map (snd \<circ> mbuf_t_cases) buf)"
  using assms
  by transfer (auto split: list.splits)

lemma mebufn_take: "mebufn_take f z buf = (z', buf') \<Longrightarrow>
  mbufn_take f z (map Rep_mbuf_t buf) = (z', map Rep_mbuf_t buf')"
proof (induction f z buf arbitrary: z' buf' rule: mebufn_take.induct)
  case (1 f z buf)
  show ?case
    using 1(1,2)
    unfolding mebufn_take.simps[of _ _ buf] mbufn_take.simps[of _ _ "map Rep_mbuf_t buf"] mbuf_t_is_empty_in_set map_is_Nil_conv
    by (auto simp del: mbufn_take.simps mebufn_take.simps simp: hd_Rep_mbuf_t tl_Rep_mbuf_t split: if_splits)
qed

lemma mbufn_take_app: "mbufn_take (\<lambda>xs zs. zs @@ [f xs]) zs buf = (buf', zs') \<Longrightarrow>
  mbufn_take (\<lambda>xs zs. zs @ [f xs]) (Rep_mbuf_t zs) buf = (buf'', zs'') \<Longrightarrow>
  buf'' = Rep_mbuf_t buf' \<and> zs'' = zs'"
proof (induction "\<lambda>xs zs. zs @@ [f xs]" zs buf rule: mbufn_take.induct)
  case (1 z buf)
  then show ?case
    by (auto simp: mbufn_take.simps[where ?buf="buf"] mbuf_t_append.rep_eq simp del: mbufn_take.simps split: if_splits)
qed

lemma mebufnt_take: "mebufnt_take f z buf t nts = (z', buf', nt, nts') \<Longrightarrow>
  mbufnt_take f z (map Rep_mbuf_t buf) t (Rep_mbuf_t nts) = (z', map Rep_mbuf_t buf', nt, Rep_mbuf_t nts')"
proof (induction f z buf t nts arbitrary: z' buf' nts' rule: mebufnt_take.induct)
  case (1 f z buf t ts)
  obtain to ts'' where ts_def: "mbuf_t_cases ts = (to, ts'')"
    by fastforce
  show ?case
    using 1(1,2) ts_def
    unfolding mebufnt_take.simps[of _ _ buf] mbufnt_take.simps[of _ _ "map Rep_mbuf_t buf"] mbuf_t_is_empty_in_set map_is_Nil_conv
    by (cases to) (auto simp del: mbufnt_take.simps mebufnt_take.simps simp: hd_Rep_mbuf_t tl_Rep_mbuf_t mbuf_t_Cons.rep_eq split: if_splits)
qed

lemma mbufnt_take_app: "mbufnt_take (\<lambda>xs t (zs, aux). case f xs t aux of (z, aux) \<Rightarrow> (zs @@ [z], aux)) (zs, aux) buf t0 ts = ((zs', aux'), buf', nt', ts') \<Longrightarrow>
  mbufnt_take (\<lambda>xs t (zs, aux). case f xs t aux of (z, aux) \<Rightarrow> (zs @ [z], aux)) (Rep_mbuf_t zs, aux) buf t0 ts = ((zs'', aux''), buf'', nt'', ts'') \<Longrightarrow>
  zs'' = Rep_mbuf_t zs' \<and> aux'' = aux' \<and> buf'' = buf' \<and> nt'' = nt' \<and> ts'' = ts'"
proof (induction "\<lambda>xs t (zs, aux). case f xs t aux of (z, aux) \<Rightarrow> (zs @@ [z], aux)" "(zs, aux)" buf t0 ts arbitrary: zs aux rule: mbufnt_take.induct)
  case (1 buf t0 ts)
  then show ?case
    by (auto simp: mbufnt_take.simps[where ?ts=ts] mbuf_t_append.rep_eq simp del: mbufnt_take.simps split: if_splits prod.splits)
qed

context
begin

end

interpretation verimon_maux: maux valid_vmsaux init_vmsaux add_new_ts_vmsaux join_vmsaux
  add_new_table_vmsaux result_vmsaux valid_vmuaux init_vmuaux add_new_vmuaux length_vmuaux
  eval_vmuaux valid_mmtaux init_mmtaux update_mmtaux result_mmtaux bin_join mmulti_join
  unfolding valid_vmsaux_def init_vmsaux_def add_new_ts_vmsaux_def join_vmsaux_def
    add_new_table_vmsaux_def result_vmsaux_def valid_vmuaux_def init_vmuaux_def add_new_vmuaux_def
    length_vmuaux_def eval_vmuaux_def 
proof (unfold_locales, goal_cases)
next
  case (2 args cur aux auxlist nt)
  then show ?case
    by clarsimp
next
  case (3 args cur aux auxlist rel1)
  then show ?case
    by clarsimp
next
  case (4 args cur aux auxlist rel2)
  then show ?case
    by clarsimp
next
  case (5 args cur aux auxlist)
  then show ?case
    by clarsimp
next
  case (7 args cur aux auxlist rel1 rel2 nt)
  then show ?case
    by clarsimp
next
  case (8 args cur aux auxlist)
  then show ?case
    by clarsimp
next
  case (9 args cur aux auxlist nt res aux' res' auxlist')
  then show ?case
    by clarsimp
next
  case (10 I L R pos n agg)
  then show ?case
    using valid_init_mmtaux[of I L R pos n agg]
    by (auto simp: Let_def split: if_splits)
next
  case (11 cur nt args l r aux auxlist)
  then show ?case 
    using valid_update_mmtaux by blast
next
  case (12 args cur aux auxlist)
  then show ?case 
    using valid_result_mmtaux by blast
qed (simp_all del: bin_join.simps mmulti_join.simps add: bin_join_table mmulti_join_correct)

interpretation default_maux: maux 
  (* msaux *) valid_mmasaux "init_mmasaux :: _ \<Rightarrow> mmasaux" add_new_ts_mmasaux gc_join_mmasaux 
    add_new_table_mmasaux result_mmasaux
  (* muaux *) valid_muaux_dq "init_muaux_dq :: _ \<Rightarrow> muaux_dq" add_new_muaux_dq
    length_muaux_dq eval_muaux_dq
  (* mtaux *) valid_mmtaux init_mmtaux update_mmtaux result_mmtaux
  (* joins *) bin_join mmulti_join
  by unfold_locales (simp_all del: bin_join.simps mmulti_join.simps add: bin_join_table mmulti_join_correct)

lemma saturate_commute:
  assumes "\<And>s. r \<in> g s" "\<And>s. g (Set.insert r s) = g s" "\<And>s. r \<in> s \<Longrightarrow> h s = g s"
  and terminates: "mono g" "\<And>X. X \<subseteq> C \<Longrightarrow> g X \<subseteq> C" "finite C"
shows "saturate g {} = saturate h {r}"
proof (cases "g {} = {r}")
  case True
  with assms have "g {r} = {r}" "h {r} = {r}" by auto
  with True show ?thesis
    by (subst (1 2) saturate_code; subst saturate_code) (simp add: Let_def)
next
  case False
  then show ?thesis
    unfolding saturate_def while_def
    using while_option_finite_subset_Some[OF terminates] assms(1-3)
    by (subst while_option_commute_invariant[of "\<lambda>S. S = {} \<or> r \<in> S" "\<lambda>S. g S \<noteq> S" g "\<lambda>S. h S \<noteq> S" "Set.insert r" h "{}", symmetric])
      (auto 4 4 dest: while_option_stop[of "\<lambda>S. g S \<noteq> S" g "{}"])
qed

lemma upd_set_empty[simp]: "upd_set m f {} = m"
  by transfer auto

lemma upd_set_insert[simp]: "upd_set m f (Set.insert x A) = Mapping.update x (f x) (upd_set m f A)"
  by (rule mapping_eqI) (auto simp: Mapping_lookup_upd_set Mapping.lookup_update')

lemma upd_set_fold:
  assumes "finite A"
  shows "upd_set m f A = Finite_Set.fold (\<lambda>a. Mapping.update a (f a)) m A"
proof -
  interpret comp_fun_idem "\<lambda>a. Mapping.update a (f a)"
    by unfold_locales (transfer; auto simp: fun_eq_iff)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) auto
qed

lemma filter_mapping_empty[simp]: "filter_mapping m {} t = m"
  unfolding filter_mapping_def
  by transfer (auto simp: fun_eq_iff split: option.splits)

lemma filter_mapping_insert[simp]: "filter_mapping m (Set.insert x A) t = (let m' = filter_mapping m A t in
  case Mapping.lookup m' x of Some u \<Rightarrow> if t = u then Mapping.delete x m' else m' | _ \<Rightarrow> m')"
  unfolding filter_mapping_def
  by transfer (auto simp: fun_eq_iff Let_def split: option.splits)

lemma filter_mapping_fold:
  assumes "finite A"
  shows "filter_mapping m A t = Finite_Set.fold (\<lambda>a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m) m A"
proof -
  interpret comp_fun_idem "\<lambda>a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m"
    by unfold_locales
      (transfer; auto simp: fun_eq_iff split: option.splits)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) (auto simp: Let_def)
qed

lemma filter_set'_empty[simp]: "filter_set' Z m {} t = Z"
  unfolding filter_set'_def
  by transfer (auto simp: fun_eq_iff split: option.splits)

lemma filter_set'_insert[simp]: "filter_set' Z m (Set.insert x A) t = (let Z' = filter_set' Z m A t in
  case Mapping.lookup m x of Some u \<Rightarrow> if t = u then Z' - {x} else Z' | _ \<Rightarrow> Z')"
  unfolding filter_set'_def
  by transfer (auto simp: Let_def split: option.splits)

lemma filter_set'_fold:
  assumes "finite A"
  shows "filter_set' Z m A t = Finite_Set.fold (\<lambda>a Z'.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Z' - {a} else Z' | _ \<Rightarrow> Z') Z A"
proof -
  interpret comp_fun_idem "\<lambda>a Z'.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Z' - {a} else Z' | _ \<Rightarrow> Z'"
    by unfold_locales
      (transfer; auto simp: fun_eq_iff split: option.splits)+
  from assms show ?thesis
    by (induct A arbitrary: Z rule: finite.induct) (auto simp: Let_def)
qed

lemma upd_set'_insert: "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_set' m d f (Set.insert x A) =
  (let m' = (upd_set' m d f A) in case Mapping.lookup m' x of None \<Rightarrow> Mapping.update x d m'
  | Some v \<Rightarrow> Mapping.update x (f v) m')"
  by (rule mapping_eqI) (auto simp: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux1: "upd_set' Mapping.empty d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k d (upd_set' Mapping.empty d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: Let_def upd_set'_lookup Mapping.lookup_update'
      split: option.splits)

lemma upd_set'_aux2: "Mapping.lookup m k = None \<Longrightarrow> upd_set' m d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k d (upd_set' m d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux3: "Mapping.lookup m k = Some v \<Longrightarrow> upd_set' m d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k (f v) (upd_set' m d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux4: "k \<notin> fst ` A \<Longrightarrow> upd_set' Mapping.empty d f {b. (k, b) \<in> A} = Mapping.empty"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' Domain.DomainI fst_eq_Domain
      split: option.splits)

lemma filter_set_empty[simp]: "filter_set (t, {}) (m, Y) = (m, Y)"
  unfolding filter_set.simps
  by transfer (auto simp: Let_def fun_eq_iff split: option.splits)

lemma upd_nested_empty[simp]: "upd_nested m d f {} = m"
  by (rule mapping_eqI)
    (clarsimp simp: upd_nested_def Mapping.lookup.abs_eq split: option.splits)

lemma upd_nested_insert:
  "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_nested m d f (Set.insert x A) =
  upd_nested_step d f x (upd_nested m d f A)"
  unfolding upd_nested_step_def
  using upd_set'_aux1[of d f _ _ A] upd_set'_aux2[of _ _ d f _ A] upd_set'_aux3[of _ _ _ d f _ A]
    upd_set'_aux4[of _ A d f]
  by (auto simp add: Let_def upd_nested_lookup upd_set'_lookup Mapping.lookup_update'
      split: option.splits prod.splits if_splits intro!: mapping_eqI)

lemma upd_nested_max_tstp_fold:
  assumes "finite X"
  shows "upd_nested_max_tstp m d X = Finite_Set.fold (upd_nested_step d (max_tstp d)) m X"
proof -
  interpret comp_fun_idem "upd_nested_step d (max_tstp d)"
    by (unfold_locales; rule ext)
      (auto simp add: comp_def upd_nested_step_def Mapping.lookup_update'
       update_update max_tstp_d_d max_tstp_idem' split: option.splits)
  note upd_nested_insert' = upd_nested_insert[of d "max_tstp d",
    OF max_tstp_d_d[symmetric] max_tstp_idem']
  show ?thesis
    using assms
    by (induct X arbitrary: m rule: finite.induct)
      (auto simp add: upd_nested_max_tstp_def upd_nested_insert')
qed

lemma filter_join_False_empty: "filter_join False {} m = m"
  unfolding filter_join_def
  by transfer (auto split: option.splits)

lemma filter_join_False_insert: "filter_join False (Set.insert a A) m =
  filter_join False A (Mapping.delete a m)"
proof -
  {
    fix x
    have "Mapping.lookup (filter_join False (Set.insert a A) m) x =
      Mapping.lookup (filter_join False A (Mapping.delete a m)) x"
      by (auto simp add: filter_join_def Mapping.lookup_filter Mapping_lookup_delete
          split: option.splits)
  }
  then show ?thesis
    by (simp add: mapping_eqI)
qed

lemma filter_set_insert[simp]: "filter_set (t, Set.insert x A) (m, Y) = (let (m', Y') = filter_set (t, A) (m, Y) in
  case Mapping.lookup m' x of Some u \<Rightarrow> if t = u then (Mapping.delete x m', Y' \<union> {x}) else (m', Y') | _ \<Rightarrow> (m', Y'))"
  unfolding filter_set.simps
  by transfer (auto simp: fun_eq_iff Let_def split: option.splits)

lemma filter_set_fold:
  assumes "finite A"
  shows "filter_set (t, A) (m, Y) = Finite_Set.fold (\<lambda>a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)) (m, Y) A"
proof -
  interpret comp_fun_idem "\<lambda>a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)"
    by unfold_locales
      (transfer; auto simp: fun_eq_iff split: option.splits)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) (auto simp: Let_def)
qed

lemma mapping_delete_set_empty: "mapping_delete_set m {} = m"
  unfolding mapping_delete_set_def
  by (auto simp: Mapping_lookup_filter_Some intro!: mapping_eqI)

lemma mapping_delete_set_insert: "mapping_delete_set m (Set.insert a X) = Mapping.delete a (mapping_delete_set m X)"
proof(rule mapping_eqI)
  fix x
  show "Mapping.lookup (mapping_delete_set m (Set.insert a X)) x =
        Mapping.lookup (Mapping.delete a (mapping_delete_set m X)) x"
    unfolding Mapping_lookup_delete mapping_delete_set_def
    by (auto simp add: Mapping_lookup_filter_None)
       (metis (mono_tags, lifting) Mapping_lookup_filter_None Mapping_lookup_filter_Some)
qed

lemma mapping_delete_fold:
  assumes "finite A"
  shows "mapping_delete_set m A = Finite_Set.fold Mapping.delete m A"
proof -
  interpret comp_fun_idem "Mapping.delete" by(unfold_locales; transfer; simp add: fun_eq_iff)
  from assms show ?thesis
  proof (induction A arbitrary: m)
    case empty
    then show ?case using mapping_delete_set_empty by auto
  next
    case (insert a A)
    then show ?case using mapping_delete_set_insert[of m a A] fold_insert[OF insert(1-2), of m] by(simp)
  qed
qed

lemma remove_Union_finite:
  assumes "finite X"
  shows "remove_Union A X B = Finite_Set.fold (\<lambda>x A. A - B x) A X"
proof -
  interpret comp_fun_idem "\<lambda>x A. A - B x"
    by unfold_locales auto
  from assms show ?thesis
    by (induct X arbitrary: A rule: finite_induct) (auto simp: remove_Union_def)
qed

lemma tabulate_remdups: "Mapping.tabulate xs f = Mapping.tabulate (remdups xs) f"
  by (transfer fixing: xs f) (auto simp: map_of_map_restrict)

lemma group_images: "(\<lambda>k. let group = Set.filter (\<lambda>x. f x = k) rel in g k group) ` f ` rel =
    (\<lambda>(k, group). g k group) ` images ((\<lambda>t. (f t, t)) ` rel)"
proof (rule set_eqI, rule iffI)
  fix x
  assume "x \<in> (\<lambda>k. Let (Set.filter (\<lambda>x. f x = k) rel) (g k)) ` f ` rel"
  then obtain t where t_def: "t \<in> rel" "x = g (f t) {x \<in> rel. f x = f t}"
    by auto
  have "(f t, {b. (f t, b) \<in> (\<lambda>t. (f t, t)) ` rel}) \<in>
    (\<lambda>a. (a, {b. (a, b) \<in> (\<lambda>t. (f t, t)) ` rel})) ` fst ` (\<lambda>t. (f t, t)) ` rel"
    using t_def(1)
    by force
  moreover have "{b. (f t, b) \<in> (\<lambda>t. (f t, t)) ` rel} = {x \<in> rel. f x = f t}"
    by (auto simp add: image_def)
  ultimately show "x \<in> (\<lambda>(k, group). g k group) ` images ((\<lambda>t. (f t, t)) ` rel)"
    unfolding t_def(2) images_def
    by auto
next
  fix x
  assume "x \<in> (\<lambda>(k, group). g k group) ` images ((\<lambda>t. (f t, t)) ` rel)"
  then obtain t where t_def: "t \<in> rel" "x = g (f t) {b. (f t, b) \<in> (\<lambda>t. (f t, t)) ` rel}"
    by (auto simp: images_def)
  have "{b. (f t, b) \<in> (\<lambda>t. (f t, t)) ` rel} = {x \<in> rel. f x = f t}"
    by (auto simp add: image_def)
  then show "x \<in> (\<lambda>k. Let (Set.filter (\<lambda>x. f x = k) rel) (g k)) ` f ` rel"
    using t_def(1)
    by (auto simp: t_def(2))
qed

lemma to_add_set_empty: "to_add_set a m {} = {}"
  unfolding to_add_set_def by auto

lemma to_add_set_insert: "to_add_set a m (Set.insert x X) = to_add_set_fun a m x (to_add_set a m X) "
  unfolding to_add_set_def to_add_set_fun_def
  by transfer auto

lemma to_add_set_fold:
  assumes "finite tmp"
  shows "to_add_set a m tmp = Finite_Set.fold (to_add_set_fun a m) {} tmp"
proof -
  interpret comp_fun_idem "to_add_set_fun a m"
    by(unfold_locales) (auto simp:to_add_set_fun_def comp_def split:if_splits)
  from assms show ?thesis
  proof (induction tmp)
    case empty
    then show ?case using to_add_set_empty[of a m] by simp
  next
    case (insert a A)
    show ?case unfolding fold_insert[OF insert(1-2)] insert(3)[symmetric] unfolding to_add_set_def to_add_set_fun_def
      by transfer auto
   qed 
 qed

lemma update_mapping_with_alt: "update_mapping_with f k v m =
  (case Mapping.lookup m k of
      None \<Rightarrow> Mapping.update k v m
    | Some v' \<Rightarrow> Mapping.update k (f k v' v) m)"
  by transfer simp

lemma finite_mset_insert_idem: 
  "comp_fun_idem finite_multiset_insert_fun"
proof -
   have *: "(finite_multiset_insert_fun (a, b) \<circ> finite_multiset_insert_fun (c, d)) e =
       (finite_multiset_insert_fun (c, d) \<circ> finite_multiset_insert_fun (a, b)) e" for a b c d e by auto
  then have aux1: "(finite_multiset_insert_fun (a, b) \<circ> finite_multiset_insert_fun (c, d)) =
       (finite_multiset_insert_fun (c, d) \<circ> finite_multiset_insert_fun (a, b))" for a b c d 
    using *[of a b c d] by presburger
  have *: "(finite_multiset_insert_fun (a, b) \<circ> finite_multiset_insert_fun (a, b)) c =
       (finite_multiset_insert_fun (a, b) c)" for a b c by auto
  then have aux2: "finite_multiset_insert_fun (a, b) \<circ> finite_multiset_insert_fun (a, b) =
       finite_multiset_insert_fun (a, b)" for a b using *[of a b] by presburger
  show ?thesis
    using aux1 aux2 by unfold_locales auto
qed

lemma finite_multiset_eq:
  assumes "finite M"
  shows "finite_multiset M = 
         Finite_Set.fold finite_multiset_insert_fun True M"
proof -
  interpret comp_fun_idem finite_multiset_insert_fun
    using finite_mset_insert_idem by auto
  from assms show ?thesis
  proof (induction M)
    case empty
    then show ?case by(auto simp:finite_multiset_def)
  next
    case (insert a A)
    have fin: "finite ((\<lambda>(x, y). case_enat (\<lambda>nat. True) False y) ` A)"
      using insert(1) by auto
    obtain s e where a_def: "a = (s, e)" by force
    then show ?case unfolding fold_insert[OF insert(1-2)] unfolding a_def
      using insert(3) by(cases e) (auto simp:finite_multiset_def)
  qed 
qed

end
(*>*)

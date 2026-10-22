(*<*)
theory Monitor_Impl_Proof
  imports "Monitor_Impl.Monitor_Impl" Optimized_Trigger_Proof Optimized_Agg_Temporal_Proof Optimized_Until_Deque_Proof
    Optimized_Join_Proof
begin
(*>*)

text \<open>The proof theories of the structures do not see @{text Monitor_Impl}'s deletion of
  @{thm [source] Let_def} from the simplifier; merging them with it would bring it back.\<close>

declare Let_def[simp del]

lemma Rep_mbuf_t_cases[simp]:
  "mbuf_t_cases xs = (None, xs') \<Longrightarrow> Rep_mbuf_t xs = []"
  "mbuf_t_cases xs = (None, xs') \<Longrightarrow> Rep_mbuf_t xs' = []"
  "mbuf_t_cases xs = (Some x, xs') \<Longrightarrow> Rep_mbuf_t xs = x # Rep_mbuf_t xs'"
  subgoal by transfer (auto split: option.splits list.splits)
  subgoal by transfer (auto split: option.splits list.splits)
  subgoal by transfer (auto split: option.splits list.splits)
  done

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

end
(*>*)

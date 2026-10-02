(*<*)
theory Since_Agg_Exec
  imports Until_Agg Generic_Ops
begin
(*>*)

section \<open>The fused Since window of the executable evaluator\<close>

text \<open>
  The fused aggregation window the executable evaluator runs: its count structure is a mapping alone,
  and its read is guarded by the node's constraint; the result cache of
  @{text Agg_Cache} is built on it.  This theory provides the window, and proves that it
  refines the window of @{theory MFODL_Monitor_Exec.Since_Agg}.
\<close>

subsection \<open>The count mapping\<close>

text \<open>
  The count structure of @{theory MFODL_Monitor_Exec.Window} keeps the tuples' counts in a
  mapping and their keys in a set beside it, so that the plain window can hand out its union in
  one step.  The fused window never hands out that union -- it hands out the aggregate, and reads
  the count structure only to learn which tuples enter the window and which leave it.  The
  mapping answers both, so the fused window keeps the mapping alone and pays one tree operation
  per tuple where the plain window pays two.  @{text ucc} reads the count structure off it: the
  key set is the mapping's domain, which is what the plain window's second half always was.
\<close>

type_synonym ucnt = "(event_data list, nat) mapping"

definition ucnt_add1 :: "event_data list \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_add1 t c = (case Mapping.lookup c t of
     None \<Rightarrow> Mapping.update t 1 c
   | Some k \<Rightarrow> Mapping.update t (k + 1) c)"

definition ucnt_del1 :: "event_data list \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_del1 t c = (case Mapping.lookup c t of
     None \<Rightarrow> c
   | Some k \<Rightarrow> (if k \<le> 1 then Mapping.delete t c else Mapping.update t (k - 1) c))"

definition ucnt_add :: "event_data list set \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_add T c = fold ucnt_add1 (csl T) c"

definition ucnt_del :: "event_data list set \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_del T c = fold ucnt_del1 (csl T) c"

fun ucc :: "ucnt \<Rightarrow> cntset" where
  "ucc c = (c, Mapping.keys c)"

declare ucc.simps[simp del]

lemma lookup_None_keys: "(Mapping.lookup c t = None) = (t \<notin> Mapping.keys c)"
  by (simp add: Mapping.keys_dom_lookup domIff)

lemma cnt_add1_ucc: "cnt_add1 t (ucc c) = ucc (ucnt_add1 t c)"
proof (cases "Mapping.lookup c t")
  case None
  then show ?thesis by (simp add: cnt_add1_def ucnt_add1_def ucc.simps)
next
  case (Some k)
  have "t \<in> Mapping.keys c" using Some lookup_None_keys[of c t] by simp
  with Some show ?thesis by (simp add: cnt_add1_def ucnt_add1_def ucc.simps insert_absorb)
qed

lemma cnt_del1_ucc: "cnt_del1 t (ucc c) = ucc (ucnt_del1 t c)"
proof (cases "Mapping.lookup c t")
  case None
  then show ?thesis by (simp add: cnt_del1_def ucnt_del1_def ucc.simps)
next
  case (Some k)
  have "t \<in> Mapping.keys c" using Some lookup_None_keys[of c t] by simp
  with Some show ?thesis
    by (simp add: cnt_del1_def ucnt_del1_def ucc.simps insert_absorb)
qed

lemma fold_cnt_add1_ucc: "fold cnt_add1 xs (ucc c) = ucc (fold ucnt_add1 xs c)"
  by (induct xs arbitrary: c) (simp_all add: cnt_add1_ucc)

lemma fold_cnt_del1_ucc: "fold cnt_del1 xs (ucc c) = ucc (fold ucnt_del1 xs c)"
  by (induct xs arbitrary: c) (simp_all add: cnt_del1_ucc)

lemma cnt_add_ucc[simp]: "cnt_add T (ucc c) = ucc (ucnt_add T c)"
  by (simp add: cnt_add_def ucnt_add_def fold_cnt_add1_ucc)

lemma cnt_del_ucc[simp]: "cnt_del T (ucc c) = ucc (ucnt_del T c)"
  by (simp add: cnt_del_def ucnt_del_def fold_cnt_del1_ucc)

text \<open>What enters the window is what the mapping does not hold yet, and what leaves it is what
  it holds exactly once: both are read off the mapping, one lookup per tuple.\<close>

type_synonym ugagg = "event_data gagg"

definition uag_ins :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> ucnt \<Rightarrow>
    ugagg option \<Rightarrow> ugagg option" where
  "uag_ins p w T c ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     gins k (umeval_trm f) (filter (\<lambda>t. Mapping.lookup c t = None) (csl T)) ax)"

definition uag_del :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> ucnt \<Rightarrow>
    ugagg option \<Rightarrow> ugagg option" where
  "uag_del p w T c ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     gdel k (umeval_trm f) (filter (\<lambda>t. Mapping.lookup c t = Some 1) (csl T)) ax)"

lemma ag_ins_ucc[simp]: "ag_ins p w T (ucc c) ax = uag_ins p w T c ax"
  by (cases p) (simp add: ag_ins_def uag_ins_def ucc.simps lookup_None_keys)

lemma ag_del_ucc[simp]: "ag_del p w T (ucc c) ax = uag_del p w T c ax"
  by (cases p) (simp add: ag_del_def uag_del_def ucc.simps)

subsection \<open>The node's guard\<close>

text \<open>
  A node whose result is an aggregate is often read through a constraint on the aggregate's own
  value: \<^verbatim>\<open>(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r\<close> is the shape of a whole family of
  policies.  Compiled as a filter over the node, that builds the table of all groups and then
  drops most of it again -- every group that fails the constraint is inserted into a tree only
  to be removed from the next one.  The constraint is carried by the node instead, as the guard
  below, and the read inserts only the groups that pass.  The guard is @{const None} at a node
  that carries no constraint, and then it admits everything.
\<close>

type_synonym uconstr = "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"

definition uqok :: "uconstr option \<Rightarrow> event_data list \<Rightarrow> bool" where
  "uqok q = (case q of None \<Rightarrow> (\<lambda>_. True) | Some c \<Rightarrow> ueval_constraint c)"

definition ufilt :: "uconstr option \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "ufilt q X = Set.filter (uqok q) X"

lemma uqok_None[simp]: "uqok None = (\<lambda>_. True)"
  by (simp add: uqok_def)

lemma ufilt_None[simp]: "ufilt None = id"
  by (simp add: ufilt_def fun_eq_iff)

lemma ufilt_Some: "ufilt (Some c) X = Set.filter (ueval_constraint c) X"
  by (simp add: ufilt_def uqok_def)

lemma ufilt_idem[simp]: "ufilt q (ufilt q X) = ufilt q X"
  by (auto simp: ufilt_def)

text \<open>The result writes the aggregate into each group and keeps what passes the node's guard.
  The fused form walks the mapping's entries -- the key and its value together, so no lookup --
  and inserts the node's own tuple straight into the answer.\<close>

definition ugmr :: "(event_data list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ('b \<Rightarrow> event_data) \<Rightarrow>
    (event_data list, 'b) mapping \<Rightarrow> event_data list set" where
  "ugmr q p f m = Set.filter q (gmr p (\<lambda>x. x) f m)"

lemma fold_insert_image:
  "fold (\<lambda>x A. let v = g x in if q v then Set.insert v A else A) xs A
   = Set.filter q (g ` set xs) \<union> A"
  by (induct xs arbitrary: A) (auto simp: Let_def)

lemma ugmr_code[code]:
  fixes t :: "(event_data list, 'b) mapping_rbt"
  shows "ugmr q p f (RBT_Mapping t) =
    (case ID CCOMPARE(event_data list) of
       None \<Rightarrow> Code.abort (STR ''ugmr RBT_Mapping: ccompare = None'')
                (\<lambda>_. ugmr q p f (RBT_Mapping t))
     | Some _ \<Rightarrow> fold (\<lambda>e A. let v = take p (fst e) @ f (snd e) # drop p (fst e)
                    in if q v then Set.insert v A else A)
                  (RBT_Mapping2.entries t) {})"
proof (cases "ID CCOMPARE(event_data list)")
  case (Some c)
  note comp = ID_ccompare'[OF Some]
  have dist: "distinct (map fst (RBT_Mapping2.entries t))"
    using Some by (transfer fixing: c)
      (simp add: ord.is_rbt_def linorder.distinct_entries[OF comparator.linorder[OF comp]])
  have mo: "map_of (RBT_Mapping2.entries t) (fst e) = Some (snd e)"
    if "e \<in> set (RBT_Mapping2.entries t)" for e
    using dist that by (cases e) simp
  have lk: "Mapping.lookup (RBT_Mapping t) = map_of (RBT_Mapping2.entries t)"
    by (simp add: lookup_Mapping_code(1) Some del: RBT_Mapping_def)
  have ky: "Mapping.keys (RBT_Mapping t) = fst ` set (RBT_Mapping2.entries t)"
    unfolding Mapping.keys_dom_lookup lk by (rule dom_map_of_conv_image_fst)
  have "ugmr q p f (RBT_Mapping t)
      = Set.filter q ((\<lambda>e. take p (fst e) @ f (snd e) # drop p (fst e))
          ` set (RBT_Mapping2.entries t))"
    unfolding ugmr_def gmr_def ky lk image_image
    by (intro arg_cong[of _ _ "Set.filter q"] image_cong[OF refl]) (simp add: mo)
  then show ?thesis using Some by (simp add: fold_insert_image)
qed simp

definition ugres :: "(event_data list \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> ugagg \<Rightarrow>
    event_data list set" where
  "ugres q g0 \<omega> p a = Set.filter q (gres g0 \<omega> p (\<lambda>x. x) a)"

lemma ugres_code[code]:
  "ugres q g0 \<omega> p a = (case a of
     GCnt m \<Rightarrow> (if g0 \<and> Mapping.is_empty m then Set.filter q {[eval_agg_op \<omega> {}]}
       else ugmr q p (\<lambda>k. EInt (integer_of_int k)) m)
   | GSum m \<Rightarrow> (if g0 \<and> Mapping.is_empty m then Set.filter q {[eval_agg_op \<omega> {}]}
       else (case fst \<omega> of
         Formula.Agg_Sum \<Rightarrow> ugmr q p (\<lambda>k. EInt (snd k)) m
       | Formula.Agg_Avg \<Rightarrow> ugmr q p
           (\<lambda>k. EFloat (double_of_event_data (EInt (snd k)) / double_of_int (fst k))) m
       | _ \<Rightarrow> {}))
   | GRank m ty \<Rightarrow> (if g0 \<and> Mapping.is_empty m then Set.filter q {[eval_agg_op \<omega> {}]}
       else (case fst \<omega> of
         Formula.Agg_Min \<Rightarrow> ugmr q p (\<lambda>k. get_edata_list k 0) m
       | Formula.Agg_Max \<Rightarrow> ugmr q p (\<lambda>k. get_edata_list k (get_length k - 1)) m
       | Formula.Agg_Med \<Rightarrow> ugmr q p (\<lambda>k. let u = get_length k; u' = u div 2;
           aggval = (if even u
             then (double_of_event_data_agg (get_edata_list k (u' - 1))
                   + double_of_event_data_agg (get_edata_list k u')) / double_of_int 2
             else double_of_event_data_agg (get_edata_list k u'))
           in EFloat aggval) m
       | _ \<Rightarrow> {})))"
  by (cases a) (simp_all add: ugres_def ugmr_def Mapping.is_empty_def
      split: Formula.agg_type.splits)

definition uag_res :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> ucnt \<Rightarrow>
    ugagg option \<Rightarrow> event_data list set" where
  "uag_res q p w c ax = ufilt q (case ax of
     None \<Rightarrow> eagg_p p (Mapping.keys c)
   | Some a \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gres g0 \<omega> pos (\<lambda>x. x) a))"

lemma uag_res_code[code]:
  "uag_res q p w c ax = (case ax of
     None \<Rightarrow> ufilt q (eagg_p p (Mapping.keys c))
   | Some a \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> ugres (uqok q) g0 \<omega> pos a))"
  by (simp add: uag_res_def ugres_def ufilt_def split: option.splits prod.splits)

lemma ag_res_ucc: "ufilt q (ag_res p w (ucc c) ax) = uag_res q p w c ax"
  by (cases ax; cases p) (simp_all add: uag_res_def ag_res_def ucc.simps id_def)

lemma ag_res_ucc_None[simp]: "ag_res p w (ucc c) ax = uag_res None p w c ax"
  using ag_res_ucc[of None] by simp

end

(*<*)
theory Optimized_Since_Imp
  imports "MFODL_Monitor_Devel.Imperative_Join"
begin
(*>*)

section \<open>Imperative refinement of the Since structure\<close>

subsection \<open>Loops over hash maps\<close>

partial_function (heap) hm_kv_rec where [code]:
  "hm_kv_rec it acc = do {
     b \<leftarrow> hm_it_has_next it;
     if b then do { (kv, it') \<leftarrow> hm_it_next it; hm_kv_rec it' (kv # acc) } else return acc }"

lemma hm_is_it_finite: "hm_is_it m ht m' it \<Longrightarrow>\<^sub>A hm_is_it m ht m' it * \<up>(finite (dom m'))"
  unfolding hm_is_it_def by (sep_auto simp: finite_dom_map_of)

lemma map_of_step: "m' k = Some v \<Longrightarrow> (map_of acc ++ m' |` (- {k}))(k \<mapsto> v) = map_of acc ++ m'"
  by (auto simp: fun_eq_iff map_add_def restrict_map_def split: option.splits)

lemma dom_step: "m' k = Some v \<Longrightarrow> Set.insert k (dom m' - {k} \<union> S) = dom m' \<union> S"
  by auto

lemma hm_kv_rec_rule_aux:
  "finite (dom m') \<Longrightarrow> <hm_is_it m ht m' it> hm_kv_rec it acc
    <\<lambda>r. is_hashmap m ht * \<up>(map_of r = map_of acc ++ m' \<and> set (map fst r) = dom m' \<union> set (map fst acc))>\<^sub>t"
proof (induction "card (dom m')" arbitrary: m' it acc rule: less_induct)
  case less
  show ?case
  proof (cases "m' = Map.empty")
    case True
    then show ?thesis
      apply (subst hm_kv_rec.simps)
      apply sep_auto
      apply (rule ent_frame_fwd[OF hm_it_finish])
      apply frame_inference
      apply solve_entails
      done
  next
    case False
    have IH: "<hm_is_it m ht (m' |` (- {k})) it'> hm_kv_rec it' acc'
      <\<lambda>r. is_hashmap m ht * \<up>(map_of r = map_of acc' ++ (m' |` (- {k})) \<and>
         set (map fst r) = dom (m' |` (- {k})) \<union> set (map fst acc'))>\<^sub>t"
      if "m' k = Some v" for k v it' acc'
    proof (rule less.hyps)
      have kin: "k \<in> dom m'" using that by auto
      have eq: "dom (m' |` (- {k})) = dom m' - {k}" by (auto simp: dom_restrict)
      show "card (dom (m' |` (- {k}))) < card (dom m')"
        unfolding eq using less.prems kin by (rule card_Diff1_less)
      show "finite (dom (m' |` (- {k})))" using less.prems by (simp add: dom_restrict)
    qed
    show ?thesis
      apply (subst hm_kv_rec.simps)
      apply (sep_auto heap: IH simp: False dom_restrict map_of_step dom_step)
      done
  qed
qed

lemma hm_kv_rec_rule:
  "<hm_is_it m ht m' it> hm_kv_rec it acc
    <\<lambda>r. is_hashmap m ht * \<up>(map_of r = map_of acc ++ m' \<and> set (map fst r) = dom m' \<union> set (map fst acc))>\<^sub>t"
  by (rule cons_pre_rule[OF hm_is_it_finite]) (sep_auto heap: hm_kv_rec_rule_aux)

definition hm_to_list :: "('k::{heap,hashable}, 'v::heap) hashtable \<Rightarrow> ('k \<times> 'v) list Heap" where
  "hm_to_list ht = do { it \<leftarrow> hm_it_init ht; hm_kv_rec it [] }"

lemma hm_to_list_rule:
  "<is_hashmap m ht> hm_to_list ht <\<lambda>l. is_hashmap m ht * \<up>(map_of l = m \<and> set (map fst l) = dom m)>\<^sub>t"
  unfolding hm_to_list_def by (sep_auto heap: hm_kv_rec_rule)

text \<open>Deleting the keys of a list that fail a predicate.\<close>

definition del_map :: "('k \<Rightarrow> bool) \<Rightarrow> 'k list \<Rightarrow> ('k \<rightharpoonup> 'v) \<Rightarrow> ('k \<rightharpoonup> 'v)" where
  "del_map P ks m = (\<lambda>k. if k \<in> set ks \<and> \<not> P k then None else m k)"

lemma del_map_Nil[simp]: "del_map P [] m = m"
  by (simp add: del_map_def)

lemma del_map_Cons[simp]: "del_map P (k # ks) m = (if P k then del_map P ks m else del_map P ks (m |` (- {k})))"
  by (auto simp: del_map_def fun_eq_iff restrict_map_def)

fun del_loop :: "('k \<Rightarrow> bool) \<Rightarrow> 'k list \<Rightarrow> ('k::{heap,hashable}, 'v::heap) hashtable \<Rightarrow> ('k, 'v) hashtable Heap" where
  "del_loop P [] h = return h"
| "del_loop P (k # ks) h = (if P k then del_loop P ks h else do { h \<leftarrow> hm_delete k h; del_loop P ks h })"

lemma del_loop_rule: "<is_hashmap m h> del_loop P ks h <is_hashmap (del_map P ks m)>\<^sub>t"
proof (induction ks arbitrary: m h)
  case Nil
  show ?case by sep_auto
next
  case (Cons k ks)
  show ?case by (sep_auto heap: Cons.IH)
qed

text \<open>Expiring the tuples of a table (@{const filter_set}): a tuple is removed if its entry is the
  expiring time stamp; the removed tuples are collected.\<close>

definition fmap :: "'v \<Rightarrow> 'k list \<Rightarrow> ('k \<rightharpoonup> 'v) \<Rightarrow> ('k \<rightharpoonup> 'v)" where
  "fmap t xs m = (\<lambda>k. if k \<in> set xs \<and> m k = Some t then None else m k)"

definition fset :: "'v \<Rightarrow> 'k list \<Rightarrow> ('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> 'k set" where
  "fset t xs m Y = Y \<union> {k \<in> set xs. m k = Some t}"

lemma fmap_Nil[simp]: "fmap t [] m = m"
  by (simp add: fmap_def)

lemma fset_Nil[simp]: "fset t [] m Y = Y"
  by (simp add: fset_def)

lemma fmap_Cons[simp]: "fmap t (x # xs) m = (if m x = Some t then fmap t xs (m |` (- {x})) else fmap t xs m)"
  by (auto simp: fmap_def fun_eq_iff restrict_map_def)

lemma fset_Cons[simp]: "fset t (x # xs) m Y = (if m x = Some t then fset t xs (m |` (- {x})) (Set.insert x Y) else fset t xs m Y)"
  by (auto simp: fset_def restrict_map_def)

fun filter_loop :: "'v \<Rightarrow> 'k list \<Rightarrow> ('k::{heap,hashable}, 'v::heap) hashtable \<Rightarrow> 'k set \<Rightarrow> (('k, 'v) hashtable \<times> 'k set) Heap" where
  "filter_loop t [] h Y = return (h, Y)"
| "filter_loop t (x # xs) h Y = do {
     v \<leftarrow> hm_lookup x h;
     if v = Some t then do { h \<leftarrow> hm_delete x h; filter_loop t xs h (Set.insert x Y) } else filter_loop t xs h Y }"

lemma filter_loop_rule:
  "<is_hashmap m h> filter_loop t xs h Y <\<lambda>r. is_hashmap (fmap t xs m) (fst r) * \<up>(snd r = fset t xs m Y)>\<^sub>t"
proof (induction xs arbitrary: m h Y)
  case Nil
  show ?case by sep_auto
next
  case (Cons x xs)
  show ?case by (sep_auto heap: Cons.IH)
qed

text \<open>Moving the tuples of a table into the window (@{const upd_set_keys}): a tuple whose entry in
  @{text tuple_since} is at most the table's time stamp gets the time stamp as its entry.\<close>

definition valid_k :: "('k \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> 'k \<Rightarrow> bool" where
  "valid_k ms t k = (case ms k of None \<Rightarrow> False | Some t' \<Rightarrow> t' \<le> t)"

definition umap :: "('k \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> 'k list \<Rightarrow> ('k \<rightharpoonup> nat) \<Rightarrow> ('k \<rightharpoonup> nat)" where
  "umap ms t xs m = (\<lambda>k. if k \<in> set xs \<and> valid_k ms t k then Some t else m k)"

definition uset :: "('k \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> 'k list \<Rightarrow> 'k set \<Rightarrow> 'k set" where
  "uset ms t xs Y = Y \<union> {k \<in> set xs. valid_k ms t k}"

lemma umap_Nil[simp]: "umap ms t [] m = m"
  by (simp add: umap_def)

lemma uset_Nil[simp]: "uset ms t [] Y = Y"
  by (simp add: uset_def)

lemma umap_Cons[simp]: "umap ms t (x # xs) m = (if valid_k ms t x then umap ms t xs (m(x \<mapsto> t)) else umap ms t xs m)"
  by (auto simp: umap_def fun_eq_iff)

lemma uset_Cons[simp]: "uset ms t (x # xs) Y = (if valid_k ms t x then uset ms t xs (Set.insert x Y) else uset ms t xs Y)"
  by (auto simp: uset_def)

fun upd_loop :: "nat \<Rightarrow> 'k list \<Rightarrow> ('k::{heap,hashable}, nat) hashtable \<Rightarrow> ('k, nat) hashtable \<Rightarrow> 'k set \<Rightarrow>
  (('k, nat) hashtable \<times> 'k set) Heap" where
  "upd_loop t [] hs h Y = return (h, Y)"
| "upd_loop t (x # xs) hs h Y = do {
     v \<leftarrow> hm_lookup x hs;
     if (case v of None \<Rightarrow> False | Some t' \<Rightarrow> t' \<le> t) then do { h \<leftarrow> hm_update x t h; upd_loop t xs hs h (Set.insert x Y) }
     else upd_loop t xs hs h Y }"

lemma upd_loop_rule:
  "<is_hashmap ms hs * is_hashmap m h> upd_loop t xs hs h Y
   <\<lambda>r. is_hashmap ms hs * is_hashmap (umap ms t xs m) (fst r) * \<up>(snd r = uset ms t xs Y)>\<^sub>t"
proof (induction xs arbitrary: m h Y)
  case Nil
  show ?case by sep_auto
next
  case (Cons x xs)
  show ?case by (sep_auto heap: Cons.IH simp: valid_k_def split: option.splits)
qed

text \<open>Inserting the tuples of a table with a time stamp (@{const upd_set}).\<close>

definition imap :: "nat \<Rightarrow> 'k list \<Rightarrow> ('k \<rightharpoonup> nat) \<Rightarrow> ('k \<rightharpoonup> nat)" where
  "imap t xs m = (\<lambda>k. if k \<in> set xs then Some t else m k)"

lemma imap_Nil[simp]: "imap t [] m = m"
  by (simp add: imap_def)

lemma imap_Cons[simp]: "imap t (x # xs) m = imap t xs (m(x \<mapsto> t))"
  by (auto simp: imap_def fun_eq_iff)

fun ins_loop :: "nat \<Rightarrow> 'k list \<Rightarrow> ('k::{heap,hashable}, nat) hashtable \<Rightarrow> ('k, nat) hashtable Heap" where
  "ins_loop t [] h = return h"
| "ins_loop t (x # xs) h = do { h \<leftarrow> hm_update x t h; ins_loop t xs h }"

lemma ins_loop_rule: "<is_hashmap m h> ins_loop t xs h <is_hashmap (imap t xs m)>\<^sub>t"
proof (induction xs arbitrary: m h)
  case Nil
  show ?case by sep_auto
next
  case (Cons x xs)
  show ?case by (sep_auto heap: Cons.IH)
qed

text \<open>Registering new tuples (@{const add_new_table_mmsaux}): a tuple without an entry gets the
  current time stamp; those tuples are collected.\<close>

definition smap :: "nat \<Rightarrow> 'k list \<Rightarrow> ('k \<rightharpoonup> nat) \<Rightarrow> ('k \<rightharpoonup> nat)" where
  "smap t xs m = (\<lambda>k. if k \<in> set xs \<and> m k = None then Some t else m k)"

definition sset :: "nat \<Rightarrow> 'k list \<Rightarrow> ('k \<rightharpoonup> nat) \<Rightarrow> 'k set \<Rightarrow> 'k set" where
  "sset t xs m Y = Y \<union> {k \<in> set xs. m k = None}"

lemma smap_Nil[simp]: "smap t [] m = m"
  by (simp add: smap_def)

lemma sset_Nil[simp]: "sset t [] m Y = Y"
  by (simp add: sset_def)

lemma smap_Cons[simp]: "smap t (x # xs) m = (if m x = None then smap t xs (m(x \<mapsto> t)) else smap t xs m)"
  by (auto simp: smap_def fun_eq_iff)

lemma sset_Cons[simp]: "sset t (x # xs) m Y = (if m x = None then sset t xs (m(x \<mapsto> t)) (Set.insert x Y) else sset t xs m Y)"
  by (auto simp: sset_def)

fun since_loop :: "nat \<Rightarrow> 'k list \<Rightarrow> ('k::{heap,hashable}, nat) hashtable \<Rightarrow> 'k set \<Rightarrow> (('k, nat) hashtable \<times> 'k set) Heap" where
  "since_loop t [] h Y = return (h, Y)"
| "since_loop t (x # xs) h Y = do {
     v \<leftarrow> hm_lookup x h;
     if v = None then do { h \<leftarrow> hm_update x t h; since_loop t xs h (Set.insert x Y) } else since_loop t xs h Y }"

lemma since_loop_rule:
  "<is_hashmap m h> since_loop t xs h Y <\<lambda>r. is_hashmap (smap t xs m) (fst r) * \<up>(snd r = sset t xs m Y)>\<^sub>t"
proof (induction xs arbitrary: m h Y)
  case Nil
  show ?case by sep_auto
next
  case (Cons x xs)
  show ?case by (sep_auto heap: Cons.IH)
qed

subsection \<open>The structure\<close>

text \<open>
  The heap holds the two tuple-keyed mappings of the Since structure as hash maps; the
  remaining components (time stamps, masks, the two queues of tables and the result table) are
  pure values carried alongside. The assertion relates the structure to a pure @{typ "'a mmsaux"}
  whose index components (@{text wf_table_in}, @{text wf_table_since}) are left unconstrained:
  they are not consulted by the operations when there are no join columns or when all columns
  are join columns, the two cases this structure implements.
\<close>

type_synonym 'a mmsaux_core = "ts \<times> ts \<times> bool list \<times> bool list \<times> (ts \<times> 'a table) queue \<times> (ts \<times> 'a table) queue \<times> 'a table"
type_synonym 'a msaux_imp = "'a mmsaux_core \<times> ('a tuple, ts) hashtable \<times> ('a tuple, ts) hashtable"

fun finite_core :: "'a mmsaux_core \<Rightarrow> bool" where
  "finite_core (t, gc, mL, mR, dp, di, tin) \<longleftrightarrow>
     (\<forall>X \<in> snd ` set (linearize dp). finite X) \<and> (\<forall>X \<in> snd ` set (linearize di). finite X) \<and> finite tin"

definition special_args :: "args \<Rightarrow> bool" where
  "special_args args \<longleftrightarrow> args_L args = {} \<or> args_L args = args_R args"

text \<open>
  In these cases the index components of the pure structure are determined by the mappings
  (@{const wf_table} equality is extensional), so the assertion fixes them; the pure
  structure can then be reconstructed exactly from the heap structure.
\<close>

abbreviation wf_keys :: "args \<Rightarrow> (event_data tuple, ts) mapping \<Rightarrow> event_data wf_table" where
  "wf_keys args m \<equiv> wf_table_of_keys (args_n args) (args_R args) m"

fun is_msaux :: "args \<Rightarrow> event_data mmsaux \<Rightarrow> event_data msaux_imp \<Rightarrow> assn" where
  "is_msaux args (t, gc, mL, mR, dp, di, tin, wfin, tuple_in, wfsince, tuple_since) (c, hin, hsince) =
    \<up>(c = (t, gc, mL, mR, dp, di, tin) \<and> special_args args \<and> mL = join_mask (args_n args) (args_L args) \<and>
      finite_core c \<and> wfin = wf_keys args tuple_in \<and> wfsince = wf_keys args tuple_since)
    * is_hashmap (Mapping.lookup tuple_in) hin * is_hashmap (Mapping.lookup tuple_since) hsince"

lemma wf_table_upd_special: "special_args args \<Longrightarrow> wf_table_upd args m w = wf_keys args m"
  by (simp add: wf_table_upd_def special_args_def)

lemma wf_table_of_set_args_empty: "wf_table_of_set_args args {} = wf_keys args Mapping.empty"
  by (rule wf_table_eqI) (auto simp: wf_table_sig_args wf_table_of_set_args wf_table_set_of_keys table_def)

lemma join_mask_empty: "\<forall>i \<in> set (join_mask n {}). \<not> i"
  by (simp add: join_mask_def)

subsection \<open>Bridging lemmas: the pure fold steps as functions of the tuple lists\<close>

lemma filter_set_lookup:
  fixes X :: "event_data table"
  assumes "finite X"
  shows "Mapping.lookup (fst (filter_set (t, X) (m, Y))) = fmap t (csorted_list_of_set X) (Mapping.lookup m)"
    and "snd (filter_set (t, X) (m, Y)) = fset t (csorted_list_of_set X) (Mapping.lookup m) Y"
  unfolding filter_set.simps Let_def fst_conv snd_conv set_csorted_list_of_set_etuple[OF assms] fmap_def fset_def
  by (auto simp: Mapping.lookup_filter fun_eq_iff keys_dom_lookup dom_def split: option.splits)

lemma upd_set_keys_lookup:
  fixes X :: "event_data table"
  assumes "finite X"
  shows "Mapping.lookup (fst (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tsm (t, as)}) (t, X) (m, Y))) =
      umap (Mapping.lookup tsm) t (csorted_list_of_set X) (Mapping.lookup m)"
    and "snd (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tsm (t, as)}) (t, X) (m, Y)) =
      uset (Mapping.lookup tsm) t (csorted_list_of_set X) Y"
  unfolding upd_set_keys.simps fst_conv snd_conv set_csorted_list_of_set_etuple[OF assms] umap_def uset_def valid_k_def valid_tuple_def
  by (auto simp: Mapping_lookup_upd_set fun_eq_iff split: option.splits)

subsection \<open>Loops over the expiring and the moved tables\<close>

fun expire_loop :: "(ts \<times> event_data table) list \<Rightarrow> (event_data tuple, ts) hashtable \<Rightarrow> event_data table \<Rightarrow>
  ((event_data tuple, ts) hashtable \<times> event_data table) Heap" where
  "expire_loop [] h Y = return (h, Y)"
| "expire_loop ((t, X) # xs) h Y = do { r \<leftarrow> filter_loop t (csorted_list_of_set X) h Y; expire_loop xs (fst r) (snd r) }"

lemma expire_loop_rule:
  "\<forall>X \<in> snd ` set xs. finite X \<Longrightarrow>
   <is_hashmap (Mapping.lookup m) h> expire_loop xs h Y
   <\<lambda>r. is_hashmap (Mapping.lookup (fst (fold filter_set xs (m, Y)))) (fst r) * \<up>(snd r = snd (fold filter_set xs (m, Y)))>\<^sub>t"
proof (induction xs arbitrary: m Y h)
  case Nil
  show ?case by sep_auto
next
  case (Cons p xs)
  obtain t X where p: "p = (t, X)" by (cases p)
  have fin: "finite X" using Cons.prems p by auto
  note IH = Cons.IH[where m = "fst (filter_set (t, X) (m, Y))" and Y = "snd (filter_set (t, X) (m, Y))", unfolded prod.collapse,
    unfolded filter_set_lookup[OF fin]]
  show ?case unfolding p using Cons.prems by (sep_auto heap: filter_loop_rule IH)
qed

fun move_loop :: "(ts \<times> event_data table) list \<Rightarrow> (event_data tuple, ts) hashtable \<Rightarrow> (event_data tuple, ts) hashtable \<Rightarrow>
  event_data table \<Rightarrow> ((event_data tuple, ts) hashtable \<times> event_data table) Heap" where
  "move_loop [] hs h Y = return (h, Y)"
| "move_loop ((t, X) # xs) hs h Y = do { r \<leftarrow> upd_loop t (csorted_list_of_set X) hs h Y; move_loop xs hs (fst r) (snd r) }"

lemma move_loop_rule:
  "\<forall>X \<in> snd ` set xs. finite X \<Longrightarrow>
   <is_hashmap (Mapping.lookup tsm) hs * is_hashmap (Mapping.lookup m) h> move_loop xs hs h Y
   <\<lambda>r. is_hashmap (Mapping.lookup tsm) hs *
      is_hashmap (Mapping.lookup (fst (fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tsm (t, as)})) xs (m, Y)))) (fst r) *
      \<up>(snd r = snd (fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tsm (t, as)})) xs (m, Y)))>\<^sub>t"
proof (induction xs arbitrary: m Y h)
  case Nil
  show ?case by sep_auto
next
  case (Cons p xs)
  obtain t X where p: "p = (t, X)" by (cases p)
  have fin: "finite X" using Cons.prems p by auto
  note IH = Cons.IH[where m = "fst (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tsm (t, as)}) (t, X) (m, Y))"
    and Y = "snd (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tsm (t, as)}) (t, X) (m, Y))", unfolded prod.collapse,
    unfolded upd_set_keys_lookup[OF fin]]
  show ?case unfolding p using Cons.prems by (sep_auto heap: upd_loop_rule IH)
qed

subsection \<open>Operations\<close>

lemma lookup_Mapping_empty: "Mapping.lookup Mapping.empty = Map.empty"
  by (simp add: fun_eq_iff Mapping.lookup_empty)

definition init_imp :: "args \<Rightarrow> event_data msaux_imp Heap" where
  "init_imp args = do { hin \<leftarrow> hm_new; hsince \<leftarrow> hm_new;
     return ((0, 0, join_mask (args_n args) (args_L args), join_mask (args_n args) (args_R args),
       empty_queue, empty_queue, {}), hin, hsince) }"

lemma init_imp_rule:
  assumes "special_args args"
  shows "<emp> init_imp args <is_msaux args (init_mmsaux args)>\<^sub>t"
  unfolding init_imp_def init_mmsaux.simps wf_table_of_set_args_def[symmetric] using assms
  by (sep_auto simp: empty_queue_rep lookup_Mapping_empty wf_table_of_set_args_empty)

definition shift_end_imp :: "args \<Rightarrow> ts \<Rightarrow> event_data msaux_imp \<Rightarrow> event_data msaux_imp Heap" where
  "shift_end_imp args nt q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    let I = args_ivl args;
        dp' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) dp;
        p = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) di
    in do { r \<leftarrow> expire_loop (snd p) hin {};
            return ((t, gc, mL, mR, dp', fst p, tin - snd r), fst r, hsince) })"

lemma finite_fold_filter_set: "finite Y \<Longrightarrow> \<forall>X \<in> snd ` set xs. finite X \<Longrightarrow> finite (snd (fold filter_set xs (m, Y)))"
proof (induction xs arbitrary: m Y)
  case (Cons p xs)
  obtain t X where p: "p = (t, X)" by (cases p)
  have "snd (filter_set (t, X) (m, Y)) \<subseteq> Y \<union> X"
    using filter_set_sub[of t X m Y "fst (filter_set (t, X) (m, Y))" "snd (filter_set (t, X) (m, Y))"] by simp
  then have "finite (snd (filter_set (t, X) (m, Y)))"
    using Cons.prems p by (auto intro: finite_subset)
  then show ?case unfolding p
    using Cons.IH[where m = "fst (filter_set (t, X) (m, Y))" and Y = "snd (filter_set (t, X) (m, Y))"] Cons.prems by simp
qed simp

lemma shift_end_imp_rule_aux:
  fixes tin_m ts_m :: "(event_data tuple, ts) mapping"
  assumes sp: "special_args args" and mask: "mL = join_mask (args_n args) (args_L args)"
    and fc: "finite_core (t, gc, mL, mR, dp, di, tin)"
    and wf: "wfin = wf_keys args tin_m" "wfsince = wf_keys args ts_m"
  shows "<is_hashmap (Mapping.lookup tin_m) hin * is_hashmap (Mapping.lookup ts_m) hsince>
    shift_end_imp args nt ((t, gc, mL, mR, dp, di, tin), hin, hsince)
    <is_msaux args (shift_end args nt (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m))>\<^sub>t"
proof -
  define P :: "ts \<times> event_data table \<Rightarrow> bool" where "P = (\<lambda>(t, X). \<not> memR (args_ivl args) (nt - t))"
  define dp' where "dp' = dropWhile_queue P dp"
  obtain di' discard where p: "takedropWhile_queue P di = (di', discard)" by (cases "takedropWhile_queue P di")
  obtain tin_m' del where f: "fold filter_set discard (tin_m, {}) = (tin_m', del)" by (cases "fold filter_set discard (tin_m, {})")
  have discard: "discard = takeWhile P (linearize di)" and di': "di' = dropWhile_queue P di"
    using p takedropWhile_queue_snd[of P di] takedropWhile_queue_fst[of P di] by auto
  have fin: "\<forall>X \<in> snd ` set discard. finite X"
    using fc unfolding finite_core.simps discard by (auto dest: set_takeWhileD)
  have fin': "finite_core (t, gc, mL, mR, dp', di', tin - del)"
    using fc unfolding finite_core.simps di' dp'_def dropWhile_queue_rep by (auto dest: set_dropWhileD)
  show ?thesis
    unfolding shift_end_imp_def shift_end.simps prod.case Let_def P_def[symmetric] dp'_def[symmetric] p f
    by (sep_auto heap: expire_loop_rule[OF fin] simp: f sp mask wf fin'[unfolded finite_core.simps] wf_table_upd_special[OF sp])
qed

lemma shift_end_imp_rule: "<is_msaux args s q> shift_end_imp args nt q <is_msaux args (shift_end args nt s)>\<^sub>t"
proof -
  obtain t gc mL mR dp di tin wfin tin_m wfsince ts_m where s:
    "s = (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m)" by (cases s) auto
  obtain c hin hsince where q: "q = (c, hin, hsince)" by (cases q)
  show ?thesis unfolding s q is_msaux.simps by (sep_auto heap: shift_end_imp_rule_aux)
qed

definition add_new_ts_imp' :: "args \<Rightarrow> ts \<Rightarrow> event_data msaux_imp \<Rightarrow> event_data msaux_imp Heap" where
  "add_new_ts_imp' args nt q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    let I = args_ivl args;
        p = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) dp;
        di' = fold append_queue (snd p) di
    in do { r \<leftarrow> move_loop (snd p) hsince hin {};
            return ((nt, gc, mL, mR, fst p, di', tin \<union> snd r), fst r, hsince) })"

lemma linearize_fold_append: "linearize (fold append_queue xs q) = linearize q @ xs"
  by (induction xs arbitrary: q) (auto simp: append_queue_rep)

lemma fold_append_queue_eta[simp]: "fold (\<lambda>(t, X) di. append_queue (t, X) di) = fold append_queue"
  by (intro ext) (simp add: fun_eq_iff split_beta cong: fold_cong)

lemma finite_fold_upd_set_keys:
  "finite Y \<Longrightarrow> \<forall>X \<in> snd ` set xs. finite X \<Longrightarrow>
   finite (snd (fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tsm (t, as)})) xs (m, Y)))"
proof (induction xs arbitrary: m Y)
  case (Cons p xs)
  obtain t X where p: "p = (t, X)" by (cases p)
  have "finite (snd (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tsm (t, as)}) (t, X) (m, Y)))"
    using Cons.prems p by (auto simp: upd_set_keys.simps)
  then show ?case unfolding p
    using Cons.IH[where m = "fst (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tsm (t, as)}) (t, X) (m, Y))"
      and Y = "snd (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tsm (t, as)}) (t, X) (m, Y))"] Cons.prems by simp
qed simp

lemma add_new_ts_imp'_rule_aux:
  fixes tin_m ts_m :: "(event_data tuple, ts) mapping"
  assumes sp: "special_args args" and mask: "mL = join_mask (args_n args) (args_L args)"
    and fc: "finite_core (t, gc, mL, mR, dp, di, tin)"
    and wf: "wfin = wf_keys args tin_m" "wfsince = wf_keys args ts_m"
  shows "<is_hashmap (Mapping.lookup tin_m) hin * is_hashmap (Mapping.lookup ts_m) hsince>
    add_new_ts_imp' args nt ((t, gc, mL, mR, dp, di, tin), hin, hsince)
    <is_msaux args (add_new_ts_mmsaux' args nt (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m))>\<^sub>t"
proof -
  define P :: "ts \<times> event_data table \<Rightarrow> bool" where "P = (\<lambda>(t, X). memL (args_ivl args) (nt - t))"
  obtain dp' move where p: "takedropWhile_queue P dp = (dp', move)" by (cases "takedropWhile_queue P dp")
  obtain tin_m' add where f: "fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple ts_m (t, as)})) move (tin_m, {}) = (tin_m', add)"
    by (cases "fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple ts_m (t, as)})) move (tin_m, {})")
  have move: "move = takeWhile P (linearize dp)" and dp': "dp' = dropWhile_queue P dp"
    using p takedropWhile_queue_snd[of P dp] takedropWhile_queue_fst[of P dp] by auto
  have fin: "\<forall>X \<in> snd ` set move. finite X"
    using fc unfolding finite_core.simps move by (auto dest: set_takeWhileD)
  have fin_add: "finite add"
    using finite_fold_upd_set_keys[where Y = "{}" and xs = move and tsm = ts_m and m = tin_m, OF finite.emptyI fin]
    unfolding f snd_conv .
  have fin': "finite_core (nt, gc, mL, mR, dp', fold append_queue move di, tin \<union> add)"
    using fc fin fin_add unfolding finite_core.simps dp' dropWhile_queue_rep linearize_fold_append by (auto dest: set_dropWhileD)
  show ?thesis
    unfolding add_new_ts_imp'_def add_new_ts_mmsaux'.simps prod.case Let_def P_def[symmetric] p f fold_append_queue_eta
    by (sep_auto heap: move_loop_rule[OF fin] simp: f sp mask wf fin_add fc[unfolded finite_core.simps] fin'[unfolded finite_core.simps]
        wf_table_upd_special[OF sp])
qed

lemma add_new_ts_imp'_rule: "<is_msaux args s q> add_new_ts_imp' args nt q <is_msaux args (add_new_ts_mmsaux' args nt s)>\<^sub>t"
proof -
  obtain t gc mL mR dp di tin wfin tin_m wfsince ts_m where s:
    "s = (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m)" by (cases s) auto
  obtain c hin hsince where q: "q = (c, hin, hsince)" by (cases q)
  show ?thesis unfolding s q is_msaux.simps by (sep_auto heap: add_new_ts_imp'_rule_aux)
qed

definition add_new_ts_imp :: "args \<Rightarrow> ts \<Rightarrow> event_data msaux_imp \<Rightarrow> event_data msaux_imp Heap" where
  "add_new_ts_imp args nt q = do { q \<leftarrow> shift_end_imp args nt q; add_new_ts_imp' args nt q }"

lemma add_new_ts_imp_rule: "<is_msaux args s q> add_new_ts_imp args nt q <is_msaux args (add_new_ts_mmsaux args nt s)>\<^sub>t"
  unfolding add_new_ts_imp_def add_new_ts_mmsaux_def
  by (sep_auto heap: shift_end_imp_rule add_new_ts_imp'_rule)

subsection \<open>Garbage collection and join\<close>

lemma del_map_filter: "set ks = dom (Mapping.lookup m) \<Longrightarrow>
  del_map P ks (Mapping.lookup m) = Mapping.lookup (Mapping.filter (\<lambda>k _. P k) m)"
  by (auto simp: del_map_def fun_eq_iff Mapping.lookup_filter dom_def split: option.splits)

lemma del_map_delete_set: "set ks = A \<Longrightarrow>
  del_map (\<lambda>k. k \<notin> A) ks (Mapping.lookup m) = Mapping.lookup (mapping_delete_set m A)"
  by (auto simp: del_map_def fun_eq_iff delete_set_lookup)

text \<open>An opaque copy of @{term join_cond}, so that the simplifier does not rewrite the condition
  differently in the program and in the specification.\<close>

definition jc :: "bool \<Rightarrow> 'a table \<Rightarrow> 'a tuple \<Rightarrow> bool" where
  "jc pos X k = join_cond pos X k"

lemma del_map_filter_join: "set ks = dom (Mapping.lookup m) \<Longrightarrow>
  del_map (jc pos X) ks (Mapping.lookup m) = Mapping.lookup (filter_join pos X m)"
  unfolding filter_join_def jc_def[abs_def] by (rule del_map_filter)

definition gc_imp :: "event_data msaux_imp \<Rightarrow> event_data msaux_imp Heap" where
  "gc_imp q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
     let all = fold (\<lambda>p acc. snd p \<union> acc) (linearize dp @ linearize di) {} in
     do { ks \<leftarrow> hm_to_list hsince;
          hsince' \<leftarrow> del_loop (\<lambda>k. k \<in> all) (map fst ks) hsince;
          return ((t, t, mL, mR, dp, di, tin), hin, hsince') })"

lemma gc_imp_rule_aux:
  fixes tin_m ts_m :: "(event_data tuple, ts) mapping"
  assumes sp: "special_args args" and mask: "mL = join_mask (args_n args) (args_L args)"
    and fc: "finite_core (t, gc, mL, mR, dp, di, tin)"
    and wf: "wfin = wf_keys args tin_m" "wfsince = wf_keys args ts_m"
  shows "<is_hashmap (Mapping.lookup tin_m) hin * is_hashmap (Mapping.lookup ts_m) hsince>
    gc_imp ((t, gc, mL, mR, dp, di, tin), hin, hsince)
    <is_msaux args (gc_mmsaux args (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m))>\<^sub>t"
proof -
  define all where "all = \<Union>(snd ` (set (linearize dp) \<union> set (linearize di)))"
  have all_fold: "fold (\<lambda>p acc. snd p \<union> acc) (linearize dp @ linearize di) {} = all"
    unfolding all_def Union_image_snd_fold[symmetric] by (simp add: image_Un)
  show ?thesis
    unfolding gc_imp_def gc_mmsaux.simps prod.case Let_def all_fold all_def[symmetric]
    by (sep_auto heap: hm_to_list_rule del_loop_rule simp: sp mask wf fc[unfolded finite_core.simps] del_map_filter
        wf_table_upd_special[OF sp])
qed

lemma gc_imp_rule: "<is_msaux args s q> gc_imp q <is_msaux args (gc_mmsaux args s)>\<^sub>t"
proof -
  obtain t gc mL mR dp di tin wfin tin_m wfsince ts_m where s:
    "s = (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m)" by (cases s) auto
  obtain c hin hsince where q: "q = (c, hin, hsince)" by (cases q)
  show ?thesis unfolding s q is_msaux.simps by (sep_auto heap: gc_imp_rule_aux)
qed

definition join_imp :: "args \<Rightarrow> event_data table \<Rightarrow> event_data msaux_imp \<Rightarrow> event_data msaux_imp Heap" where
  "join_imp args X q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    let pos = args_pos args in
    if (\<forall>i \<in> set mL. \<not> i) then
      (if (pos \<longleftrightarrow> replicate (length mL) None \<in> X) then return q
       else do { hin' \<leftarrow> hm_new; hsince' \<leftarrow> hm_new; return ((t, gc, mL, mR, dp, di, {}), hin', hsince') })
    else (let in_del = (if pos then tin - X else tin \<inter> X) in
      do { hin' \<leftarrow> del_loop (\<lambda>k. k \<notin> in_del) (csorted_list_of_set in_del) hin;
           ks \<leftarrow> hm_to_list hsince;
           hsince' \<leftarrow> del_loop (jc pos X) (map fst ks) hsince;
           return ((t, gc, mL, mR, dp, di, tin - in_del), hin', hsince') }))"

lemma join_imp_rule_aux:
  fixes tin_m ts_m :: "(event_data tuple, ts) mapping"
  assumes sp: "special_args args" and mask: "mL = join_mask (args_n args) (args_L args)"
    and fc: "finite_core (t, gc, mL, mR, dp, di, tin)"
    and wf: "wfin = wf_keys args tin_m" "wfsince = wf_keys args ts_m"
  shows "<is_hashmap (Mapping.lookup tin_m) hin * is_hashmap (Mapping.lookup ts_m) hsince>
    join_imp args X ((t, gc, mL, mR, dp, di, tin), hin, hsince)
    <is_msaux args (join_mmsaux args X (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m))>\<^sub>t"
proof (cases "\<forall>i \<in> set mL. \<not> i")
  case True
  show ?thesis
    unfolding join_imp_def join_mmsaux.simps prod.case Let_def if_P[OF True]
    by (sep_auto simp: sp mask wf fc[unfolded finite_core.simps] lookup_Mapping_empty wf_table_of_set_args_empty)
next
  case False
  then have LR: "args_L args = args_R args" using sp join_mask_empty[of "args_n args"] unfolding special_args_def mask by auto
  define in_del where "in_del = (if args_pos args then tin - X else tin \<inter> X)"
  have fin_del: "finite in_del" using fc unfolding finite_core.simps in_del_def by auto
  have set_del: "set (csorted_list_of_set in_del) = in_del" by (rule set_csorted_list_of_set_etuple[OF fin_del])
  have fin': "finite_core (t, gc, mL, mR, dp, di, tin - in_del)" using fc unfolding finite_core.simps by auto
  show ?thesis
    unfolding join_imp_def join_mmsaux.simps prod.case Let_def if_not_P[OF False] if_P[OF LR] in_del_def[symmetric]
      filter_join_def[symmetric]
    by (sep_auto heap: hm_to_list_rule del_loop_rule
        simp: sp mask wf fin'[unfolded finite_core.simps] del_map_filter_join del_map_delete_set[OF set_del]
        wf_table_upd_special[OF sp])
qed

lemma join_imp_rule: "<is_msaux args s q> join_imp args X q <is_msaux args (join_mmsaux args X s)>\<^sub>t"
proof -
  obtain t gc mL mR dp di tin wfin tin_m wfsince ts_m where s:
    "s = (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m)" by (cases s) auto
  obtain c hin hsince where q: "q = (c, hin, hsince)" by (cases q)
  show ?thesis unfolding s q is_msaux.simps by (sep_auto heap: join_imp_rule_aux)
qed

definition gc_join_imp :: "args \<Rightarrow> event_data table \<Rightarrow> event_data msaux_imp \<Rightarrow> event_data msaux_imp Heap" where
  "gc_join_imp args X q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    if \<not> memR (args_ivl args) (t - gc) then do { q \<leftarrow> gc_imp q; join_imp args X q } else join_imp args X q)"

lemma gc_join_imp_rule_aux:
  fixes tin_m ts_m :: "(event_data tuple, ts) mapping"
  assumes sp: "special_args args" and mask: "mL = join_mask (args_n args) (args_L args)"
    and fc: "finite_core (t, gc, mL, mR, dp, di, tin)"
    and wf: "wfin = wf_keys args tin_m" "wfsince = wf_keys args ts_m"
  shows "<is_hashmap (Mapping.lookup tin_m) hin * is_hashmap (Mapping.lookup ts_m) hsince>
    gc_join_imp args X ((t, gc, mL, mR, dp, di, tin), hin, hsince)
    <is_msaux args (gc_join_mmsaux args X (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m))>\<^sub>t"
  unfolding gc_join_imp_def gc_join_mmsaux.simps prod.case
  by (sep_auto heap: gc_imp_rule_aux[OF sp mask fc wf] join_imp_rule_aux[OF sp mask fc wf] join_imp_rule
      simp del: join_mmsaux.simps gc_mmsaux.simps)

lemma gc_join_imp_rule: "<is_msaux args s q> gc_join_imp args X q <is_msaux args (gc_join_mmsaux args X s)>\<^sub>t"
proof -
  obtain t gc mL mR dp di tin wfin tin_m wfsince ts_m where s:
    "s = (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m)" by (cases s) auto
  obtain c hin hsince where q: "q = (c, hin, hsince)" by (cases q)
  show ?thesis unfolding s q is_msaux.simps by (sep_auto heap: gc_join_imp_rule_aux)
qed

subsection \<open>Adding a table and reading the result\<close>

lemma smap_upd_set: "set xs = X \<Longrightarrow>
  smap t xs (Mapping.lookup m) = Mapping.lookup (upd_set m (\<lambda>_. t) (minus_keys X m))"
  by (auto simp: smap_def fun_eq_iff Mapping_lookup_upd_set minus_keys_def keys_dom_lookup dom_def)

lemma imap_upd_set: "set xs = X \<Longrightarrow> imap t xs (Mapping.lookup m) = Mapping.lookup (upd_set m (\<lambda>_. t) X)"
  by (auto simp: imap_def fun_eq_iff Mapping_lookup_upd_set)

definition add_new_table_imp :: "args \<Rightarrow> event_data table \<Rightarrow> event_data msaux_imp \<Rightarrow> event_data msaux_imp Heap" where
  "add_new_table_imp args X q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow>
    let xs = csorted_list_of_set X in
    do { r \<leftarrow> since_loop t xs hsince {};
         if memL (args_ivl args) 0 then do {
           hin' \<leftarrow> ins_loop t xs hin;
           return ((t, gc, mL, mR, dp, append_queue (t, X) di, tin \<union> X), hin', fst r) }
         else return ((t, gc, mL, mR, append_queue (t, X) dp, di, tin), hin, fst r) })"

lemma add_new_table_imp_rule_aux:
  fixes tin_m ts_m :: "(event_data tuple, ts) mapping"
  assumes sp: "special_args args" and mask: "mL = join_mask (args_n args) (args_L args)"
    and fc: "finite_core (t, gc, mL, mR, dp, di, tin)"
    and wf: "wfin = wf_keys args tin_m" "wfsince = wf_keys args ts_m" and fin: "finite X"
  shows "<is_hashmap (Mapping.lookup tin_m) hin * is_hashmap (Mapping.lookup ts_m) hsince>
    add_new_table_imp args X ((t, gc, mL, mR, dp, di, tin), hin, hsince)
    <is_msaux args (add_new_table_mmsaux args X (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m))>\<^sub>t"
proof -
  have set_xs: "set (csorted_list_of_set X) = X" by (rule set_csorted_list_of_set_etuple[OF fin])
  have fin1: "finite_core (t, gc, mL, mR, dp, append_queue (t, X) di, tin \<union> X)"
    and fin2: "finite_core (t, gc, mL, mR, append_queue (t, X) dp, di, tin)"
    using fc fin unfolding finite_core.simps append_queue_rep by auto
  show ?thesis
    unfolding add_new_table_imp_def add_new_table_mmsaux.simps prod.case Let_def
    by (sep_auto heap: since_loop_rule ins_loop_rule
        simp: sp mask wf fin fin1[unfolded finite_core.simps] fin2[unfolded finite_core.simps] smap_upd_set[OF set_xs]
        imap_upd_set[OF set_xs] wf_table_upd_special[OF sp])
qed

lemma add_new_table_imp_rule:
  "finite X \<Longrightarrow> <is_msaux args s q> add_new_table_imp args X q <is_msaux args (add_new_table_mmsaux args X s)>\<^sub>t"
proof -
  assume fin: "finite X"
  obtain t gc mL mR dp di tin wfin tin_m wfsince ts_m where s:
    "s = (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m)" by (cases s) auto
  obtain c hin hsince where q: "q = (c, hin, hsince)" by (cases q)
  show ?thesis unfolding s q is_msaux.simps by (sep_auto heap: add_new_table_imp_rule_aux[OF _ _ _ _ _ fin])
qed

definition result_imp :: "event_data msaux_imp \<Rightarrow> event_data table Heap" where
  "result_imp q = return (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow> tin)"

lemma result_imp_rule: "<is_msaux args s q> result_imp q <\<lambda>r. is_msaux args s q * \<up>(r = result_mmsaux args s)>\<^sub>t"
proof -
  obtain t gc mL mR dp di tin wfin tin_m wfsince ts_m where s:
    "s = (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m)" by (cases s) auto
  obtain c hin hsince where q: "q = (c, hin, hsince)" by (cases q)
  show ?thesis unfolding s q is_msaux.simps result_imp_def result_mmsaux.simps by sep_auto
qed

subsection \<open>The interface for the monitor: heap structure or pure structure\<close>

text \<open>
  The monitor uses the imperative structure for Since operators without aggregation whose
  join columns are none or all columns, and the pure aggregation-aware structure
  @{typ mmasaux} otherwise. A pure structure also results when an infinite table is added
  (which cannot happen for tables produced by the monitor, but is not excluded by the locale
  assumptions): the heap structure is then converted to the pure one.
\<close>

lemma mmasaux_None:
  assumes agg: "args_agg args = None"
  shows "init_mmasaux args = (init_mmsaux args, None)"
    "add_new_ts_mmasaux args nt (s, ag) = (add_new_ts_mmsaux args nt s, ag)"
    "gc_join_mmasaux args X (s, ag) = (gc_join_mmsaux args X s, ag)"
    "add_new_table_mmasaux args X (s, ag) = (add_new_table_mmsaux args X s, ag)"
    "result_mmasaux args (s, ag) = result_mmsaux args s"
proof -
  obtain t gc mL mR dp di tin wfin tin_m wfs ts_m where s: "s = (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfs, ts_m)"
    by (cases s) auto
  obtain t1 gc1 mL1 mR1 dp1 di1 tin1 wfin1 tin_m1 wfs1 ts_m1 where sh:
    "shift_end args nt (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfs, ts_m) = (t1, gc1, mL1, mR1, dp1, di1, tin1, wfin1, tin_m1, wfs1, ts_m1)"
    by (cases "shift_end args nt (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfs, ts_m)") auto
  obtain t2 gc2 mL2 mR2 dp2 di2 tin2 wfin2 tin_m2 wfs2 ts_m2 where g:
    "gc_mmsaux args (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfs, ts_m) = (t2, gc2, mL2, mR2, dp2, di2, tin2, wfin2, tin_m2, wfs2, ts_m2)"
    by (cases "gc_mmsaux args (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfs, ts_m)") auto
  show "init_mmasaux args = (init_mmsaux args, None)" using agg by simp
  show "add_new_ts_mmasaux args nt (s, ag) = (add_new_ts_mmsaux args nt s, ag)"
    unfolding s add_new_ts_mmasaux_def add_new_ts_mmsaux_def shift_end_mmasaux.simps agg option.case sh
      add_new_ts_mmasaux'.simps option.case ..
  show "gc_join_mmasaux args X (s, ag) = (gc_join_mmsaux args X s, ag)"
    unfolding s gc_join_mmasaux.simps gc_join_mmsaux.simps g join_mmasaux.simps agg option.case
    by (cases "memR (args_ivl args) (t - gc)") simp_all
  show "add_new_table_mmasaux args X (s, ag) = (add_new_table_mmsaux args X s, ag)"
    unfolding s add_new_table_mmasaux.simps Let_def agg option.case ..
  show "result_mmasaux args (s, ag) = result_mmsaux args s"
    unfolding s using agg by (cases ag) simp_all
qed

subsubsection \<open>Conversion to the pure structure\<close>

lemma of_alist_eq: "map_of l = Mapping.lookup m \<Longrightarrow> Mapping.of_alist l = m"
  by (rule mapping_eqI) (simp add: lookup_of_alist)

definition to_pure :: "args \<Rightarrow> event_data msaux_imp \<Rightarrow> event_data mmsaux Heap" where
  "to_pure args q = (case q of ((t, gc, mL, mR, dp, di, tin), hin, hsince) \<Rightarrow> do {
     l1 \<leftarrow> hm_to_list hin; l2 \<leftarrow> hm_to_list hsince;
     return (t, gc, mL, mR, dp, di, tin, wf_keys args (Mapping.of_alist l1), Mapping.of_alist l1,
       wf_keys args (Mapping.of_alist l2), Mapping.of_alist l2) })"

lemma to_pure_rule: "<is_msaux args s q> to_pure args q <\<lambda>r. \<up>(r = s)>\<^sub>t"
proof -
  obtain t gc mL mR dp di tin wfin tin_m wfsince ts_m where s:
    "s = (t, gc, mL, mR, dp, di, tin, wfin, tin_m, wfsince, ts_m)" by (cases s) auto
  obtain c hin hsince where q: "q = (c, hin, hsince)" by (cases q)
  show ?thesis unfolding s q is_msaux.simps to_pure_def
    by (sep_auto heap: hm_to_list_rule simp: of_alist_eq)
qed

subsubsection \<open>The sum type and its operations\<close>

datatype msaux_h = MSH_imp "event_data msaux_imp" | MSH_pure mmasaux

fun is_msaux_h :: "args \<Rightarrow> mmasaux \<Rightarrow> msaux_h \<Rightarrow> assn" where
  "is_msaux_h args s (MSH_imp q) = is_msaux args (fst s) q * \<up>(args_agg args = None \<and> snd s = None)"
| "is_msaux_h args s (MSH_pure s') = \<up>(s' = s)"

definition init_h :: "args \<Rightarrow> msaux_h Heap" where
  "init_h args = (if args_agg args = None \<and> special_args args
     then do { q \<leftarrow> init_imp args; return (MSH_imp q) } else return (MSH_pure (init_mmasaux args)))"

fun add_new_ts_h :: "args \<Rightarrow> ts \<Rightarrow> msaux_h \<Rightarrow> msaux_h Heap" where
  "add_new_ts_h args nt (MSH_imp q) = do { q \<leftarrow> add_new_ts_imp args nt q; return (MSH_imp q) }"
| "add_new_ts_h args nt (MSH_pure s) = return (MSH_pure (add_new_ts_mmasaux args nt s))"

fun join_h :: "args \<Rightarrow> event_data table \<Rightarrow> msaux_h \<Rightarrow> msaux_h Heap" where
  "join_h args X (MSH_imp q) = do { q \<leftarrow> gc_join_imp args X q; return (MSH_imp q) }"
| "join_h args X (MSH_pure s) = return (MSH_pure (gc_join_mmasaux args X s))"

fun add_new_table_h :: "args \<Rightarrow> event_data table \<Rightarrow> msaux_h \<Rightarrow> msaux_h Heap" where
  "add_new_table_h args X (MSH_imp q) = (if finite X then do { q \<leftarrow> add_new_table_imp args X q; return (MSH_imp q) }
     else do { s \<leftarrow> to_pure args q; return (MSH_pure (add_new_table_mmasaux args X (s, None))) })"
| "add_new_table_h args X (MSH_pure s) = return (MSH_pure (add_new_table_mmasaux args X s))"

fun result_h :: "args \<Rightarrow> msaux_h \<Rightarrow> event_data table Heap" where
  "result_h args (MSH_imp q) = result_imp q"
| "result_h args (MSH_pure s) = return (result_mmasaux args s)"

lemma init_h_rule: "<emp> init_h args <is_msaux_h args (init_mmasaux args)>\<^sub>t"
proof (cases "args_agg args = None \<and> special_args args")
  case True
  then show ?thesis unfolding init_h_def if_P[OF True]
    by (sep_auto heap: init_imp_rule simp: mmasaux_None(1))
next
  case False
  then show ?thesis unfolding init_h_def if_not_P[OF False] by sep_auto
qed

lemma add_new_ts_h_rule: "<is_msaux_h args s q> add_new_ts_h args nt q <is_msaux_h args (add_new_ts_mmasaux args nt s)>\<^sub>t"
proof (cases q)
  case (MSH_imp qi)
  show ?thesis unfolding MSH_imp
    by (cases s) (sep_auto heap: add_new_ts_imp_rule simp: mmasaux_None(2))
next
  case (MSH_pure sp)
  show ?thesis unfolding MSH_pure by sep_auto
qed

lemma join_h_rule: "<is_msaux_h args s q> join_h args X q <is_msaux_h args (gc_join_mmasaux args X s)>\<^sub>t"
proof (cases q)
  case (MSH_imp qi)
  show ?thesis unfolding MSH_imp
    by (cases s) (sep_auto heap: gc_join_imp_rule simp: mmasaux_None(3))
next
  case (MSH_pure sp)
  show ?thesis unfolding MSH_pure by sep_auto
qed

lemma add_new_table_h_rule:
  "<is_msaux_h args s q> add_new_table_h args X q <is_msaux_h args (add_new_table_mmasaux args X s)>\<^sub>t"
proof (cases q)
  case (MSH_imp qi)
  obtain s0 ag where s: "s = (s0, ag)" by (cases s)
  show ?thesis
  proof (cases "finite X")
    case True
    show ?thesis unfolding MSH_imp s add_new_table_h.simps if_P[OF True]
      by (sep_auto heap: add_new_table_imp_rule[OF True] simp: mmasaux_None(4))
  next
    case False
    show ?thesis unfolding MSH_imp s add_new_table_h.simps if_not_P[OF False]
      by (sep_auto heap: to_pure_rule)
  qed
next
  case (MSH_pure sp)
  show ?thesis unfolding MSH_pure by sep_auto
qed

lemma result_h_rule: "<is_msaux_h args s q> result_h args q <\<lambda>r. is_msaux_h args s q * \<up>(r = result_mmasaux args s)>\<^sub>t"
proof (cases q)
  case (MSH_imp qi)
  show ?thesis unfolding MSH_imp
    by (cases s) (sep_auto heap: result_imp_rule simp: mmasaux_None(5))
next
  case (MSH_pure sp)
  show ?thesis unfolding MSH_pure by sep_auto
qed

(*<*)
end
(*>*)

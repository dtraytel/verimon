(*<*)
theory Imperative_Join
  imports Code_Opt "Separation_Logic_Imperative_HOL.Hash_Map_Impl"
begin
(*>*)

section \<open>Imperative refinement of the probe join\<close>

text \<open>
  The probe join of theory @{text Code_Opt} indexes the smaller table with a persistent
  red-black tree. Here the index is refined to an imperative hash table (from
  @{text Separation_Logic_Imperative_HOL}): the tuples of the smaller table are inserted into
  a hash table in the heap, the larger table probes it, and the joined tuples are collected in
  an ordinary (functional) table. The heap is used only inside a single, terminating
  computation whose result is a pure value; the computation is specified by a total-correctness
  Hoare triple in separation logic and executed from pure code through @{text run} below.
\<close>

subsection \<open>Heap and hash instances for event data\<close>

instance integer :: countable
  by (rule countable_classI[of "to_nat \<circ> int_of_integer"]) (simp add: int_of_integer_inject)

instance float :: (len, len) countable
  by (rule countable_classI[of "to_nat \<circ> Rep_float"]) (simp add: Rep_float_inject)

instance double :: countable
proof (rule countable_classI[of "to_nat \<circ> rep_double"])
  fix x y :: double
  assume "(to_nat \<circ> rep_double) x = (to_nat \<circ> rep_double) y"
  then have "abs_double (rep_double x) = abs_double (rep_double y)"
    by simp
  then show "x = y"
    by (simp add: Quotient3_abs_rep[OF Quotient3_double])
qed

instance string8 :: countable
  by (rule countable_classI[of "to_nat \<circ> Rep_string8"]) (simp add: Rep_string8_inject)

instance event_data :: countable
  by countable_datatype

instance double :: heap ..
instance string8 :: heap ..
instance event_data :: heap ..

instantiation event_data :: hashable
begin

fun hashcode_event_data :: "event_data \<Rightarrow> uint32" where
  "hashcode_event_data (EInt i) = hashcode i"
| "hashcode_event_data (EFloat d) = hashcode (integer_of_double d)"
| "hashcode_event_data (EString s) = hashcode (literal_string8 s)"

definition def_hashmap_size_event_data :: "event_data itself \<Rightarrow> nat" where
  "def_hashmap_size_event_data _ = 16"

instance
  by intro_classes (simp add: def_hashmap_size_event_data_def)

end

text \<open>
  Two adaptations for the generated OCaml code: @{const literal_string8} is the identity on the
  common string representation (the adaptation in @{text Event_Data} prints it as @{text id},
  which does not exist in OCaml's toplevel), and the hash of a string literal, defined in
  @{text HashCode} as @{term "foldl (\<lambda>h c. h * 33 + uint32_of_int (of_char c)) 5381"} over
  the exploded string, is computed directly over the bytes of the OCaml string with wrap-around
  32-bit arithmetic instead of materialising a character list first.
\<close>

text \<open>
  The default OCaml code for the conversions between @{typ integer} and @{typ uint32} tests
  bits one by one and re-parses big-integer literals from strings on every call, which
  dominated the cost of hashing. Both conversions are total functions on machine integers:
  @{term "Uint32 i"} is @{text i} modulo \<open>2\<^sup>3\<^sup>2\<close> (OCaml's @{text Int32.of_int} takes the low 32
  bits) and @{term "integer_of_uint32 w"} is the unsigned value of @{text w}.
\<close>

code_printing
  constant "Uint32 :: integer \<Rightarrow> uint32" \<rightharpoonup> (OCaml)
    "Int32.of'_int (Z.to'_int (Z.logand _ (Z.of'_int 4294967295)))"
| constant "integer_of_uint32 :: uint32 \<Rightarrow> integer" \<rightharpoonup> (OCaml)
    "Z.of'_int ((Int32.to'_int _) land 4294967295)"

code_printing
  constant "literal_string8 :: string8 \<Rightarrow> String.literal" \<rightharpoonup> (OCaml) "(fun x -> x)"
| constant "hashcode :: String.literal \<Rightarrow> uint32" \<rightharpoonup> (OCaml)
    "(fun s -> let h = ref 5381l in String.iter (fun c -> h := Int32.add (Int32.mul !h 33l) (Int32.of'_int (Char.code c))) s; !h)"

subsection \<open>Running heap computations from pure code\<close>

text \<open>
  A heap computation with a total-correctness specification that fixes its result can be run
  from pure code: its result does not depend on the heap. The generated OCaml code applies the
  thunk representing the computation (this and the standard Imperative HOL adaptation are the
  only trusted elements).
\<close>

definition run :: "'a Heap \<Rightarrow> 'a" where
  "run c = fst (the (execute c Heap.empty))"

lemma run_hoare:
  assumes "<emp> c <\<lambda>r. \<up>(r = v)>\<^sub>t"
  shows "run c = v"
proof -
  obtain h' r where "effect c Heap.empty h' r" "(h', new_addrs Heap.empty {} h') \<Turnstile> \<up>(r = v) * true"
    using hoare_triple_effect[OF assms mod_emp_simp] by blast
  moreover have "\<up>(r = v) * true = true * \<up>(r = v)"
    by (simp add: mult.commute)
  ultimately show ?thesis
    by (auto simp: run_def effect_def)
qed

code_printing constant run \<rightharpoonup> (OCaml) "(_ ())"

subsection \<open>Hash-indexed probe join\<close>

type_synonym 'a idx = "('a tuple, 'a tuple list) hashtable"

fun bucket_list :: "'a list option \<Rightarrow> 'a list" where
  "bucket_list None = []"
| "bucket_list (Some l) = l"

definition bucket_map :: "nat set \<Rightarrow> 'a tuple list \<Rightarrow> ('a tuple \<rightharpoonup> 'a tuple list) \<Rightarrow> bool" where
  "bucket_map I xs m \<longleftrightarrow> (\<forall>k. set (bucket_list (m k)) = {x \<in> set xs. restrict I x = k})"

lemma bucket_map_Nil: "bucket_map I [] Map.empty"
  by (simp add: bucket_map_def)

lemma bucket_map_bucket:
  assumes "bucket_map I xs m"
  shows "set (bucket_list (m k)) = {x \<in> set xs. restrict I x = k}"
  using assms unfolding bucket_map_def by blast

lemma bucket_map_step:
  assumes "bucket_map I ys m"
  shows "bucket_map I (ys @ [x]) (m(restrict I x \<mapsto> x # bucket_list (m (restrict I x))))"
  unfolding bucket_map_def
proof
  fix k
  show "set (bucket_list ((m(restrict I x \<mapsto> x # bucket_list (m (restrict I x)))) k)) =
    {x' \<in> set (ys @ [x]). restrict I x' = k}"
    using bucket_map_bucket[OF assms, of k] bucket_map_bucket[OF assms, of "restrict I x"]
    by (cases "k = restrict I x") auto
qed

fun hm_insert_all :: "nat set \<Rightarrow> 'a tuple list \<Rightarrow> ('a::{heap,hashable}) idx \<Rightarrow> 'a idx Heap" where
  "hm_insert_all I [] ht = return ht"
| "hm_insert_all I (x # xs) ht = do {
     b \<leftarrow> hm_lookup (restrict I x) ht;
     ht \<leftarrow> hm_update (restrict I x) (x # bucket_list b) ht;
     hm_insert_all I xs ht
   }"

lemma hm_insert_all_rule:
  "bucket_map I ys m \<Longrightarrow>
   <is_hashmap m ht> hm_insert_all I xs ht <\<lambda>ht'. \<exists>\<^sub>Am'. is_hashmap m' ht' * \<up>(bucket_map I (ys @ xs) m')>\<^sub>t"
proof (induction xs arbitrary: ys m ht)
  case Nil
  then show ?case
    by sep_auto
next
  case (Cons x xs)
  show ?case
    by (sep_auto heap: Cons.IH[OF bucket_map_step[OF Cons.prems]])
qed

fun probe_all :: "nat set \<Rightarrow> 'a tuple list \<Rightarrow> ('a::{heap,hashable}) idx \<Rightarrow> 'a table \<Rightarrow> 'a table Heap" where
  "probe_all I [] ht acc = return acc"
| "probe_all I (y # ys) ht acc = do {
     b \<leftarrow> hm_lookup (restrict I y) ht;
     probe_all I ys ht (fold (\<lambda>x. join1_insert x y) (bucket_list b) acc)
   }"

lemma fold_join1_insert_list:
  "fold (\<lambda>x. join1_insert x y) l acc = acc \<union> (\<Union>x \<in> set l. set_option (join1 (x, y)))"
  by (induction l arbitrary: acc) (auto simp: join1_insert_def split: option.splits)

definition probe_result :: "nat set \<Rightarrow> 'a tuple list \<Rightarrow> 'a tuple list \<Rightarrow> 'a table" where
  "probe_result I xs ys = (\<Union>y \<in> set ys. \<Union>x \<in> {x \<in> set xs. restrict I x = restrict I y}. set_option (join1 (x, y)))"

lemma probe_all_rule:
  "bucket_map I xs m \<Longrightarrow>
   <is_hashmap m ht> probe_all I ys ht acc <\<lambda>r. is_hashmap m ht * \<up>(r = acc \<union> probe_result I xs ys)>\<^sub>t"
proof (induction ys arbitrary: acc)
  case Nil
  then show ?case
    by (sep_auto simp: probe_result_def)
next
  case (Cons y ys)
  have step: "fold (\<lambda>x. join1_insert x y) (bucket_list (m (restrict I y))) acc \<union> probe_result I xs ys =
    acc \<union> probe_result I xs (y # ys)"
    unfolding fold_join1_insert_list bucket_map_bucket[OF Cons.prems] probe_result_def by auto
  show ?case
    by (sep_auto heap: Cons.IH[OF Cons.prems] simp: step)
qed

definition probe_join_imp :: "nat set \<Rightarrow> 'a tuple list \<Rightarrow> 'a tuple list \<Rightarrow> ('a::{heap,hashable}) table Heap" where
  "probe_join_imp I xs ys = do { ht \<leftarrow> hm_new; ht \<leftarrow> hm_insert_all I xs ht; probe_all I ys ht {} }"

lemma probe_join_imp_rule: "<emp> probe_join_imp I xs ys <\<lambda>r. \<up>(r = probe_result I xs ys)>\<^sub>t"
  unfolding probe_join_imp_def
  by (sep_auto heap: hm_insert_all_rule[OF bucket_map_Nil] probe_all_rule)

definition hprobe_join :: "nat set \<Rightarrow> ('a::{heap,hashable,ccompare}) table \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "hprobe_join I t t' = run (probe_join_imp I (csorted_list_of_set t) (csorted_list_of_set t'))"

lemma probe_result_join:
  assumes "\<forall>x \<in> t. complete_on I x" "\<forall>y \<in> t'. complete_on I y"
  shows "(\<Union>b \<in> t'. \<Union>a \<in> {a \<in> t. restrict I a = restrict I b}. set_option (join1 (a, b))) = join t True t'"
proof (intro set_eqI iffI)
  fix z
  assume "z \<in> (\<Union>b \<in> t'. \<Union>a \<in> {a \<in> t. restrict I a = restrict I b}. set_option (join1 (a, b)))"
  then show "z \<in> join t True t'"
    unfolding join_True_code by auto
next
  fix z
  assume "z \<in> join t True t'"
  then obtain a b where ab: "a \<in> t" "b \<in> t'" "join1 (a, b) = Some z"
    unfolding join_True_code by auto
  then have "restrict I a = restrict I b"
    using assms join1_Some_restrict_complete by blast
  then show "z \<in> (\<Union>b \<in> t'. \<Union>a \<in> {a \<in> t. restrict I a = restrict I b}. set_option (join1 (a, b)))"
    using ab by (intro UN_I[of b] UN_I[of a]) auto
qed

lemma hprobe_join_join:
  assumes "ID CCOMPARE('a tuple) \<noteq> None" "finite (t :: ('a::{heap,hashable,ccompare}) table)" "finite t'"
    "\<forall>x \<in> t. complete_on I x" "\<forall>y \<in> t'. complete_on I y"
  shows "hprobe_join I t t' = join t True t'"
proof -
  have "set (csorted_list_of_set t) = t"
    using assms(1,2) by (subst csorted_list_of_set_split) auto
  moreover have "set (csorted_list_of_set t') = t'"
    using assms(1,3) by (subst csorted_list_of_set_split) auto
  ultimately
  show ?thesis
    unfolding hprobe_join_def run_hoare[OF probe_join_imp_rule] probe_result_def
    using probe_result_join[OF assms(4,5)] by simp
qed

subsection \<open>Code equation\<close>

text \<open>
  As for the multi-way join strategy, the choice between the persistent index
  (@{const probe_join}) and the imperative hash index (@{const hprobe_join}) is left open in
  the formalization through an unspecified constant, proved correct for both values and read
  from a mutable flag by the generated code (command line option @{text "-imperative_join"}).
\<close>

consts use_imperative_join :: bool

code_printing constant use_imperative_join \<rightharpoonup> (OCaml) "'!Config.imperative'_join"

declare [[code drop: bin_join]]

lemma bin_join_code_imp[code]:
  "bin_join n A (t :: ('a::{heap,hashable,ccompare}) table) pos A' t' =
    (if t = {} then {}
    else if t' = {} then (if pos then {} else t)
    else if A' = {} then (if (pos \<longleftrightarrow> replicate n None \<in> t') then t else {})
    else if A' = A then (if pos then t \<inter> t' else t - t')
    else if A' \<subseteq> A then (let m = join_mask n A' in {as \<in> t. proj_tuple_in_join pos m as t'})
    else if A \<subseteq> A' \<and> pos then (let m = join_mask n A in {as \<in> t'. proj_tuple_in_join pos m as t})
    else if pos \<and> finite t \<and> finite t' \<and>
        (\<forall>x \<in> t. complete_on (A \<inter> A') x) \<and> (\<forall>y \<in> t'. complete_on (A \<inter> A') y)
      then (case ID CCOMPARE('a tuple) of
          None \<Rightarrow> (if card t \<le> card t' then probe_join_n n (A \<inter> A') t t' else probe_join_n n (A \<inter> A') t' t)
        | Some _ \<Rightarrow> (if use_imperative_join
            then (if card t \<le> card t' then hprobe_join (A \<inter> A') t t' else hprobe_join (A \<inter> A') t' t)
            else (if card t \<le> card t' then probe_join_n n (A \<inter> A') t t' else probe_join_n n (A \<inter> A') t' t)))
    else join t pos t')"
  by (subst bin_join.simps) (auto simp: Let_def probe_join_n_def probe_join_join hprobe_join_join join_commute split: option.splits)

(*<*)
end
(*>*)

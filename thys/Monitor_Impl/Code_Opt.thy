(*<*)
theory Code_Opt
  imports Monitor_Impl
begin
(*>*)

section \<open>Efficient code equations\<close>

subsection \<open>Folding a red-black tree of keys\<close>

text \<open>
  @{const RBT_Set2.fold} is defined by discarding the value of each entry, which the generated
  code does by wrapping the element function in a closure: one closure allocated per fold, and
  two indirect calls per element instead of one.  A fold that takes the element function
  directly does the same work.
\<close>

fun rbt_fold_key :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, unit) RBT_Impl.rbt \<Rightarrow> 'b \<Rightarrow> 'b" where
  "rbt_fold_key f RBT_Impl.Empty s = s"
| "rbt_fold_key f (RBT_Impl.Branch c l k v r) s = rbt_fold_key f r (f k (rbt_fold_key f l s))"

lemma rbt_fold_key_eq: "rbt_fold_key f t s = RBT_Impl.fold (\<lambda>a _. f a) t s"
  by (induction f t s rule: rbt_fold_key.induct) (auto simp: RBT_Impl.fold_def)

declare [[code drop: RBT_Set2.fold]]

lemma rbt_set2_fold_code[code]:
  "RBT_Set2.fold f t = rbt_fold_key f (RBT_Mapping2.impl_of t)"
  by (rule ext) (simp add: rbt_fold_key_eq RBT_Set2.fold.rep_eq)

declare [[code drop: rbt_fold]]

lemma rbt_fold_code[code]: "rbt_fold f t = rbt_fold_key f (RBT_Mapping2.impl_of t)"
  by (simp add: rbt_fold_def rbt_set2_fold_code)

text \<open>
  Folding over a mapped list builds the mapped list first.  Applying the two functions to the
  element in one step removes it, and -- because the redirections of Section \<open>Monomorphic_Code\<close>
  rewrite an operation applied to an argument, not an operation on its own -- it also lets the
  monomorphic container operations reach folds whose function argument was written point-free.
\<close>

lemma fold_map_unfold[code_unfold]: "fold f (map g xs) = fold (\<lambda>x. f (g x)) xs"
  by (simp add: fold_map comp_def)

text \<open>
  @{const fst} and @{const snd} are generated from their defining equations on a pair pattern,
  which compiles them as functions of two arguments; every application to a pair that is not
  written out at the call site then goes through the adapter that rebuilds the pair.  They
  account for five of the eleven million entries into it on P2.
\<close>

declare [[code drop: fst snd]]

lemma fst_code[code]: "fst p = (case p of (a, b) \<Rightarrow> a)"
  by (simp split: prod.splits)

lemma snd_code[code]: "snd p = (case p of (a, b) \<Rightarrow> b)"
  by (simp split: prod.splits)

text \<open>
  The lookup in a red-black tree is stated point-free, so the generated code applies it to the
  tree, gets a closure back and then applies that to the key: one closure allocated per lookup,
  and on P2 that is 1.3\% of everything the monitor allocates.
\<close>

declare [[code drop: RBT_Mapping2.lookup]]

lemma rbt_mapping2_lookup_code[code]:
  "RBT_Mapping2.lookup t k = rbt_comp_lookup ccomp (RBT_Mapping2.impl_of t) k"
  by (simp add: RBT_Mapping2.lookup_def)

subsection \<open>Direct comparators\<close>

text \<open>
  The comparators derived by the @{text derive} command are expressed via the generic
  @{const comparator_of}, whose generated code performs two dictionary-dispatched comparisons
  (@{text "<"} followed by @{text "="}) per element. The following code equations spell out the
  comparators for the base types occurring in event data and tuples directly.
\<close>

declare [[code drop: "compare :: nat \<Rightarrow> _" "compare :: integer \<Rightarrow> _" "compare :: string8 \<Rightarrow> _" comparator_event_data]]

lemma compare_nat_code[code]: "compare (x :: nat) y = (if x < y then Lt else if x = y then Eq else Gt)"
  by (simp add: compare_nat_def comparator_of_def)

lemma compare_integer_code[code]: "compare (x :: integer) y = (if x < y then Lt else if x = y then Eq else Gt)"
  by (simp add: compare_integer_def comparator_of_def)

lemma compare_string8_code[code]: "compare (x :: string8) y = (if x < y then Lt else if x = y then Eq else Gt)"
  by (simp add: compare_string8_def comparator_of_def)

text \<open>
  Comparing two integers with @{text "<"} and then @{text "="} is two calls into the
  arbitrary-precision library where one would do; on the Until benchmark they are 5.3\% and 1.8\%
  of the run.  The comparison below makes the one call and reads its sign.

  Even the one call is a call out of OCaml, and after the change above it was the single
  costliest symbol of the Until benchmark at 5.7\%.  Zarith keeps every integer that fits in an
  OCaml integer as an immediate and only larger ones as a custom block, so two immediates are
  in the same order as the machine integers they carry, and the two cases are told apart by
  the tag.  The printing below takes that path in OCaml and falls back to the library for
  everything else, which is where the values that do not fit are compared.  This reads the
  representation that the library documents rather than its interface, so it is one more thing
  to believe about the generated code, next to the hash functions of the imperative tables.
\<close>

definition cmp_integer :: "integer \<Rightarrow> integer \<Rightarrow> order" where
  "cmp_integer x y = (if x < y then Lt else if x = y then Eq else Gt)"

code_printing constant cmp_integer \<rightharpoonup> (OCaml)
  "(fun x y -> if Obj.is'_int (Obj.repr x) && Obj.is'_int (Obj.repr y) then (let a = (Obj.magic x : int) and b = (Obj.magic y : int) in if a < b then Lt else if a = b then Eqa else Gt) else (let c = Z.compare x y in if c < 0 then Lt else if c = 0 then Eqa else Gt))"

lemma comparator_event_data_code[code]:
  "comparator_event_data (EInt x) (EInt y) = cmp_integer x y"
  "comparator_event_data (EInt x) (EFloat e) = Lt"
  "comparator_event_data (EInt x) (EString t) = Lt"
  "comparator_event_data (EFloat d) (EInt y) = Gt"
  "comparator_event_data (EFloat d) (EFloat e) = comparator_double d e"
  "comparator_event_data (EFloat d) (EString t) = Lt"
  "comparator_event_data (EString s) (EInt y) = Gt"
  "comparator_event_data (EString s) (EFloat e) = Gt"
  "comparator_event_data (EString s) (EString t) = (if s < t then Lt else if s = t then Eq else Gt)"
  by (simp_all add: comparator_of_def cmp_integer_def)

subsection \<open>Run-time selection of the multi-way join strategy\<close>

text \<open>
  @{const use_generic_join} is an unspecified constant; both values are covered by the
  correctness proofs. The generated code reads it from a mutable flag in a small auxiliary
  module, so that the front end can choose the strategy at run time.
\<close>

code_printing code_module Config \<rightharpoonup> (OCaml)
\<open>module Config : sig
  val generic_join : bool ref
end = struct
  let generic_join = ref false
end\<close>
| constant use_generic_join \<rightharpoonup> (OCaml) "'!Config.generic'_join"

section \<open>Since without join columns\<close>

text \<open>
  The Since structure keeps two @{typ "'a wf_table"}s indexed by the join columns
  @{term "args_L args"}. They are consulted by @{const join_mmsaux} only when there are join
  columns that do not cover all columns; without them (@{term "args_L args = []"}, e.g. for
  @{text ONCE}) or when all columns are join columns (@{term "args_L args = args_R args"}) the
  operations of @{text Optimized_Since} maintain them as @{term "wf_table_of_keys R m"}, the
  set of keys of the corresponding mapping. Both @{const wf_table_of_set} and @{const wf_table_of_keys} are made
  representations of @{typ "'a wf_table"} for the code generator: constructing them costs
  nothing, the (never taken) reads filter lazily, and the binary operations convert them to the
  plain set representation first. Constructing an index for the empty or the full join column
  set is also replaced by the plain representation.
\<close>

lemma wf_table_of_idx_of_set: "wf_table_of_idx (wf_idx_of_set cs I X) = wf_table_of_set cs X"
proof (cases "distinct cs")
  case True
  then show ?thesis
    by (intro wf_table_eqI) (simp_all add: wf_idx_sig_of_set wf_idx_set_of_set wf_table_sig_of_set wf_table_set_of_set)
next
  case False
  have e: "set_of_idx (Mapping.empty :: ('a list, 'a table) mapping) = {}"
    by transfer simp
  show ?thesis
    by (rule Rep_wf_table_inject[THEN iffD1])
      (simp add: wf_table_of_idx.rep_eq wf_table_of_set.rep_eq wf_idx_of_set.rep_eq False e)
qed

declare [[code drop: wf_table_of_set_args]]

lemma wf_table_of_set_args_code[code]:
  "wf_table_of_set_args args X = (if args_L args = [] \<or> args_L args = args_R args
     then wf_table_of_set (args_R args) X
     else wf_table_of_idx (wf_idx_of_set (args_R args) (args_L args) X))"
  by (simp add: wf_table_of_set_args_def wf_table_of_idx_of_set)

declare [[code drop: init_mmsaux]]

lemma init_mmsaux_code[code]:
  "init_mmsaux args = (0, 0, empty_queue, empty_queue,
    {}, wf_table_of_set_args args {}, Mapping.empty, wf_table_of_set_args args {}, Mapping.empty)"
  by (simp add: wf_table_of_set_args_def)

declare [[code drop: wf_table_of_set wf_table_of_keys]]

code_datatype wf_table_of_wf_set wf_table_of_idx wf_table_of_set wf_table_of_keys

text \<open>Re-declaring the representations drops the existing code equations that match on them.\<close>

declare wf_table_sig_code[code] wf_table_set_code[code] wf_table_union_code[code]
  wf_table_join_code[code] wf_table_antijoin_code[code]

lemma wf_table_conv:
  "wf_table_of_set cs X = wf_table_of_wf_set (wf_set_of_set cs X)"
  "wf_table_of_keys cs m = wf_table_of_wf_set (wf_set_of_set cs (Mapping.keys m))"
  by (simp_all add: wf_table_of_set_code wf_table_of_keys_def)

lemma wf_table_sig_code'[code]:
  "wf_table_sig (wf_table_of_set cs X) = (if distinct cs then cs else [])"
  "wf_table_sig (wf_table_of_keys cs m) = (if distinct cs then cs else [])"
  unfolding wf_table_of_keys_def by (transfer, simp)+

lemma wf_table_set_code'[code]:
  "wf_table_set (wf_table_of_set cs X) = (if distinct cs then Set.filter (wf_tuple cs) X else {})"
  "wf_table_set (wf_table_of_keys cs m) = (if distinct cs then Set.filter (wf_tuple cs) (Mapping.keys m) else {})"
  unfolding wf_table_of_keys_def by (transfer, simp)+

lemma wf_table_union_code'[code]:
  "wf_table_union (wf_table_of_set cs X) t = wf_table_union (wf_table_of_wf_set (wf_set_of_set cs X)) t"
  "wf_table_union (wf_table_of_keys cs m) t = wf_table_union (wf_table_of_wf_set (wf_set_of_set cs (Mapping.keys m))) t"
  "wf_table_union t (wf_table_of_set cs X) = wf_table_union t (wf_table_of_wf_set (wf_set_of_set cs X))"
  "wf_table_union t (wf_table_of_keys cs m) = wf_table_union t (wf_table_of_wf_set (wf_set_of_set cs (Mapping.keys m)))"
  by (simp_all only: wf_table_conv)

lemma wf_table_join_code'[code]:
  "wf_table_join (wf_table_of_set cs X) t = wf_table_join (wf_table_of_wf_set (wf_set_of_set cs X)) t"
  "wf_table_join (wf_table_of_keys cs m) t = wf_table_join (wf_table_of_wf_set (wf_set_of_set cs (Mapping.keys m))) t"
  "wf_table_join t (wf_table_of_set cs X) = wf_table_join t (wf_table_of_wf_set (wf_set_of_set cs X))"
  "wf_table_join t (wf_table_of_keys cs m) = wf_table_join t (wf_table_of_wf_set (wf_set_of_set cs (Mapping.keys m)))"
  by (simp_all only: wf_table_conv)

lemma wf_table_antijoin_code'[code]:
  "wf_table_antijoin (wf_table_of_set cs X) t = wf_table_antijoin (wf_table_of_wf_set (wf_set_of_set cs X)) t"
  "wf_table_antijoin (wf_table_of_keys cs m) t = wf_table_antijoin (wf_table_of_wf_set (wf_set_of_set cs (Mapping.keys m))) t"
  "wf_table_antijoin t (wf_table_of_set cs X) = wf_table_antijoin t (wf_table_of_wf_set (wf_set_of_set cs X))"
  "wf_table_antijoin t (wf_table_of_keys cs m) = wf_table_antijoin t (wf_table_of_wf_set (wf_set_of_set cs (Mapping.keys m)))"
  by (simp_all only: wf_table_conv)

section \<open>Clustering\<close>

derive (no) cenum event_data

lemma keys_cluster: "Mapping.keys (cluster (Some \<circ> g) X) = g ` X"
  by (auto simp: Mapping.keys_dom_lookup lookup_cluster image_iff split: if_splits)

lemma lookup_cluster_Some: "k \<in> g ` X \<Longrightarrow> Mapping.lookup (cluster (Some \<circ> g) X) k = Some (Set.filter (\<lambda>x. g x = k) X)"
  by (auto simp: lookup_cluster image_iff)

subsection \<open>Unions of option-valued images without sets of sets\<close>

text \<open>
  @{term "\<Union>v \<in> X. set_option (f v)"} (used by the @{text Match} mode of predicate evaluation)
  is compiled by Containers through a set of sets, whose comparator compares whole tables.
  The rewrite below turns it into an image followed by @{const Option.these}.
\<close>

lemma Union_set_option_these[code_unfold]: "(\<Union>v \<in> X. set_option (f v)) = Option.these (f ` X)"
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> (\<Union>v \<in> X. set_option (f v))"
  then obtain v where "v \<in> X" "f v = Some x" by auto
  then show "x \<in> Option.these (f ` X)" by (auto simp: in_these_eq intro: rev_image_eqI)
next
  fix x
  assume "x \<in> Option.these (f ` X)"
  then show "x \<in> (\<Union>v \<in> X. set_option (f v))" by (auto simp: in_these_eq)
qed

(*<*)
end
(*>*)

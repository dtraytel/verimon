(*<*)
theory Optimized_Join
  imports "Generic_Join_Devel.Generic_Join" "MFODL_Logic.Table_Join"
begin
(*>*)

section \<open>Optimized relational join\<close>

subsection \<open>Binary join\<close>

text \<open>The join of @{term t} over the columns @{term cs} with @{term t'} over @{term ds}, with
  shortcuts for the cases in which one table's columns are among the other's.  The last but one
  case filters the right table and brings its tuples into the join's column order
  @{term "cols_union cs ds"}.\<close>

fun bin_join :: "nat list \<Rightarrow> 'a table \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "bin_join cs t pos ds t' =
    (if t = {} then {}
    else if t' = {} then (if pos then {} else t)
    else if ds = [] then (if (pos \<longleftrightarrow> [] \<in> t') then t else {})
    else if ds = cs then (if pos then t \<inter> t' else t - t')
    else if set ds \<subseteq> set cs then {as \<in> t. join_cond pos t' (restrict ds cs as)}
    else if set cs \<subseteq> set ds \<and> pos then
      restrict (cols_union cs ds) ds ` {as \<in> t'. restrict cs ds as \<in> t}
    else join cs t pos ds t')"

lemma bin_join_table:
  assumes "distinct cs" "distinct ds" "table cs t" "table ds t'"
  shows "bin_join cs t pos ds t' = join cs t pos ds t'"
proof (cases "t = {} \<or> t' = {}")
  case True
  then show ?thesis
    by (auto simp: join_def)
next
  case False
  then have ne: "t \<noteq> {}" "t' \<noteq> {}"
    by simp_all
  note sub = join_sub[OF assms]
  consider (no_cols) "ds = []"
    | (eq) "ds \<noteq> []" "ds = cs"
    | (sub) "ds \<noteq> []" "ds \<noteq> cs" "set ds \<subseteq> set cs"
    | (sub') "ds \<noteq> []" "ds \<noteq> cs" "\<not> set ds \<subseteq> set cs" "set cs \<subseteq> set ds" "pos"
    | (other) "ds \<noteq> []" "ds \<noteq> cs" "\<not> set ds \<subseteq> set cs" "\<not> (set cs \<subseteq> set ds \<and> pos)"
    by blast
  then show ?thesis
  proof cases
    case no_cols
    with assms(4) ne(2) have t': "t' = {[]}"
      by (auto simp: table_def)
    have "join cs t pos ds t' = {as \<in> t. join_cond pos t' (restrict ds cs as)}"
      by (rule sub) (simp add: no_cols)
    with ne no_cols t' show ?thesis
      by simp  next
    case eq
    with ne sub[of pos] assms(1,3) show ?thesis
      by (auto simp: restrict_idle table_def)
  next
    case sub
    with ne show ?thesis
      by (simp add: join_sub[OF assms])
  next
    case sub'
    with ne show ?thesis
      by (simp add: join_sub'[OF assms])
  next
    case other
    with ne show ?thesis
      by auto
  qed
qed

subsection \<open>Multi-way join\<close>

text \<open>The columns of the positive tables, in the order of the generic join's result.\<close>

abbreviation mcols :: "nat list list \<Rightarrow> nat list" where
  "mcols A_pos \<equiv> cols (\<Union>A\<in>set A_pos. set A)"

fun mmulti_join' :: "(nat list list \<Rightarrow> nat list list \<Rightarrow> 'a table list \<Rightarrow> 'a table)" where
  "mmulti_join' A_pos A_neg L = (
    let Q = set (zip A_pos L) in
    let Q_neg = set (zip A_neg (drop (length A_pos) L)) in
    New_max_getIJ_wrapperGenericJoin Q Q_neg)"

fun find_sub_in :: "'a list \<Rightarrow> 'a list list \<Rightarrow> bool \<Rightarrow>
  ('a list list \<times> 'a list \<times> 'a list list) option" where
  "find_sub_in X [] b = None"
| "find_sub_in X (x # xs) b = (if (set x \<subseteq> set X \<or> (b \<and> set X \<subseteq> set x)) then Some ([], x, xs)
    else (case find_sub_in X xs b of None \<Rightarrow> None | Some (ys, z, zs) \<Rightarrow> Some (x # ys, z, zs)))"

lemma find_sub_in_sound: "find_sub_in X xs b = Some (ys, z, zs) \<Longrightarrow>
  xs = ys @ z # zs \<and> (set z \<subseteq> set X \<or> (b \<and> set X \<subseteq> set z))"
  by (induction X xs b arbitrary: ys z zs rule: find_sub_in.induct)
     (fastforce split: if_splits option.splits)+

fun find_sub_True :: "'a list list \<Rightarrow>
  ('a list list \<times> 'a list \<times> 'a list list \<times> 'a list \<times> 'a list list) option" where
  "find_sub_True [] = None"
| "find_sub_True (x # xs) = (case find_sub_in x xs True of None \<Rightarrow>
    (case find_sub_True xs of None \<Rightarrow> None
    | Some (ys, w, ws, z, zs) \<Rightarrow> Some (x # ys, w, ws, z, zs))
  | Some (ys, z, zs) \<Rightarrow> Some ([], x, ys, z, zs))"

lemma find_sub_True_sound: "find_sub_True xs = Some (ys, w, ws, z, zs) \<Longrightarrow>
  xs = ys @ w # ws @ z # zs \<and> (set z \<subseteq> set w \<or> set w \<subseteq> set z)"
  using find_sub_in_sound
  by (induction xs arbitrary: ys w ws z zs rule: find_sub_True.induct)
     (fastforce split: option.splits)+

fun find_sub_False :: "'a list list \<Rightarrow> 'a list list \<Rightarrow>
  (('a list list \<times> 'a list \<times> 'a list list) \<times> ('a list list \<times> 'a list \<times> 'a list list)) option" where
  "find_sub_False [] ns = None"
| "find_sub_False (x # xs) ns = (case find_sub_in x ns False of None \<Rightarrow>
    (case find_sub_False xs ns of None \<Rightarrow> None
    | Some ((rs, w, ws), (ys, z, zs)) \<Rightarrow> Some ((x # rs, w, ws), (ys, z, zs)))
  | Some (ys, z, zs) \<Rightarrow> Some (([], x, xs), (ys, z, zs)))"

lemma find_sub_False_sound: "find_sub_False xs ns = Some ((rs, w, ws), (ys, z, zs)) \<Longrightarrow>
  xs = rs @ w # ws \<and> ns = ys @ z # zs \<and> (set z \<subseteq> set w)"
  using find_sub_in_sound
  by (induction xs ns arbitrary: rs w ws ys z zs rule: find_sub_False.induct)
     (fastforce split: option.splits)+
fun proj_list_3 :: "'a list \<Rightarrow> ('b list \<times> 'b \<times> 'b list) \<Rightarrow> ('a list \<times> 'a \<times> 'a list)" where
  "proj_list_3 xs (ys, z, zs) = (take (length ys) xs, xs ! (length ys),
    take (length zs) (drop (length ys + 1) xs))"

fun proj_list_5 :: "'a list \<Rightarrow>
  ('b list \<times> 'b \<times> 'b list \<times> 'b \<times> 'b list) \<Rightarrow>
  ('a list \<times> 'a \<times> 'a list \<times> 'a \<times> 'a list)" where
  "proj_list_5 xs (ys, w, ws, z, zs) = (take (length ys) xs, xs ! (length ys),
    take (length ws) (drop (length ys + 1) xs), xs ! (length ys + 1 + length ws),
    drop (length ys + 1 + length ws + 1) xs)"

fun dominate_True :: "nat list list \<Rightarrow> 'a table list \<Rightarrow>
  ((nat list list \<times> nat list \<times> nat list list \<times> nat list \<times> nat list list) \<times>
  ('a table list \<times> 'a table \<times> 'a table list \<times> 'a table \<times> 'a table list)) option" where  "dominate_True A_pos L_pos = (case find_sub_True A_pos of None \<Rightarrow> None
  | Some split \<Rightarrow> Some (split, proj_list_5 L_pos split))"

fun dominate_False :: "nat list list \<Rightarrow> 'a table list \<Rightarrow> nat list list \<Rightarrow> 'a table list \<Rightarrow>
  (((nat list list \<times> nat list \<times> nat list list) \<times> nat list list \<times> nat list \<times> nat list list) \<times>
  (('a table list \<times> 'a table \<times> 'a table list) \<times>
  'a table list \<times> 'a table \<times> 'a table list)) option" where
  "dominate_False A_pos L_pos A_neg L_neg = (case find_sub_False A_pos A_neg of None \<Rightarrow> None
  | Some (pos_split, neg_split) \<Rightarrow>
    Some ((pos_split, neg_split), (proj_list_3 L_pos pos_split, proj_list_3 L_neg neg_split)))"

function mmulti_join_gen :: "(nat list list \<Rightarrow> nat list list \<Rightarrow> 'a table list \<Rightarrow> 'a table)" where
  "mmulti_join_gen A_pos A_neg L = (if length A_pos + length A_neg \<noteq> length L then {} else
    let L_pos = take (length A_pos) L; L_neg = drop (length A_pos) L in
    (case dominate_True A_pos L_pos of None \<Rightarrow>
      (case dominate_False A_pos L_pos A_neg L_neg of None \<Rightarrow> mmulti_join' A_pos A_neg L
      | Some (((A_zs, A_x, A_xs), A_ws, A_y, A_ys), ((zs, x, xs), ws, y, ys)) \<Rightarrow>
        mmulti_join_gen (A_zs @ A_x # A_xs) (A_ws @ A_ys)
        ((zs @ bin_join A_x x False A_y y # xs) @ (ws @ ys)))
    | Some ((A_zs, A_x, A_xs, A_y, A_ys), (zs, x, xs, y, ys)) \<Rightarrow>
      mmulti_join_gen (A_zs @ cols_union A_x A_y # A_xs @ A_ys) A_neg
      ((zs @ bin_join A_x x True A_y y # xs @ ys) @ L_neg)))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(A_pos, A_neg, L). length A_pos + length A_neg)")
    (use find_sub_True_sound find_sub_False_sound in \<open>fastforce split: option.splits\<close>)+

subsection \<open>Multi-way join as a sequence of binary joins\<close>

text \<open>
  The worst-case optimal generic join above has large constant factors in the generated code.
  The monitor therefore evaluates multi-way joins as a left-deep sequence of binary joins
  (which use an index on the common columns, see @{const bin_join}) followed by anti-joins
  for the negated conjuncts. The correctness statement @{text mmulti_join_correct} is the same
  as for the generic join. The two strategies produce their results in different column
  orders (the generic join sorts the columns, the binary joins accumulate them with
  @{const cols_union}); @{text mmulti_join} takes the column order of its result as an
  argument and reorders the tuples if needed.
\<close>

fun mmulti_join_pos :: "nat list \<Rightarrow> 'a table \<Rightarrow> (nat list \<times> 'a table) list \<Rightarrow> nat list \<times> 'a table" where
  "mmulti_join_pos cs t [] = (cs, t)"
| "mmulti_join_pos cs t ((cs', t') # L) = mmulti_join_pos (cols_union cs cs') (bin_join cs t True cs' t') L"

fun mmulti_join_neg :: "nat list \<Rightarrow> 'a table \<Rightarrow> (nat list \<times> 'a table) list \<Rightarrow> 'a table" where
  "mmulti_join_neg cs t [] = t"
| "mmulti_join_neg cs t ((cs', t') # L) = mmulti_join_neg cs (bin_join cs t False cs' t') L"

text \<open>
  The choice between the two evaluation strategies is left open in the formalization: the
  constant @{text use_generic_join} is unspecified, and the correctness of @{text mmulti_join}
  (theory @{text Optimized_Join_Correctness}) is proved for both of its values. The generated code
  reads it from a mutable flag (see theory @{text Efficient_Instance}), which the front end sets from the
  command line option @{text "-generic_join"}.
\<close>

consts use_generic_join :: bool

fun mmulti_join_pw :: "nat list list \<Rightarrow> nat list list \<Rightarrow> 'a table list \<Rightarrow> nat list \<times> 'a table" where
  "mmulti_join_pw A_pos A_neg L = (case zip A_pos L of [] \<Rightarrow> ([], {})
    | (A, t) # Lpos \<Rightarrow> (case mmulti_join_pos A t Lpos of (A', t') \<Rightarrow>
        (A', mmulti_join_neg A' t' (zip A_neg (drop (length A_pos) L)))))"

fun mmulti_join :: "nat list \<Rightarrow> nat list list \<Rightarrow> nat list list \<Rightarrow> 'a table list \<Rightarrow> 'a table" where
  "mmulti_join cs A_pos A_neg L =
    (if use_generic_join then reorder cs (mcols A_pos) (mmulti_join_gen A_pos A_neg L)
    else (case mmulti_join_pw A_pos A_neg L of (cs', t) \<Rightarrow> reorder cs cs' t))"

(*<*)
end
(*>*)

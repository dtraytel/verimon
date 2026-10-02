(*<*)
theory Dense_Aux
  imports Dense "MFODL_Monitor_Devel.Correctness"
begin
(*>*)

section \<open>The dense Since and Until structures\<close>

text \<open>
  The temporal structures run over the ascending columns @{term "dargs cs_R cs_L args"}: a stored
  tuple is a tuple over the right operand's columns @{term cs_R}, and the probe table is the left
  operand's, over @{term cs_L}.  The kernel's structures read the probe at a stored tuple by
  restricting the latter to the left operand's columns; over ascending columns that restriction
  is the dense projection at the mask @{term "mrg_left_key (mrg_plan cs_R cs_L)"}, which is a
  single pass over the tuple.  This theory adds an index on that projection and proves the
  resulting structures equal to the verified ones.
\<close>

subsection \<open>The dense index under the semi-join\<close>

text \<open>
  Restricting the index to the surviving keys is the index of the surviving tuples: a bucket
  passes or fails as a whole, because the filter only looks at the key.
\<close>

lemma keys_didx: "Mapping.keys (didx msk T) = dproj msk ` T"
  by (auto simp: Mapping.keys_dom_lookup lookup_didx dom_def split: if_splits)

lemma didx_filter:
  "Mapping.filter (\<lambda>k _. (k \<in> X) = pos) (didx msk T) = didx msk (dsemi msk pos T X)"
proof -
  have "Mapping.lookup (Mapping.filter (\<lambda>k _. (k \<in> X) = pos) (didx msk T)) k
      = Mapping.lookup (didx msk (dsemi msk pos T X)) k" for k
  proof -
    have img: "(k \<in> dproj msk ` dsemi msk pos T X) = (k \<in> dproj msk ` T \<and> (k \<in> X) = pos)"
      by (auto simp: dsemi_def)
    have bucket: "(k \<in> X) = pos \<Longrightarrow> {y \<in> dsemi msk pos T X. dproj msk y = k}
        = {y \<in> T. dproj msk y = k}"
      by (auto simp: dsemi_def)
    show ?thesis
      using bucket by (simp add: Mapping.lookup_filter lookup_didx img)
  qed
  then show ?thesis by (simp add: mapping_eqI)
qed

lemma keys_Mapping_filter_dsemi:
  "Mapping.keys (Mapping.filter (\<lambda>as _. (dproj msk as \<in> X) = pos) m)
   = dsemi msk pos (Mapping.keys m) X"
  by (auto simp: Mapping.keys_dom_lookup Mapping.lookup_filter dsemi_def dom_def
      split: option.splits if_splits)

subsection \<open>Maintaining the index incrementally\<close>

text \<open>
  The structure adds and removes whole tables at a time, so the index is maintained by combining
  it with the index of the added table, and by subtracting the index of the removed one bucket by
  bucket.
\<close>

lemma didx_empty[simp]: "didx msk {} = Mapping.empty"
  by (intro mapping_eqI) (simp add: lookup_didx)

definition didx_union :: "('b list, 'b list set) mapping \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow>
    ('b list, 'b list set) mapping" where
  "didx_union = Mapping.combine (\<union>)"

lemma didx_union_eq: "didx msk (S \<union> A) = didx_union (didx msk S) (didx msk A)"
proof -
  have "Mapping.lookup (didx msk (S \<union> A)) k
      = Mapping.lookup (didx_union (didx msk S) (didx msk A)) k" for k
  proof -
    have eS: "k \<notin> dproj msk ` S \<Longrightarrow> {y \<in> S. dproj msk y = k} = {}" by auto
    have eA: "k \<notin> dproj msk ` A \<Longrightarrow> {y \<in> A. dproj msk y = k} = {}" by auto
    have u: "{y \<in> S \<union> A. dproj msk y = k}
        = {y \<in> S. dproj msk y = k} \<union> {y \<in> A. dproj msk y = k}" by auto
    have iU: "(k \<in> dproj msk ` (S \<union> A)) = (k \<in> dproj msk ` S \<or> k \<in> dproj msk ` A)" by auto
    show ?thesis
      by (simp add: didx_union_def Mapping.lookup_combine lookup_didx combine_options_def
          u iU eS eA) blast
  qed
  then show ?thesis by (simp add: mapping_eqI)
qed

definition dbucket :: "('b list, 'b list set) mapping \<Rightarrow> 'b list \<Rightarrow> 'b list set" where
  "dbucket d k = (case Mapping.lookup d k of None \<Rightarrow> {} | Some Z \<Rightarrow> Z)"

definition didx_minus :: "('b list, 'b list set) mapping \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow>
    ('b list, 'b list set) mapping" where
  "didx_minus i d = Mapping.filter (\<lambda>k Y. Mapping.lookup d k = None \<or> Y \<noteq> {})
     (Mapping.map_values (\<lambda>k Y. Y - dbucket d k) i)"

text \<open>Only the buckets that the subtrahend touches are dropped when they empty: a bucket at a key
  the subtrahend does not have is left as it is.  On a clustering, which has no empty buckets, the
  two readings agree; the executable version of the subtraction, which only visits the
  subtrahend's keys, realises this one exactly.\<close>

lemma didx_minus_eq: "didx msk (S - D) = didx_minus (didx msk S) (didx msk D)"
proof -
  have "Mapping.lookup (didx msk (S - D)) k
      = Mapping.lookup (didx_minus (didx msk S) (didx msk D)) k" for k
  proof -
    have b: "{y \<in> S. dproj msk y = k} - dbucket (didx msk D) k = {y \<in> S - D. dproj msk y = k}"
      by (auto simp: dbucket_def lookup_didx split: if_splits)
    show ?thesis
      by (auto simp: didx_minus_def Mapping.lookup_filter Mapping.lookup_map_values lookup_didx b
          split: option.splits if_splits intro: rev_image_eqI)
  qed
  then show ?thesis by (simp add: mapping_eqI)
qed

subsection \<open>The mask of the left operand's columns among the right operand's\<close>

lemma length_mrg_left_key:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     length (mrg_left_key (mrg_plan cs1 cs2)) = length cs1"
  by (induct cs1 cs2 rule: mrg_plan.induct) auto

lemma length_filter_mrg_left_key:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     length (filter id (mrg_left_key (mrg_plan cs1 cs2))) = length cs2"
  by (induct cs1 cs2 rule: mrg_plan.induct) auto

lemma mrg_left_key_MRgt: "mrg_left_key (map (\<lambda>_. MRgt) ds) = []"
  by (induct ds) auto

lemma mrg_plan_Cons_cases:
  fixes c d :: nat
  assumes "sorted_wrt (<) (c # cs)" "sorted_wrt (<) (d # ds)" "set (d # ds) \<subseteq> set (c # cs)"
  shows "\<not> d < c" and "c < d \<Longrightarrow> set (d # ds) \<subseteq> set cs" and "c = d \<Longrightarrow> set ds \<subseteq> set cs"
proof -
  have d: "d \<in> set (c # cs)" using assms(3) by simp
  then show "\<not> d < c" using assms(1) by auto
  show "set (d # ds) \<subseteq> set cs" if cd: "c < d"
  proof
    fix x assume x: "x \<in> set (d # ds)"
    then have "c < x" using cd assms(2) by (auto intro: less_trans)
    then show "x \<in> set cs" using x assms(3) by auto
  qed
  show "set ds \<subseteq> set cs" if cd: "c = d"
    using assms(2,3) cd by auto
qed

lemma mrg_left_key_all_False:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     (\<forall>i \<in> set (mrg_left_key (mrg_plan cs1 cs2)). \<not> i) = (cs2 = [])"
proof (induct cs1 cs2 rule: mrg_plan.induct)
  case (1 ds)
  then show ?case by (simp add: mrg_left_key_MRgt)
next
  case (2 c cs)
  then show ?case by simp
next
  case (3 c cs d ds)
  note cc = mrg_plan_Cons_cases[OF 3(4,5,6)]
  show ?case
  proof (cases "c < d")
    case True
    then show ?thesis using 3(1)[OF True] 3(4,5) cc(2)[OF True] by simp
  next
    case False
    then have "c = d" using cc(1) by simp
    then show ?thesis by simp
  qed
qed

lemma mrg_left_key_all_True:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     (\<forall>i \<in> set (mrg_left_key (mrg_plan cs1 cs2)). i) = (cs2 = cs1)"
proof (induct cs1 cs2 rule: mrg_plan.induct)
  case (1 ds)
  then show ?case by (simp add: mrg_left_key_MRgt)
next
  case (2 c cs)
  then show ?case by simp
next
  case (3 c cs d ds)
  note cc = mrg_plan_Cons_cases[OF 3(4,5,6)]
  show ?case
  proof (cases "c < d")
    case True
    then show ?thesis by simp
  next
    case False
    then have e: "c = d" using cc(1) by simp
    then show ?thesis using 3(3)[OF False cc(1)] 3(4,5) cc(3)[OF e] False by simp
  qed
qed

text \<open>
  The mask and the arguments describe the same frame: both column lists are ascending, the left
  one's columns are among the right one's, and the mask marks them.  This is what @{const dargs}
  sets up.
\<close>

definition dmsk_args :: "args \<Rightarrow> bool list \<Rightarrow> bool" where
  "dmsk_args args msk \<longleftrightarrow> sorted_wrt (<) (args_R args) \<and> sorted_wrt (<) (args_L args) \<and>
     set (args_L args) \<subseteq> set (args_R args) \<and> msk = mrg_left_key (mrg_plan (args_R args) (args_L args))"

lemma dmsk_args_dproj:
  assumes dm: "dmsk_args args msk" and l: "length as = length (args_R args)"
  shows "dproj msk as = restrict (args_L args) (args_R args) as"
proof -
  let ?R = "args_R args" and ?L = "args_L args"
  have sR: "sorted_wrt (<) ?R" and sL: "sorted_wrt (<) ?L" and sub: "set ?L \<subseteq> set ?R"
    and m: "msk = mrg_left_key (mrg_plan ?R ?L)" using dm by (auto simp: dmsk_args_def)
  have fR: "dframe ?R ?R" and fL: "dframe ?L ?L"
    using sR sL by (auto simp: dframe_def strict_sorted_iff)
  have w: "wf_tuple ?R as" using l by (simp add: wf_tuple_def)
  have "dproj msk (restrict ?R ?R as) = restrict ?L ?L (restrict ?L ?R as)"
    unfolding m by (rule dproj_left_key_eq[OF fR fL sub])
  then show ?thesis
    using restrict_idle[OF dframeD(1)[OF fR] w]
      restrict_idle[OF dframeD(1)[OF fL] wf_tuple_restrict[of ?L ?R as]] by simp
qed

lemma dmsk_args_empty: "dmsk_args args msk \<Longrightarrow> (args_L args = []) = (\<forall>i \<in> set msk. \<not> i)"
  by (simp add: dmsk_args_def mrg_left_key_all_False)

lemma dmsk_args_full: "dmsk_args args msk \<Longrightarrow> (args_L args = args_R args) = (\<forall>i \<in> set msk. i)"
  by (simp add: dmsk_args_def mrg_left_key_all_True)

lemma dmsk_args_dargs:
  assumes "sorted_wrt (<) cs_R" "sorted_wrt (<) cs_L" "set cs_L \<subseteq> set cs_R"
  shows "dmsk_args (dargs cs_R cs_L args) (mrg_left_key (mrg_plan cs_R cs_L))"
  using assms by (simp add: dmsk_args_def)

subsection \<open>The dense Since structure\<close>

text \<open>
  The state is the verified one with the two indexed tables replaced by @{const didx} indices,
  and the mask carried along.  Everything else -- the two queues, the window's table, and the two
  mappings that carry the timestamps -- is kept verbatim.

  The verified state a dense state stands for is recovered by \<open>dmsaux_of\<close> below.  It is a
  specification device only: it rebuilds the two indexed tables from the keys of the mappings,
  which the generated code never does.
\<close>

type_synonym 'a dmsaux = "ts \<times> ts \<times> bool list \<times>
  (ts \<times> 'a table) queue \<times> (ts \<times> 'a table) queue \<times> 'a table \<times>
  ('a tuple, 'a table) mapping \<times> ('a tuple, ts) mapping \<times>
  ('a tuple, 'a table) mapping \<times> ('a tuple, ts) mapping"

text \<open>
  The index is consulted only by the general branch of the join.  Where the verified structure
  falls back on the plain key set -- no join columns, or all columns join columns -- the dense
  structure keeps no index at all.
\<close>

definition didx_live :: "args \<Rightarrow> bool" where
  "didx_live args \<longleftrightarrow> args_L args \<noteq> [] \<and> args_L args \<noteq> args_R args"

definition didx_upd :: "args \<Rightarrow> (unit \<Rightarrow> ('a tuple, 'a table) mapping) \<Rightarrow>
    ('a tuple, 'a table) mapping" where
  "didx_upd args w = (if didx_live args then w () else Mapping.empty)"

fun dmsaux_of :: "args \<Rightarrow> 'a dmsaux \<Rightarrow> 'a mmsaux" where
  "dmsaux_of args (nt, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
     (nt, gc, data_prev, data_in, table_in, wf_table_of_set_args args (Mapping.keys tuple_in), tuple_in,
      wf_table_of_set_args args (Mapping.keys tuple_since), tuple_since)"

fun mmsaux_norm :: "args \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "mmsaux_norm args (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in,
      wf_table_since, tuple_since) =
     (nt, gc, data_prev, data_in, table_in,
      wf_table_of_set_args args (Mapping.keys tuple_in), tuple_in,
      wf_table_of_set_args args (Mapping.keys tuple_since), tuple_since)"

text \<open>
  Both indexed tables are determined by the mapping they index, so normalising them away does not
  leave the invariant.
\<close>

lemma valid_mmsaux_norm: "valid_mmsaux args cur aux ys \<Longrightarrow>
    valid_mmsaux args cur (mmsaux_norm args aux) ys"
  by (cases aux) (auto simp: wf_table_sig_args wf_table_of_set_args)

fun dmsaux_inv :: "args \<Rightarrow> bool list \<Rightarrow> 'a dmsaux \<Rightarrow> bool" where
  "dmsaux_inv args msk (nt, gc, m, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) \<longleftrightarrow>
     m = msk \<and> (didx_live args \<longrightarrow> idx_in = didx msk (Mapping.keys tuple_in)
       \<and> idx_since = didx msk (Mapping.keys tuple_since))"

definition valid_dmsaux :: "args \<Rightarrow> bool list \<Rightarrow> ts \<Rightarrow> 'a dmsaux \<Rightarrow> 'a Monitor.msaux \<Rightarrow> bool" where
  "valid_dmsaux args msk cur daux ys \<longleftrightarrow>
     valid_mmsaux args cur (dmsaux_of args daux) ys \<and> dmsaux_inv args msk daux"

lemma dmsk_args_length: "dmsk_args args msk \<Longrightarrow> length msk = length (args_R args)"
  by (simp add: dmsk_args_def length_mrg_left_key)

subsection \<open>What the window's entry and exit do to the keys\<close>

text \<open>
  The two folds that move tables out of and into the window report the tuples they removed and
  added.  That report is exactly the difference between the old and the new key set, which is what
  the index has to be reduced by and combined with.
\<close>

lemma fold_filter_set_keys:
  "fold filter_set ds (m, Y) = (m', Y') \<Longrightarrow> Y \<inter> Mapping.keys m = {} \<Longrightarrow>
     Mapping.keys m' = Mapping.keys m - Y' \<and> Y \<subseteq> Y'"
proof (induct ds arbitrary: m Y)
  case (Cons a ds)
  obtain t X where a: "a = (t, X)" by (cases a)
  define m'' where "m'' = Mapping.filter (filter_cond X m t) m"
  define Y'' where "Y'' = Y \<union> (Mapping.keys m - Mapping.keys m'')"
  have step: "filter_set a (m, Y) = (m'', Y'')"
    by (simp add: a filter_set.simps Let_def m''_def Y''_def)
  have sub: "Mapping.keys m'' \<subseteq> Mapping.keys m"
    by (auto simp: m''_def Mapping_keys_filter)
  have dis: "Y'' \<inter> Mapping.keys m'' = {}"
    using Cons(3) sub by (auto simp: Y''_def)
  have f: "fold filter_set ds (m'', Y'') = (m', Y')" using Cons(2) step by simp
  have IH: "Mapping.keys m' = Mapping.keys m'' - Y' \<and> Y'' \<subseteq> Y'" by (rule Cons(1)[OF f dis])
  show ?case using IH sub by (auto simp: Y''_def)
qed auto

lemma fold_upd_set_keys_keys:
  "fold (upd_set_keys Z) ds (m, Y) = (m', Y') \<Longrightarrow> Y \<subseteq> Mapping.keys m \<Longrightarrow>
     Mapping.keys m' = Mapping.keys m \<union> Y' \<and> Y \<subseteq> Y'"
proof (induct ds arbitrary: m Y)
  case (Cons a ds)
  obtain t X where a: "a = (t, X)" by (cases a)
  define A where "A = Z X t"
  have step: "upd_set_keys Z a (m, Y) = (upd_set m (\<lambda>_. t) A, Y \<union> A)"
    by (simp add: a upd_set_keys.simps A_def)
  have k: "Mapping.keys (upd_set m (\<lambda>_. t) A) = Mapping.keys m \<union> A"
    by (simp add: Mapping_upd_set_keys)
  have f: "fold (upd_set_keys Z) ds (upd_set m (\<lambda>_. t) A, Y \<union> A) = (m', Y')"
    using Cons(2) step by simp
  have sub: "Y \<union> A \<subseteq> Mapping.keys (upd_set m (\<lambda>_. t) A)" using Cons(3) k by auto
  have IH: "Mapping.keys m' = Mapping.keys (upd_set m (\<lambda>_. t) A) \<union> Y' \<and> Y \<union> A \<subseteq> Y'"
    by (rule Cons(1)[OF f sub])
  show ?case using IH k by auto
qed auto

lemma fold_filter_set_keys':
  "fold filter_set ds (m, {}) = (m', Y') \<Longrightarrow> Mapping.keys m' = Mapping.keys m - Y'"
  using fold_filter_set_keys[of ds m "{}" m' Y'] by simp

lemma fold_upd_set_keys_keys':
  "fold (upd_set_keys Z) ds (m, {}) = (m', Y') \<Longrightarrow> Mapping.keys m' = Mapping.keys m \<union> Y'"
  using fold_upd_set_keys_keys[of Z ds m "{}" m' Y'] by simp

subsection \<open>The operations that do not probe\<close>

text \<open>
  All but the join leave the probe alone, so each is the verified operation with the index
  maintenance put in place of the indexed table's.  The window's entry and exit are the only
  places where the index changes without the join: a table enters or leaves in one piece, so the
  index is combined with, or reduced by, the index of that table.
\<close>

definition dinit_msaux :: "args \<Rightarrow> bool list \<Rightarrow> 'a dmsaux" where
  "dinit_msaux args msk = (0, 0, msk, empty_queue, empty_queue, {},
     Mapping.empty, Mapping.empty, Mapping.empty, Mapping.empty)"

fun dshift_end :: "args \<Rightarrow> ts \<Rightarrow> 'a dmsaux \<Rightarrow> 'a dmsaux" where
  "dshift_end args nt (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let I = args_ivl args;
     data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev;
     (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in;
     (tuple_in, del) = fold filter_set discard (tuple_in, {}) in
     (t, gc, msk, data_prev', data_in, table_in - del,
      didx_upd args (\<lambda>_. didx_minus idx_in (didx msk del)), tuple_in, idx_since, tuple_since))"

fun dadd_new_ts_msaux' :: "args \<Rightarrow> ts \<Rightarrow> 'a dmsaux \<Rightarrow> 'a dmsaux" where
  "dadd_new_ts_msaux' args nt (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let I = args_ivl args;
     (data_prev, move) = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev;
     data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
     (tuple_in, add) = fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}))
        move (tuple_in, {}) in
     (nt, gc, msk, data_prev, data_in, table_in \<union> add,
      didx_upd args (\<lambda>_. didx_union idx_in (didx msk add)), tuple_in, idx_since, tuple_since))"

definition dadd_new_ts_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'a dmsaux \<Rightarrow> 'a dmsaux" where
  "dadd_new_ts_msaux args nt daux = dadd_new_ts_msaux' args nt (dshift_end args nt daux)"

fun dgc_msaux :: "args \<Rightarrow> 'a dmsaux \<Rightarrow> 'a dmsaux" where
  "dgc_msaux args (nt, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let all_tuples = \<Union>(snd ` (set (linearize data_prev) \<union> set (linearize data_in)));
     tuple_since' = Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since in
     (nt, nt, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      didx_upd args (\<lambda>_. didx msk (Mapping.keys tuple_since')), tuple_since'))"

fun dadd_new_table_msaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a dmsaux \<Rightarrow> 'a dmsaux" where
  "dadd_new_table_msaux args X (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let X' = minus_keys X tuple_since;
     tuple_since' = upd_set tuple_since (\<lambda>_. t) X';
     idx_since' = didx_upd args (\<lambda>_. didx_union idx_since (didx msk X')) in
     (if memL (args_ivl args) 0 then
        (t, gc, msk, data_prev, append_queue (t, X) data_in, table_in \<union> X,
         didx_upd args (\<lambda>_. didx_union idx_in (didx msk X)), upd_set tuple_in (\<lambda>_. t) X,
         idx_since', tuple_since')
      else (t, gc, msk, append_queue (t, X) data_prev, data_in, table_in, idx_in, tuple_in,
         idx_since', tuple_since')))"

fun dresult_msaux :: "args \<Rightarrow> 'a dmsaux \<Rightarrow> 'a table" where
  "dresult_msaux args (nt, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) = table_in"

subsection \<open>The join\<close>

text \<open>
  The three branches are the verified ones, read densely.  Without join columns the mask is
  all-false, the dense projection of every stored tuple is the empty tuple, and the whole window
  stands or falls with @{term \<open>[] \<in> Y\<close>}.  When every column is a join column the mask is
  all-true, the dense projection is the identity, and the probe table is compared with the stored
  tables directly.  Otherwise the index decides: a bucket's key is what the probe table holds, so
  the surviving tuples are the union of the surviving buckets, and the index of the survivors is
  the restriction of the index.
\<close>

fun djoin_msaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a dmsaux \<Rightarrow> 'a dmsaux" where
  "djoin_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let pos = args_pos args in
     (if \<forall>i \<in> set msk. \<not> i then
        (let take_all = (([] \<in> Y) = pos) in
         (t, gc, msk, data_prev, data_in,
          if take_all then table_in else {},
          if take_all then idx_in else Mapping.empty,
          if take_all then tuple_in else Mapping.empty,
          if take_all then idx_since else Mapping.empty,
          if take_all then tuple_since else Mapping.empty))
      else if \<forall>i \<in> set msk. i then
        (let in_del = (if pos then table_in - Y else table_in \<inter> Y);
         tuple_in' = mapping_delete_set tuple_in in_del;
         tuple_since' = Mapping.filter (\<lambda>as _. (as \<in> Y) = pos) tuple_since in
         (t, gc, msk, data_prev, data_in, table_in - in_del, Mapping.empty, tuple_in',
          Mapping.empty, tuple_since'))
      else
        (let in_del = dsemi_idx msk (\<not> pos) idx_in Y;
         since_del = dsemi_idx msk (\<not> pos) idx_since Y in
         (t, gc, msk, data_prev, data_in, table_in - in_del,
          Mapping.filter (\<lambda>k _. (k \<in> Y) = pos) idx_in, mapping_delete_set tuple_in in_del,
          Mapping.filter (\<lambda>k _. (k \<in> Y) = pos) idx_since,
          mapping_delete_set tuple_since since_del))))"

fun dgc_join_msaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a dmsaux \<Rightarrow> 'a dmsaux" where
  "dgc_join_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (if \<not> memR (args_ivl args) (t - gc)
     then djoin_msaux args Y (dgc_msaux args (t, gc, msk, data_prev, data_in, table_in, idx_in,
       tuple_in, idx_since, tuple_since))
     else djoin_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
       idx_since, tuple_since))"

subsection \<open>The dense operations are the verified ones\<close>

lemma dmsaux_cases:
  fixes daux :: "'a dmsaux"
  obtains t gc msk data_prev data_in table_in idx_in tuple_in idx_since tuple_since
  where "daux = (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
    idx_since, tuple_since)"
  by (metis prod.collapse)

lemma dmsaux_of_dinit: "dmsaux_of args (dinit_msaux args msk) = init_mmsaux args"
  by (simp add: dinit_msaux_def wf_table_of_set_args_def)

lemma dmsaux_inv_dinit: "dmsaux_inv args msk (dinit_msaux args msk)"
  by (simp add: dinit_msaux_def)

lemma valid_dinit_msaux:
  assumes "set L \<subseteq> set R" "distinct L" "distinct R"
  shows "valid_dmsaux (init_args I n L R b agg) msk 0
    (dinit_msaux (init_args I n L R b agg) msk) []"
  unfolding valid_dmsaux_def dmsaux_of_dinit
  by (rule conjI[OF valid_init_mmsaux[OF assms] dmsaux_inv_dinit])

lemma dmsaux_of_dshift_end:
  "dmsaux_of args (dshift_end args nt daux)
   = mmsaux_norm args (shift_end args nt (dmsaux_of args daux))"
  by (cases daux rule: dmsaux_cases) (simp add: Let_def split: prod.splits)

lemma dmsaux_inv_dshift_end:
  assumes "dmsaux_inv args msk daux"
  shows "dmsaux_inv args msk (dshift_end args nt daux)"
proof (cases daux rule: dmsaux_cases)
  case (1 t gc m dp di ti ii tui idxs tus)
  show ?thesis
    using assms unfolding 1
    by (auto simp: Let_def didx_upd_def didx_minus_eq split: prod.splits
        dest!: fold_filter_set_keys')
qed

lemma valid_dmsauxI:
  assumes "valid_mmsaux args cur aux ys"
    and "dmsaux_of args daux = mmsaux_norm args aux"
    and "dmsaux_inv args msk daux"
  shows "valid_dmsaux args msk cur daux ys"
  unfolding valid_dmsaux_def assms(2)
  by (rule conjI[OF valid_mmsaux_norm[OF assms(1)] assms(3)])

lemma valid_dmsauxD:
  "valid_dmsaux args msk cur daux ys \<Longrightarrow> valid_mmsaux args cur (dmsaux_of args daux) ys"
  by (simp add: valid_dmsaux_def)

lemma valid_dmsaux_inv: "valid_dmsaux args msk cur daux ys \<Longrightarrow> dmsaux_inv args msk daux"
  by (simp add: valid_dmsaux_def)

lemma valid_dshift_end:
  assumes "valid_dmsaux args msk cur daux ys" and "nt \<ge> cur"
  shows "valid_dmsaux args msk cur (dshift_end args nt daux)
     (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) ys)"
  by (rule valid_dmsauxI[OF valid_shift_end_mmsaux[OF valid_dmsauxD[OF assms(1)] assms(2)]
      dmsaux_of_dshift_end dmsaux_inv_dshift_end[OF valid_dmsaux_inv[OF assms(1)]]])

lemma dmsaux_of_dadd_new_ts':
  "dmsaux_of args (dadd_new_ts_msaux' args nt daux)
   = mmsaux_norm args (add_new_ts_mmsaux' args nt (dmsaux_of args daux))"
  by (cases daux rule: dmsaux_cases) (simp add: Let_def split: prod.splits)

lemma dmsaux_inv_dadd_new_ts':
  assumes "dmsaux_inv args msk daux"
  shows "dmsaux_inv args msk (dadd_new_ts_msaux' args nt daux)"
proof (cases daux rule: dmsaux_cases)
  case (1 t gc m dp di ti ii tui idxs tus)
  show ?thesis
    using assms unfolding 1
    by (auto simp: Let_def didx_upd_def didx_union_eq split: prod.splits
        dest!: fold_upd_set_keys_keys')
qed

lemma valid_dadd_new_ts':
  assumes "valid_dmsaux args msk cur daux ys" and "nt \<ge> cur"
  shows "valid_dmsaux args msk nt (dadd_new_ts_msaux' args nt daux) ys"
  by (rule valid_dmsauxI[OF valid_add_new_ts_mmsaux'[OF valid_dmsauxD[OF assms(1)] assms(2)]
      dmsaux_of_dadd_new_ts' dmsaux_inv_dadd_new_ts'[OF valid_dmsaux_inv[OF assms(1)]]])

lemma valid_dadd_new_ts:
  assumes "valid_dmsaux args msk cur daux ys" and "nt \<ge> cur"
  shows "valid_dmsaux args msk nt (dadd_new_ts_msaux args nt daux)
     (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) ys)"
  unfolding dadd_new_ts_msaux_def
  by (rule valid_dadd_new_ts'[OF valid_dshift_end[OF assms] assms(2)])

lemma dmsaux_of_dgc:
  "dmsaux_of args (dgc_msaux args daux) = mmsaux_norm args (gc_mmsaux args (dmsaux_of args daux))"
  by (cases daux rule: dmsaux_cases) (simp add: Let_def)

lemma dmsaux_inv_dgc:
  "dmsaux_inv args msk daux \<Longrightarrow> dmsaux_inv args msk (dgc_msaux args daux)"
  by (cases daux rule: dmsaux_cases) (simp add: Let_def didx_upd_def)

lemma valid_dgc:
  assumes "valid_dmsaux args msk cur daux ys"
  shows "valid_dmsaux args msk cur (dgc_msaux args daux) ys"
  by (rule valid_dmsauxI[OF valid_gc_mmsaux[OF valid_dmsauxD[OF assms]]
      dmsaux_of_dgc dmsaux_inv_dgc[OF valid_dmsaux_inv[OF assms]]])

lemma dmsaux_of_dadd_new_table:
  "dmsaux_of args (dadd_new_table_msaux args X daux)
   = mmsaux_norm args (add_new_table_mmsaux args X (dmsaux_of args daux))"
  by (cases daux rule: dmsaux_cases) (simp add: Let_def)

lemma dmsaux_inv_dadd_new_table:
  "dmsaux_inv args msk daux \<Longrightarrow> dmsaux_inv args msk (dadd_new_table_msaux args X daux)"
  by (cases daux rule: dmsaux_cases)
     (simp add: Let_def didx_upd_def didx_union_eq Mapping_upd_set_keys)

lemma valid_dadd_new_table:
  assumes "valid_dmsaux args msk cur daux ys" and "table (args_R args) X"
  shows "valid_dmsaux args msk cur (dadd_new_table_msaux args X daux)
    (case ys of [] \<Rightarrow> [(cur, X)]
     | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # ys)"
  by (rule valid_dmsauxI[OF valid_add_new_table_mmsaux[OF valid_dmsauxD[OF assms(1)] assms(2)]
      dmsaux_of_dadd_new_table dmsaux_inv_dadd_new_table[OF valid_dmsaux_inv[OF assms(1)]]])

lemma dresult_msaux_eq: "dresult_msaux args daux = result_mmsaux args (dmsaux_of args daux)"
  by (cases daux rule: dmsaux_cases) simp

lemma valid_dresult_msaux:
  "valid_dmsaux args msk cur daux ys \<Longrightarrow> dresult_msaux args daux
    = foldr (\<union>) [rel. (t, rel) \<leftarrow> ys, memL (args_ivl args) (cur - t)] {}"
  by (simp add: dresult_msaux_eq valid_result_mmsaux[OF valid_dmsauxD])

subsection \<open>The join is the verified join\<close>

lemma dproj_all_False: "\<forall>i \<in> set msk. \<not> i \<Longrightarrow> length as = length msk \<Longrightarrow> dproj msk as = []"
  by (induct msk as rule: dproj.induct) auto

lemma dproj_all_True_mask: "\<forall>i \<in> set msk. i \<Longrightarrow> length as = length msk \<Longrightarrow> dproj msk as = as"
  by (induct msk as rule: dproj.induct) auto

lemma Mapping_filter_True: "Mapping.filter (\<lambda>_ _. True) m = m"
  by (intro mapping_eqI) (simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_filter_False: "Mapping.filter (\<lambda>_ _. False) m = Mapping.empty"
  by (intro mapping_eqI) (simp add: Mapping.lookup_filter split: option.splits)

lemma mapping_delete_set_filter:
  "D = {as \<in> Mapping.keys m. \<not> P as} \<Longrightarrow> mapping_delete_set m D = Mapping.filter (\<lambda>as _. P as) m"
  by (intro mapping_eqI)
     (auto simp: delete_set_lookup Mapping.lookup_filter Mapping.keys_dom_lookup
       split: option.splits)

text \<open>
  Whichever branch it takes, the dense join filters both mappings by the dense test, and the
  window's table follows the mapping it indexes.  That is the verified join's abstract form
  (@{const join_mmsaux_abs}).
\<close>

lemma djoin_msaux_abs:
  assumes v: "valid_dmsaux args msk cur (t, gc, m, dp, di, ti, ii, tui, idxs, tus) ys"
    and dm: "dmsk_args args msk"
  shows "dmsaux_of args (djoin_msaux args Y (t, gc, m, dp, di, ti, ii, tui, idxs, tus))
     = join_mmsaux_abs args Y (dmsaux_of args (t, gc, m, dp, di, ti, ii, tui, idxs, tus))"
proof -
  have vm: "valid_mmsaux args cur (dmsaux_of args (t, gc, m, dp, di, ti, ii, tui, idxs, tus)) ys"
    by (rule valid_dmsauxD[OF v])
  have mm: "m = msk" using valid_dmsaux_inv[OF v] by simp
  have lm: "length msk = length (args_R args)" by (rule dmsk_args_length[OF dm])
  have ti_keys: "ti = Mapping.keys tui"
    and tab_in: "table (args_R args) (Mapping.keys tui)"
    and tab_since: "table (args_R args) (Mapping.keys tus)"
    using vm by simp_all
  have len_in: "length as = length (args_R args)" if "as \<in> Mapping.keys tui" for as
    using tab_in that by (auto simp: table_def wf_tuple_def)
  have len_since: "length as = length (args_R args)" if "as \<in> Mapping.keys tus" for as
    using tab_since that by (auto simp: table_def wf_tuple_def)
  have fin: "Mapping.filter (\<lambda>as _. join_cond (args_pos args) Y
        (restrict (args_L args) (args_R args) as)) tui
      = Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tui"
    by (rule Mapping_filter_cong) (simp add: join_cond_eq dmsk_args_dproj[OF dm len_in])
  have fsince: "Mapping.filter (\<lambda>as _. join_cond (args_pos args) Y
        (restrict (args_L args) (args_R args) as)) tus
      = Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tus"
    by (rule Mapping_filter_cong) (simp add: join_cond_eq dmsk_args_dproj[OF dm len_since])
  show ?thesis
  proof (cases "\<forall>i \<in> set msk. \<not> i")
    case True
    have cin: "Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tui
        = (if ([] \<in> Y) = args_pos args then tui else Mapping.empty)"
    proof -
      have "Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tui
          = Mapping.filter (\<lambda>as _. ([] \<in> Y) = args_pos args) tui"
        by (rule Mapping_filter_cong) (simp add: dproj_all_False[OF True] len_in lm)
      then show ?thesis
        by (cases "([] \<in> Y) = args_pos args")
           (simp_all add: Mapping_filter_True Mapping_filter_False)
    qed
    have csince: "Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tus
        = (if ([] \<in> Y) = args_pos args then tus else Mapping.empty)"
    proof -
      have "Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tus
          = Mapping.filter (\<lambda>as _. ([] \<in> Y) = args_pos args) tus"
        by (rule Mapping_filter_cong) (simp add: dproj_all_False[OF True] len_since lm)
      then show ?thesis
        by (cases "([] \<in> Y) = args_pos args")
           (simp_all add: Mapping_filter_True Mapping_filter_False)
    qed
    show ?thesis
      using True unfolding mm by (auto simp: Let_def fin fsince cin csince ti_keys wf_table_of_set_args_def)
  next
    case False
    note noneF = False
    show ?thesis
    proof (cases "\<forall>i \<in> set msk. i")
      case True
      have cin: "Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tui
          = Mapping.filter (\<lambda>as _. (as \<in> Y) = args_pos args) tui"
        by (rule Mapping_filter_cong) (simp add: dproj_all_True_mask[OF True] len_in lm)
      have csince: "Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tus
          = Mapping.filter (\<lambda>as _. (as \<in> Y) = args_pos args) tus"
        by (rule Mapping_filter_cong) (simp add: dproj_all_True_mask[OF True] len_since lm)
      have d: "(if args_pos args then ti - Y else ti \<inter> Y)
          = {as \<in> Mapping.keys tui. \<not> ((as \<in> Y) = args_pos args)}"
        unfolding ti_keys by auto
      have e: "mapping_delete_set tui (if args_pos args then ti - Y else ti \<inter> Y)
          = Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tui"
        unfolding cin by (rule mapping_delete_set_filter[OF d])
      have f: "ti - (if args_pos args then ti - Y else ti \<inter> Y)
          = Mapping.keys (Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tui)"
        unfolding e[symmetric] ti_keys by simp
      show ?thesis
        using noneF True unfolding mm
        by (auto simp: Let_def fin fsince e f csince[symmetric])
    next
      case False
      have live: "didx_live args"
        using noneF False dmsk_args_empty[OF dm] dmsk_args_full[OF dm]
        by (simp add: didx_live_def)
      have ixin: "ii = didx msk (Mapping.keys tui)"
        and ixs: "idxs = didx msk (Mapping.keys tus)"
        using valid_dmsaux_inv[OF v] live by simp_all
      have din: "dsemi_idx msk (\<not> args_pos args) ii Y
          = {as \<in> Mapping.keys tui. \<not> ((dproj msk as \<in> Y) = args_pos args)}"
        unfolding ixin dsemi_idx_dsemi by (auto simp: dsemi_def)
      have ds: "dsemi_idx msk (\<not> args_pos args) idxs Y
          = {as \<in> Mapping.keys tus. \<not> ((dproj msk as \<in> Y) = args_pos args)}"
        unfolding ixs dsemi_idx_dsemi by (auto simp: dsemi_def)
      have e: "mapping_delete_set tui (dsemi_idx msk (\<not> args_pos args) ii Y)
          = Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tui"
        by (rule mapping_delete_set_filter[OF din])
      have e': "mapping_delete_set tus (dsemi_idx msk (\<not> args_pos args) idxs Y)
          = Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tus"
        by (rule mapping_delete_set_filter[OF ds])
      have f: "ti - dsemi_idx msk (\<not> args_pos args) ii Y
          = Mapping.keys (Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tui)"
        unfolding e[symmetric] ti_keys by simp
      show ?thesis
        using noneF False unfolding mm
        by (auto simp: Let_def fin fsince e e' f)
    qed
  qed
qed

lemma dmsaux_inv_djoin:
  assumes v: "valid_dmsaux args msk cur (t, gc, m, dp, di, ti, ii, tui, idxs, tus) ys"
    and dm: "dmsk_args args msk"
  shows "dmsaux_inv args msk (djoin_msaux args Y (t, gc, m, dp, di, ti, ii, tui, idxs, tus))"
proof (cases "\<forall>i \<in> set msk. \<not> i")
  case True
  then have "\<not> didx_live args" using dmsk_args_empty[OF dm] by (auto simp: didx_live_def)
  then show ?thesis using valid_dmsaux_inv[OF v] True by (simp add: Let_def)
next
  case False
  note noneF = False
  show ?thesis
  proof (cases "\<forall>i \<in> set msk. i")
    case True
    then have "\<not> didx_live args" using dmsk_args_full[OF dm] by (auto simp: didx_live_def)
    then show ?thesis using valid_dmsaux_inv[OF v] noneF True by (simp add: Let_def)
  next
    case False
    have live: "didx_live args"
      using noneF False dmsk_args_empty[OF dm] dmsk_args_full[OF dm] by (simp add: didx_live_def)
    have mm: "m = msk" using valid_dmsaux_inv[OF v] by simp
    have ixin: "ii = didx msk (Mapping.keys tui)"
      and ixs: "idxs = didx msk (Mapping.keys tus)"
      using valid_dmsaux_inv[OF v] live by simp_all
    have fi: "Mapping.filter (\<lambda>k _. (k \<in> Y) = args_pos args) ii
        = didx msk (dsemi msk (args_pos args) (Mapping.keys tui) Y)"
      unfolding ixin by (rule didx_filter)
    have fs: "Mapping.filter (\<lambda>k _. (k \<in> Y) = args_pos args) idxs
        = didx msk (dsemi msk (args_pos args) (Mapping.keys tus) Y)"
      unfolding ixs by (rule didx_filter)
    have ki: "Mapping.keys tui - dsemi_idx msk (\<not> args_pos args) ii Y
        = dsemi msk (args_pos args) (Mapping.keys tui) Y"
      unfolding ixin dsemi_idx_dsemi by (auto simp: dsemi_def)
    have ks: "Mapping.keys tus - dsemi_idx msk (\<not> args_pos args) idxs Y
        = dsemi msk (args_pos args) (Mapping.keys tus) Y"
      unfolding ixs dsemi_idx_dsemi by (auto simp: dsemi_def)
    show ?thesis
      using noneF False unfolding mm by (auto simp: Let_def fi fs ki ks)
  qed
qed

subsection \<open>The join's validity\<close>

lemma mmsaux_cases:
  fixes aux :: "'a mmsaux"
  obtains nt gc data_prev data_in table_in wf_table_in tuple_in wf_table_since tuple_since
  where "aux = (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in,
    wf_table_since, tuple_since)"
  by (metis prod.collapse)

lemma join_mmsaux_abs_eq':
  assumes "valid_mmsaux args cur aux auxlist" and "table (args_L args) X"
  shows "join_mmsaux args X aux = join_mmsaux_abs args X aux"
proof (cases aux rule: mmsaux_cases)
  case (1 nt gc dp di ti wi tui ws tus)
  show ?thesis unfolding 1
    by (rule join_mmsaux_abs_eq[OF assms(1)[unfolded 1] assms(2)])
qed

lemma mmsaux_norm_join_mmsaux_abs:
  "mmsaux_norm args (join_mmsaux_abs args X aux) = join_mmsaux_abs args X aux"
  by (cases aux rule: mmsaux_cases) (simp add: Let_def)

lemma valid_djoin:
  assumes v: "valid_dmsaux args msk cur daux ys" and dm: "dmsk_args args msk"
    and tY: "table (args_L args) Y"
  shows "valid_dmsaux args msk cur (djoin_msaux args Y daux)
     (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) Y)) ys)"
proof (cases daux rule: dmsaux_cases)
  case (1 t gc m dp di ti ii tui idxs tus)
  have vm: "valid_mmsaux args cur (dmsaux_of args daux) ys" by (rule valid_dmsauxD[OF v])
  have abs: "dmsaux_of args (djoin_msaux args Y daux)
      = join_mmsaux_abs args Y (dmsaux_of args daux)"
    using djoin_msaux_abs[OF v[unfolded 1] dm] unfolding 1 .
  have eq: "dmsaux_of args (djoin_msaux args Y daux)
      = mmsaux_norm args (join_mmsaux args Y (dmsaux_of args daux))"
    unfolding abs join_mmsaux_abs_eq'[OF vm tY] mmsaux_norm_join_mmsaux_abs ..
  have inv: "dmsaux_inv args msk (djoin_msaux args Y daux)"
    using dmsaux_inv_djoin[OF v[unfolded 1] dm] unfolding 1 .
  show ?thesis
    by (rule valid_dmsauxI[OF valid_join_mmsaux[OF vm tY] eq inv])
qed

lemma valid_dgc_join:
  assumes v: "valid_dmsaux args msk cur daux ys" and dm: "dmsk_args args msk"
    and tY: "table (args_L args) Y"
  shows "valid_dmsaux args msk cur (dgc_join_msaux args Y daux)
     (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) Y)) ys)"
proof -
  have alt: "dgc_join_msaux args Y daux = djoin_msaux args Y (dgc_msaux args daux)
      \<or> dgc_join_msaux args Y daux = djoin_msaux args Y daux"
    by (cases daux rule: dmsaux_cases) auto
  show ?thesis
    using alt
  proof
    assume "dgc_join_msaux args Y daux = djoin_msaux args Y (dgc_msaux args daux)"
    then show ?thesis using valid_djoin[OF valid_dgc[OF v] dm tY] by simp
  next
    assume "dgc_join_msaux args Y daux = djoin_msaux args Y daux"
    then show ?thesis using valid_djoin[OF v dm tY] by simp
  qed
qed

subsection \<open>A window that starts at the current time point\<close>

text \<open>
  The two mappings that record since when a tuple has been seen, @{text tuple_since} and its
  index @{text idx_since}, are read at one place only: when a time point moves from
  @{text data_prev}, the part of the window not yet old enough to count, into @{text data_in}.
  When the interval contains zero no time point is ever too young, the insertion puts every
  table into @{text data_in} directly, and @{text data_prev} stays empty -- so the two mappings,
  and the garbage collection that prunes them, are bookkeeping that nothing reads.  The
  operations below skip them in that case.

  Their validity is the verified one for \<^emph>\<open>some\<close> choice of the two mappings and of the time of
  the last collection, @{text dset_since}; the operations that touch them are the only ones
  that change, and on the fields they do not touch they agree with the verified ones.
\<close>

fun dset_since :: "ts \<Rightarrow> ('a tuple, 'a table) mapping \<Rightarrow> ('a tuple, ts) mapping \<Rightarrow> 'a dmsaux \<Rightarrow>
    'a dmsaux" where
  "dset_since gc' is ts (t, gc, msk, dp, di, ti, ii, tui, idxs, tus) =
     (t, gc', msk, dp, di, ti, ii, tui, is, ts)"

fun dprev_of :: "'a dmsaux \<Rightarrow> (ts \<times> 'a table) queue" where
  "dprev_of (t, gc, msk, dp, di, ti, ii, tui, idxs, tus) = dp"

fun dadd_new_table_lz :: "args \<Rightarrow> 'a table \<Rightarrow> 'a dmsaux \<Rightarrow> 'a dmsaux" where
  "dadd_new_table_lz args X (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (if memL (args_ivl args) 0 then
       (t, gc, msk, data_prev, append_queue (t, X) data_in, table_in \<union> X,
        didx_upd args (\<lambda>_. didx_union idx_in (didx msk X)), upd_set tuple_in (\<lambda>_. t) X,
        idx_since, tuple_since)
     else dadd_new_table_msaux args X (t, gc, msk, data_prev, data_in, table_in, idx_in,
       tuple_in, idx_since, tuple_since))"

definition dgc_join_lz :: "args \<Rightarrow> 'a table \<Rightarrow> 'a dmsaux \<Rightarrow> 'a dmsaux" where
  "dgc_join_lz args Y daux =
    (if memL (args_ivl args) 0 then djoin_msaux args Y daux else dgc_join_msaux args Y daux)"

definition valid_dmsaux_lz :: "args \<Rightarrow> bool list \<Rightarrow> ts \<Rightarrow> 'a dmsaux \<Rightarrow> 'a Monitor.msaux \<Rightarrow> bool"
  where
  "valid_dmsaux_lz args msk cur daux ys \<longleftrightarrow> (if memL (args_ivl args) 0
     then linearize (dprev_of daux) = [] \<and>
       (\<exists>gc is ts. valid_dmsaux args msk cur (dset_since gc is ts daux) ys)
     else valid_dmsaux args msk cur daux ys)"

lemma valid_dmsaux_lz_intro:
  "valid_dmsaux args msk cur daux ys \<Longrightarrow> (memL (args_ivl args) 0 \<Longrightarrow> linearize (dprev_of daux) = [])
    \<Longrightarrow> valid_dmsaux_lz args msk cur daux ys"
  unfolding valid_dmsaux_lz_def by (cases daux rule: dmsaux_cases) (simp, metis)

lemma valid_dinit_msaux_lz:
  assumes "set L \<subseteq> set R" "distinct L" "distinct R"
  shows "valid_dmsaux_lz (init_args I n L R b agg) msk 0
    (dinit_msaux (init_args I n L R b agg) msk) []"
  by (rule valid_dmsaux_lz_intro[OF valid_dinit_msaux[OF assms]])
    (simp add: dinit_msaux_def empty_queue_rep)

lemma dshift_end_dset_since:
  "dshift_end args nt (dset_since g i s daux) = dset_since g i s (dshift_end args nt daux)"
  by (cases daux rule: dmsaux_cases) (simp add: Let_def split: prod.splits)

lemma dadd_new_ts'_dset_since:
  assumes e: "linearize (dprev_of daux) = []"
  shows "dadd_new_ts_msaux' args nt (dset_since g i s daux)
    = dset_since g i s (dadd_new_ts_msaux' args nt daux)"
proof (cases daux rule: dmsaux_cases)
  case (1 t gc m dp di ti ii tui idxs tus)
  obtain dp' mv where tdw: "takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) dp = (dp', mv)"
    by (cases "takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) dp")
  have mv: "mv = []"
    using takedropWhile_queue_snd[of "\<lambda>(t, X). memL (args_ivl args) (nt - t)" dp] e
    unfolding 1 tdw by simp
  show ?thesis unfolding 1
    by (simp add: tdw mv Let_def del: takedropWhile_queue.simps)
qed

lemma dprev_of_dshift_end:
  assumes e: "linearize (dprev_of daux) = []"
  shows "linearize (dprev_of (dshift_end args nt daux)) = []"
proof (cases daux rule: dmsaux_cases)
  case (1 t gc m dp di ti ii tui idxs tus)
  show ?thesis using e unfolding 1
    by (simp add: Let_def dropWhile_queue_rep del: dropWhile_queue.simps takedropWhile_queue.simps
        split: prod.splits)
qed

lemma dprev_of_dadd_new_ts':
  assumes e: "linearize (dprev_of daux) = []"
  shows "linearize (dprev_of (dadd_new_ts_msaux' args nt daux)) = []"
proof (cases daux rule: dmsaux_cases)
  case (1 t gc m dp di ti ii tui idxs tus)
  obtain dp' mv where tdw: "takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) dp = (dp', mv)"
    by (cases "takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) dp")
  have "linearize dp' = []"
    using takedropWhile_queue_fst[of "\<lambda>(t, X). memL (args_ivl args) (nt - t)" dp] e
    unfolding 1 tdw by (simp add: dropWhile_queue_rep del: dropWhile_queue.simps)
  then show ?thesis unfolding 1
    by (simp add: tdw Let_def del: takedropWhile_queue.simps split: prod.splits)
qed

lemma valid_dadd_new_ts_lz:
  assumes v: "valid_dmsaux_lz args msk cur daux ys" and nt: "nt \<ge> cur"
  shows "valid_dmsaux_lz args msk nt (dadd_new_ts_msaux args nt daux)
     (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) ys)"
proof (cases "memL (args_ivl args) 0")
  case True
  obtain g i s where vw: "valid_dmsaux args msk cur (dset_since g i s daux) ys"
    and dp: "linearize (dprev_of daux) = []"
    using v True unfolding valid_dmsaux_lz_def by auto
  have dp': "linearize (dprev_of (dshift_end args nt daux)) = []"
    by (rule dprev_of_dshift_end[OF dp])
  have "dadd_new_ts_msaux args nt (dset_since g i s daux)
      = dset_since g i s (dadd_new_ts_msaux args nt daux)"
    unfolding dadd_new_ts_msaux_def dshift_end_dset_since dadd_new_ts'_dset_since[OF dp'] ..
  then have "valid_dmsaux args msk nt (dset_since g i s (dadd_new_ts_msaux args nt daux))
      (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) ys)"
    using valid_dadd_new_ts[OF vw nt] by simp
  moreover have "linearize (dprev_of (dadd_new_ts_msaux args nt daux)) = []"
    unfolding dadd_new_ts_msaux_def by (rule dprev_of_dadd_new_ts'[OF dp'])
  ultimately show ?thesis unfolding valid_dmsaux_lz_def if_P[OF True] by blast
next
  case False
  then show ?thesis using v valid_dadd_new_ts[OF _ nt] by (simp add: valid_dmsaux_lz_def)
qed

lemma dadd_new_table_lz_dset_since:
  assumes "memL (args_ivl args) 0"
  shows "\<exists>i' s'. dadd_new_table_msaux args X (dset_since g i s daux)
    = dset_since g i' s' (dadd_new_table_lz args X daux)"
  using assms by (cases daux rule: dmsaux_cases) (auto simp: Let_def)

lemma valid_dadd_new_table_lz:
  assumes v: "valid_dmsaux_lz args msk cur daux ys" and X: "table (args_R args) X"
  shows "valid_dmsaux_lz args msk cur (dadd_new_table_lz args X daux)
    (case ys of [] \<Rightarrow> [(cur, X)]
     | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # ys)"
proof (cases "memL (args_ivl args) 0")
  case True
  obtain g i s where vw: "valid_dmsaux args msk cur (dset_since g i s daux) ys"
    and dp: "linearize (dprev_of daux) = []"
    using v True unfolding valid_dmsaux_lz_def by auto
  obtain i' s' where e: "dadd_new_table_msaux args X (dset_since g i s daux)
      = dset_since g i' s' (dadd_new_table_lz args X daux)"
    using dadd_new_table_lz_dset_since[OF True] by blast
  have "linearize (dprev_of (dadd_new_table_lz args X daux)) = []"
    using dp True by (cases daux rule: dmsaux_cases) simp
  then show ?thesis using valid_dadd_new_table[OF vw X]
    unfolding e valid_dmsaux_lz_def if_P[OF True] by blast
next
  case False
  have "dadd_new_table_lz args X daux = dadd_new_table_msaux args X daux"
    using False by (cases daux rule: dmsaux_cases) simp
  then show ?thesis using v valid_dadd_new_table[OF _ X] False
    by (simp add: valid_dmsaux_lz_def)
qed

lemma djoin_dset_since:
  "\<exists>i' s'. djoin_msaux args Y (dset_since g i s daux) = dset_since g i' s' (djoin_msaux args Y daux)"
proof (cases daux rule: dmsaux_cases)
  case (1 t gc msk dp di ti ii tui idxs tus)
  show ?thesis
  proof (cases "\<forall>i \<in> set msk. \<not> i")
    case True
    show ?thesis
      unfolding 1 dset_since.simps djoin_msaux.simps if_P[OF True] Let_def by simp
  next
    case nA: False
    show ?thesis
    proof (cases "\<forall>i \<in> set msk. i")
      case True
      show ?thesis
        unfolding 1 dset_since.simps djoin_msaux.simps if_not_P[OF nA] if_P[OF True] Let_def
        by simp
    next
      case False
      show ?thesis
        unfolding 1 dset_since.simps djoin_msaux.simps if_not_P[OF nA] if_not_P[OF False] Let_def
        by simp
    qed
  qed
qed

lemma dgc_dset_since:
  "\<exists>g' i' s'. dgc_msaux args (dset_since g i s daux) = dset_since g' i' s' daux"
  by (cases daux rule: dmsaux_cases) (auto simp: Let_def)

lemma valid_dgc_join_lz:
  assumes v: "valid_dmsaux_lz args msk cur daux ys" and dm: "dmsk_args args msk"
    and tY: "table (args_L args) Y"
  shows "valid_dmsaux_lz args msk cur (dgc_join_lz args Y daux)
     (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) Y)) ys)"
proof (cases "memL (args_ivl args) 0")
  case True
  obtain g i s where vw: "valid_dmsaux args msk cur (dset_since g i s daux) ys"
    and dp: "linearize (dprev_of daux) = []"
    using v True unfolding valid_dmsaux_lz_def by auto
  have gj: "\<exists>g' i' s'. dgc_join_msaux args Y (dset_since g i s daux)
      = dset_since g' i' s' (djoin_msaux args Y daux)"
  proof -
    have alt: "dgc_join_msaux args Y (dset_since g i s daux)
        = djoin_msaux args Y (dgc_msaux args (dset_since g i s daux))
      \<or> dgc_join_msaux args Y (dset_since g i s daux) = djoin_msaux args Y (dset_since g i s daux)"
      by (cases daux rule: dmsaux_cases) auto
    obtain g1 i1 s1 where c: "dgc_msaux args (dset_since g i s daux) = dset_since g1 i1 s1 daux"
      using dgc_dset_since by blast
    show ?thesis using alt unfolding c by (metis djoin_dset_since)
  qed
  then obtain g' i' s' where e: "dgc_join_msaux args Y (dset_since g i s daux)
      = dset_since g' i' s' (djoin_msaux args Y daux)" by blast
  have "linearize (dprev_of (djoin_msaux args Y daux)) = []"
    using dp by (cases daux rule: dmsaux_cases) (simp add: Let_def)
  moreover have "valid_dmsaux args msk cur (dgc_join_msaux args Y (dset_since g i s daux))
      (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) Y)) ys)"
    by (rule valid_dgc_join[OF vw dm tY])
  ultimately show ?thesis
    unfolding e dgc_join_lz_def valid_dmsaux_lz_def if_P[OF True] by blast
next
  case False
  then show ?thesis using v valid_dgc_join[OF _ dm tY]
    by (simp add: valid_dmsaux_lz_def dgc_join_lz_def)
qed

lemma valid_dresult_msaux_lz:
  "valid_dmsaux_lz args msk cur daux ys \<Longrightarrow> dresult_msaux args daux
    = foldr (\<union>) [rel. (t, rel) \<leftarrow> ys, memL (args_ivl args) (cur - t)] {}"
  unfolding valid_dmsaux_lz_def
  by (cases daux rule: dmsaux_cases) (auto dest: valid_dresult_msaux split: if_splits)

section \<open>The dense Since structure over ascending columns\<close>

text \<open>
  The same relation the verified structure has to the reordered auxiliary list
  (@{const dsaux}), now for the dense structure.
\<close>

definition dmsk :: "cols \<Rightarrow> cols \<Rightarrow> bool list" where
  "dmsk cs_R cs_L = mrg_left_key (mrg_plan cs_R cs_L)"

definition dsaux' :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> event_data dmsaux \<Rightarrow>
    (ts \<times> event_data table) list \<Rightarrow> bool" where
  "dsaux' kR cR cL args cur daux auxlist \<longleftrightarrow>
     (\<forall>(t, rel) \<in> set auxlist. table kR rel) \<and>
     valid_dmsaux_lz (dargs cR cL args) (dmsk cR cL) cur daux (dauxlist kR cR auxlist)"

lemma dframe_sub:
  "dframe kR cR \<Longrightarrow> dframe kL cL \<Longrightarrow> set kL \<subseteq> set kR \<Longrightarrow> set cL \<subseteq> set cR"
  by (simp add: dframe_def)

lemma dsaux'_init:
  assumes fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
  shows "dsaux' kR cR cL args 0 (dinit_msaux (dargs cR cL args) (dmsk cR cL)) []"
proof -
  have "valid_dmsaux_lz (init_args (args_ivl args) (length cR) cL cR (args_pos args) None)
      (dmsk cR cL) 0
      (dinit_msaux (init_args (args_ivl args) (length cR) cL cR (args_pos args) None) (dmsk cR cL)) []"
    by (rule valid_dinit_msaux_lz[OF dframe_sub[OF fR fL sub] dframeD(4)[OF fL] dframeD(4)[OF fR]])
  then show ?thesis by (simp add: dsaux'_def dargs_def dauxlist_def)
qed

lemma dsaux'_add_new_ts:
  assumes v: "dsaux' kR cR cL args cur daux auxlist" and nt: "cur \<le> nt"
  shows "dsaux' kR cR cL args nt (dadd_new_ts_msaux (dargs cR cL args) nt daux)
      (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and d: "valid_dmsaux_lz (dargs cR cL args) (dmsk cR cL) cur daux (dauxlist kR cR auxlist)"
    using v by (auto simp: dsaux'_def)
  have "valid_dmsaux_lz (dargs cR cL args) (dmsk cR cL) nt
      (dadd_new_ts_msaux (dargs cR cL args) nt daux)
      (filter (\<lambda>(t, rel). memR (args_ivl (dargs cR cL args)) (nt - t)) (dauxlist kR cR auxlist))"
    by (rule valid_dadd_new_ts_lz[OF d nt])
  then show ?thesis using w by (simp add: dsaux'_def dauxlist_filter)
qed

lemma dsaux'_join:
  assumes v: "dsaux' kR cR cL args cur daux auxlist"
    and fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and t1: "table kL rel1"
  shows "dsaux' kR cR cL args cur (dgc_join_lz (dargs cR cL args) (dtabc kL cL rel1) daux)
      (map (\<lambda>(t, rel). (t, join kR rel (args_pos args) kL rel1)) auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and d: "valid_dmsaux_lz (dargs cR cL args) (dmsk cR cL) cur daux (dauxlist kR cR auxlist)"
    using v by (auto simp: dsaux'_def)
  have dm: "dmsk_args (dargs cR cL args) (dmsk cR cL)"
    unfolding dmsk_def
    by (rule dmsk_args_dargs[OF dframeD(2)[OF fR] dframeD(2)[OF fL] dframe_sub[OF fR fL sub]])
  have tY: "table (args_L (dargs cR cL args)) (dtabc kL cL rel1)" by (simp add: table_dtabc)
  have "valid_dmsaux_lz (dargs cR cL args) (dmsk cR cL) cur
      (dgc_join_lz (dargs cR cL args) (dtabc kL cL rel1) daux)
      (map (\<lambda>(t, rel). (t, join cR rel (args_pos args) cL (dtabc kL cL rel1)))
        (dauxlist kR cR auxlist))"
    using valid_dgc_join_lz[OF d dm tY] by simp
  then show ?thesis using w
    by (simp add: dsaux'_def dauxlist_join[OF fR fL sub w t1] dauxlist_wf_join[OF w sub t1])
qed

lemma dsaux'_add_new_table:
  assumes v: "dsaux' kR cR cL args cur daux auxlist" and t2: "table kR rel2"
  shows "dsaux' kR cR cL args cur (dadd_new_table_lz (dargs cR cL args) (dtabc kR cR rel2) daux)
      (case auxlist of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and d: "valid_dmsaux_lz (dargs cR cL args) (dmsk cR cL) cur daux (dauxlist kR cR auxlist)"
    using v by (auto simp: dsaux'_def)
  have tt: "table (args_R (dargs cR cL args)) (dtabc kR cR rel2)" by (simp add: table_dtabc)
  have "valid_dmsaux_lz (dargs cR cL args) (dmsk cR cL) cur
      (dadd_new_table_lz (dargs cR cL args) (dtabc kR cR rel2) daux)
      (case dauxlist kR cR auxlist of [] \<Rightarrow> [(cur, dtabc kR cR rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> dtabc kR cR rel2) # r
                         else (cur, dtabc kR cR rel2) # dauxlist kR cR auxlist)"
    by (rule valid_dadd_new_table_lz[OF d tt])
  then show ?thesis using w t2
    by (simp add: dsaux'_def dauxlist_add_new_table[symmetric] dauxlist_wf_add_new_table[OF w t2])
qed

lemma dsaux'_result:
  assumes v: "dsaux' kR cR cL args cur daux auxlist"
  shows "dresult_msaux (dargs cR cL args) daux
      = dtabc kR cR (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
proof -
  have d: "valid_dmsaux_lz (dargs cR cL args) (dmsk cR cL) cur daux (dauxlist kR cR auxlist)"
    using v by (auto simp: dsaux'_def)
  have "dresult_msaux (dargs cR cL args) daux
      = foldr (\<union>) [rel. (t, rel) \<leftarrow> dauxlist kR cR auxlist,
          memL (args_ivl (dargs cR cL args)) (cur - t)] {}"
    by (rule valid_dresult_msaux_lz[OF d])
  then show ?thesis by (simp add: dtabc_result)
qed

section \<open>The dense Until structure\<close>

text \<open>
  The Until structure needs far less than the Since one.  Only one of its components mentions
  the left operand: the mapping @{text a1_map} that records, for each tuple over the left
  operand's columns, the last time point at which it held.  The verified structure looks a stored
  tuple's restriction to those columns up in it; the dense one looks up the tuple's dense
  projection, which is the same tuple.  Every other operation is the verified one.
\<close>

lemma mmuaux_dq_cases:
  fixes d :: "event_data mmuaux_dq"
  obtains tp tss tables len result a1_map a2_dq tstp_dq dn
  where "d = (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn)"
  by (metis prod.collapse)

definition duntil_elem_step_dq :: "('a tuple, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
    (nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> 'a tuple \<Rightarrow> 'a until_acc_dq \<Rightarrow> 'a until_acc_dq" where
  "duntil_elem_step_dq a1_map msk pos tp len inz P d as acc =
    (let acc' = (if inz then until_step_dq P d (tp - len) (tp, as) acc else acc) in
     case Mapping.lookup a1_map (dproj msk as) of
        None \<Rightarrow> (if \<not>pos then until_step_dq P d (tp - len) (tp - len, as) acc' else acc')
      | Some tp' \<Rightarrow> until_step_dq P d (tp - len) (if pos then (max (tp - len) tp', as)
          else (max (tp - len) (tp' + 1), as)) acc')"

lemma duntil_elem_step_dq_eq:
  "dmsk_args args msk \<Longrightarrow> length as = length (args_R args) \<Longrightarrow>
     duntil_elem_step_dq a1_map msk pos tp len inz P d as acc
     = until_elem_step_dq a1_map (args_L args) (args_R args) pos tp len inz P d as acc"
  by (simp add: duntil_elem_step_dq_def until_elem_step_dq_def dmsk_args_dproj)

lemma fold_duntil_elem_step_dq:
  "dmsk_args args msk \<Longrightarrow> (\<And>as. as \<in> set xs \<Longrightarrow> length as = length (args_R args)) \<Longrightarrow>
     fold (duntil_elem_step_dq a1_map msk pos tp len inz P d) xs acc
     = fold (until_elem_step_dq a1_map (args_L args) (args_R args) pos tp len inz P d) xs acc"
  by (induct xs arbitrary: acc) (simp_all add: duntil_elem_step_dq_eq)

definition dadd_new_dq :: "args \<Rightarrow> bool list \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow>
    event_data mmuaux_dq \<Rightarrow> event_data mmuaux_dq" where
  "dadd_new_dq args msk rel1 rel2 nt aux =
    (let (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) = shift_dq args nt aux;
     I = args_ivl args; pos = args_pos args; inz = memL I 0;
     new_tstp = (if inz then Inr tp else Inl nt);
     tstp_dq = dq_push nt tstp_dq;
     P = (\<lambda>t. memL I (nt - dq_nth tstp_dq (t - (tp - len))));
     (tbl, a2_dq', result') = fold (duntil_elem_step_dq a1_map msk pos tp len inz P new_tstp)
       (csl rel2) ({}, a2_dq, result);
     tables = append_queue (tbl, new_tstp) tables;
     a2_dq = dq_push Mapping.empty a2_dq';
     a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
       (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
     tss = append_queue nt tss in
     (tp + 1, tss, tables, len + 1, result', a1_map, a2_dq, tstp_dq, dn))"

text \<open>
  The dense operation is the verified one.  Where @{const add_new_dq} guards the fold with
  @{term \<open>finite rel2\<close>} and falls back on the other structure, this one folds unconditionally:
  every table the evaluator produces is finite.
\<close>

theorem dadd_new_dq_eq:
  assumes fin: "finite rel2" and dm: "dmsk_args args msk"
    and r2: "\<And>as. as \<in> rel2 \<Longrightarrow> length as = length (args_R args)"
  shows "dadd_new_dq args msk rel1 rel2 nt aux = add_new_dq args rel1 rel2 nt aux"
proof (cases "shift_dq args nt aux" rule: mmuaux_dq_cases)
  case (1 tp tss tables len result a1_map a2_dq tstp_dq dn)
  have rs: "set (csorted_list_of_set rel2) = rel2" by (rule set_csorted_list_of_set_etuple[OF fin])
  have fl: "fold (duntil_elem_step_dq a1_map msk (args_pos args) tp len (memL (args_ivl args) 0)
        (\<lambda>t. memL (args_ivl args) (nt - dq_nth (dq_push nt tstp_dq) (t - (tp - len))))
        (if memL (args_ivl args) 0 then Inr tp else Inl nt))
      (csorted_list_of_set rel2) ({}, a2_dq, result)
    = fold (until_elem_step_dq a1_map (args_L args) (args_R args) (args_pos args) tp len
        (memL (args_ivl args) 0)
        (\<lambda>t. memL (args_ivl args) (nt - dq_nth (dq_push nt tstp_dq) (t - (tp - len))))
        (if memL (args_ivl args) 0 then Inr tp else Inl nt))
      (csorted_list_of_set rel2) ({}, a2_dq, result)"
    by (rule fold_duntil_elem_step_dq[OF dm]) (use rs r2 in auto)
  show ?thesis
    unfolding dadd_new_dq_def add_new_dq_def if_P[OF fin] 1 csl_finite[OF fin]
    by (simp add: Let_def fl split: prod.splits)
qed

subsection \<open>The dense Until structure's validity\<close>

definition dvalid_muaux :: "args \<Rightarrow> bool list \<Rightarrow> ts \<Rightarrow> event_data mmuaux_dq \<Rightarrow> event_data muaux \<Rightarrow>
    bool" where
  "dvalid_muaux args msk cur daux auxlist \<longleftrightarrow> valid_muaux_dq args cur (MU_dq daux) auxlist"

lemma dvalid_init_muaux:
  assumes LR: "set L \<subseteq> set R" "distinct L" "distinct R"
  shows "dvalid_muaux (init_args I n L R pos None) msk 0 (init_dq (init_args I n L R pos None)) []"
proof -
  have "valid_muaux_dq (init_args I n L R pos None) 0 (init_muaux_dq (init_args I n L R pos None)) []"
    by (rule valid_init_muaux_dq[OF LR])
  then show ?thesis
    unfolding dvalid_muaux_def init_muaux_dq_def by (simp add: init_args_def)
qed

lemma dvalid_add_new_muaux:
  assumes v: "dvalid_muaux args msk cur daux auxlist"
    and fin: "finite rel2" and dm: "dmsk_args args msk"
    and t1: "table (args_L args) rel1" and t2: "table (args_R args) rel2"
    and nt: "nt \<ge> cur"
  shows "dvalid_muaux args msk nt (dadd_new_dq args msk rel1 rel2 nt daux)
     (update_until args rel1 rel2 nt auxlist)"
proof -
  have r2: "\<And>as. as \<in> rel2 \<Longrightarrow> length as = length (args_R args)"
    using t2 by (auto simp: table_def wf_tuple_def)
  have "valid_muaux_dq args nt (add_new_muaux_dq args rel1 rel2 nt (MU_dq daux))
      (update_until args rel1 rel2 nt auxlist)"
    by (rule valid_add_new_muaux_dq[OF v[unfolded dvalid_muaux_def] t1 t2 nt])
  then show ?thesis
    by (simp add: dvalid_muaux_def dadd_new_dq_eq[OF fin dm r2])
qed

lemma dvalid_eval_muaux:
  assumes v: "dvalid_muaux args msk cur daux auxlist" and nt: "nt \<ge> cur"
    and ev: "eval_dq args nt daux = (res, daux')"
    and eu: "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "dvalid_muaux args msk cur daux' auxlist' \<and> res = map (eval_args_agg args) res'"
proof -
  have e: "eval_muaux_dq args nt (MU_dq daux) = (res, MU_dq daux')"
    using ev by (simp del: eval_dq.simps)
  show ?thesis
    using valid_eval_muaux_dq[OF v[unfolded dvalid_muaux_def] nt e eu]
    by (simp add: dvalid_muaux_def)
qed

lemma dvalid_length_muaux:
  "dvalid_muaux args msk cur daux auxlist \<Longrightarrow> length_dq args daux = length auxlist"
  using valid_length_muaux_dq[of args cur "MU_dq daux" auxlist]
  by (simp add: dvalid_muaux_def)

section \<open>The dense Until structure over ascending columns\<close>

definition duaux' :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> event_data mmuaux_dq \<Rightarrow>
    event_data muaux \<Rightarrow> bool" where
  "duaux' kL cL kR cR args cur daux auxlist \<longleftrightarrow>
     (\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2) \<and>
     dvalid_muaux (dargs cR cL args) (dmsk cR cL) cur daux (dauxlist3 kL cL kR cR auxlist)"

lemma duaux'_init:
  assumes fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
  shows "duaux' kL cL kR cR args 0 (init_dq (dargs cR cL args)) []"
proof -
  have "dvalid_muaux (init_args (args_ivl args) (length cR) cL cR (args_pos args) None)
      (dmsk cR cL) 0 (init_dq (init_args (args_ivl args) (length cR) cL cR (args_pos args) None)) []"
    by (rule dvalid_init_muaux[OF dframe_sub[OF fR fL sub] dframeD(4)[OF fL] dframeD(4)[OF fR]])
  then show ?thesis by (simp add: duaux'_def dargs_def dauxlist3_def)
qed

lemma duaux'_add_new:
  assumes v: "duaux' kL cL kR cR args cur daux auxlist"
    and fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and t1: "table kL rel1" and t2: "table kR rel2"
    and f2: "finite rel2" and nt: "cur \<le> nt"
  shows "duaux' kL cL kR cR args nt
      (dadd_new_dq (dargs cR cL args) (dmsk cR cL) (dtabc kL cL rel1) (dtabc kR cR rel2) nt daux)
      (update_until args rel1 rel2 nt auxlist)"
proof -
  have w: "\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2"
    and d: "dvalid_muaux (dargs cR cL args) (dmsk cR cL) cur daux (dauxlist3 kL cL kR cR auxlist)"
    using v by (auto simp: duaux'_def)
  have dm: "dmsk_args (dargs cR cL args) (dmsk cR cL)"
    unfolding dmsk_def
    by (rule dmsk_args_dargs[OF dframeD(2)[OF fR] dframeD(2)[OF fL] dframe_sub[OF fR fL sub]])
  have fin: "finite (dtabc kR cR rel2)" using f2 by (rule finite_dtabc)
  have tt1: "table (args_L (dargs cR cL args)) (dtabc kL cL rel1)" by (simp add: table_dtabc)
  have tt2: "table (args_R (dargs cR cL args)) (dtabc kR cR rel2)" by (simp add: table_dtabc)
  have "dvalid_muaux (dargs cR cL args) (dmsk cR cL) nt
      (dadd_new_dq (dargs cR cL args) (dmsk cR cL) (dtabc kL cL rel1) (dtabc kR cR rel2) nt daux)
      (update_until (dargs cR cL args) (dtabc kL cL rel1) (dtabc kR cR rel2) nt
        (dauxlist3 kL cL kR cR auxlist))"
    by (rule dvalid_add_new_muaux[OF d fin dm tt1 tt2 nt])
  moreover have "dauxlist3 kL cL kR cR (update_until args rel1 rel2 nt auxlist)
      = update_until (dargs cR cL args) (dtabc kL cL rel1) (dtabc kR cR rel2) nt
          (dauxlist3 kL cL kR cR auxlist)"
    by (rule dauxlist3_update_until[OF fR fL sub w t1 t2 aL aR]) simp_all
  ultimately show ?thesis using dauxlist3_wf_update_until[OF w sub t1 t2 aL aR]
    by (simp add: duaux'_def)
qed

lemma duaux'_eval:
  assumes v: "duaux' kL cL kR cR args cur daux auxlist" and nt: "cur \<le> nt"
    and de: "eval_dq (dargs cR cL args) nt daux = (dres, daux')"
    and we: "eval_until (args_ivl args) nt auxlist = (res, auxlist')"
  shows "dres = map (dtabc kR cR) res \<and> duaux' kL cL kR cR args cur daux' auxlist'"
proof -
  have w: "\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2"
    and d: "dvalid_muaux (dargs cR cL args) (dmsk cR cL) cur daux (dauxlist3 kL cL kR cR auxlist)"
    using v by (auto simp: duaux'_def)
  have de': "eval_until (args_ivl (dargs cR cL args)) nt (dauxlist3 kL cL kR cR auxlist)
      = (map (dtabc kR cR) res, dauxlist3 kL cL kR cR auxlist')"
    using dauxlist3_eval_until[OF we] by simp
  have vd: "dvalid_muaux (dargs cR cL args) (dmsk cR cL) cur daux' (dauxlist3 kL cL kR cR auxlist')"
    and r: "dres = map (eval_args_agg (dargs cR cL args)) (map (dtabc kR cR) res)"
    using dvalid_eval_muaux[OF d nt de de'] by simp_all
  have "set auxlist' \<subseteq> set auxlist"
    using eval_until_auxlist'[OF we] by (simp add: set_drop_subset)
  then show ?thesis using vd r w by (auto simp: duaux'_def)
qed

lemma duaux'_length:
  "duaux' kL cL kR cR args cur daux auxlist \<Longrightarrow>
     length_dq (dargs cR cL args) daux = length auxlist"
  unfolding duaux'_def by (auto dest: dvalid_length_muaux)

section \<open>The match structures over ascending columns\<close>

text \<open>
  The regular-expression nodes need no dense operations of their own.  Every table a match node
  handles lives over the node's own columns or over an atom's, and the reordering turns the
  kernel's operations into the very same operations over the ascending columns: the joins are
  @{thm [source] dtabc_join_sub}, the unions are @{thm [source] dtabc_Un_img}.  The one thing
  that does not come for free is that the guards really are tables over the node's columns: that
  is the regular expression's safety condition, and the lemmas below carry it.
\<close>

text \<open>The atoms' tables, reordered each at its own columns.\<close>

definition dtabcs :: "cols list \<Rightarrow> cols list \<Rightarrow> 'b list set list \<Rightarrow> 'b list set list" where
  "dtabcs kss css rels = map (\<lambda>i. dtabc (kss ! i) (css ! i) (rels ! i)) [0..<length rels]"

lemma length_dtabcs[simp]: "length (dtabcs kss css rels) = length rels"
  by (simp add: dtabcs_def)

lemma nth_dtabcs[simp]: "i < length rels \<Longrightarrow> dtabcs kss css rels ! i = dtabc (kss ! i) (css ! i) (rels ! i)"
  by (simp add: dtabcs_def)

definition wf_atoms :: "cols \<Rightarrow> cols list \<Rightarrow> cols list \<Rightarrow> 'b list set list \<Rightarrow> bool" where
  "wf_atoms ks kss css rels \<longleftrightarrow> length kss = length rels \<and> length css = length rels \<and>
     (\<forall>i < length rels. dframe (kss ! i) (css ! i) \<and> set (kss ! i) \<subseteq> set ks \<and> table (kss ! i) (rels ! i))"

lemma wf_atomsD:
  assumes "wf_atoms ks kss css rels" "i < length rels"
  shows "dframe (kss ! i) (css ! i)" "set (kss ! i) \<subseteq> set ks" "table (kss ! i) (rels ! i)"
  using assms by (auto simp: wf_atoms_def)

lemma table_unit_table_Nil: "table ks unit_table \<Longrightarrow> ks = []"
  by (simp add: table_def unit_table_def)

lemma dtabc_eq_empty_table[simp]: "dtabc ks cs T = empty_table \<longleftrightarrow> T = empty_table"
  by (simp add: dtabc_empty_iff empty_table_def)

subsection \<open>The lax epsilon\<close>

lemma table_eps_lax:
  assumes wf: "wf_atoms ks kss css rels"
  shows "ok (length rels) mr \<Longrightarrow> table ks guard \<Longrightarrow> table ks (\<epsilon>_lax ks kss guard rels mr)"
proof (induct mr arbitrary: guard)
  case (MSkip m)
  then show ?case by (simp add: table_def empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length rels" by simp
  show ?case by (simp, rule table_join_sub[OF MTestPos(2) wf_atomsD(3)[OF wf i] wf_atomsD(2)[OF wf i]])
next
  case (MTestNeg i)
  then have i: "i < length rels" by simp
  show ?case by (simp, rule table_join_sub[OF MTestNeg(2) wf_atomsD(3)[OF wf i] wf_atomsD(2)[OF wf i]])
next
  case (MPlus r t)
  then show ?case by simp
next
  case (MTimes r t)
  then show ?case by (auto intro: table_join_sub)
next
  case (MStar r)
  then show ?case by simp
qed

lemma dtabc_eps_lax:
  assumes fK: "dframe ks cs" and wf: "wf_atoms ks kss css rels"
  shows "ok (length rels) mr \<Longrightarrow> table ks guard \<Longrightarrow>
     dtabc ks cs (\<epsilon>_lax ks kss guard rels mr) = \<epsilon>_lax cs css (dtabc ks cs guard) (dtabcs kss css rels) mr"
proof (induct mr arbitrary: guard)
  case (MSkip m)
  then show ?case by (simp add: empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length rels" by simp
  show ?case using i
    by (simp add: dtabc_join_sub[OF fK wf_atomsD(1,2)[OF wf i] MTestPos(2) wf_atomsD(3)[OF wf i]])
next
  case (MTestNeg i)
  then have i: "i < length rels" by simp
  show ?case using i
    by (simp add: dtabc_join_sub[OF fK wf_atomsD(1,2)[OF wf i] MTestNeg(2) wf_atomsD(3)[OF wf i]])
next
  case (MPlus r t)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length rels) r" and o2: "ok (length rels) t" using MTimes(3) by simp_all
  have t1: "table ks (\<epsilon>_lax ks kss guard rels r)" by (rule table_eps_lax[OF wf o1 MTimes(4)])
  have t2: "table ks (\<epsilon>_lax ks kss guard rels t)" by (rule table_eps_lax[OF wf o2 MTimes(4)])
  show ?case using MTimes(1)[OF o1 MTimes(4)] MTimes(2)[OF o2 MTimes(4)]
    by (simp add: dtabc_join_sub[OF fK fK subset_refl t1 t2])
qed simp

subsection \<open>The strict epsilons\<close>

text \<open>
  Unlike the lax one, a strict epsilon does not carry a guard, and its value is a table over the
  node's columns only because the regular expression is safe: an empty skip and a star return the
  unit table, which is a table over the node's columns only when there are none, and safety is
  what rules the other case out.  The kernel's own correctness proof establishes exactly that, so
  the lemmas below read it off @{thm [source] qtable_r\<epsilon>_strict} at the empty restriction.
\<close>

lemma qtable_mem_restr_empty: "qtable A (mem_restr {} A) Q X \<longleftrightarrow> table A X"
  by (auto simp: qtable_def mem_restr_def)

lemma table_reps_strict:
  fixes \<psi>s :: "ty Formula.formula list" and rels :: "event_data table list"
  assumes sr: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<psi>s)"
    and ok: "ok (length \<psi>s) mr" and A: "set A = fv_regex (from_mregex mr \<psi>s)" "distinct A"
    and ops: "list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel) \<psi>s rels"
  shows "table A (r\<epsilon>_strict A (map Formula.fv_list \<psi>s) rels mr)"
proof -
  have q: "list_all2 (\<lambda>\<psi> rel. sat_table \<sigma> V n {} (Formula.fv_list \<psi>) i \<psi> rel) \<psi>s rels"
    using ops by (simp add: list_all2_conv_all_nth qtable_mem_restr_empty)
  show ?thesis using qtable_r\<epsilon>_strict[OF sr ok A q] by (simp add: qtable_mem_restr_empty)
qed

lemma table_leps_strict:
  fixes \<psi>s :: "ty Formula.formula list" and rels :: "event_data table list"
  assumes sr: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<psi>s)"
    and ok: "ok (length \<psi>s) mr" and A: "set A = fv_regex (from_mregex mr \<psi>s)" "distinct A"
    and ops: "list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel) \<psi>s rels"
  shows "table A (l\<epsilon>_strict A (map Formula.fv_list \<psi>s) rels mr)"
proof -
  have q: "list_all2 (\<lambda>\<psi> rel. sat_table \<sigma> V n {} (Formula.fv_list \<psi>) i \<psi> rel) \<psi>s rels"
    using ops by (simp add: list_all2_conv_all_nth qtable_mem_restr_empty)
  show ?thesis using qtable_l\<epsilon>_strict[OF sr ok A q] by (simp add: qtable_mem_restr_empty)
qed

text \<open>A tested atom is moved to the node's column order; the dense one is already in it.\<close>

lemma dtabc_reorder:
  assumes fK: "dframe ks cs" and f: "dframe k c" and e: "set k = set ks" and t: "table k T"
  shows "dtabc ks cs (reorder ks k T) = reorder cs c (dtabc k c T)"
proof -
  have cc: "c = cs"
    using dframeD(2,3)[OF fK] dframeD(2,3)[OF f] e by (intro strict_sorted_equal) auto
  have r: "reorder ks k T = restrict ks k ` T"
    using t restrict_idle[OF dframeD(1)[OF f]] by (force simp: reorder_def table_def)
  have fk: "dframe k cs" using f cc by simp
  show ?thesis
    unfolding r cc reorder_def using dtabc_restrict[OF fk e[symmetric] t] by simp
qed

locale dregex_frame =
  fixes ks cs :: cols and \<psi>s :: "ty Formula.formula list" and css :: "cols list"
  assumes fK: "dframe ks cs" and lc: "length css = length \<psi>s"
    and fa: "\<And>i. i < length \<psi>s \<Longrightarrow> dframe (Formula.fv_list (\<psi>s ! i)) (css ! i)"
    and sub: "\<And>i. i < length \<psi>s \<Longrightarrow> Formula.fv (\<psi>s ! i) \<subseteq> set ks"
begin

abbreviation (input) wfrels :: "event_data table list \<Rightarrow> bool" where
  "wfrels rels \<equiv> list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel) \<psi>s rels"

abbreviation (input) drels :: "event_data table list \<Rightarrow> event_data table list" where
  "drels rels \<equiv> dtabcs (map Formula.fv_list \<psi>s) css rels"

lemma lr: "wfrels rels \<Longrightarrow> length \<psi>s = length rels"
  by (simp add: list_all2_lengthD)

lemma wf_atoms: "wfrels rels \<Longrightarrow> wf_atoms ks (map Formula.fv_list \<psi>s) css rels"
  using lc fa sub by (auto simp: wf_atoms_def list_all2_conv_all_nth)

lemma dtabc_reps_strict:
  assumes ops: "wfrels rels"
  shows "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     dtabc ks cs (r\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels mr)
       = r\<epsilon>_strict cs css (drels rels) mr"
proof (induct mr)
  case (MSkip m)
  then have "ks = []" by simp
  then have "cs = []" using dframeD(3)[OF fK] by simp
  with \<open>ks = []\<close> show ?case by (simp add: dtabc_unit_table)
next
  case (MTestPos i)
  then have i: "i < length rels" using lr[OF ops] by simp
  have e: "set (Formula.fv_list (\<psi>s ! i)) = set ks" using MTestPos(3) by simp
  have t: "table (Formula.fv_list (\<psi>s ! i)) (rels ! i)" using ops i by (simp add: list_all2_conv_all_nth)
  show ?case using i lr[OF ops]
    by (simp add: dtabc_reorder[OF fK fa e t])
next
  case (MTestNeg i)
  then have i: "i < length rels" using lr[OF ops] by simp
  have dk: "distinct ks" by (rule dframeD(1)[OF fK])
  have tb: "table ks (r\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels (MTestNeg i))"
    by (rule table_reps_strict[OF MTestNeg(1,2,3) dk ops])
  show ?case
  proof (cases "rels ! i = empty_table")
    case True
    then have "ks = []" using tb by (simp add: table_unit_table_Nil)
    then have "cs = []" using dframeD(3)[OF fK] by simp
    then show ?thesis using True i \<open>ks = []\<close> lr[OF ops] by (simp add: dtabc_unit_table)
  next
    case False
    then show ?thesis using i lr[OF ops] by simp
  qed
next
  case (MPlus r t)
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case
    using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4)
    by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr1: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex r \<psi>s)"
    using MTimes(3) by simp
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)" using MTimes(3,5) by auto
  have tg: "table ks (r\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels r)"
    by (rule table_reps_strict[OF sr1 o1 fvr dframeD(1)[OF fK] ops])
  show ?case
    using MTimes(1)[OF sr1 o1 fvr] o2 lr[OF ops]
    by (simp add: dtabc_eps_lax[OF fK wf_atoms[OF ops] _ tg])
next
  case (MStar r)
  have tb: "table ks (r\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels (MStar r))"
    by (rule table_reps_strict[OF MStar(2,3,4) dframeD(1)[OF fK] ops])
  then have "ks = []" by (simp add: table_unit_table_Nil)
  then have "cs = []" using dframeD(3)[OF fK] by simp
  with \<open>ks = []\<close> show ?case by (simp add: dtabc_unit_table)
qed

lemma dtabc_leps_strict:
  assumes ops: "wfrels rels"
  shows "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     dtabc ks cs (l\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels mr)
       = l\<epsilon>_strict cs css (drels rels) mr"
proof (induct mr)
  case (MSkip m)
  then have "ks = []" by simp
  then have "cs = []" using dframeD(3)[OF fK] by simp
  with \<open>ks = []\<close> show ?case by (simp add: dtabc_unit_table)
next
  case (MTestPos i)
  then have i: "i < length rels" using lr[OF ops] by simp
  have e: "set (Formula.fv_list (\<psi>s ! i)) = set ks" using MTestPos(3) by simp
  have t: "table (Formula.fv_list (\<psi>s ! i)) (rels ! i)" using ops i by (simp add: list_all2_conv_all_nth)
  show ?case using i lr[OF ops]
    by (simp add: dtabc_reorder[OF fK fa e t])
next
  case (MTestNeg i)
  then have i: "i < length rels" using lr[OF ops] by simp
  have tb: "table ks (l\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels (MTestNeg i))"
    by (rule table_leps_strict[OF MTestNeg(1,2,3) dframeD(1)[OF fK] ops])
  show ?case
  proof (cases "rels ! i = empty_table")
    case True
    then have "ks = []" using tb by (simp add: table_unit_table_Nil)
    then have "cs = []" using dframeD(3)[OF fK] by simp
    then show ?thesis using True i \<open>ks = []\<close> lr[OF ops] by (simp add: dtabc_unit_table)
  next
    case False
    then show ?thesis using i lr[OF ops] by simp
  qed
next
  case (MPlus r t)
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case
    using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4)
    by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr2: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex t \<psi>s)"
    using MTimes(3) by simp
  have fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MTimes(3,5) by auto
  have tg: "table ks (l\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels t)"
    by (rule table_leps_strict[OF sr2 o2 fvt dframeD(1)[OF fK] ops])
  show ?case
    using MTimes(2)[OF sr2 o2 fvt] o1 lr[OF ops]
    by (simp add: dtabc_eps_lax[OF fK wf_atoms[OF ops] _ tg])
next
  case (MStar r)
  have tb: "table ks (l\<epsilon>_strict ks (map Formula.fv_list \<psi>s) rels (MStar r))"
    by (rule table_leps_strict[OF MStar(2,3,4) dframeD(1)[OF fK] ops])
  then have "ks = []" by (simp add: table_unit_table_Nil)
  then have "cs = []" using dframeD(3)[OF fK] by simp
  with \<open>ks = []\<close> show ?case by (simp add: dtabc_unit_table)
qed

end

subsection \<open>The derivatives\<close>

text \<open>
  The two derivatives read the previous firing's tabulation, which the node keeps reordered, and
  join what they find against the atoms through the lax epsilon.  Reordering a tabulation is
  reordering every entry, so the lookups agree; the rest is the lax epsilon again.
\<close>

lemma table_rdelta:
  assumes wf: "wf_atoms ks kss css rels" and X: "\<And>ms. table ks (lookup X ms)"
  shows "ok (length rels) mr \<Longrightarrow> table ks (r\<delta> ks kss \<kappa> X rels mr)"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using X by (cases m) (auto simp: table_def empty_table_def)
next
  case (MPlus r t)
  then show ?case by simp
next
  case (MTimes r t)
  have o: "ok (length rels) r" "ok (length rels) t" using MTimes(3) by simp_all
  have u: "table ks (r\<delta> ks kss (\<lambda>u. \<kappa> (MTimes r u)) X rels t)" and g: "table ks (r\<delta> ks kss \<kappa> X rels r)"
    using MTimes(1,2) o by simp_all
  show ?case using u by (simp add: table_eps_lax[OF wf o(2) g])
qed (auto simp: table_def empty_table_def)

lemma table_ldelta:
  assumes wf: "wf_atoms ks kss css rels" and X: "\<And>ms. table ks (lookup X ms)"
  shows "ok (length rels) mr \<Longrightarrow> table ks (l\<delta> ks kss \<kappa> X rels mr)"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using X by (cases m) (auto simp: table_def empty_table_def)
next
  case (MPlus r t)
  then show ?case by simp
next
  case (MTimes r t)
  have o: "ok (length rels) r" "ok (length rels) t" using MTimes(3) by simp_all
  have u: "table ks (l\<delta> ks kss (\<lambda>u. \<kappa> (MTimes u t)) X rels r)" and g: "table ks (l\<delta> ks kss \<kappa> X rels t)"
    using MTimes(1,2) o by simp_all
  show ?case using u by (simp add: table_eps_lax[OF wf o(1) g])
qed (auto simp: table_def empty_table_def)

lemma dtabc_rdelta:
  assumes fK: "dframe ks cs" and wf: "wf_atoms ks kss css rels"
    and X: "\<And>ms. table ks (lookup X ms)" and dX: "\<And>ms. lookup dX ms = dtabc ks cs (lookup X ms)"
  shows "ok (length rels) mr \<Longrightarrow>
     dtabc ks cs (r\<delta> ks kss \<kappa> X rels mr) = r\<delta> cs css \<kappa> dX (dtabcs kss css rels) mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using dX by (cases m) (simp_all add: empty_table_def)
next
  case (MPlus r t)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length rels) r" and o2: "ok (length rels) t" using MTimes(3) by simp_all
  have tg: "table ks (r\<delta> ks kss \<kappa> X rels r)" by (rule table_rdelta[OF wf X o1])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2]
    by (simp add: dtabc_Un_img dtabc_eps_lax[OF fK wf o2 tg])
qed (simp_all add: empty_table_def)

lemma dtabc_ldelta:
  assumes fK: "dframe ks cs" and wf: "wf_atoms ks kss css rels"
    and X: "\<And>ms. table ks (lookup X ms)" and dX: "\<And>ms. lookup dX ms = dtabc ks cs (lookup X ms)"
  shows "ok (length rels) mr \<Longrightarrow>
     dtabc ks cs (l\<delta> ks kss \<kappa> X rels mr) = l\<delta> cs css \<kappa> dX (dtabcs kss css rels) mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using dX by (cases m) (simp_all add: empty_table_def)
next
  case (MPlus r t)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length rels) r" and o2: "ok (length rels) t" using MTimes(3) by simp_all
  have tg: "table ks (l\<delta> ks kss \<kappa> X rels t)" by (rule table_ldelta[OF wf X o2])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2]
    by (simp add: dtabc_Un_img dtabc_eps_lax[OF fK wf o1 tg])
qed (simp_all add: empty_table_def)

subsection \<open>The past-match structure\<close>

text \<open>
  A past-match structure is a list of tabulations indexed by a time stamp; the dense one is the
  same list with every entry reordered.  Since a tabulation is only ever read through
  @{const lookup}, the relation below says just that, and adds the invariant the derivatives
  need: every entry is a table over the node's columns.
\<close>

definition dmrd_rel :: "cols \<Rightarrow> cols \<Rightarrow> event_data mr\<delta>aux \<Rightarrow> event_data mr\<delta>aux \<Rightarrow> bool" where
  "dmrd_rel ks cs = list_all2 (\<lambda>(t, X) (t', X'). t = t' \<and>
     (\<forall>ms. table ks (lookup X ms)) \<and> (\<forall>ms. lookup X' ms = dtabc ks cs (lookup X ms)))"

lemma dmrd_rel_Nil[simp]: "dmrd_rel ks cs [] []"
  by (simp add: dmrd_rel_def)

lemma dmrd_rel_Cons[simp]:
  "dmrd_rel ks cs ((t, X) # aux) ((t', X') # daux) \<longleftrightarrow> t = t' \<and>
     (\<forall>ms. table ks (lookup X ms)) \<and> (\<forall>ms. lookup X' ms = dtabc ks cs (lookup X ms)) \<and>
     dmrd_rel ks cs aux daux"
  by (simp add: dmrd_rel_def)

lemma dmrd_rel_length: "dmrd_rel ks cs aux daux \<Longrightarrow> length aux = length daux"
  by (simp add: dmrd_rel_def list_all2_lengthD)

lemma dmrd_rel_induct[consumes 1, case_names Nil Cons]:
  assumes "dmrd_rel ks cs aux daux"
    and "P [] []"
    and "\<And>t X X' aux daux. (\<forall>ms. table ks (lookup X ms)) \<Longrightarrow>
       (\<forall>ms. lookup X' ms = dtabc ks cs (lookup X ms)) \<Longrightarrow> dmrd_rel ks cs aux daux \<Longrightarrow>
       P aux daux \<Longrightarrow> P ((t, X) # aux) ((t, X') # daux)"
  shows "P aux daux"
  using assms(1)[unfolded dmrd_rel_def]
  by (induct rule: list_all2_induct) (use assms(2,3) in \<open>auto simp: dmrd_rel_def\<close>)

text \<open>Reordering a tabulation entry by entry is reordering what it tabulates.\<close>

lemma lookup_mrtabulate_cong:
  assumes d: "distinct mrs" and f: "\<And>ms. ms \<in> set mrs \<Longrightarrow> dtabc ks cs (f ms) = g ms"
  shows "lookup (mrtabulate mrs g) ms = dtabc ks cs (lookup (mrtabulate mrs f) ms)"
  using f by (simp add: lookup_tabulate[OF d] empty_table_def)

text \<open>Reading a structure is a union of lookups, which the reordering distributes over.\<close>

lemma dtabc_foldr_lookup:
  assumes "dmrd_rel ks cs aux daux"
  shows "dtabc ks cs (foldr (\<union>) [lookup rel ms. (t, rel) \<leftarrow> aux, P t] {})
       = foldr (\<union>) [lookup rel ms. (t, rel) \<leftarrow> daux, P t] {}"
  using assms by (induct rule: dmrd_rel_induct) (auto simp: dtabc_Un_img dtabc_def)

locale dmatchP_frame = dregex_frame ks cs \<psi>s css
  for ks cs :: cols and \<psi>s :: "ty Formula.formula list" and css :: "cols list" +
  fixes rels :: "event_data table list" and mrs :: "mregex list"
  assumes ops: "list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel) \<psi>s rels"
    and d: "distinct mrs"
    and mrsok: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
       Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex ms \<psi>s) \<and> ok (length \<psi>s) ms \<and>
       set ks = fv_regex (from_mregex ms \<psi>s)"
begin

abbreviation (input) "kss \<equiv> map Formula.fv_list \<psi>s"

lemma wfa: "wf_atoms ks kss css rels" by (rule wf_atoms[OF ops])

lemma tabT: "ms \<in> set mrs \<Longrightarrow> table ks (r\<epsilon>_strict ks kss rels ms)"
  using mrsok by (intro table_reps_strict[OF _ _ _ dframeD(1)[OF fK] ops]) auto

lemma dtabT: "ms \<in> set mrs \<Longrightarrow> dtabc ks cs (r\<epsilon>_strict ks kss rels ms) = r\<epsilon>_strict cs css (drels rels) ms"
  using mrsok by (intro dtabc_reps_strict[OF ops]) auto

lemma table_lookup_head: "table ks (lookup (mrtabulate mrs (r\<epsilon>_strict ks kss rels)) ms)"
  using tabT by (simp add: lookup_tabulate[OF d])

lemma dtabc_lookup_head:
  "lookup (mrtabulate mrs (r\<epsilon>_strict cs css (drels rels))) ms
     = dtabc ks cs (lookup (mrtabulate mrs (r\<epsilon>_strict ks kss rels)) ms)"
  by (rule lookup_mrtabulate_cong[OF d dtabT])

lemma dmrd_rel_head:
  "dmrd_rel ks cs [(nt, mrtabulate mrs (r\<epsilon>_strict ks kss rels))]
     [(nt, mrtabulate mrs (r\<epsilon>_strict cs css (drels rels)))]"
  using table_lookup_head dtabc_lookup_head by simp

lemma dmrd_rel_step:
  assumes rel: "dmrd_rel ks cs aux daux"
  shows "dmrd_rel ks cs
     [(t, mrtabulate mrs (\<lambda>ms. r\<delta> ks kss id X rels ms \<union> (if t = nt then r\<epsilon>_strict ks kss rels ms else {}))).
        (t, X) \<leftarrow> aux, memR I (nt - t)]
     [(t, mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X (drels rels) ms
          \<union> (if t = nt then r\<epsilon>_strict cs css (drels rels) ms else {}))).
        (t, X) \<leftarrow> daux, memR I (nt - t)]"
  using rel
proof (induct rule: dmrd_rel_induct)
  case (Cons t X X' aux daux)
  have okms: "\<And>ms. ms \<in> set mrs \<Longrightarrow> ok (length rels) ms" using mrsok lr[OF ops] by auto
  have tX: "\<And>ms. table ks (lookup X ms)" using Cons(1) by blast
  have dXe: "\<And>ms. lookup X' ms = dtabc ks cs (lookup X ms)" using Cons(2) by blast
  have tD: "\<And>ms. ms \<in> set mrs \<Longrightarrow> table ks (r\<delta> ks kss id X rels ms)"
    by (rule table_rdelta[OF wfa tX okms])
  have tE: "\<And>ms. table ks
      (lookup (mrtabulate mrs (\<lambda>ms. r\<delta> ks kss id X rels ms
         \<union> (if t = nt then r\<epsilon>_strict ks kss rels ms else {}))) ms)"
    using tD tabT by (auto simp: lookup_tabulate[OF d] table_def empty_table_def)
  have dR: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
      dtabc ks cs (r\<delta> ks kss id X rels ms) = r\<delta> cs css id X' (drels rels) ms"
    by (rule dtabc_rdelta[OF fK wfa tX dXe okms])
  have dD: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
      dtabc ks cs (r\<delta> ks kss id X rels ms \<union> (if t = nt then r\<epsilon>_strict ks kss rels ms else {}))
        = r\<delta> cs css id X' (drels rels) ms
          \<union> (if t = nt then r\<epsilon>_strict cs css (drels rels) ms else {})"
    by (simp add: dtabc_Un_img dR dtabT)
  have dE: "\<And>ms. lookup (mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X' (drels rels) ms
         \<union> (if t = nt then r\<epsilon>_strict cs css (drels rels) ms else {}))) ms
      = dtabc ks cs (lookup (mrtabulate mrs (\<lambda>ms. r\<delta> ks kss id X rels ms
         \<union> (if t = nt then r\<epsilon>_strict ks kss rels ms else {}))) ms)"
    by (rule lookup_mrtabulate_cong[OF d dD])
  show ?case using Cons(4) tE dE by simp
qed simp

lemma dtabc_update_matchP:
  assumes rel: "dmrd_rel ks cs aux daux"
  shows "dtabc ks cs (fst (update_matchP ks kss I mr mrs rels nt aux))
       = fst (update_matchP cs css I mr mrs (drels rels) nt daux) \<and>
     dmrd_rel ks cs (snd (update_matchP ks kss I mr mrs rels nt aux))
       (snd (update_matchP cs css I mr mrs (drels rels) nt daux))"
proof -
  let ?W = "[(t, mrtabulate mrs (\<lambda>ms. r\<delta> ks kss id X rels ms
       \<union> (if t = nt then r\<epsilon>_strict ks kss rels ms else {}))). (t, X) \<leftarrow> aux, memR I (nt - t)]"
  let ?D = "[(t, mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X (drels rels) ms
       \<union> (if t = nt then r\<epsilon>_strict cs css (drels rels) ms else {}))).
         (t, X) \<leftarrow> daux, memR I (nt - t)]"
  have st: "dmrd_rel ks cs ?W ?D" by (rule dmrd_rel_step[OF rel])
  have both: "dmrd_rel ks cs
      (case ?W of [] \<Rightarrow> [(nt, mrtabulate mrs (r\<epsilon>_strict ks kss rels))]
       | x # w' \<Rightarrow> (if fst x = nt then x # w'
                   else (nt, mrtabulate mrs (r\<epsilon>_strict ks kss rels)) # x # w'))
      (case ?D of [] \<Rightarrow> [(nt, mrtabulate mrs (r\<epsilon>_strict cs css (drels rels)))]
       | x # w' \<Rightarrow> (if fst x = nt then x # w'
                   else (nt, mrtabulate mrs (r\<epsilon>_strict cs css (drels rels))) # x # w'))"
  proof (cases ?W)
    case Nil
    have DN: "?D = []" using dmrd_rel_length[OF st] unfolding Nil by simp
    show ?thesis unfolding Nil DN using dmrd_rel_head by simp
  next
    case (Cons x w')
    have "length ?D = Suc (length w')" using dmrd_rel_length[OF st] unfolding Cons by simp
    then obtain y d' where D: "?D = y # d'" by (cases ?D) auto
    have rel': "dmrd_rel ks cs (x # w') (y # d')" using st unfolding Cons D .
    show ?thesis unfolding Cons D
      using rel' table_lookup_head dtabc_lookup_head
      by (cases x; cases y) auto
  qed
  show ?thesis
    using both dtabc_foldr_lookup[OF both]
    by (simp add: update_matchP_def Let_def)
qed

end

subsection \<open>The future-match structure\<close>

text \<open>
  A future-match structure keeps, per time stamp, the operands' tables at that time point and the
  result accumulated for it so far.  The dense one keeps the same list with both reordered.
\<close>

definition dmld_rel :: "cols \<Rightarrow> cols \<Rightarrow> ty Formula.formula list \<Rightarrow> cols list \<Rightarrow>
    event_data ml\<delta>aux \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> bool" where
  "dmld_rel ks cs \<psi>s css = list_all2 (\<lambda>(t, rls, rel) (t', drls, drel). t = t' \<and>
     list_all2 (\<lambda>\<psi> r. table (Formula.fv_list \<psi>) r) \<psi>s rls \<and>
     drls = dtabcs (map Formula.fv_list \<psi>s) css rls \<and> drel = dtabc ks cs rel)"

lemma dmld_rel_Nil[simp]: "dmld_rel ks cs \<psi>s css [] []"
  by (simp add: dmld_rel_def)

lemma dmld_rel_Cons[simp]:
  "dmld_rel ks cs \<psi>s css ((t, rls, rel) # aux) ((t', drls, drel) # daux) \<longleftrightarrow> t = t' \<and>
     list_all2 (\<lambda>\<psi> r. table (Formula.fv_list \<psi>) r) \<psi>s rls \<and>
     drls = dtabcs (map Formula.fv_list \<psi>s) css rls \<and> drel = dtabc ks cs rel \<and>
     dmld_rel ks cs \<psi>s css aux daux"
  by (simp add: dmld_rel_def)

lemma dmld_rel_induct[consumes 1, case_names Nil Cons]:
  assumes "dmld_rel ks cs \<psi>s css aux daux"
    and "P [] []"
    and "\<And>t rls rel aux daux. list_all2 (\<lambda>\<psi> r. table (Formula.fv_list \<psi>) r) \<psi>s rls \<Longrightarrow>
       dmld_rel ks cs \<psi>s css aux daux \<Longrightarrow> P aux daux \<Longrightarrow>
       P ((t, rls, rel) # aux) ((t, dtabcs (map Formula.fv_list \<psi>s) css rls, dtabc ks cs rel) # daux)"
  shows "P aux daux"
  using assms(1)[unfolded dmld_rel_def]
  by (induct rule: list_all2_induct) (use assms(2,3) in \<open>auto simp: dmld_rel_def\<close>)

locale dmatchF_frame = dregex_frame ks cs \<psi>s css
  for ks cs :: cols and \<psi>s :: "ty Formula.formula list" and css :: "cols list" +
  fixes mrs :: "mregex list"
  assumes d: "distinct mrs"
    and mrsok: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
       Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex ms \<psi>s) \<and> ok (length \<psi>s) ms \<and>
       set ks = fv_regex (from_mregex ms \<psi>s)"
begin

abbreviation (input) "kss \<equiv> map Formula.fv_list \<psi>s"

lemma okms: "ms \<in> set mrs \<Longrightarrow> wfrels rels \<Longrightarrow> ok (length rels) ms"
  using mrsok lr by auto

lemma tabL: "wfrels rels \<Longrightarrow> ms \<in> set mrs \<Longrightarrow> table ks (l\<epsilon>_strict ks kss rels ms)"
  using mrsok by (intro table_leps_strict[OF _ _ _ dframeD(1)[OF fK]]) auto

lemma dtabL: "wfrels rels \<Longrightarrow> ms \<in> set mrs \<Longrightarrow>
    dtabc ks cs (l\<epsilon>_strict ks kss rels ms) = l\<epsilon>_strict cs css (drels rels) ms"
  using mrsok by (intro dtabc_leps_strict) auto

lemma table_lookup_base:
  "wfrels rels \<Longrightarrow> table ks (lookup (mrtabulate mrs (l\<epsilon>_strict ks kss rels)) ms)"
  using tabL by (simp add: lookup_tabulate[OF d])

lemma dtabc_lookup_base:
  "wfrels rels \<Longrightarrow>
     lookup (mrtabulate mrs (l\<epsilon>_strict cs css (drels rels))) ms
       = dtabc ks cs (lookup (mrtabulate mrs (l\<epsilon>_strict ks kss rels)) ms)"
  by (intro lookup_mrtabulate_cong[OF d]) (rule dtabL)

lemma table_lookup_step:
  assumes rls: "wfrels rls" and X: "\<And>ms. table ks (lookup X ms)"
  shows "table ks (lookup (mrtabulate mrs (l\<delta> ks kss id X rls)) ms)"
  using table_ldelta[OF wf_atoms[OF rls] X] okms[OF _ rls]
  by (auto simp: lookup_tabulate[OF d] table_def empty_table_def)

lemma dtabc_matchF_foldr:
  assumes rels: "wfrels rels" and rel: "dmld_rel ks cs \<psi>s css aux daux"
  shows "dmld_rel ks cs \<psi>s css
       (fst (foldr (update_matchF_step ks kss I mr mrs nt) aux
          (update_matchF_base ks kss I mr mrs rels nt)))
       (fst (foldr (update_matchF_step cs css I mr mrs nt) daux
          (update_matchF_base cs css I mr mrs (drels rels) nt)))
     \<and> (\<forall>ms. table ks
          (lookup (snd (foldr (update_matchF_step ks kss I mr mrs nt) aux
             (update_matchF_base ks kss I mr mrs rels nt))) ms))
     \<and> (\<forall>ms. lookup (snd (foldr (update_matchF_step cs css I mr mrs nt) daux
             (update_matchF_base cs css I mr mrs (drels rels) nt))) ms
          = dtabc ks cs (lookup (snd (foldr (update_matchF_step ks kss I mr mrs nt) aux
             (update_matchF_base ks kss I mr mrs rels nt))) ms))"
  using rel
proof (induct rule: dmld_rel_induct)
  case Nil
  show ?case
    using rels table_lookup_base[OF rels] dtabc_lookup_base[OF rels]
    by (simp add: update_matchF_base_def Let_def empty_table_def)
next
  case (Cons t rls rel aux daux)
  obtain A X where W: "foldr (update_matchF_step ks kss I mr mrs nt) aux
      (update_matchF_base ks kss I mr mrs rels nt) = (A, X)"
    by (cases "foldr (update_matchF_step ks kss I mr mrs nt) aux
      (update_matchF_base ks kss I mr mrs rels nt)")
  obtain DA DX where D: "foldr (update_matchF_step cs css I mr mrs nt) daux
      (update_matchF_base cs css I mr mrs (drels rels) nt) = (DA, DX)"
    by (cases "foldr (update_matchF_step cs css I mr mrs nt) daux
      (update_matchF_base cs css I mr mrs (drels rels) nt)")
  have IH: "dmld_rel ks cs \<psi>s css A DA" and tX: "\<And>ms. table ks (lookup X ms)"
    and dXe: "\<And>ms. lookup DX ms = dtabc ks cs (lookup X ms)"
    using Cons(3) unfolding W D by simp_all
  have tY: "\<forall>ms. table ks (lookup (mrtabulate mrs (l\<delta> ks kss id X rls)) ms)"
    using table_lookup_step[OF Cons(1) tX] by blast
  have dLY: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
      dtabc ks cs (l\<delta> ks kss id X rls ms) = l\<delta> cs css id DX (drels rls) ms"
    by (rule dtabc_ldelta[OF fK wf_atoms[OF Cons(1)] tX dXe okms[OF _ Cons(1)]])
  have dY: "\<forall>ms. lookup (mrtabulate mrs (l\<delta> cs css id DX (drels rls))) ms
      = dtabc ks cs (lookup (mrtabulate mrs (l\<delta> ks kss id X rls)) ms)"
    by (intro allI lookup_mrtabulate_cong[OF d, where f = "l\<delta> ks kss id X rls"
        and g = "l\<delta> cs css id DX (drels rls)"]) (rule dLY)
  have E: "foldr (update_matchF_step ks kss I mr mrs nt) ((t, rls, rel) # aux)
      (update_matchF_base ks kss I mr mrs rels nt)
      = update_matchF_step ks kss I mr mrs nt (t, rls, rel) (A, X)"
    unfolding W[symmetric] by simp
  have DE: "foldr (update_matchF_step cs css I mr mrs nt)
      ((t, drels rls, dtabc ks cs rel) # daux)
      (update_matchF_base cs css I mr mrs (drels rels) nt)
      = update_matchF_step cs css I mr mrs nt (t, drels rls, dtabc ks cs rel) (DA, DX)"
    unfolding D[symmetric] by simp
  show ?case unfolding E DE
    using IH tY dY Cons(1)
    by (simp add: update_matchF_step_def Let_def dtabc_Un_img)
qed

lemma dtabc_update_matchF:
  assumes rels: "wfrels rels" and rel: "dmld_rel ks cs \<psi>s css aux daux"
  shows "dmld_rel ks cs \<psi>s css (update_matchF ks kss I mr mrs rels nt aux)
     (update_matchF cs css I mr mrs (drels rels) nt daux)"
  using dtabc_matchF_foldr[OF rels rel] by (simp add: update_matchF_def)

text \<open>Reading the structure hands out the entries that have left the window, reordered.\<close>

lemma dtabc_eval_matchF:
  assumes "dmld_rel ks cs \<psi>s css aux daux"
  shows "fst (eval_matchF I mr nt daux) = map (dtabc ks cs) (fst (eval_matchF I mr nt aux)) \<and>
     dmld_rel ks cs \<psi>s css (snd (eval_matchF I mr nt aux)) (snd (eval_matchF I mr nt daux))"
  using assms
proof (induct rule: dmld_rel_induct)
  case (Cons t rls rel aux daux)
  obtain ys ax where e: "eval_matchF I mr nt aux = (ys, ax)"
    by (cases "eval_matchF I mr nt aux")
  obtain dys dax where de: "eval_matchF I mr nt daux = (dys, dax)"
    by (cases "eval_matchF I mr nt daux")
  have i1: "dys = map (dtabc ks cs) ys" and i2: "dmld_rel ks cs \<psi>s css ax dax"
    using Cons(3) unfolding e de by simp_all
  show ?case using Cons(1,2) i1 i2 by (simp add: e de)
qed simp

end

(*<*)
end
(*>*)
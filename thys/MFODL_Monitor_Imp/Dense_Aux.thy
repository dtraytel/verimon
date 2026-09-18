(*<*)
theory Dense_Aux
  imports Dense
begin
(*>*)

section \<open>The dense Since and Until structures\<close>

text \<open>
  The temporal structures run at the dense frame \<open>dargs cs_R cs_L args\<close> (20.6): a stored tuple is
  a hole-free tuple of width \<open>length cs_R\<close>.  What is \<open>not\<close> dense there is the probe.  The left
  operand produces its tables at its own, narrower frame \<open>cs_L\<close>, and the evaluator widens each of
  them to \<open>cs_R\<close> with @{const dembedp} before handing it to the structure, only for the
  structure's join to project it back down again.  That is one allocation per left tuple per time
  point, and it reintroduces exactly the holes the dense representation was meant to remove.

  This theory takes the probe table at the frame the left operand already produces it at.  The key
  is that the structure's masked projection and the dense projection at the mask
  \<open>mrg_left_key (mrg_plan cs_R cs_L)\<close> classify a stored tuple identically, the first against the
  widened table and the second against the narrow one.
\<close>

subsection \<open>The dense index under the semi-join\<close>

text \<open>
  Restricting the index (20.32) to the surviving keys is the index of the surviving tuples: a
  bucket passes or fails as a whole, because the filter only looks at the key.
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

subsection \<open>The two projections classify a stored tuple alike\<close>

text \<open>
  The left-hand side is what the verified structure's join tests, against the widened table; the
  right-hand side is what the dense join tests, against the table the left operand produced.  Both
  are the kernel's own test at the wide frame, so they agree.
\<close>

lemma dproj_key_in_iff:
  assumes s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and sub: "set cs_L \<subseteq> set cs_R" and b_R: "\<forall>c \<in> set cs_R. c < n"
    and t: "table n (set cs_L) T" and w: "wf_tuple n (set cs_R) a"
  shows "(proj_tuple (join_mask (length cs_R) (cpos cs_R (set cs_L))) (dproj (wide_mask n cs_R) a)
           \<in> dtabc n cs_R T)
       = (dproj (mrg_left_key (mrg_plan cs_R cs_L)) (dproj (wide_mask n cs_R) a) \<in> dtabc n cs_L T)"
proof -
  have l: "length a = n" using w by (simp add: wf_tuple_def)
  have wp: "wf_tuple n (set cs_L) (proj_tuple (join_mask n (set cs_L)) a)"
    using wf_tuple_proj_tuple[OF w sub] .
  have lhs: "(proj_tuple (join_mask (length cs_R) (cpos cs_R (set cs_L)))
        (dproj (wide_mask n cs_R) a) \<in> dtabc n cs_R T)
      = (proj_tuple (join_mask n (set cs_L)) a \<in> T)"
    unfolding proj_tuple_dproj[OF s_R b_R sub l] dtabc_def
    using dproj_inj_sub[OF s_R b_R sub] wp t by (auto simp: table_def inj_on_def)
  have rhs: "(dproj (mrg_left_key (mrg_plan cs_R cs_L)) (dproj (wide_mask n cs_R) a)
        \<in> dtabc n cs_L T)
      = (proj_tuple (join_mask n (set cs_L)) a \<in> T)"
    unfolding dproj_left_key_eq[OF s_R s_L sub b_R w] dtabc_eq_dtab[OF s_L]
    by (subst wide_mask_eq_join_mask[OF s_L], rule dtab_in_iff[OF t wp])
  show ?thesis unfolding lhs rhs ..
qed

subsection \<open>Maintaining the index incrementally\<close>

text \<open>
  The structure adds and removes whole tables at a time, so the index is maintained by combining
  it with the index of the added table, and by subtracting the index of the removed one bucket by
  bucket.  Both mappings are red-black trees in the generated code, and @{const Mapping.combine}
  and @{const Mapping.map_values} are tree operations there.
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
  "didx_minus i d = Mapping.filter (\<lambda>_ Y. Y \<noteq> {}) (Mapping.map_values (\<lambda>k Y. Y - dbucket d k) i)"

lemma didx_minus_eq: "didx msk (S - D) = didx_minus (didx msk S) (didx msk D)"
proof -
  have "Mapping.lookup (didx msk (S - D)) k
      = Mapping.lookup (didx_minus (didx msk S) (didx msk D)) k" for k
  proof -
    have b: "{y \<in> S. dproj msk y = k} - dbucket (didx msk D) k = {y \<in> S - D. dproj msk y = k}"
      by (auto simp: dbucket_def lookup_didx split: if_splits)
    show ?thesis
      by (auto simp: didx_minus_def Mapping.lookup_filter Mapping.lookup_map_values lookup_didx b
          split: option.splits if_splits)
  qed
  then show ?thesis by (simp add: mapping_eqI)
qed

subsection \<open>Widening the probe table instead of projecting the stored one\<close>

text \<open>
  Inside the structure the probe table is compared against the mask's projection of a stored
  tuple.  The kernel's projection keeps the frame and blanks the columns outside the mask; the
  dense one drops them.  The two differ by @{const dwiden}, which is injective on tables of the
  narrow width, so a stored tuple passes the kernel's test against the widened probe table exactly
  when it passes the dense test against the narrow one.
\<close>

lemma proj_tuple_dwiden_dproj:
  "length as = length msk \<Longrightarrow> proj_tuple msk as = dwiden msk (dproj msk as)"
  by (induct msk as rule: proj_tuple.induct) auto

lemma length_dproj: "length as = length msk \<Longrightarrow> length (dproj msk as) = length (filter id msk)"
  by (induct msk as rule: dproj.induct) auto

lemma proj_tuple_dwiden_image_iff:
  assumes as: "length as = length msk"
    and Y: "\<And>y. y \<in> Y \<Longrightarrow> length y = length (filter id msk)"
  shows "(proj_tuple msk as \<in> dwiden msk ` Y) = (dproj msk as \<in> Y)"
proof
  assume "proj_tuple msk as \<in> dwiden msk ` Y"
  then obtain y where y: "y \<in> Y" "proj_tuple msk as = dwiden msk y" by auto
  then have "dproj msk (proj_tuple msk as) = y" by (simp add: dproj_dwiden Y)
  then show "dproj msk as \<in> Y"
    using y(1) by (simp add: proj_tuple_dwiden_dproj[OF as] dproj_dwiden length_dproj[OF as])
next
  assume "dproj msk as \<in> Y"
  then show "proj_tuple msk as \<in> dwiden msk ` Y"
    by (simp add: proj_tuple_dwiden_dproj[OF as])
qed

subsection \<open>The dense Since structure\<close>

text \<open>
  The state is the verified one with the two indexed tables replaced by @{const didx} indices.
  Everything else -- the two queues, the window's table, and the two mappings that carry the
  timestamps -- is kept verbatim, and the two masks collapse to the single dense mask: at the
  dense frame every column is a column of the right operand, so \<open>maskR\<close> is all-true, and \<open>maskL\<close>
  is the mask the dense projection uses.

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
  falls back on the plain key set -- no join columns, or all columns join columns (7d, 13) -- the
  dense structure keeps no index at all.
\<close>

definition didx_live :: "args \<Rightarrow> bool" where
  "didx_live args \<longleftrightarrow> args_L args \<noteq> {} \<and> args_L args \<noteq> args_R args"

definition didx_upd :: "args \<Rightarrow> (unit \<Rightarrow> ('a tuple, 'a table) mapping) \<Rightarrow>
    ('a tuple, 'a table) mapping" where
  "didx_upd args w = (if didx_live args then w () else Mapping.empty)"

fun dmsaux_of :: "args \<Rightarrow> 'a dmsaux \<Rightarrow> 'a mmsaux" where
  "dmsaux_of args (nt, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
     (nt, gc, join_mask (args_n args) (args_L args), join_mask (args_n args) (args_R args),
      data_prev, data_in, table_in, wf_table_of_set_args args (Mapping.keys tuple_in), tuple_in,
      wf_table_of_set_args args (Mapping.keys tuple_since), tuple_since)"

fun mmsaux_norm :: "args \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "mmsaux_norm args (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in,
      wf_table_since, tuple_since) =
     (nt, gc, maskL, maskR, data_prev, data_in, table_in,
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

text \<open>
  The mask and the arguments describe the same frame: the structure runs at width \<open>args_n args\<close>,
  every column is a column of the right operand, and the left operand's columns are the mask's
  true positions.  This is what @{const dargs} sets up (20.6).
\<close>

definition dmsk_args :: "args \<Rightarrow> bool list \<Rightarrow> bool" where
  "dmsk_args args msk \<longleftrightarrow> length msk = args_n args \<and> args_R args = {0..<args_n args} \<and>
     args_L args = {i. i < length msk \<and> msk ! i}"

lemma dmsk_args_maskL: "dmsk_args args msk \<Longrightarrow> join_mask (args_n args) (args_L args) = msk"
  by (auto simp: dmsk_args_def join_mask_def intro!: nth_equalityI)

lemma dmsk_args_empty: "dmsk_args args msk \<Longrightarrow> (args_L args = {}) = (\<forall>i \<in> set msk. \<not> i)"
  by (auto simp: dmsk_args_def in_set_conv_nth)

lemma dmsk_args_full:
  assumes "dmsk_args args msk"
  shows "(args_L args = args_R args) = (\<forall>i \<in> set msk. i)"
proof -
  have l: "length msk = args_n args" and R: "args_R args = {0..<args_n args}"
    and L: "args_L args = {i. i < length msk \<and> msk ! i}"
    using assms by (auto simp: dmsk_args_def)
  have "(args_L args = args_R args) = (\<forall>i. (i < length msk \<and> msk ! i) = (i < args_n args))"
    by (simp add: L R set_eq_iff)
  also have "\<dots> = (\<forall>i < length msk. msk ! i)" using l by auto
  also have "\<dots> = (\<forall>i \<in> set msk. i)" by (simp add: all_set_conv_all_nth)
  finally show ?thesis .
qed

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

subsection \<open>The join, at the frame the left operand produces\<close>

text \<open>
  The three branches are the verified ones (7d, 13), read densely.  Without join columns the mask
  is all-false, the dense projection of every stored tuple is the empty tuple, and the whole
  window stands or falls with @{term \<open>[] \<in> Y\<close>}.  When every column is a join column the mask is
  all-true, the dense projection is the identity, and the probe table is compared with the stored
  tables directly.  Otherwise the index decides: a bucket's key is what the probe table holds, so
  the surviving tuples are the union of the surviving buckets, and the index of the survivors is
  the restriction of the index -- no tuple of the probe table is touched, and none is widened.
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

text \<open>
  Each dense operation stands for the verified one on the state it stands for, up to the indexed
  tables that @{const mmsaux_norm} rebuilds, and preserves the index invariant.  Validity is then
  the verified lemma.
\<close>

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
  assumes "L \<subseteq> R"
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
  assumes "valid_dmsaux args msk cur daux ys" and "table (args_n args) (args_R args) X"
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

subsection \<open>The join is the verified join against the widened probe table\<close>

lemma dproj_all_False: "\<forall>i \<in> set msk. \<not> i \<Longrightarrow> length as = length msk \<Longrightarrow> dproj msk as = []"
  by (induct msk as rule: dproj.induct) auto

lemma dproj_all_True: "\<forall>i \<in> set msk. i \<Longrightarrow> length as = length msk \<Longrightarrow> dproj msk as = as"
  by (induct msk as rule: dproj.induct) auto

lemma wf_tuple_dwiden_mask:
  assumes "dwf_tuple (length (filter id msk)) y"
  shows "wf_tuple (length msk) {i. i < length msk \<and> msk ! i} (dwiden msk y)"
proof -
  have l: "length y = length (filter id msk)" and s: "\<forall>x \<in> set y. x \<noteq> None"
    using assms by (auto simp: dwf_tuple_def in_set_conv_nth)
  show ?thesis using dwiden_props[OF l s] by (auto simp: wf_tuple_def)
qed

lemma table_dwiden_image:
  assumes dm: "dmsk_args args msk"
    and Y: "\<And>y. y \<in> Y \<Longrightarrow> dwf_tuple (length (filter id msk)) y"
  shows "table (args_n args) (args_L args) (dwiden msk ` Y)"
proof -
  have n: "args_n args = length msk" and L: "args_L args = {i. i < length msk \<and> msk ! i}"
    using dm by (auto simp: dmsk_args_def)
  show ?thesis
    unfolding table_def n L using Y wf_tuple_dwiden_mask by auto
qed

lemma Mapping_filter_True: "Mapping.filter (\<lambda>_ _. True) m = m"
  by (intro mapping_eqI) (simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_filter_False: "Mapping.filter (\<lambda>_ _. False) m = Mapping.empty"
  by (intro mapping_eqI) (simp add: Mapping.lookup_filter split: option.splits)

lemma mapping_delete_set_filter:
  "D = {as \<in> Mapping.keys m. \<not> P as} \<Longrightarrow> mapping_delete_set m D = Mapping.filter (\<lambda>as _. P as) m"
  by (intro mapping_eqI)
     (auto simp: delete_set_lookup Mapping.lookup_filter Mapping.keys_dom_lookup
       split: option.splits)

lemma proj_tuple_in_join_dense:
  assumes as: "length as = length msk"
    and Y: "\<And>y. y \<in> Y \<Longrightarrow> dwf_tuple (length (filter id msk)) y"
  shows "proj_tuple_in_join pos msk as (dwiden msk ` Y) = ((dproj msk as \<in> Y) = pos)"
proof -
  have l: "\<And>y. y \<in> Y \<Longrightarrow> length y = length (filter id msk)" using Y by (simp add: dwf_tuple_def)
  show ?thesis
    using proj_tuple_dwiden_image_iff[OF as l] by (auto simp: proj_tuple_in_join_def)
qed

text \<open>
  Whichever branch it takes, the dense join filters both mappings by the dense test, and the
  window's table follows the mapping it indexes.  That is the verified join's abstract form
  (@{const join_mmsaux_abs}) at the widened probe table.
\<close>

lemma djoin_msaux_abs:
  assumes v: "valid_dmsaux args msk cur (t, gc, m, dp, di, ti, ii, tui, idxs, tus) ys"
    and dm: "dmsk_args args msk"
    and Yw: "\<And>y. y \<in> Y \<Longrightarrow> dwf_tuple (length (filter id msk)) y"
  shows "dmsaux_of args (djoin_msaux args Y (t, gc, m, dp, di, ti, ii, tui, idxs, tus))
     = join_mmsaux_abs args (dwiden msk ` Y)
         (dmsaux_of args (t, gc, m, dp, di, ti, ii, tui, idxs, tus))"
proof -
  have vm: "valid_mmsaux args cur (dmsaux_of args (t, gc, m, dp, di, ti, ii, tui, idxs, tus)) ys"
    by (rule valid_dmsauxD[OF v])
  have mm: "m = msk" using valid_dmsaux_inv[OF v] by simp
  have n: "args_n args = length msk" using dm by (simp add: dmsk_args_def)
  have mL: "join_mask (args_n args) (args_L args) = msk" by (rule dmsk_args_maskL[OF dm])
  have ti_keys: "ti = Mapping.keys tui"
    and tab_in: "table (args_n args) (args_R args) (Mapping.keys tui)"
    and tab_since: "table (args_n args) (args_R args) (Mapping.keys tus)"
    using vm by simp_all
  have len_in: "length as = length msk" if "as \<in> Mapping.keys tui" for as
    using tab_in that by (auto simp: table_def wf_tuple_def n)
  have len_since: "length as = length msk" if "as \<in> Mapping.keys tus" for as
    using tab_since that by (auto simp: table_def wf_tuple_def n)
  have fin: "Mapping.filter
        (\<lambda>as _. proj_tuple_in_join (args_pos args) msk as (dwiden msk ` Y)) tui
      = Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tui"
    by (rule Mapping_filter_cong) (simp add: proj_tuple_in_join_dense[OF len_in Yw])
  have fsince: "Mapping.filter
        (\<lambda>as _. proj_tuple_in_join (args_pos args) msk as (dwiden msk ` Y)) tus
      = Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tus"
    by (rule Mapping_filter_cong) (simp add: proj_tuple_in_join_dense[OF len_since Yw])
  show ?thesis
  proof (cases "\<forall>i \<in> set msk. \<not> i")
    case True
    have cin: "Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tui
        = (if ([] \<in> Y) = args_pos args then tui else Mapping.empty)"
    proof -
      have "Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tui
          = Mapping.filter (\<lambda>as _. ([] \<in> Y) = args_pos args) tui"
        by (rule Mapping_filter_cong) (simp add: dproj_all_False[OF True len_in])
      then show ?thesis
        by (cases "([] \<in> Y) = args_pos args")
           (simp_all add: Mapping_filter_True Mapping_filter_False)
    qed
    have csince: "Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tus
        = (if ([] \<in> Y) = args_pos args then tus else Mapping.empty)"
    proof -
      have "Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tus
          = Mapping.filter (\<lambda>as _. ([] \<in> Y) = args_pos args) tus"
        by (rule Mapping_filter_cong) (simp add: dproj_all_False[OF True len_since])
      then show ?thesis
        by (cases "([] \<in> Y) = args_pos args")
           (simp_all add: Mapping_filter_True Mapping_filter_False)
    qed
    show ?thesis
      using True unfolding mm by (auto simp: Let_def mL fin fsince cin csince ti_keys)
  next
    case False
    note noneF = False
    show ?thesis
    proof (cases "\<forall>i \<in> set msk. i")
      case True
      have cin: "Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tui
          = Mapping.filter (\<lambda>as _. (as \<in> Y) = args_pos args) tui"
        by (rule Mapping_filter_cong) (simp add: dproj_all_True[OF True len_in])
      have csince: "Mapping.filter (\<lambda>as _. (dproj msk as \<in> Y) = args_pos args) tus
          = Mapping.filter (\<lambda>as _. (as \<in> Y) = args_pos args) tus"
        by (rule Mapping_filter_cong) (simp add: dproj_all_True[OF True len_since])
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
        by (auto simp: Let_def mL fin fsince e f csince[symmetric])
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
        by (auto simp: Let_def mL fin fsince e e' f)
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
  obtains nt gc maskL maskR data_prev data_in table_in wf_table_in tuple_in
    wf_table_since tuple_since
  where "aux = (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in,
    wf_table_since, tuple_since)"
  by (metis prod.collapse)

lemma join_mmsaux_abs_eq':
  assumes "valid_mmsaux args cur aux auxlist" and "table (args_n args) (args_L args) X"
  shows "join_mmsaux args X aux = join_mmsaux_abs args X aux"
proof (cases aux rule: mmsaux_cases)
  case (1 nt gc maskL maskR dp di ti wi tui ws tus)
  show ?thesis unfolding 1
    by (rule join_mmsaux_abs_eq[OF assms(1)[unfolded 1] assms(2)])
qed

lemma mmsaux_norm_join_mmsaux_abs:
  "mmsaux_norm args (join_mmsaux_abs args X aux) = join_mmsaux_abs args X aux"
  by (cases aux rule: mmsaux_cases) (simp add: Let_def)

lemma valid_djoin:
  assumes v: "valid_dmsaux args msk cur daux ys" and dm: "dmsk_args args msk"
    and Yw: "\<And>y. y \<in> Y \<Longrightarrow> dwf_tuple (length (filter id msk)) y"
  shows "valid_dmsaux args msk cur (djoin_msaux args Y daux)
     (map (\<lambda>(t, rel). (t, join rel (args_pos args) (dwiden msk ` Y))) ys)"
proof (cases daux rule: dmsaux_cases)
  case (1 t gc m dp di ti ii tui idxs tus)
  have tY: "table (args_n args) (args_L args) (dwiden msk ` Y)"
    by (rule table_dwiden_image[OF dm Yw])
  have vm: "valid_mmsaux args cur (dmsaux_of args daux) ys" by (rule valid_dmsauxD[OF v])
  have abs: "dmsaux_of args (djoin_msaux args Y daux)
      = join_mmsaux_abs args (dwiden msk ` Y) (dmsaux_of args daux)"
    using djoin_msaux_abs[OF v[unfolded 1] dm Yw] unfolding 1 .
  have eq: "dmsaux_of args (djoin_msaux args Y daux)
      = mmsaux_norm args (join_mmsaux args (dwiden msk ` Y) (dmsaux_of args daux))"
    unfolding abs join_mmsaux_abs_eq'[OF vm tY] mmsaux_norm_join_mmsaux_abs ..
  have inv: "dmsaux_inv args msk (djoin_msaux args Y daux)"
    using dmsaux_inv_djoin[OF v[unfolded 1] dm] unfolding 1 .
  show ?thesis
    by (rule valid_dmsauxI[OF valid_join_mmsaux[OF vm tY] eq inv])
qed

lemma valid_dgc_join:
  assumes v: "valid_dmsaux args msk cur daux ys" and dm: "dmsk_args args msk"
    and Yw: "\<And>y. y \<in> Y \<Longrightarrow> dwf_tuple (length (filter id msk)) y"
  shows "valid_dmsaux args msk cur (dgc_join_msaux args Y daux)
     (map (\<lambda>(t, rel). (t, join rel (args_pos args) (dwiden msk ` Y))) ys)"
proof -
  have alt: "dgc_join_msaux args Y daux = djoin_msaux args Y (dgc_msaux args daux)
      \<or> dgc_join_msaux args Y daux = djoin_msaux args Y daux"
    by (cases daux rule: dmsaux_cases) auto
  show ?thesis
    using alt
  proof
    assume "dgc_join_msaux args Y daux = djoin_msaux args Y (dgc_msaux args daux)"
    then show ?thesis using valid_djoin[OF valid_dgc[OF v] dm Yw] by simp
  next
    assume "dgc_join_msaux args Y daux = djoin_msaux args Y daux"
    then show ?thesis using valid_djoin[OF v dm Yw] by simp
  qed
qed

subsection \<open>The dense mask at the dense frame\<close>

text \<open>
  At the frame @{const dargs} sets up, the mask is the one the dense join of 20.8 already uses,
  and widening a table of the left operand's frame by it is the same as narrowing the wide table
  to the right operand's columns -- which is what the evaluator computes today by embedding.
\<close>

lemma length_mrg_left_key:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     length (mrg_left_key (mrg_plan cs1 cs2)) = length cs1"
  by (induct cs1 cs2 rule: mrg_plan.induct) auto

lemma length_filter_mrg_left_key:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     length (filter id (mrg_left_key (mrg_plan cs1 cs2))) = length cs2"
  by (induct cs1 cs2 rule: mrg_plan.induct) auto

lemma dwiden_mrg_left_key:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     dwiden (mrg_left_key (mrg_plan cs1 cs2)) (map f cs2)
     = map (\<lambda>c. if c \<in> set cs2 then f c else None) cs1"
proof (induct cs1 cs2 rule: mrg_plan.induct)
  case (3 c cs d ds)
  from 3 have nc: "c \<notin> set cs" by auto
  have aux: "map (\<lambda>ca. if ca = c \<or> ca \<in> set ds then f ca else None) cs
      = map (\<lambda>ca. if ca \<in> set ds then f ca else None) cs"
    using nc by (intro map_cong[OF refl]) auto
  show ?case
  proof (cases "c = d")
    case True
    from 3 True have sub: "set ds \<subseteq> set cs" by auto
    from 3 True sub show ?thesis by (auto simp: aux)
  next
    case False
    from 3 False show ?thesis by (auto dest: order.asym)
  qed
qed auto

lemma nth_mrg_left_key:
  assumes s1: "sorted_wrt (<) cs1" and s2: "sorted_wrt (<) cs2"
    and sub: "set cs2 \<subseteq> set cs1" and i: "i < length cs1"
  shows "mrg_left_key (mrg_plan cs1 cs2) ! i = (cs1 ! i \<in> set cs2)"
proof -
  let ?msk = "mrg_left_key (mrg_plan cs1 cs2)"
  have l: "length ?msk = length cs1" by (rule length_mrg_left_key[OF s1 s2 sub])
  have lf: "length (map Some cs2) = length (filter id ?msk)"
    by (simp add: length_filter_mrg_left_key[OF s1 s2 sub])
  have ns: "\<forall>x \<in> set (map Some cs2). x \<noteq> None" by auto
  have "dwiden ?msk (map Some cs2) = map (\<lambda>c. if c \<in> set cs2 then Some c else None) cs1"
    by (rule dwiden_mrg_left_key[OF s1 s2 sub])
  then have "(map (\<lambda>c. if c \<in> set cs2 then Some c else None) cs1 ! i = None) = (\<not> ?msk ! i)"
    using dwiden_props[OF lf ns] i l by simp
  then show ?thesis using i by (simp split: if_splits)
qed

lemma dmsk_args_dargs:
  assumes s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and sub: "set cs_L \<subseteq> set cs_R"
  shows "dmsk_args (dargs cs_R cs_L args) (mrg_left_key (mrg_plan cs_R cs_L))"
  unfolding dmsk_args_def dargs_simps length_mrg_left_key[OF s_R s_L sub]
  by (auto simp: cpos_def nth_mrg_left_key[OF s_R s_L sub])

lemma dwiden_dtabc:
  assumes s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and sub: "set cs_L \<subseteq> set cs_R" and b_R: "\<forall>c \<in> set cs_R. c < n"
    and w: "wf_tuple n (set cs_L) x"
  shows "dwiden (mrg_left_key (mrg_plan cs_R cs_L)) (dproj (wide_mask n cs_L) x)
       = dproj (wide_mask n cs_R) x"
proof -
  have l: "length x = n" using w by (simp add: wf_tuple_def)
  have b_L: "\<forall>c \<in> set cs_L. c < n" using sub b_R by auto
  have none: "\<And>c. c \<in> set cs_R \<Longrightarrow> c \<notin> set cs_L \<Longrightarrow> x ! c = None"
    using w b_R by (auto simp: wf_tuple_def)
  have "dwiden (mrg_left_key (mrg_plan cs_R cs_L)) (map (\<lambda>c. x ! c) cs_L)
      = map (\<lambda>c. if c \<in> set cs_L then x ! c else None) cs_R"
    by (rule dwiden_mrg_left_key[OF s_R s_L sub])
  also have "\<dots> = map (\<lambda>c. x ! c) cs_R" using none by (intro map_cong[OF refl]) auto
  finally show ?thesis
    unfolding dproj_wide_mask_eq_map_nth[OF s_L b_L l] dproj_wide_mask_eq_map_nth[OF s_R b_R l] .
qed

lemma dwiden_image_dtabc:
  assumes s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and sub: "set cs_L \<subseteq> set cs_R" and b_R: "\<forall>c \<in> set cs_R. c < n"
    and t: "table n (set cs_L) T"
  shows "dwiden (mrg_left_key (mrg_plan cs_R cs_L)) ` dtabc n cs_L T = dtabc n cs_R T"
proof -
  have key: "dwiden (mrg_left_key (mrg_plan cs_R cs_L)) (dproj (wide_mask n cs_L) x)
      = dproj (wide_mask n cs_R) x" if "x \<in> T" for x
    using t that dwiden_dtabc[OF s_R s_L sub b_R] by (auto simp: table_def)
  show ?thesis unfolding dtabc_def image_image by (intro image_cong[OF refl]) (simp add: key)
qed

lemma dwf_tuple_dtabc:
  assumes s_L: "sorted_wrt (<) cs_L" and b_L: "\<forall>c \<in> set cs_L. c < n"
    and t: "table n (set cs_L) T" and y: "y \<in> dtabc n cs_L T"
  shows "dwf_tuple (length cs_L) y"
proof -
  obtain x where x: "x \<in> T" "y = dproj (wide_mask n cs_L) x" using y by (auto simp: dtabc_def)
  then have w: "wf_tuple n (set cs_L) x" using t by (simp add: table_def)
  then have l: "length x = n" by (simp add: wf_tuple_def)
  have "y = map (\<lambda>c. x ! c) cs_L"
    unfolding x(2) by (rule dproj_wide_mask_eq_map_nth[OF s_L b_L l])
  then show ?thesis using w b_L by (auto simp: dwf_tuple_def wf_tuple_def)
qed

section \<open>The dense Since structure at the dense frame\<close>

text \<open>
  The same relation the wide structure has to the narrowed auxiliary list (20.6), now for the
  dense structure.  Only the join reads differently: it takes the left operand's table at the left
  operand's own frame, so the node need not embed it.
\<close>

definition dmsk :: "cols \<Rightarrow> cols \<Rightarrow> bool list" where
  "dmsk cs_R cs_L = mrg_left_key (mrg_plan cs_R cs_L)"

definition dsaux' :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> event_data dmsaux \<Rightarrow>
    (ts \<times> event_data table) list \<Rightarrow> bool" where
  "dsaux' n cs_R cs_L args cur daux auxlist \<longleftrightarrow>
     (\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel) \<and>
     valid_dmsaux (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux (dauxlist n cs_R auxlist)"

lemma dsaux'_init:
  assumes sub: "set cs_L \<subseteq> set cs_R"
  shows "dsaux' n cs_R cs_L args 0 (dinit_msaux (dargs cs_R cs_L args) (dmsk cs_R cs_L)) []"
proof -
  have "valid_dmsaux (init_args (args_ivl args) (length cs_R) (cpos cs_R (set cs_L))
      {0..<length cs_R} (args_pos args) None) (dmsk cs_R cs_L) 0
      (dinit_msaux (init_args (args_ivl args) (length cs_R) (cpos cs_R (set cs_L))
        {0..<length cs_R} (args_pos args) None) (dmsk cs_R cs_L)) []"
    by (rule valid_dinit_msaux) (use sub in \<open>auto simp: cpos_def\<close>)
  then show ?thesis by (simp add: dsaux'_def dargs_def dauxlist_def)
qed

lemma dsaux'_add_new_ts:
  assumes v: "dsaux' n cs_R cs_L args cur daux auxlist" and nt: "cur \<le> nt"
  shows "dsaux' n cs_R cs_L args nt (dadd_new_ts_msaux (dargs cs_R cs_L args) nt daux)
      (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and d: "valid_dmsaux (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux
      (dauxlist n cs_R auxlist)"
    using v by (auto simp: dsaux'_def)
  have "valid_dmsaux (dargs cs_R cs_L args) (dmsk cs_R cs_L) nt
      (dadd_new_ts_msaux (dargs cs_R cs_L args) nt daux)
      (filter (\<lambda>(t, rel). memR (args_ivl (dargs cs_R cs_L args)) (nt - t))
        (dauxlist n cs_R auxlist))"
    by (rule valid_dadd_new_ts[OF d nt])
  then show ?thesis using w by (simp add: dsaux'_def dauxlist_filter)
qed

lemma dsaux'_join:
  assumes v: "dsaux' n cs_R cs_L args cur daux auxlist"
    and s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and b_R: "\<forall>c \<in> set cs_R. c < n"
    and sub: "set cs_L \<subseteq> set cs_R" and t1: "table n (set cs_L) rel1"
  shows "dsaux' n cs_R cs_L args cur
      (dgc_join_msaux (dargs cs_R cs_L args) (dtabc n cs_L rel1) daux)
      (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and d: "valid_dmsaux (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux
      (dauxlist n cs_R auxlist)"
    using v by (auto simp: dsaux'_def)
  have b_L: "\<forall>c \<in> set cs_L. c < n" using sub b_R by auto
  have dm: "dmsk_args (dargs cs_R cs_L args) (dmsk cs_R cs_L)"
    unfolding dmsk_def by (rule dmsk_args_dargs[OF s_R s_L sub])
  have lf: "length (filter id (dmsk cs_R cs_L)) = length cs_L"
    unfolding dmsk_def by (rule length_filter_mrg_left_key[OF s_R s_L sub])
  have Yw: "\<And>y. y \<in> dtabc n cs_L rel1 \<Longrightarrow> dwf_tuple (length (filter id (dmsk cs_R cs_L))) y"
    unfolding lf by (rule dwf_tuple_dtabc[OF s_L b_L t1])
  have wi: "dwiden (dmsk cs_R cs_L) ` dtabc n cs_L rel1 = dtabc n cs_R rel1"
    unfolding dmsk_def by (rule dwiden_image_dtabc[OF s_R s_L sub b_R t1])
  have jj: "valid_dmsaux (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur
      (dgc_join_msaux (dargs cs_R cs_L args) (dtabc n cs_L rel1) daux)
      (map (\<lambda>(t, rel). (t, join rel (args_pos (dargs cs_R cs_L args))
        (dwiden (dmsk cs_R cs_L) ` dtabc n cs_L rel1))) (dauxlist n cs_R auxlist))"
    by (rule valid_dgc_join[OF d dm]) (rule Yw)
  from jj[unfolded wi] show ?thesis using w
    by (simp add: dsaux'_def dauxlist_join[OF s_R b_R sub w t1]
        dauxlist_wf_join[OF w sub t1])
qed

lemma dsaux'_add_new_table:
  assumes v: "dsaux' n cs_R cs_L args cur daux auxlist"
    and s_R: "sorted_wrt (<) cs_R" and b_R: "\<forall>c \<in> set cs_R. c < n"
    and t2: "table n (set cs_R) rel2"
  shows "dsaux' n cs_R cs_L args cur
      (dadd_new_table_msaux (dargs cs_R cs_L args) (dtabc n cs_R rel2) daux)
      (case auxlist of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and d: "valid_dmsaux (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux
      (dauxlist n cs_R auxlist)"
    using v by (auto simp: dsaux'_def)
  have tt: "table (args_n (dargs cs_R cs_L args)) (args_R (dargs cs_R cs_L args))
      (dtabc n cs_R rel2)"
    using table_dtabc_cpos[OF s_R b_R subset_refl t2] by (simp add: cpos_all)
  have "valid_dmsaux (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur
      (dadd_new_table_msaux (dargs cs_R cs_L args) (dtabc n cs_R rel2) daux)
      (case dauxlist n cs_R auxlist of [] \<Rightarrow> [(cur, dtabc n cs_R rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> dtabc n cs_R rel2) # r
                         else (cur, dtabc n cs_R rel2) # dauxlist n cs_R auxlist)"
    by (rule valid_dadd_new_table[OF d tt])
  then show ?thesis using w t2
    by (simp add: dsaux'_def dauxlist_add_new_table[symmetric]
        dauxlist_wf_add_new_table[OF w t2])
qed

lemma dsaux'_result:
  assumes v: "dsaux' n cs_R cs_L args cur daux auxlist"
  shows "dresult_msaux (dargs cs_R cs_L args) daux
      = dtabc n cs_R (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist,
          memL (args_ivl args) (cur - t)] {})"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and d: "valid_dmsaux (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux
      (dauxlist n cs_R auxlist)"
    using v by (auto simp: dsaux'_def)
  have "dresult_msaux (dargs cs_R cs_L args) daux
      = foldr (\<union>) [rel. (t, rel) \<leftarrow> dauxlist n cs_R auxlist,
          memL (args_ivl (dargs cs_R cs_L args)) (cur - t)] {}"
    by (rule valid_dresult_msaux[OF d])
  then show ?thesis by (simp add: dtabc_result[OF w])
qed

section \<open>The dense evaluation of a Since buffer\<close>

text \<open>
  The kernel's @{text eval_since} with the dense operations put in.  The left operand's tables
  reach it at the left operand's own frame; nothing is embedded on the way in, and the
  structure's join reads them there.
\<close>

fun deval_since :: "args \<Rightarrow> event_data table list \<Rightarrow> event_data mbuf2S \<Rightarrow> event_data dmsaux \<Rightarrow>
    event_data table list \<times> event_data mbuf2S \<times> event_data dmsaux" where
  "deval_since args rs (x # xs, [], t # ts, skew) daux =
    (if skew \<or> memL (args_ivl args) 0
     then (rev rs, (x # xs, [], t # ts, skew), daux)
     else (let daux' = dgc_join_msaux args x (dadd_new_ts_msaux args t daux)
       in (rev (dresult_msaux args daux' # rs), (xs, [], ts, True), daux')))"
| "deval_since args rs (xs, y # ys, ts, True) daux =
    deval_since args rs (xs, ys, ts, False) (dadd_new_table_msaux args y daux)"
| "deval_since args rs (x # xs, y # ys, t # ts, False) daux =
    (let daux' = dadd_new_table_msaux args y
       (dgc_join_msaux args x (dadd_new_ts_msaux args t daux))
     in deval_since args (dresult_msaux args daux' # rs) (xs, ys, ts, False) daux')"
| "deval_since args rs buf daux = (rev rs, buf, daux)"

(*<*)
end
(*>*)

(*<*)
theory Dense_Aux
  imports Dense "MFODL_Monitor_Devel.Correctness"
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
  unfolding valid_dmsaux_lz_def by (cases daux rule: dmsaux_cases) (auto intro!: exI)

lemma valid_dinit_msaux_lz:
  assumes "L \<subseteq> R"
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
  assumes v: "valid_dmsaux_lz args msk cur daux ys" and X: "table (args_n args) (args_R args) X"
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
  by (cases daux rule: dmsaux_cases) (auto simp: Let_def)

lemma dgc_dset_since:
  "\<exists>g' i' s'. dgc_msaux args (dset_since g i s daux) = dset_since g' i' s' daux"
  by (cases daux rule: dmsaux_cases) (auto simp: Let_def)

lemma valid_dgc_join_lz:
  assumes v: "valid_dmsaux_lz args msk cur daux ys" and dm: "dmsk_args args msk"
    and Yw: "\<And>y. y \<in> Y \<Longrightarrow> dwf_tuple (length (filter id msk)) y"
  shows "valid_dmsaux_lz args msk cur (dgc_join_lz args Y daux)
     (map (\<lambda>(t, rel). (t, join rel (args_pos args) (dwiden msk ` Y))) ys)"
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
      (map (\<lambda>(t, rel). (t, join rel (args_pos args) (dwiden msk ` Y))) ys)"
    by (rule valid_dgc_join[OF vw dm]) (rule Yw)
  ultimately show ?thesis
    unfolding e dgc_join_lz_def valid_dmsaux_lz_def if_P[OF True] by blast
next
  case False
  then show ?thesis using v valid_dgc_join[OF _ dm Yw]
    by (simp add: valid_dmsaux_lz_def dgc_join_lz_def)
qed

lemma valid_dresult_msaux_lz:
  "valid_dmsaux_lz args msk cur daux ys \<Longrightarrow> dresult_msaux args daux
    = foldr (\<union>) [rel. (t, rel) \<leftarrow> ys, memL (args_ivl args) (cur - t)] {}"
  unfolding valid_dmsaux_lz_def
  by (cases daux rule: dmsaux_cases) (auto dest: valid_dresult_msaux split: if_splits)

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
     valid_dmsaux_lz (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux (dauxlist n cs_R auxlist)"

lemma dsaux'_init:
  assumes sub: "set cs_L \<subseteq> set cs_R"
  shows "dsaux' n cs_R cs_L args 0 (dinit_msaux (dargs cs_R cs_L args) (dmsk cs_R cs_L)) []"
proof -
  have "valid_dmsaux_lz (init_args (args_ivl args) (length cs_R) (cpos cs_R (set cs_L))
      {0..<length cs_R} (args_pos args) None) (dmsk cs_R cs_L) 0
      (dinit_msaux (init_args (args_ivl args) (length cs_R) (cpos cs_R (set cs_L))
        {0..<length cs_R} (args_pos args) None) (dmsk cs_R cs_L)) []"
    by (rule valid_dinit_msaux_lz) (use sub in \<open>auto simp: cpos_def\<close>)
  then show ?thesis by (simp add: dsaux'_def dargs_def dauxlist_def)
qed

lemma dsaux'_add_new_ts:
  assumes v: "dsaux' n cs_R cs_L args cur daux auxlist" and nt: "cur \<le> nt"
  shows "dsaux' n cs_R cs_L args nt (dadd_new_ts_msaux (dargs cs_R cs_L args) nt daux)
      (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and d: "valid_dmsaux_lz (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux
      (dauxlist n cs_R auxlist)"
    using v by (auto simp: dsaux'_def)
  have "valid_dmsaux_lz (dargs cs_R cs_L args) (dmsk cs_R cs_L) nt
      (dadd_new_ts_msaux (dargs cs_R cs_L args) nt daux)
      (filter (\<lambda>(t, rel). memR (args_ivl (dargs cs_R cs_L args)) (nt - t))
        (dauxlist n cs_R auxlist))"
    by (rule valid_dadd_new_ts_lz[OF d nt])
  then show ?thesis using w by (simp add: dsaux'_def dauxlist_filter)
qed

lemma dsaux'_join:
  assumes v: "dsaux' n cs_R cs_L args cur daux auxlist"
    and s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and b_R: "\<forall>c \<in> set cs_R. c < n"
    and sub: "set cs_L \<subseteq> set cs_R" and t1: "table n (set cs_L) rel1"
  shows "dsaux' n cs_R cs_L args cur
      (dgc_join_lz (dargs cs_R cs_L args) (dtabc n cs_L rel1) daux)
      (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and d: "valid_dmsaux_lz (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux
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
  have jj: "valid_dmsaux_lz (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur
      (dgc_join_lz (dargs cs_R cs_L args) (dtabc n cs_L rel1) daux)
      (map (\<lambda>(t, rel). (t, join rel (args_pos (dargs cs_R cs_L args))
        (dwiden (dmsk cs_R cs_L) ` dtabc n cs_L rel1))) (dauxlist n cs_R auxlist))"
    by (rule valid_dgc_join_lz[OF d dm]) (rule Yw)
  from jj[unfolded wi] show ?thesis using w
    by (simp add: dsaux'_def dauxlist_join[OF s_R b_R sub w t1]
        dauxlist_wf_join[OF w sub t1])
qed

lemma dsaux'_add_new_table:
  assumes v: "dsaux' n cs_R cs_L args cur daux auxlist"
    and s_R: "sorted_wrt (<) cs_R" and b_R: "\<forall>c \<in> set cs_R. c < n"
    and t2: "table n (set cs_R) rel2"
  shows "dsaux' n cs_R cs_L args cur
      (dadd_new_table_lz (dargs cs_R cs_L args) (dtabc n cs_R rel2) daux)
      (case auxlist of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # auxlist)"
proof -
  have w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and d: "valid_dmsaux_lz (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux
      (dauxlist n cs_R auxlist)"
    using v by (auto simp: dsaux'_def)
  have tt: "table (args_n (dargs cs_R cs_L args)) (args_R (dargs cs_R cs_L args))
      (dtabc n cs_R rel2)"
    using table_dtabc_cpos[OF s_R b_R subset_refl t2] by (simp add: cpos_all)
  have "valid_dmsaux_lz (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur
      (dadd_new_table_lz (dargs cs_R cs_L args) (dtabc n cs_R rel2) daux)
      (case dauxlist n cs_R auxlist of [] \<Rightarrow> [(cur, dtabc n cs_R rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> dtabc n cs_R rel2) # r
                         else (cur, dtabc n cs_R rel2) # dauxlist n cs_R auxlist)"
    by (rule valid_dadd_new_table_lz[OF d tt])
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
    and d: "valid_dmsaux_lz (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux
      (dauxlist n cs_R auxlist)"
    using v by (auto simp: dsaux'_def)
  have "dresult_msaux (dargs cs_R cs_L args) daux
      = foldr (\<union>) [rel. (t, rel) \<leftarrow> dauxlist n cs_R auxlist,
          memL (args_ivl (dargs cs_R cs_L args)) (cur - t)] {}"
    by (rule valid_dresult_msaux_lz[OF d])
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

section \<open>The dense Until structure\<close>

text \<open>
  The Until structure needs far less than the Since one.  Of its eleven components only two
  mention the left operand at all: the mask, and the mapping @{text a1_map} that records, for each
  tuple of the left operand's frame, the last time point at which it held.  Every other operation
  -- the window's step, the shift, the evaluation, the length -- carries both through untouched.
  So the dense structure is the verified one with @{text a1_map} keyed by the left operand's
  \<^emph>\<open>dense\<close> tuples, and only the one operation that reads the left operand changes.

  The two key transformations below are mutually inverse on the states that occur: @{text wkeys}
  widens a narrow key set to the frame the verified structure stores at, @{text nkeys} narrows it
  back.
\<close>

lift_definition wkeys :: "bool list \<Rightarrow> ('a tuple, 'b) mapping \<Rightarrow> ('a tuple, 'b) mapping" is
  "\<lambda>msk m k. if k = dwiden msk (dproj msk k) then m (dproj msk k) else None" .

lift_definition nkeys :: "bool list \<Rightarrow> ('a tuple, 'b) mapping \<Rightarrow> ('a tuple, 'b) mapping" is
  "\<lambda>msk m k. m (dwiden msk k)" .

lemma lookup_wkeys: "Mapping.lookup (wkeys msk m) k =
  (if k = dwiden msk (dproj msk k) then Mapping.lookup m (dproj msk k) else None)"
  by transfer simp

lemma lookup_nkeys: "Mapping.lookup (nkeys msk m) k = Mapping.lookup m (dwiden msk k)"
  by transfer simp

lemma dwiden_dproj_dwiden:
  "length y = length (filter id msk) \<Longrightarrow> dwiden msk (dproj msk (dwiden msk y)) = dwiden msk y"
  by (simp add: dproj_dwiden)

lemma lookup_wkeys_dwiden:
  "length y = length (filter id msk) \<Longrightarrow>
     Mapping.lookup (wkeys msk m) (dwiden msk y) = Mapping.lookup m y"
  by (simp add: lookup_wkeys dproj_dwiden dwiden_dproj_dwiden)

lemma lookup_wkeys_proj_tuple:
  "length as = length msk \<Longrightarrow>
     Mapping.lookup (wkeys msk m) (proj_tuple msk as) = Mapping.lookup m (dproj msk as)"
  by (simp add: proj_tuple_dwiden_dproj lookup_wkeys_dwiden length_dproj)

abbreviation (input) dnarrow_tuple :: "bool list \<Rightarrow> 'a tuple \<Rightarrow> bool" where
  "dnarrow_tuple msk y \<equiv> length y = length (filter id msk)"

lemma inj_on_dwiden: "inj_on (dwiden msk) {y. dnarrow_tuple msk y}"
  by (rule inj_onI) (metis dproj_dwiden mem_Collect_eq)

lemma dwiden_image_iff:
  assumes X: "\<And>y. y \<in> X \<Longrightarrow> dnarrow_tuple msk y" and k: "k = dwiden msk (dproj msk k)"
  shows "(k \<in> dwiden msk ` X) = (dproj msk k \<in> X)"
proof
  assume "k \<in> dwiden msk ` X"
  then obtain y where y: "y \<in> X" "k = dwiden msk y" by auto
  then show "dproj msk k \<in> X" using X[OF y(1)] by (simp add: dproj_dwiden)
next
  assume "dproj msk k \<in> X"
  then show "k \<in> dwiden msk ` X" using k by (metis image_eqI)
qed

lemma dwiden_image_not:
  assumes X: "\<And>y. y \<in> X \<Longrightarrow> dnarrow_tuple msk y" and k: "k \<noteq> dwiden msk (dproj msk k)"
  shows "k \<notin> dwiden msk ` X"
  using X k by (auto simp: dproj_dwiden)

lemma keys_wkeys:
  assumes m: "\<And>k. k \<in> Mapping.keys m \<Longrightarrow> dnarrow_tuple msk k"
  shows "Mapping.keys (wkeys msk m) = dwiden msk ` Mapping.keys m"
proof (intro set_eqI iffI)
  fix k assume "k \<in> Mapping.keys (wkeys msk m)"
  then have "k = dwiden msk (dproj msk k)" and "dproj msk k \<in> Mapping.keys m"
    by (auto simp: Mapping.keys_dom_lookup lookup_wkeys dom_def split: if_splits)
  then show "k \<in> dwiden msk ` Mapping.keys m" by (metis image_eqI)
next
  fix k assume "k \<in> dwiden msk ` Mapping.keys m"
  then obtain y where y: "y \<in> Mapping.keys m" "k = dwiden msk y" by auto
  then show "k \<in> Mapping.keys (wkeys msk m)"
    using m[OF y(1)] by (auto simp: Mapping.keys_dom_lookup lookup_wkeys dom_def dproj_dwiden)
qed

lemma wkeys_upd_set:
  assumes X: "\<And>y. y \<in> X \<Longrightarrow> dnarrow_tuple msk y"
  shows "wkeys msk (upd_set m (\<lambda>_. v) X) = upd_set (wkeys msk m) (\<lambda>_. v) (dwiden msk ` X)"
proof (intro mapping_eqI)
  fix k
  show "Mapping.lookup (wkeys msk (upd_set m (\<lambda>_. v) X)) k
      = Mapping.lookup (upd_set (wkeys msk m) (\<lambda>_. v) (dwiden msk ` X)) k"
  proof (cases "k = dwiden msk (dproj msk k)")
    case True
    show ?thesis
      by (simp add: lookup_wkeys Mapping_lookup_upd_set dwiden_image_iff[OF X True]
          if_P[OF True])
  next
    case False
    show ?thesis
      by (simp add: lookup_wkeys Mapping_lookup_upd_set dwiden_image_not[OF X False]
          if_not_P[OF False])
  qed
qed

lemma wkeys_filter:
  assumes X: "\<And>y. y \<in> X \<Longrightarrow> dnarrow_tuple msk y"
  shows "wkeys msk (Mapping.filter (\<lambda>as _. as \<in> X) m)
       = Mapping.filter (\<lambda>as _. as \<in> dwiden msk ` X) (wkeys msk m)"
proof (intro mapping_eqI)
  fix k
  show "Mapping.lookup (wkeys msk (Mapping.filter (\<lambda>as _. as \<in> X) m)) k
      = Mapping.lookup (Mapping.filter (\<lambda>as _. as \<in> dwiden msk ` X) (wkeys msk m)) k"
  proof (cases "k = dwiden msk (dproj msk k)")
    case True
    show ?thesis
      by (simp add: lookup_wkeys Mapping.lookup_filter dwiden_image_iff[OF X True]
          if_P[OF True] split: option.splits)
  next
    case False
    show ?thesis
      by (simp add: lookup_wkeys Mapping.lookup_filter if_not_P[OF False] split: option.splits)
  qed
qed

subsection \<open>The state transformation, and the operations that ignore it\<close>

lemma mmuaux_dq_cases:
  fixes d :: "event_data mmuaux_dq"
  obtains tp tss tables len mL mR result a1_map a2_dq tstp_dq dn
  where "d = (tp, tss, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"
  by (metis prod.collapse)

fun wkeys_uaux :: "bool list \<Rightarrow> event_data mmuaux_dq \<Rightarrow> event_data mmuaux_dq" where
  "wkeys_uaux msk (tp, tss, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn) =
     (tp, tss, tables, len, mL, mR, result, wkeys msk a1_map, a2_dq, tstp_dq, dn)"

fun nkeys_uaux :: "bool list \<Rightarrow> event_data mmuaux_dq \<Rightarrow> event_data mmuaux_dq" where
  "nkeys_uaux msk (tp, tss, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn) =
     (tp, tss, tables, len, mL, mR, result, nkeys msk a1_map, a2_dq, tstp_dq, dn)"

text \<open>
  The window's step never reads the mapping the left operand fills, so it commutes with the
  transformation, and so do the shift and the evaluation built on it.
\<close>

lemma eval_step_dq_wkeys:
  assumes ne: "linearize (fst (snd d)) \<noteq> []"
  shows "eval_step_dq args (wkeys_uaux msk d) = wkeys_uaux msk (eval_step_dq args d)"
proof (cases d rule: mmuaux_dq_cases)
  case (1 tp tss tables len mL mR result a1_map a2_dq tstp_dq dn)
  obtain a q' where hd: "safe_hd tss = (Some a, q')"
    using ne unfolding 1
    by (cases "safe_hd tss") (auto dest!: safe_hd_rep split: option.splits)
  show ?thesis unfolding 1 wkeys_uaux.simps eval_step_dq.simps hd
    by (simp add: Let_def split: prod.splits option.splits)
qed

lemma linearize_eval_step_dq:
  assumes ne: "linearize (fst (snd d)) \<noteq> []"
  shows "linearize (fst (snd (eval_step_dq args d))) = tl (linearize (fst (snd d)))"
proof (cases d rule: mmuaux_dq_cases)
  case (1 tp tss tables len mL mR result a1_map a2_dq tstp_dq dn)
  obtain a q' where hd: "safe_hd tss = (Some a, q')"
    using ne unfolding 1
    by (cases "safe_hd tss") (auto dest!: safe_hd_rep split: option.splits)
  have lq: "linearize q' = linearize tss" using safe_hd_rep[OF hd] by simp
  obtain b q'' where hd': "safe_hd (tl_queue q') = (b, q'')" by fastforce
  have lq'': "linearize q'' = tl (linearize tss)"
    using safe_hd_rep[OF hd'] lq by (simp add: tl_queue_rep)
  show ?thesis unfolding 1 eval_step_dq.simps hd
    by (simp add: Let_def hd' lq'' split: prod.splits option.splits)
qed

lemma foldl_eval_step_dq_wkeys:
  "length xs \<le> length (linearize (fst (snd d))) \<Longrightarrow>
     foldl (\<lambda>aux _. eval_step_dq args aux) (wkeys_uaux msk d) xs
     = wkeys_uaux msk (foldl (\<lambda>aux _. eval_step_dq args aux) d xs)"
proof (induct xs arbitrary: d)
  case (Cons x xs)
  then have ne: "linearize (fst (snd d)) \<noteq> []" by auto
  have "length xs \<le> length (linearize (fst (snd (eval_step_dq args d))))"
    using Cons(2) linearize_eval_step_dq[OF ne] by simp
  then show ?case using Cons(1) eval_step_dq_wkeys[OF ne] by simp
qed simp

lemma shift_dq_wkeys: "shift_dq args nt (wkeys_uaux msk d) = wkeys_uaux msk (shift_dq args nt d)"
proof (cases d rule: mmuaux_dq_cases)
  case (1 tp tss tables len mL mR result a1_map a2_dq tstp_dq dn)
  obtain q0 q1 where tw: "takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss = (q0, q1)"
    by fastforce
  have le: "length (linearize q0) \<le> length (linearize q1)"
    using takeWhile_queue_rep_fst[of "\<lambda>t. \<not> memR (args_ivl args) (nt - t)" tss]
      takeWhile_queue_rep_snd[of "\<lambda>t. \<not> memR (args_ivl args) (nt - t)" tss]
    unfolding tw by (simp add: length_takeWhile_le)
  have key: "foldl (\<lambda>aux _. eval_step_dq args aux)
      (tp, q1, tables, len, mL, mR, result, wkeys msk a1_map, a2_dq, tstp_dq, dn) (linearize q0)
    = wkeys_uaux msk (foldl (\<lambda>aux _. eval_step_dq args aux)
      (tp, q1, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn) (linearize q0))"
    using foldl_eval_step_dq_wkeys[where xs = "linearize q0"
      and d = "(tp, q1, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"] le by simp
  show ?thesis unfolding 1 wkeys_uaux.simps shift_dq.simps tw by (simp add: key)
qed

lemma eval_dq_wkeys:
  "eval_dq args nt (wkeys_uaux msk d)
   = (fst (eval_dq args nt d), wkeys_uaux msk (snd (eval_dq args nt d)))"
  by (cases "shift_dq args nt d" rule: mmuaux_dq_cases) (simp add: shift_dq_wkeys)

lemma length_dq_wkeys: "length_dq args (wkeys_uaux msk d) = length_dq args d"
  by (cases d rule: mmuaux_dq_cases) simp

lemma wkeys_uaux_init: "wkeys_uaux msk (init_dq args) = init_dq args"
  by (simp add: init_dq_def wkeys.abs_eq Mapping.empty_def)

fun lft_of :: "event_data mmuaux_dq \<Rightarrow> bool list \<times> (event_data tuple, nat) mapping" where
  "lft_of (tp, tss, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn) = (mL, a1_map)"

lemma a1_of_eval_step_dq:
  assumes ne: "linearize (fst (snd d)) \<noteq> []"
  shows "lft_of (eval_step_dq args d) = lft_of d"
proof (cases d rule: mmuaux_dq_cases)
  case (1 tp tss tables len mL mR result a1_map a2_dq tstp_dq dn)
  obtain a q' where hd: "safe_hd tss = (Some a, q')"
    using ne unfolding 1
    by (cases "safe_hd tss") (auto dest!: safe_hd_rep split: option.splits)
  show ?thesis unfolding 1 eval_step_dq.simps hd
    by (simp add: Let_def split: prod.splits option.splits)
qed

lemma a1_of_foldl_eval_step_dq:
  "length xs \<le> length (linearize (fst (snd d))) \<Longrightarrow>
     lft_of (foldl (\<lambda>aux _. eval_step_dq args aux) d xs) = lft_of d"
proof (induct xs arbitrary: d)
  case (Cons x xs)
  then have ne: "linearize (fst (snd d)) \<noteq> []" by auto
  have "length xs \<le> length (linearize (fst (snd (eval_step_dq args d))))"
    using Cons(2) linearize_eval_step_dq[OF ne] by simp
  then show ?case using Cons(1) a1_of_eval_step_dq[OF ne] by simp
qed simp

lemma a1_of_shift_dq: "lft_of (shift_dq args nt d) = lft_of d"
proof (cases d rule: mmuaux_dq_cases)
  case (1 tp tss tables len mL mR result a1_map a2_dq tstp_dq dn)
  obtain q0 q1 where tw: "takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss = (q0, q1)"
    by fastforce
  have le: "length (linearize q0) \<le> length (linearize q1)"
    using takeWhile_queue_rep_fst[of "\<lambda>t. \<not> memR (args_ivl args) (nt - t)" tss]
      takeWhile_queue_rep_snd[of "\<lambda>t. \<not> memR (args_ivl args) (nt - t)" tss]
    unfolding tw by (simp add: length_takeWhile_le)
  have key: "lft_of (foldl (\<lambda>aux _. eval_step_dq args aux)
      (tp, q1, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn) (linearize q0))
    = (mL, a1_map)"
    using a1_of_foldl_eval_step_dq[where xs = "linearize q0"
      and d = "(tp, q1, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"] le by simp
  show ?thesis unfolding 1 shift_dq.simps tw by (simp add: key)
qed

subsection \<open>The one operation that reads the left operand\<close>

text \<open>
  The verified operation looks the stored tuple's masked projection up in @{text a1_map}; the dense
  one looks up its dense projection.  Everything else it does -- the accumulation over the right
  operand's table, the window's tables and timestamps -- is unchanged.
\<close>

definition duntil_elem_step_dq :: "('a tuple, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
    (nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> 'a tuple \<Rightarrow> 'a until_acc_dq \<Rightarrow> 'a until_acc_dq" where
  "duntil_elem_step_dq a1_map msk pos tp len inz P d as acc =
    (let acc' = (if inz then until_step_dq P d (tp - len) (tp, as) acc else acc) in
     case Mapping.lookup a1_map (dproj msk as) of
        None \<Rightarrow> (if \<not>pos then until_step_dq P d (tp - len) (tp - len, as) acc' else acc')
      | Some tp' \<Rightarrow> until_step_dq P d (tp - len) (if pos then (max (tp - len) tp', as)
          else (max (tp - len) (tp' + 1), as)) acc')"

lemma duntil_elem_step_dq_eq:
  "length as = length msk \<Longrightarrow>
     duntil_elem_step_dq a1_map msk pos tp len inz P d as acc
     = until_elem_step_dq (wkeys msk a1_map) msk pos tp len inz P d as acc"
  by (simp add: duntil_elem_step_dq_def until_elem_step_dq_def lookup_wkeys_proj_tuple)

lemma fold_duntil_elem_step_dq:
  "(\<And>as. as \<in> set xs \<Longrightarrow> length as = length msk) \<Longrightarrow>
     fold (duntil_elem_step_dq a1_map msk pos tp len inz P d) xs acc
     = fold (until_elem_step_dq (wkeys msk a1_map) msk pos tp len inz P d) xs acc"
  by (induct xs arbitrary: acc) (simp_all add: duntil_elem_step_dq_eq)

definition dadd_new_dq :: "args \<Rightarrow> bool list \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow>
    event_data mmuaux_dq \<Rightarrow> event_data mmuaux_dq" where
  "dadd_new_dq args msk rel1 rel2 nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) =
       shift_dq args nt aux;
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
     (tp + 1, tss, tables, len + 1, maskL, maskR, result', a1_map, a2_dq, tstp_dq, dn))"

text \<open>
  The dense operation is the verified one against the widened table of the left operand, so the
  node need not widen it.  Only the right operand's table has to be finite, which is all the
  evaluator ever produces.

  Where @{const add_new_dq} guards the fold with @{term \<open>finite rel2\<close>} and falls back on the
  wide structure, this one folds unconditionally: the fold is over
  @{term \<open>csorted_list_of_set rel2\<close>}, which is unspecified for an infinite table, and every
  theorem below assumes the table finite anyway.  A fallback keyed the other way round would have
  to rename the keys of a mapping, which @{const wkeys} and @{const nkeys} do over the whole
  function space and which therefore does not execute.
\<close>

lemma wkeys_a1_update:
  assumes narrow: "\<And>k. k \<in> Mapping.keys m \<Longrightarrow> dnarrow_tuple msk k"
    and r1: "\<And>y. y \<in> rel1 \<Longrightarrow> dnarrow_tuple msk y"
  shows "wkeys msk (Mapping.filter (\<lambda>as _. as \<in> rel1)
       (upd_set m (\<lambda>_. tp) (rel1 - Mapping.keys m)))
     = Mapping.filter (\<lambda>as _. as \<in> dwiden msk ` rel1)
       (upd_set (wkeys msk m) (\<lambda>_. tp) (dwiden msk ` rel1 - Mapping.keys (wkeys msk m)))"
proof -
  have kw: "Mapping.keys (wkeys msk m) = dwiden msk ` Mapping.keys m"
    by (rule keys_wkeys[OF narrow])
  have inj: "\<And>x y. dnarrow_tuple msk x \<Longrightarrow> dnarrow_tuple msk y \<Longrightarrow> dwiden msk x = dwiden msk y \<Longrightarrow> x = y"
    using inj_on_dwiden[of msk] by (auto simp: inj_on_def)
  have d: "dwiden msk ` (rel1 - Mapping.keys m) = dwiden msk ` rel1 - Mapping.keys (wkeys msk m)"
    unfolding kw using narrow r1 by (blast dest: inj)
  have sub: "\<And>y. y \<in> rel1 - Mapping.keys m \<Longrightarrow> dnarrow_tuple msk y" using r1 by auto
  have e1: "wkeys msk (upd_set m (\<lambda>_. tp) (rel1 - Mapping.keys m))
      = upd_set (wkeys msk m) (\<lambda>_. tp) (dwiden msk ` rel1 - Mapping.keys (wkeys msk m))"
    by (simp only: wkeys_upd_set[OF sub] d)
  show ?thesis by (simp only: wkeys_filter[OF r1] e1)
qed

theorem wkeys_uaux_dadd_new_dq:
  assumes fin: "finite rel2"
    and mk: "fst (lft_of aux) = msk"
    and narrow: "\<And>k. k \<in> Mapping.keys (snd (lft_of aux)) \<Longrightarrow> dnarrow_tuple msk k"
    and r1: "\<And>y. y \<in> rel1 \<Longrightarrow> dnarrow_tuple msk y"
    and r2: "\<And>as. as \<in> rel2 \<Longrightarrow> length as = length msk"
  shows "wkeys_uaux msk (dadd_new_dq args msk rel1 rel2 nt aux)
       = add_new_dq args (dwiden msk ` rel1) rel2 nt (wkeys_uaux msk aux)"
proof (cases "shift_dq args nt aux" rule: mmuaux_dq_cases)
  case (1 tp tss tables len maskL maskR result a1_map a2_dq tstp_dq dn)
  have sh: "shift_dq args nt (wkeys_uaux msk aux)
      = (tp, tss, tables, len, maskL, maskR, result, wkeys msk a1_map, a2_dq, tstp_dq, dn)"
    unfolding shift_dq_wkeys 1 by simp
  have lf: "(maskL, a1_map) = lft_of aux"
    using a1_of_shift_dq[of args nt aux] unfolding 1 by simp
  have mm: "maskL = msk" using mk lf by (metis fst_conv)
  have na: "\<And>k. k \<in> Mapping.keys a1_map \<Longrightarrow> dnarrow_tuple msk k"
    using narrow lf by (metis snd_conv)
  have rs: "set (csorted_list_of_set rel2) = rel2" by (rule set_csorted_list_of_set_etuple[OF fin])
  have fl: "fold (duntil_elem_step_dq a1_map msk (args_pos args) tp len (memL (args_ivl args) 0)
        (\<lambda>t. memL (args_ivl args) (nt - dq_nth (dq_push nt tstp_dq) (t - (tp - len))))
        (if memL (args_ivl args) 0 then Inr tp else Inl nt))
      (csorted_list_of_set rel2) ({}, a2_dq, result)
    = fold (until_elem_step_dq (wkeys msk a1_map) msk (args_pos args) tp len
        (memL (args_ivl args) 0)
        (\<lambda>t. memL (args_ivl args) (nt - dq_nth (dq_push nt tstp_dq) (t - (tp - len))))
        (if memL (args_ivl args) 0 then Inr tp else Inl nt))
      (csorted_list_of_set rel2) ({}, a2_dq, result)"
    by (rule fold_duntil_elem_step_dq) (use rs r2 in auto)
  show ?thesis
    unfolding dadd_new_dq_def add_new_dq_def if_P[OF fin] 1 sh mm csl_finite[OF fin]
    by (simp add: Let_def fl wkeys_a1_update[OF na r1] wkeys_upd_set[OF r1] split: prod.splits)
qed

subsection \<open>The dense Until structure's validity\<close>

text \<open>
  A dense state is valid when the verified state it stands for is, the mask it carries is the
  frame's, and every key of the mapping the left operand fills is a tuple of the left operand's
  own width.
\<close>

definition dvalid_muaux :: "args \<Rightarrow> bool list \<Rightarrow> ts \<Rightarrow> event_data mmuaux_dq \<Rightarrow> event_data muaux \<Rightarrow>
    bool" where
  "dvalid_muaux args msk cur daux auxlist \<longleftrightarrow>
     valid_muaux_dq args cur (MU_dq (wkeys_uaux msk daux)) auxlist \<and>
     fst (lft_of daux) = msk \<and> (\<forall>k \<in> Mapping.keys (snd (lft_of daux)). dnarrow_tuple msk k)"

lemma lft_of_init_dq: "lft_of (init_dq args)
    = (join_mask (args_n args) (args_L args), Mapping.empty)"
  by (simp add: init_dq_def)

lemma dvalid_init_muaux:
  assumes LR: "L \<subseteq> R" and ag: "aggargs = None"
    and dm: "dmsk_args (init_args I n L R pos aggargs) msk"
  shows "dvalid_muaux (init_args I n L R pos aggargs) msk 0
     (init_dq (init_args I n L R pos aggargs)) []"
proof -
  have a: "args_agg (init_args I n L R pos aggargs) = None" using ag by (simp add: init_args_def)
  have "valid_muaux_dq (init_args I n L R pos aggargs) 0
      (init_muaux_dq (init_args I n L R pos aggargs)) []"
    by (rule valid_init_muaux_dq[OF LR])
  then show ?thesis
    unfolding dvalid_muaux_def init_muaux_dq_def if_P[OF a]
    by (simp add: wkeys_uaux_init lft_of_init_dq dmsk_args_maskL[OF dm])
qed

lemma fst_lft_of_dadd_new_dq:
  "fst (lft_of (dadd_new_dq args msk rel1 rel2 nt daux)) = fst (lft_of daux)"
proof (cases "shift_dq args nt daux" rule: mmuaux_dq_cases)
  case (1 tp tss tables len maskL maskR result a1_map a2_dq tstp_dq dn)
  have lf: "(maskL, a1_map) = lft_of daux"
    using a1_of_shift_dq[of args nt daux] unfolding 1 by simp
  show ?thesis unfolding dadd_new_dq_def 1
    by (simp add: Let_def lf[symmetric] split: prod.splits)
qed

lemma keys_snd_lft_of_dadd_new_dq:
  "Mapping.keys (snd (lft_of (dadd_new_dq args msk rel1 rel2 nt daux)))
     \<subseteq> Mapping.keys (snd (lft_of daux)) \<union> rel1"
proof (cases "shift_dq args nt daux" rule: mmuaux_dq_cases)
  case (1 tp tss tables len maskL maskR result a1_map a2_dq tstp_dq dn)
  have lf: "(maskL, a1_map) = lft_of daux"
    using a1_of_shift_dq[of args nt daux] unfolding 1 by simp
  show ?thesis unfolding dadd_new_dq_def 1
    by (auto simp: Let_def lf[symmetric] Mapping_upd_set_keys Mapping_keys_filter
        split: prod.splits)
qed

lemma dvalid_add_new_muaux:
  assumes v: "dvalid_muaux args msk cur daux auxlist"
    and fin: "finite rel2"
    and r1: "\<And>y. y \<in> rel1 \<Longrightarrow> dnarrow_tuple msk y"
    and tw: "table (args_n args) (args_L args) (dwiden msk ` rel1)"
    and t2: "table (args_n args) (args_R args) rel2"
    and r2: "\<And>as. as \<in> rel2 \<Longrightarrow> length as = length msk"
    and nt: "nt \<ge> cur"
  shows "dvalid_muaux args msk nt (dadd_new_dq args msk rel1 rel2 nt daux)
     (update_until args (dwiden msk ` rel1) rel2 nt auxlist)"
proof -
  have vm: "valid_muaux_dq args cur (MU_dq (wkeys_uaux msk daux)) auxlist"
    and mk: "fst (lft_of daux) = msk"
    and na: "\<And>k. k \<in> Mapping.keys (snd (lft_of daux)) \<Longrightarrow> dnarrow_tuple msk k"
    using v by (auto simp: dvalid_muaux_def)
  have "valid_muaux_dq args nt
      (add_new_muaux_dq args (dwiden msk ` rel1) rel2 nt (MU_dq (wkeys_uaux msk daux)))
      (update_until args (dwiden msk ` rel1) rel2 nt auxlist)"
    by (rule valid_add_new_muaux_dq[OF vm tw t2 nt])
  then have vv: "valid_muaux_dq args nt
      (MU_dq (wkeys_uaux msk (dadd_new_dq args msk rel1 rel2 nt daux)))
      (update_until args (dwiden msk ` rel1) rel2 nt auxlist)"
    by (simp add: wkeys_uaux_dadd_new_dq[OF fin mk na r1 r2])
  show ?thesis
    unfolding dvalid_muaux_def
    using vv mk na r1 fst_lft_of_dadd_new_dq keys_snd_lft_of_dadd_new_dq by blast
qed

lemma lft_of_eval_dq: "lft_of (snd (eval_dq args nt d)) = lft_of d"
proof (cases "shift_dq args nt d" rule: mmuaux_dq_cases)
  case (1 tp tss tables len maskL maskR result a1_map a2_dq tstp_dq dn)
  have lf: "(maskL, a1_map) = lft_of d"
    using a1_of_shift_dq[of args nt d] unfolding 1 by simp
  show ?thesis unfolding eval_dq.simps 1 by (simp add: lf[symmetric])
qed

lemma dvalid_eval_muaux:
  assumes v: "dvalid_muaux args msk cur daux auxlist" and nt: "nt \<ge> cur"
    and ev: "eval_dq args nt daux = (res, daux')"
    and eu: "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "dvalid_muaux args msk cur daux' auxlist' \<and> res = map (eval_args_agg args) res'"
proof -
  have vm: "valid_muaux_dq args cur (MU_dq (wkeys_uaux msk daux)) auxlist"
    and mk: "fst (lft_of daux) = msk"
    and na: "\<And>k. k \<in> Mapping.keys (snd (lft_of daux)) \<Longrightarrow> dnarrow_tuple msk k"
    using v by (auto simp: dvalid_muaux_def)
  have e0: "eval_dq args nt (wkeys_uaux msk daux) = (res, wkeys_uaux msk daux')"
    using eval_dq_wkeys[where args = args and nt = nt and msk = msk and d = daux] ev
    by (simp del: eval_dq.simps)
  have e: "eval_muaux_dq args nt (MU_dq (wkeys_uaux msk daux))
      = (res, MU_dq (wkeys_uaux msk daux'))"
    by (simp add: e0 del: eval_dq.simps)
  have vv: "valid_muaux_dq args cur (MU_dq (wkeys_uaux msk daux')) auxlist'
      \<and> res = map (eval_args_agg args) res'"
    by (rule valid_eval_muaux_dq[OF vm nt e eu])
  have lf: "lft_of daux' = lft_of daux" using ev lft_of_eval_dq[of args nt daux] by simp
  show ?thesis using vv mk na unfolding dvalid_muaux_def lf by blast
qed

lemma dvalid_length_muaux:
  "dvalid_muaux args msk cur daux auxlist \<Longrightarrow> length_dq args daux = length auxlist"
  using valid_length_muaux_dq[of args cur "MU_dq (wkeys_uaux msk daux)" auxlist]
  by (simp add: dvalid_muaux_def length_dq_wkeys)

section \<open>The dense Until structure at the dense frame\<close>

text \<open>
  The same relation the wide structure has to the narrowed auxiliary list (20.8), now for the
  dense structure.  Only the addition reads differently: it takes the left operand's table at the
  left operand's own frame, so the node need not embed it.
\<close>

definition duaux' :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> event_data mmuaux_dq \<Rightarrow>
    event_data muaux \<Rightarrow> bool" where
  "duaux' n cs_R cs_L args cur daux auxlist \<longleftrightarrow>
     (\<forall>(t, a1, a2) \<in> set auxlist. table n (set cs_L) a1 \<and> table n (set cs_R) a2) \<and>
     dvalid_muaux (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux (dauxlist3 n cs_R auxlist)"

lemma duaux'_init:
  assumes s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and sub: "set cs_L \<subseteq> set cs_R"
  shows "duaux' n cs_R cs_L args 0 (init_dq (dargs cs_R cs_L args)) []"
proof -
  have LR: "cpos cs_R (set cs_L) \<subseteq> {0..<length cs_R}" by (auto simp: cpos_def)
  have dm: "dmsk_args (dargs cs_R cs_L args) (dmsk cs_R cs_L)"
    unfolding dmsk_def by (rule dmsk_args_dargs[OF s_R s_L sub])
  have "dvalid_muaux (init_args (args_ivl args) (length cs_R) (cpos cs_R (set cs_L))
      {0..<length cs_R} (args_pos args) None) (dmsk cs_R cs_L) 0
      (init_dq (init_args (args_ivl args) (length cs_R) (cpos cs_R (set cs_L))
        {0..<length cs_R} (args_pos args) None)) []"
    by (rule dvalid_init_muaux[OF LR refl]) (use dm in \<open>simp add: dargs_def\<close>)
  then show ?thesis by (simp add: duaux'_def dargs_def dauxlist3_def)
qed

lemma duaux'_add_new:
  assumes v: "duaux' n cs_R cs_L args cur daux auxlist"
    and s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and b_R: "\<forall>c \<in> set cs_R. c < n" and sub: "set cs_L \<subseteq> set cs_R"
    and t1: "table n (set cs_L) rel1" and t2: "table n (set cs_R) rel2"
    and f2: "finite rel2" and nt: "cur \<le> nt"
  shows "duaux' n cs_R cs_L args nt
      (dadd_new_dq (dargs cs_R cs_L args) (dmsk cs_R cs_L)
        (dtabc n cs_L rel1) (dtabc n cs_R rel2) nt daux)
      (update_until args rel1 rel2 nt auxlist)"
proof -
  have w: "\<forall>(t, a1, a2) \<in> set auxlist. table n (set cs_L) a1 \<and> table n (set cs_R) a2"
    and d: "dvalid_muaux (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux
      (dauxlist3 n cs_R auxlist)"
    using v by (auto simp: duaux'_def)
  have b_L: "\<forall>c \<in> set cs_L. c < n" using sub b_R by auto
  have fin: "finite (dtabc n cs_R rel2)" using f2 by (simp add: dtabc_def)
  have lf: "length (filter id (dmsk cs_R cs_L)) = length cs_L"
    unfolding dmsk_def by (rule length_filter_mrg_left_key[OF s_R s_L sub])
  have lm: "length (dmsk cs_R cs_L) = length cs_R"
    unfolding dmsk_def by (rule length_mrg_left_key[OF s_R s_L sub])
  have r1: "\<And>y. y \<in> dtabc n cs_L rel1 \<Longrightarrow> dnarrow_tuple (dmsk cs_R cs_L) y"
    unfolding lf using dwf_tuple_dtabc[OF s_L b_L t1] by (simp add: dwf_tuple_def)
  have r2: "\<And>as. as \<in> dtabc n cs_R rel2 \<Longrightarrow> length as = length (dmsk cs_R cs_L)"
    unfolding lm using dwf_tuple_dtabc[OF s_R b_R t2] by (simp add: dwf_tuple_def)
  have wi: "dwiden (dmsk cs_R cs_L) ` dtabc n cs_L rel1 = dtabc n cs_R rel1"
    unfolding dmsk_def by (rule dwiden_image_dtabc[OF s_R s_L sub b_R t1])
  have tt1: "table (args_n (dargs cs_R cs_L args)) (args_L (dargs cs_R cs_L args))
      (dwiden (dmsk cs_R cs_L) ` dtabc n cs_L rel1)"
    unfolding wi by (simp add: table_dtabc_cpos[OF s_R b_R sub t1])
  have tt2: "table (args_n (dargs cs_R cs_L args)) (args_R (dargs cs_R cs_L args))
      (dtabc n cs_R rel2)"
    using table_dtabc_cpos[OF s_R b_R subset_refl t2] by (simp add: cpos_all)
  have "dvalid_muaux (dargs cs_R cs_L args) (dmsk cs_R cs_L) nt
      (dadd_new_dq (dargs cs_R cs_L args) (dmsk cs_R cs_L)
        (dtabc n cs_L rel1) (dtabc n cs_R rel2) nt daux)
      (update_until (dargs cs_R cs_L args) (dtabc n cs_R rel1) (dtabc n cs_R rel2) nt
        (dauxlist3 n cs_R auxlist))"
    unfolding wi[symmetric]
    by (rule dvalid_add_new_muaux[OF d fin r1 tt1 tt2 r2 nt])
  then show ?thesis using dauxlist3_wf_update_until[OF w sub t1 t2]
    by (simp add: duaux'_def dauxlist3_update_until[OF s_R b_R sub w t1 t2, symmetric])
qed

lemma duaux'_eval:
  assumes v: "duaux' n cs_R cs_L args cur daux auxlist" and nt: "cur \<le> nt"
    and de: "eval_dq (dargs cs_R cs_L args) nt daux = (dres, daux')"
    and we: "eval_until (args_ivl args) nt auxlist = (res, auxlist')"
  shows "dres = map (dtabc n cs_R) res \<and> duaux' n cs_R cs_L args cur daux' auxlist'"
proof -
  have w: "\<forall>(t, a1, a2) \<in> set auxlist. table n (set cs_L) a1 \<and> table n (set cs_R) a2"
    and d: "dvalid_muaux (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux
      (dauxlist3 n cs_R auxlist)"
    using v by (auto simp: duaux'_def)
  have de': "eval_until (args_ivl (dargs cs_R cs_L args)) nt (dauxlist3 n cs_R auxlist)
      = (map (dtabc n cs_R) res, dauxlist3 n cs_R auxlist')"
    using dauxlist3_eval_until[OF we] by simp
  have vd: "dvalid_muaux (dargs cs_R cs_L args) (dmsk cs_R cs_L) cur daux'
      (dauxlist3 n cs_R auxlist')"
    and r: "dres = map (eval_args_agg (dargs cs_R cs_L args)) (map (dtabc n cs_R) res)"
    using dvalid_eval_muaux[OF d nt de de'] by simp_all
  have "set auxlist' \<subseteq> set auxlist"
    using eval_until_auxlist'[OF we] by (simp add: set_drop_subset)
  then show ?thesis using vd r w by (auto simp: duaux'_def)
qed

lemma duaux'_length:
  "duaux' n cs_R cs_L args cur daux auxlist \<Longrightarrow>
     length_dq (dargs cs_R cs_L args) daux = length auxlist"
  using dvalid_length_muaux by (fastforce simp: duaux'_def dauxlist3_def)

section \<open>The match structures at the dense frame\<close>

text \<open>
  The regular-expression nodes need no dense operations of their own.  Every table a match node
  handles -- the operands', the derivatives', the structures' -- lives at the node's own columns,
  and narrowing turns the kernel's operations at the wide frame into the very same operations at
  the node's width: the joins are @{thm [source] dtabc_join_frame}, the unions are
  @{thm [source] dtabc_Un_img}, and the unit table narrows to the unit table of the node's width,
  which is what the section below shows first.  Only the operands arrive narrowed at their own
  column lists, so the node embeds them once per firing, by @{thm [source] dembedp_dtabc}, exactly
  as the trigger node embeds its left operand.

  The one thing that does not come for free is that the guards really are tables over the node's
  columns: that is the regular expression's safety condition, and the lemmas below carry it.
\<close>

text \<open>Narrowing the wide unit table -- the tuple that is blank everywhere -- gives the short
  tuple that is blank everywhere, which is the unit table of the node's own width.\<close>

lemma dtabc_empty_table[simp]: "dtabc n cs empty_table = empty_table"
  by (simp add: dtabc_def empty_table_def)

lemma dtabc_eq_empty_table[simp]: "dtabc n cs T = empty_table \<longleftrightarrow> T = empty_table"
  by (simp add: dtabc_def empty_table_def)

lemma dproj_replicate: "dproj bs (replicate (length bs) z) = replicate (length (filter id bs)) z"
  by (induct bs) auto

lemma dtabc_unit_table_len:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
  shows "dtabc n cs (unit_table n) = unit_table (length cs)"
  using dproj_replicate[of "wide_mask n cs" None]
  by (simp add: dtabc_def unit_table_def length_filter_wide_mask[OF s b])

subsection \<open>The lax epsilon\<close>

text \<open>The lax epsilon's result lives at the node's own columns: the guard does, and every step
  either joins an atom's table onto it, unions two such or intersects them.\<close>

lemma table_eps_lax:
  assumes ops: "\<forall>i < length \<phi>s. \<exists>B \<subseteq> A. table n B (\<phi>s ! i)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> table n A guard \<Longrightarrow> table n A (\<epsilon>_lax guard \<phi>s mr)"
proof (induct mr arbitrary: guard)
  case (MSkip m)
  then show ?case by (simp add: table_def empty_table_def)
next
  case (MTestPos i)
  then obtain B where "B \<subseteq> A" "table n B (\<phi>s ! i)" using ops by auto
  then show ?case using MTestPos(2) by (auto intro!: join_table[where C = A])
next
  case (MTestNeg i)
  then obtain B where "B \<subseteq> A" "table n B (\<phi>s ! i)" using ops by auto
  then show ?case using MTestNeg(2) by (auto intro!: join_table[where C = A])
next
  case (MPlus r t)
  have "table n A (\<epsilon>_lax guard \<phi>s r)" and "table n A (\<epsilon>_lax guard \<phi>s t)"
    using MPlus(1,2)[OF _ MPlus(4)] MPlus(3) by simp_all
  then show ?case by (simp add: table_Un)
next
  case (MTimes r t)
  then show ?case by (auto intro!: join_table[where C = A])
next
  case (MStar r)
  then show ?case by simp
qed

text \<open>Narrowing turns the wide lax epsilon into the lax epsilon at the node's width, over the
  narrowed operands.  Each join is @{thm [source] dtabc_join_frame} -- the guard's columns are
  the node's, an atom's are among them -- and each union is @{thm [source] dtabc_Un_img}.\<close>

lemma dtabc_eps_lax:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and css: "\<And>i. i < length \<phi>s \<Longrightarrow> \<exists>B \<subseteq> set cs. table n B (\<phi>s ! i)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> table n (set cs) guard \<Longrightarrow>
     dtabc n cs (\<epsilon>_lax guard \<phi>s mr)
       = \<epsilon>_lax (dtabc n cs guard) (map (dtabc n cs) \<phi>s) mr"
proof (induct mr arbitrary: guard)
  case (MSkip m)
  then show ?case by (simp add: dtabc_def empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length \<phi>s" by simp
  then obtain B where B: "B \<subseteq> set cs" "table n B (\<phi>s ! i)" using css by blast
  show ?case using i
    by (simp add: dtabc_join_frame[OF s b B(1) subset_refl MTestPos(2) B(2)])
next
  case (MTestNeg i)
  then have i: "i < length \<phi>s" by simp
  then obtain B where B: "B \<subseteq> set cs" "table n B (\<phi>s ! i)" using css by blast
  show ?case using i
    by (simp add: dtabc_join_frame[OF s b B(1) subset_refl MTestNeg(2) B(2)])
next
  case (MPlus r t)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have opsA: "\<forall>i < length \<phi>s. \<exists>B \<subseteq> set cs. table n B (\<phi>s ! i)" using css by auto
  have t1: "table n (set cs) (\<epsilon>_lax guard \<phi>s r)"
    by (rule table_eps_lax[OF opsA o1 MTimes(4)])
  have t2: "table n (set cs) (\<epsilon>_lax guard \<phi>s t)"
    by (rule table_eps_lax[OF opsA o2 MTimes(4)])
  show ?case using MTimes(1)[OF o1 MTimes(4)] MTimes(2)[OF o2 MTimes(4)]
    by (simp add: dtabc_join_frame[OF s b subset_refl subset_refl t1 t2])
qed simp

lemma table_dtabc_eps_lax:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and css: "\<And>i. i < length \<phi>s \<Longrightarrow> \<exists>B \<subseteq> set cs. table n B (\<phi>s ! i)"
    and ok: "ok (length \<phi>s) mr" and g: "table n (set cs) guard"
  shows "table n (set cs) (\<epsilon>_lax guard \<phi>s mr)"
  using css by (intro table_eps_lax[OF _ ok g]) auto
subsection \<open>The strict epsilons\<close>

text \<open>
  Unlike the lax one, a strict epsilon does not carry a guard, and its value is a table over the
  node's columns only because the regular expression is safe: an empty skip and a star return the
  tuple that stands for every valuation, which is a table over the node's columns only when there
  are none, and safety is what rules the other case out.  The kernel's own correctness proof
  establishes exactly that, so the lemma below reads it off @{thm [source] qtable_r\<epsilon>_strict} at the
  empty restriction.
\<close>

lemma qtable_mem_restr_empty: "qtable n A (mem_restr {}) Q X \<longleftrightarrow> table n A X"
  by (auto simp: qtable_def mem_restr_def)

lemma table_reps_strict:
  fixes \<psi>s :: "ty Formula.formula list" and rels :: "event_data table list"
  assumes sr: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<psi>s)"
    and ok: "ok (length \<psi>s) mr" and A: "A = fv_regex (from_mregex mr \<psi>s)"
    and ops: "list_all2 (\<lambda>\<psi> rel. table n (Formula.fv \<psi>) rel) \<psi>s rels"
  shows "table n A (r\<epsilon>_strict n rels mr)"
proof -
  have q: "list_all2 (\<lambda>\<psi> rel. qtable n (Formula.fv \<psi>) (mem_restr {})
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) rel) \<psi>s rels"
    using ops by (simp add: list_all2_conv_all_nth qtable_mem_restr_empty)
  have "qtable n A (mem_restr {})
      (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (map the v)) i (from_mregex mr \<psi>s)) (r\<epsilon>_strict n rels mr)"
    by (rule qtable_r\<epsilon>_strict[OF sr ok A q])
  then show ?thesis by (simp add: qtable_mem_restr_empty)
qed

lemma table_leps_strict:
  fixes \<psi>s :: "ty Formula.formula list" and rels :: "event_data table list"
  assumes sr: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<psi>s)"
    and ok: "ok (length \<psi>s) mr" and A: "A = fv_regex (from_mregex mr \<psi>s)"
    and ops: "list_all2 (\<lambda>\<psi> rel. table n (Formula.fv \<psi>) rel) \<psi>s rels"
  shows "table n A (l\<epsilon>_strict n rels mr)"
proof -
  have q: "list_all2 (\<lambda>\<psi> rel. qtable n (Formula.fv \<psi>) (mem_restr {})
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) rel) \<psi>s rels"
    using ops by (simp add: list_all2_conv_all_nth qtable_mem_restr_empty)
  have "qtable n A (mem_restr {})
      (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (map the v)) i (from_mregex mr \<psi>s)) (l\<epsilon>_strict n rels mr)"
    by (rule qtable_l\<epsilon>_strict[OF sr ok A q])
  then show ?thesis by (simp add: qtable_mem_restr_empty)
qed

text \<open>With that in hand the two strict epsilons narrow like everything else, by induction on the
  safety of the regular expression.\<close>

lemma dtabc_reps_strict:
  fixes \<psi>s :: "ty Formula.formula list" and rels :: "event_data table list"
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and ops: "list_all2 (\<lambda>\<psi> rel. table n (Formula.fv \<psi>) rel) \<psi>s rels"
    and sub: "\<And>i. i < length \<psi>s \<Longrightarrow> Formula.fv (\<psi>s ! i) \<subseteq> set cs"
  shows "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set cs = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     dtabc n cs (r\<epsilon>_strict n rels mr) = r\<epsilon>_strict (length cs) (map (dtabc n cs) rels) mr"
proof (induct mr)
  case (MSkip m)
  then show ?case by (simp add: dtabc_unit_table_len[OF s b] dtabc_unit_table)
next
  case (MTestPos i)
  then have i: "i < length rels" using ops by (simp add: list_all2_lengthD)
  then show ?case by simp
next
  case (MTestNeg i)
  then have i: "i < length rels" using ops by (simp add: list_all2_lengthD)
  then show ?case
    by (simp add: dtabc_unit_table_len[OF s b] dtabc_empty_iff)
next
  case (MPlus r t)
  have fvr: "set cs = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set cs = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case
    using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4)
    by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have lr: "length \<psi>s = length rels" using ops by (simp add: list_all2_lengthD)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr1: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex r \<psi>s)"
    using MTimes(3) by simp
  have fvr: "set cs = fv_regex (from_mregex r \<psi>s)" using MTimes(3,5) by auto
  have tg: "table n (set cs) (r\<epsilon>_strict n rels r)"
    by (rule table_reps_strict[OF sr1 o1 fvr ops])
  have opsB: "\<And>i. i < length rels \<Longrightarrow> \<exists>B \<subseteq> set cs. table n B (rels ! i)"
    using ops sub lr by (auto simp: list_all2_conv_all_nth)
  show ?case
    using MTimes(1)[OF sr1 o1 fvr]
    by (simp add: dtabc_eps_lax[OF s b opsB o2[unfolded lr] tg])
next
  case (MStar r)
  then show ?case by (simp add: dtabc_unit_table_len[OF s b] dtabc_unit_table)
qed

lemma dtabc_leps_strict:
  fixes \<psi>s :: "ty Formula.formula list" and rels :: "event_data table list"
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and ops: "list_all2 (\<lambda>\<psi> rel. table n (Formula.fv \<psi>) rel) \<psi>s rels"
    and sub: "\<And>i. i < length \<psi>s \<Longrightarrow> Formula.fv (\<psi>s ! i) \<subseteq> set cs"
  shows "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set cs = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     dtabc n cs (l\<epsilon>_strict n rels mr) = l\<epsilon>_strict (length cs) (map (dtabc n cs) rels) mr"
proof (induct mr)
  case (MSkip m)
  then show ?case by (simp add: dtabc_unit_table_len[OF s b] dtabc_unit_table)
next
  case (MTestPos i)
  then have i: "i < length rels" using ops by (simp add: list_all2_lengthD)
  then show ?case by simp
next
  case (MTestNeg i)
  then have i: "i < length rels" using ops by (simp add: list_all2_lengthD)
  then show ?case by (simp add: dtabc_unit_table_len[OF s b])
next
  case (MPlus r t)
  have fvr: "set cs = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set cs = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case
    using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4)
    by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have lr: "length \<psi>s = length rels" using ops by (simp add: list_all2_lengthD)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr2: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex t \<psi>s)"
    using MTimes(3) by simp
  have fvt: "set cs = fv_regex (from_mregex t \<psi>s)" using MTimes(3,5) by auto
  have tg: "table n (set cs) (l\<epsilon>_strict n rels t)"
    by (rule table_leps_strict[OF sr2 o2 fvt ops])
  have opsB: "\<And>i. i < length rels \<Longrightarrow> \<exists>B \<subseteq> set cs. table n B (rels ! i)"
    using ops sub lr by (auto simp: list_all2_conv_all_nth)
  show ?case
    using MTimes(2)[OF sr2 o2 fvt]
    by (simp add: dtabc_eps_lax[OF s b opsB o1[unfolded lr] tg])
next
  case (MStar r)
  then show ?case by (simp add: dtabc_unit_table_len[OF s b] dtabc_unit_table)
qed

subsection \<open>The derivatives\<close>

text \<open>
  The two derivatives read the previous firing's tabulation, which the node keeps narrowed, and
  join what they find against the atoms through the lax epsilon.  Narrowing a tabulation is
  narrowing every entry, so the lookups agree; the rest is the lax epsilon again.  The guard the
  lax epsilon sees here is a derivative's value, which is a table over the node's columns because
  the tabulation's entries are.
\<close>

lemma table_rdelta:
  assumes ops: "\<forall>i < length \<phi>s. \<exists>B \<subseteq> A. table n B (\<phi>s ! i)"
    and X: "\<And>ms. table n A (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> table n A (r\<delta> \<kappa> X \<phi>s mr)"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using X by (cases m) (auto simp: table_def empty_table_def)
next
  case (MPlus r t)
  then show ?case by (simp add: table_Un)
next
  case (MTimes r t)
  have o: "ok (length \<phi>s) r" "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have u: "table n A (r\<delta> (\<lambda>u. \<kappa> (MTimes r u)) X \<phi>s t)" and g: "table n A (r\<delta> \<kappa> X \<phi>s r)"
    using MTimes(1,2) o by simp_all
  show ?case using u by (simp add: table_Un table_eps_lax[OF ops o(2) g])
qed (auto simp: table_def empty_table_def)

lemma table_ldelta:
  assumes ops: "\<forall>i < length \<phi>s. \<exists>B \<subseteq> A. table n B (\<phi>s ! i)"
    and X: "\<And>ms. table n A (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> table n A (l\<delta> \<kappa> X \<phi>s mr)"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using X by (cases m) (auto simp: table_def empty_table_def)
next
  case (MPlus r t)
  then show ?case by (simp add: table_Un)
next
  case (MTimes r t)
  have o: "ok (length \<phi>s) r" "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have u: "table n A (l\<delta> (\<lambda>u. \<kappa> (MTimes u t)) X \<phi>s r)" and g: "table n A (l\<delta> \<kappa> X \<phi>s t)"
    using MTimes(1,2) o by simp_all
  show ?case using u by (simp add: table_Un table_eps_lax[OF ops o(1) g])
qed (auto simp: table_def empty_table_def)

lemma dtabc_rdelta:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and css: "\<And>i. i < length \<phi>s \<Longrightarrow> \<exists>B \<subseteq> set cs. table n B (\<phi>s ! i)"
    and X: "\<And>ms. table n (set cs) (lookup X ms)"
    and dX: "\<And>ms. lookup dX ms = dtabc n cs (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow>
     dtabc n cs (r\<delta> \<kappa> X \<phi>s mr) = r\<delta> \<kappa> dX (map (dtabc n cs) \<phi>s) mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using dX by (cases m) simp_all
next
  case (MPlus r t)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have opsA: "\<forall>i < length \<phi>s. \<exists>B \<subseteq> set cs. table n B (\<phi>s ! i)" using css by auto
  have tg: "table n (set cs) (r\<delta> \<kappa> X \<phi>s r)" by (rule table_rdelta[OF opsA X o1])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2]
    by (simp add: dtabc_Un_img dtabc_eps_lax[OF s b css o2 tg])
qed simp_all

lemma dtabc_ldelta:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and css: "\<And>i. i < length \<phi>s \<Longrightarrow> \<exists>B \<subseteq> set cs. table n B (\<phi>s ! i)"
    and X: "\<And>ms. table n (set cs) (lookup X ms)"
    and dX: "\<And>ms. lookup dX ms = dtabc n cs (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow>
     dtabc n cs (l\<delta> \<kappa> X \<phi>s mr) = l\<delta> \<kappa> dX (map (dtabc n cs) \<phi>s) mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using dX by (cases m) simp_all
next
  case (MPlus r t)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have opsA: "\<forall>i < length \<phi>s. \<exists>B \<subseteq> set cs. table n B (\<phi>s ! i)" using css by auto
  have tg: "table n (set cs) (l\<delta> \<kappa> X \<phi>s t)" by (rule table_ldelta[OF opsA X o2])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2]
    by (simp add: dtabc_Un_img dtabc_eps_lax[OF s b css o1 tg])
qed simp_all

subsection \<open>The two structures\<close>

text \<open>
  A past-match structure is a list of tabulations indexed by a time stamp; the dense one is the
  same list with every entry narrowed.  Since a tabulation is only ever read through
  @{const lookup}, the relation below says just that, and adds the invariant the derivatives
  need: every entry is a table over the node's columns.
\<close>

definition dmrd_rel :: "nat \<Rightarrow> cols \<Rightarrow> event_data mr\<delta>aux \<Rightarrow> event_data mr\<delta>aux \<Rightarrow> bool" where
  "dmrd_rel n cs = list_all2 (\<lambda>(t, X) (t', X'). t = t' \<and>
     (\<forall>ms. table n (set cs) (lookup X ms)) \<and> (\<forall>ms. lookup X' ms = dtabc n cs (lookup X ms)))"

lemma dmrd_rel_Nil[simp]: "dmrd_rel n cs [] []"
  by (simp add: dmrd_rel_def)

lemma dmrd_rel_Cons[simp]:
  "dmrd_rel n cs ((t, X) # aux) ((t', X') # daux) \<longleftrightarrow> t = t' \<and>
     (\<forall>ms. table n (set cs) (lookup X ms)) \<and> (\<forall>ms. lookup X' ms = dtabc n cs (lookup X ms)) \<and>
     dmrd_rel n cs aux daux"
  by (simp add: dmrd_rel_def)

lemma dmrd_rel_length: "dmrd_rel n cs aux daux \<Longrightarrow> length aux = length daux"
  by (simp add: dmrd_rel_def list_all2_lengthD)

lemma dmrd_rel_induct[consumes 1, case_names Nil Cons]:
  assumes "dmrd_rel n cs aux daux"
    and "P [] []"
    and "\<And>t X X' aux daux. (\<forall>ms. table n (set cs) (lookup X ms)) \<Longrightarrow>
       (\<forall>ms. lookup X' ms = dtabc n cs (lookup X ms)) \<Longrightarrow> dmrd_rel n cs aux daux \<Longrightarrow>
       P aux daux \<Longrightarrow> P ((t, X) # aux) ((t, X') # daux)"
  shows "P aux daux"
  using assms(1)[unfolded dmrd_rel_def]
  by (induct rule: list_all2_induct) (use assms(2,3) in \<open>auto simp: dmrd_rel_def\<close>)text \<open>Narrowing a tabulation entry by entry is narrowing what it tabulates.\<close>

lemma lookup_mrtabulate_cong:
  assumes d: "distinct mrs" and f: "\<And>ms. ms \<in> set mrs \<Longrightarrow> dtabc n cs (f ms) = g ms"
  shows "lookup (mrtabulate mrs g) ms = dtabc n cs (lookup (mrtabulate mrs f) ms)"
  using f by (simp add: lookup_tabulate[OF d])

text \<open>Reading a structure is a union of lookups, which narrowing distributes over.\<close>

lemma dtabc_foldr_lookup:
  assumes "dmrd_rel n cs aux daux"
  shows "dtabc n cs (foldr (\<union>) [lookup rel ms. (t, rel) \<leftarrow> aux, P t] {})
       = foldr (\<union>) [lookup rel ms. (t, rel) \<leftarrow> daux, P t] {}"
  using assms by (induct rule: dmrd_rel_induct) (auto simp: dtabc_Un_img dtabc_def)

text \<open>
  One firing of the past-match structure.  The entries the window keeps are stepped by the right
  derivative and, at the current time stamp, joined with the strict epsilon; both narrow, so the
  stepped structures stay related and the reported table is the narrowing of the kernel's.
\<close>

locale dmatchP_frame =
  fixes n :: nat and cs :: cols and \<psi>s :: "ty Formula.formula list"
    and rels :: "event_data table list" and mrs :: "mregex list"
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and ops: "list_all2 (\<lambda>\<psi> rel. table n (Formula.fv \<psi>) rel) \<psi>s rels"
    and sub: "\<And>i. i < length \<psi>s \<Longrightarrow> Formula.fv (\<psi>s ! i) \<subseteq> set cs"
    and d: "distinct mrs"
    and mrsok: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
       Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex ms \<psi>s) \<and> ok (length \<psi>s) ms \<and>
       set cs = fv_regex (from_mregex ms \<psi>s)"
begin

lemma lr: "length \<psi>s = length rels"
  using ops by (simp add: list_all2_lengthD)

lemma opsB: "\<And>i. i < length rels \<Longrightarrow> \<exists>B \<subseteq> set cs. table n B (rels ! i)"
  using ops sub lr by (auto simp: list_all2_conv_all_nth)

lemma tabT: "ms \<in> set mrs \<Longrightarrow> table n (set cs) (r\<epsilon>_strict n rels ms)"
  using mrsok by (intro table_reps_strict[OF _ _ _ ops]) auto

lemma dtabT: "ms \<in> set mrs \<Longrightarrow>
    dtabc n cs (r\<epsilon>_strict n rels ms) = r\<epsilon>_strict (length cs) (map (dtabc n cs) rels) ms"
  using mrsok by (intro dtabc_reps_strict[OF s b ops sub]) auto

lemma table_lookup_head: "table n (set cs) (lookup (mrtabulate mrs (r\<epsilon>_strict n rels)) ms)"
  using tabT by (simp add: lookup_tabulate[OF d])

lemma dtabc_lookup_head:
  "lookup (mrtabulate mrs (r\<epsilon>_strict (length cs) (map (dtabc n cs) rels))) ms
     = dtabc n cs (lookup (mrtabulate mrs (r\<epsilon>_strict n rels)) ms)"
  by (rule lookup_mrtabulate_cong[OF d dtabT])

lemma dmrd_rel_head:
  "dmrd_rel n cs [(nt, mrtabulate mrs (r\<epsilon>_strict n rels))]
     [(nt, mrtabulate mrs (r\<epsilon>_strict (length cs) (map (dtabc n cs) rels)))]"
  using table_lookup_head dtabc_lookup_head by simp

lemma dmrd_rel_step:
  assumes rel: "dmrd_rel n cs aux daux"
  shows "dmrd_rel n cs
     [(t, mrtabulate mrs (\<lambda>ms. r\<delta> id X rels ms \<union> (if t = nt then r\<epsilon>_strict n rels ms else {}))).
        (t, X) \<leftarrow> aux, memR I (nt - t)]
     [(t, mrtabulate mrs (\<lambda>ms. r\<delta> id X (map (dtabc n cs) rels) ms
          \<union> (if t = nt then r\<epsilon>_strict (length cs) (map (dtabc n cs) rels) ms else {}))).
        (t, X) \<leftarrow> daux, memR I (nt - t)]"
  using rel
proof (induct rule: dmrd_rel_induct)
  case (Cons t X X' aux daux)
  have okms: "\<And>ms. ms \<in> set mrs \<Longrightarrow> ok (length rels) ms" using mrsok lr by auto
  have tD: "\<And>ms. ms \<in> set mrs \<Longrightarrow> table n (set cs) (r\<delta> id X rels ms)"
    using Cons(1) by (intro table_rdelta[OF _ _ okms]) (use opsB in auto)
  have tE: "\<And>ms. table n (set cs)
      (lookup (mrtabulate mrs (\<lambda>ms. r\<delta> id X rels ms
         \<union> (if t = nt then r\<epsilon>_strict n rels ms else {}))) ms)"
    using tD tabT by (auto simp: lookup_tabulate[OF d] table_Un)
  have tX: "\<And>ms. table n (set cs) (lookup X ms)" using Cons(1) by blast
  have dXe: "\<And>ms. lookup X' ms = dtabc n cs (lookup X ms)" using Cons(2) by blast
  have dR: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
      dtabc n cs (r\<delta> id X rels ms) = r\<delta> id X' (map (dtabc n cs) rels) ms"
    by (rule dtabc_rdelta[OF s b opsB tX dXe okms])
  have dD: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
      dtabc n cs (r\<delta> id X rels ms \<union> (if t = nt then r\<epsilon>_strict n rels ms else {}))
        = r\<delta> id X' (map (dtabc n cs) rels) ms
          \<union> (if t = nt then r\<epsilon>_strict (length cs) (map (dtabc n cs) rels) ms else {})"
    by (simp add: dtabc_Un_img dR dtabT)
  have dE: "\<And>ms. lookup (mrtabulate mrs (\<lambda>ms. r\<delta> id X' (map (dtabc n cs) rels) ms
         \<union> (if t = nt then r\<epsilon>_strict (length cs) (map (dtabc n cs) rels) ms else {}))) ms
      = dtabc n cs (lookup (mrtabulate mrs (\<lambda>ms. r\<delta> id X rels ms
         \<union> (if t = nt then r\<epsilon>_strict n rels ms else {}))) ms)"
    by (rule lookup_mrtabulate_cong[OF d dD])
  show ?case using Cons(4) tE dE by simp
qed simp

lemma dtabc_update_matchP:
  assumes rel: "dmrd_rel n cs aux daux"
  shows "dtabc n cs (fst (update_matchP n I mr mrs rels nt aux))
       = fst (update_matchP (length cs) I mr mrs (map (dtabc n cs) rels) nt daux) \<and>
     dmrd_rel n cs (snd (update_matchP n I mr mrs rels nt aux))
       (snd (update_matchP (length cs) I mr mrs (map (dtabc n cs) rels) nt daux))"
proof -
  let ?W = "[(t, mrtabulate mrs (\<lambda>ms. r\<delta> id X rels ms
       \<union> (if t = nt then r\<epsilon>_strict n rels ms else {}))). (t, X) \<leftarrow> aux, memR I (nt - t)]"
  let ?D = "[(t, mrtabulate mrs (\<lambda>ms. r\<delta> id X (map (dtabc n cs) rels) ms
       \<union> (if t = nt then r\<epsilon>_strict (length cs) (map (dtabc n cs) rels) ms else {}))).
         (t, X) \<leftarrow> daux, memR I (nt - t)]"
  have st: "dmrd_rel n cs ?W ?D" by (rule dmrd_rel_step[OF rel])
  have both: "dmrd_rel n cs
      (case ?W of [] \<Rightarrow> [(nt, mrtabulate mrs (r\<epsilon>_strict n rels))]
       | x # w' \<Rightarrow> (if fst x = nt then x # w'
                   else (nt, mrtabulate mrs (r\<epsilon>_strict n rels)) # x # w'))
      (case ?D of [] \<Rightarrow> [(nt, mrtabulate mrs (r\<epsilon>_strict (length cs) (map (dtabc n cs) rels)))]
       | x # w' \<Rightarrow> (if fst x = nt then x # w'
                   else (nt, mrtabulate mrs (r\<epsilon>_strict (length cs) (map (dtabc n cs) rels)))
                        # x # w'))"
  proof (cases ?W)
    case Nil
    have DN: "?D = []" using dmrd_rel_length[OF st] unfolding Nil by simp
    show ?thesis unfolding Nil DN using dmrd_rel_head by simp
  next
    case (Cons x w')
    have "length ?D = Suc (length w')" using dmrd_rel_length[OF st] unfolding Cons by simp
    then obtain y d' where D: "?D = y # d'" by (cases ?D) auto
    have rel': "dmrd_rel n cs (x # w') (y # d')" using st unfolding Cons D .
    show ?thesis unfolding Cons D
      using rel' table_lookup_head dtabc_lookup_head
      by (cases x; cases y) (auto simp: dmrd_rel_Cons)
  qed
  show ?thesis
    using both dtabc_foldr_lookup[OF both]
    by (simp add: update_matchP_def Let_def)
qed

end

subsection \<open>The future-match structure\<close>

text \<open>
  A future-match structure keeps, per time stamp, the operands' tables at that time point and the
  result accumulated for it so far.  The dense one keeps the same list with both narrowed.
\<close>

definition dmld_rel :: "nat \<Rightarrow> cols \<Rightarrow> ty Formula.formula list \<Rightarrow>
    event_data ml\<delta>aux \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> bool" where
  "dmld_rel n cs \<psi>s = list_all2 (\<lambda>(t, rls, rel) (t', drls, drel). t = t' \<and>
     list_all2 (\<lambda>\<psi> r. table n (Formula.fv \<psi>) r) \<psi>s rls \<and>
     drls = map (dtabc n cs) rls \<and> drel = dtabc n cs rel)"

lemma dmld_rel_Nil[simp]: "dmld_rel n cs \<psi>s [] []"
  by (simp add: dmld_rel_def)

lemma dmld_rel_Cons[simp]:
  "dmld_rel n cs \<psi>s ((t, rls, rel) # aux) ((t', drls, drel) # daux) \<longleftrightarrow> t = t' \<and>
     list_all2 (\<lambda>\<psi> r. table n (Formula.fv \<psi>) r) \<psi>s rls \<and>
     drls = map (dtabc n cs) rls \<and> drel = dtabc n cs rel \<and> dmld_rel n cs \<psi>s aux daux"
  by (simp add: dmld_rel_def)

lemma dmld_rel_induct[consumes 1, case_names Nil Cons]:
  assumes "dmld_rel n cs \<psi>s aux daux"
    and "P [] []"
    and "\<And>t rls rel aux daux. list_all2 (\<lambda>\<psi> r. table n (Formula.fv \<psi>) r) \<psi>s rls \<Longrightarrow>
       dmld_rel n cs \<psi>s aux daux \<Longrightarrow> P aux daux \<Longrightarrow>
       P ((t, rls, rel) # aux) ((t, map (dtabc n cs) rls, dtabc n cs rel) # daux)"
  shows "P aux daux"
  using assms(1)[unfolded dmld_rel_def]
  by (induct rule: list_all2_induct) (use assms(2,3) in \<open>auto simp: dmld_rel_def\<close>)

text \<open>
  The frame a future-match node runs at: the node's columns, the operand formulas and the marked
  expressions the structure tabulates over.  Unlike the past-match node, the operands' tables are
  not fixed -- the structure keeps one list per stored time point -- so they stay a parameter.
\<close>

locale dmatchF_frame =
  fixes n :: nat and cs :: cols and \<psi>s :: "ty Formula.formula list" and mrs :: "mregex list"
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and sub: "\<And>i. i < length \<psi>s \<Longrightarrow> Formula.fv (\<psi>s ! i) \<subseteq> set cs"
    and d: "distinct mrs"
    and mrsok: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
       Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex ms \<psi>s) \<and> ok (length \<psi>s) ms \<and>
       set cs = fv_regex (from_mregex ms \<psi>s)"
begin

abbreviation (input) wfrels :: "event_data table list \<Rightarrow> bool" where
  "wfrels rels \<equiv> list_all2 (\<lambda>\<psi> rel. table n (Formula.fv \<psi>) rel) \<psi>s rels"

lemma lr: "wfrels rels \<Longrightarrow> length \<psi>s = length rels"
  by (simp add: list_all2_lengthD)

lemma opsB:
  assumes w: "wfrels rels" and i: "i < length rels"
  shows "\<exists>B \<subseteq> set cs. table n B (rels ! i)"
proof -
  have i': "i < length \<psi>s" using lr[OF w] i by simp
  then have "table n (Formula.fv (\<psi>s ! i)) (rels ! i)"
    using w by (simp add: list_all2_conv_all_nth)
  then show ?thesis using sub[OF i'] by blast
qed

lemma okms: "ms \<in> set mrs \<Longrightarrow> wfrels rels \<Longrightarrow> ok (length rels) ms"
  using mrsok lr by auto

lemma tabL: "wfrels rels \<Longrightarrow> ms \<in> set mrs \<Longrightarrow> table n (set cs) (l\<epsilon>_strict n rels ms)"
  using mrsok by (intro table_leps_strict[where \<psi>s = \<psi>s]) auto

lemma dtabL: "wfrels rels \<Longrightarrow> ms \<in> set mrs \<Longrightarrow>
    dtabc n cs (l\<epsilon>_strict n rels ms) = l\<epsilon>_strict (length cs) (map (dtabc n cs) rels) ms"
  using mrsok by (intro dtabc_leps_strict[OF s b _ sub]) auto

lemma table_lookup_base:
  "wfrels rels \<Longrightarrow> table n (set cs) (lookup (mrtabulate mrs (l\<epsilon>_strict n rels)) ms)"
  using tabL by (simp add: lookup_tabulate[OF d])

lemma dtabc_lookup_base:
  "wfrels rels \<Longrightarrow>
     lookup (mrtabulate mrs (l\<epsilon>_strict (length cs) (map (dtabc n cs) rels))) ms
       = dtabc n cs (lookup (mrtabulate mrs (l\<epsilon>_strict n rels)) ms)"
  by (intro lookup_mrtabulate_cong[OF d]) (rule dtabL)

lemma table_lookup_step:
  assumes rls: "wfrels rls" and X: "\<And>ms. table n (set cs) (lookup X ms)"
  shows "table n (set cs) (lookup (mrtabulate mrs (l\<delta> id X rls)) ms)"
  using table_ldelta[OF _ X] okms[OF _ rls] opsB[OF rls]
  by (auto simp: lookup_tabulate[OF d])

lemma dtabc_lookup_step:
  assumes rls: "wfrels rls" and X: "\<And>ms. table n (set cs) (lookup X ms)"
    and dX: "\<And>ms. lookup dX ms = dtabc n cs (lookup X ms)"
  shows "lookup (mrtabulate mrs (l\<delta> id dX (map (dtabc n cs) rls))) ms
       = dtabc n cs (lookup (mrtabulate mrs (l\<delta> id X rls)) ms)"
proof -
  have dL: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
      dtabc n cs (l\<delta> id X rls ms) = l\<delta> id dX (map (dtabc n cs) rls) ms"
    by (rule dtabc_ldelta[OF s b opsB[OF rls] X dX okms[OF _ rls]])
  show ?thesis by (intro lookup_mrtabulate_cong[OF d]) (rule dL)
qed

text \<open>
  The fold that steps the structure keeps two things related: the stored list, and the tabulation
  the fold threads through it.  Both are proved at once.
\<close>

lemma dtabc_matchF_foldr:
  assumes rels: "wfrels rels" and rel: "dmld_rel n cs \<psi>s aux daux"
  shows "dmld_rel n cs \<psi>s
       (fst (foldr (update_matchF_step I mr mrs nt) aux
          (update_matchF_base n I mr mrs rels nt)))
       (fst (foldr (update_matchF_step I mr mrs nt) daux
          (update_matchF_base (length cs) I mr mrs (map (dtabc n cs) rels) nt)))
     \<and> (\<forall>ms. table n (set cs)
          (lookup (snd (foldr (update_matchF_step I mr mrs nt) aux
             (update_matchF_base n I mr mrs rels nt))) ms))
     \<and> (\<forall>ms. lookup (snd (foldr (update_matchF_step I mr mrs nt) daux
             (update_matchF_base (length cs) I mr mrs (map (dtabc n cs) rels) nt))) ms
          = dtabc n cs (lookup (snd (foldr (update_matchF_step I mr mrs nt) aux
             (update_matchF_base n I mr mrs rels nt))) ms))"
  using rel
proof (induct rule: dmld_rel_induct)
  case Nil
  show ?case
    using rels table_lookup_base[OF rels] dtabc_lookup_base[OF rels]
    by (simp add: update_matchF_base_def Let_def)
next
  case (Cons t rls rel aux daux)
  obtain A X where W: "foldr (update_matchF_step I mr mrs nt) aux
      (update_matchF_base n I mr mrs rels nt) = (A, X)"
    by (cases "foldr (update_matchF_step I mr mrs nt) aux
      (update_matchF_base n I mr mrs rels nt)")
  obtain DA DX where D: "foldr (update_matchF_step I mr mrs nt) daux
      (update_matchF_base (length cs) I mr mrs (map (dtabc n cs) rels) nt) = (DA, DX)"
    by (cases "foldr (update_matchF_step I mr mrs nt) daux
      (update_matchF_base (length cs) I mr mrs (map (dtabc n cs) rels) nt)")
  have IH: "dmld_rel n cs \<psi>s A DA" and tX: "\<And>ms. table n (set cs) (lookup X ms)"
    and dXe: "\<And>ms. lookup DX ms = dtabc n cs (lookup X ms)"
    using Cons(3) unfolding W D by simp_all
  have tY: "\<forall>ms. table n (set cs) (lookup (mrtabulate mrs (l\<delta> id X rls)) ms)"
    using table_lookup_step[OF Cons(1) tX] by blast
  have dLY: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
      dtabc n cs (l\<delta> id X rls ms) = l\<delta> id DX (map (dtabc n cs) rls) ms"
    by (rule dtabc_ldelta[OF s b opsB[OF Cons(1)] tX dXe okms[OF _ Cons(1)]])
  have dY: "\<forall>ms. lookup (mrtabulate mrs (l\<delta> id DX (map (dtabc n cs) rls))) ms
      = dtabc n cs (lookup (mrtabulate mrs (l\<delta> id X rls)) ms)"
    by (intro allI lookup_mrtabulate_cong[OF d, where f = "l\<delta> id X rls"
        and g = "l\<delta> id DX (map (dtabc n cs) rls)"]) (rule dLY)
  have E: "foldr (update_matchF_step I mr mrs nt) ((t, rls, rel) # aux)
      (update_matchF_base n I mr mrs rels nt)
      = update_matchF_step I mr mrs nt (t, rls, rel) (A, X)"
    unfolding W[symmetric] by simp
  have DE: "foldr (update_matchF_step I mr mrs nt)
      ((t, map (dtabc n cs) rls, dtabc n cs rel) # daux)
      (update_matchF_base (length cs) I mr mrs (map (dtabc n cs) rels) nt)
      = update_matchF_step I mr mrs nt (t, map (dtabc n cs) rls, dtabc n cs rel) (DA, DX)"
    unfolding D[symmetric] by simp
  show ?case unfolding E DE
    using IH tY dY Cons(1)
    by (simp add: update_matchF_step_def Let_def dtabc_Un_img)
qed

lemma dtabc_update_matchF:
  assumes rels: "wfrels rels" and rel: "dmld_rel n cs \<psi>s aux daux"
  shows "dmld_rel n cs \<psi>s (update_matchF n I mr mrs rels nt aux)
     (update_matchF (length cs) I mr mrs (map (dtabc n cs) rels) nt daux)"
  using dtabc_matchF_foldr[OF rels rel] by (simp add: update_matchF_def)

text \<open>Reading the structure hands out the entries that have left the window, narrowed.\<close>

lemma dtabc_eval_matchF:
  assumes "dmld_rel n cs \<psi>s aux daux"
  shows "fst (eval_matchF I mr nt daux) = map (dtabc n cs) (fst (eval_matchF I mr nt aux)) \<and>
     dmld_rel n cs \<psi>s (snd (eval_matchF I mr nt aux)) (snd (eval_matchF I mr nt daux))"
  using assms
proof (induct rule: dmld_rel_induct)
  case (Cons t rls rel aux daux)
  obtain ys ax where e: "eval_matchF I mr nt aux = (ys, ax)"
    by (cases "eval_matchF I mr nt aux")
  obtain dys dax where de: "eval_matchF I mr nt daux = (dys, dax)"
    by (cases "eval_matchF I mr nt daux")
  have i1: "dys = map (dtabc n cs) ys" and i2: "dmld_rel n cs \<psi>s ax dax"
    using Cons(3) unfolding e de by simp_all
  show ?case using Cons(1,2) i1 i2 by (simp add: e de)
qed simp

end

(*<*)
end
(*>*)
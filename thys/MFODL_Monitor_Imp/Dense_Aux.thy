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

(*<*)
end
(*>*)

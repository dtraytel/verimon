(*<*)
theory Exec_Tables
  imports Short_Tuples
begin
(*>*)

section \<open>Tables over ascending columns\<close>

text \<open>
  The kernel orders a table's columns by @{const Formula.fv_list}, the executable monitor
  ascendingly; a kernel tuple @{term x} over @{term ks} is read as @{term "restrict cs ks x"}.
\<close>

type_synonym cols = "nat list"

subsection \<open>Ascending frames and reordering\<close>

definition eframe :: "cols \<Rightarrow> cols \<Rightarrow> bool" where
  "eframe ks cs \<longleftrightarrow> distinct ks \<and> sorted_wrt (<) cs \<and> set cs = set ks"

lemma eframeD:
  assumes "eframe ks cs"
  shows "distinct ks" "sorted_wrt (<) cs" "set cs = set ks" "distinct cs"
  using assms by (auto simp: eframe_def strict_sorted_iff)

fun eproj :: "bool list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "eproj [] xs = []"
| "eproj (True # bs) (x # xs) = x # eproj bs xs"
| "eproj (False # bs) (x # xs) = eproj bs xs"
| "eproj (b # bs) [] = []"

definition etabc :: "cols \<Rightarrow> cols \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "etabc ks cs T = restrict cs ks ` T"

definition etabw :: "cols \<Rightarrow> cols \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "etabw ks cs D = restrict ks cs ` D"

lemma restrict_map: "restrict cs ks x = map (tup_get ks x) cs"
  by (simp add: restrict_def)

lemma restrict_inv:
  assumes "eframe ks cs" "wf_tuple ks x"
  shows "restrict ks cs (restrict cs ks x) = x"
  using assms by (simp add: eframe_def restrict_restrict restrict_idle)

lemma inj_on_restrict:
  "eframe ks cs \<Longrightarrow> inj_on (restrict cs ks) {x. wf_tuple ks x}"
  by (rule inj_onI) (metis mem_Collect_eq restrict_inv)

lemma etabc_empty[simp]: "etabc ks cs {} = {}"
  by (simp add: etabc_def)

subsection \<open>Binary join\<close>

subsubsection \<open>Merging two column lists\<close>

datatype mrg = MLft | MRgt | MBth

fun mrg_plan :: "cols \<Rightarrow> cols \<Rightarrow> mrg list" where
  "mrg_plan [] ds = map (\<lambda>_. MRgt) ds"
| "mrg_plan (c # cs) [] = MLft # mrg_plan cs []"
| "mrg_plan (c # cs) (d # ds) =
    (if c < d then MLft # mrg_plan cs (d # ds)
     else if d < c then MRgt # mrg_plan (c # cs) ds
     else MBth # mrg_plan cs ds)"

fun merge_cols :: "cols \<Rightarrow> cols \<Rightarrow> cols" where
  "merge_cols [] ds = ds"
| "merge_cols (c # cs) [] = c # merge_cols cs []"
| "merge_cols (c # cs) (d # ds) =
    (if c < d then c # merge_cols cs (d # ds)
     else if d < c then d # merge_cols (c # cs) ds
     else c # merge_cols cs ds)"

fun ejoin1 :: "mrg list \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list option" where
  "ejoin1 [] xs ys = Some []"
| "ejoin1 (MLft # p) (x # xs) ys = map_option (Cons x) (ejoin1 p xs ys)"
| "ejoin1 (MRgt # p) xs (y # ys) = map_option (Cons y) (ejoin1 p xs ys)"
| "ejoin1 (MBth # p) (x # xs) (y # ys) =
    (if x = y then map_option (Cons x) (ejoin1 p xs ys) else None)"
| "ejoin1 (m # p) xs ys = None"

lemma merge_cols_Nil2: "merge_cols cs [] = cs"
  by (induct cs) auto

subsubsection \<open>Join on contained columns\<close>

fun mrg_left_key :: "mrg list \<Rightarrow> bool list" where
  "mrg_left_key [] = []"
| "mrg_left_key (MLft # p) = False # mrg_left_key p"
| "mrg_left_key (MRgt # p) = mrg_left_key p"
| "mrg_left_key (MBth # p) = True # mrg_left_key p"

definition no_right :: "mrg list \<Rightarrow> bool" where
  "no_right p = list_all (\<lambda>m. m \<noteq> MRgt) p"

definition esemi :: "bool list \<Rightarrow> bool \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "esemi msk pos A B = Set.filter (\<lambda>a. (eproj msk a \<in> B) = pos) A"

fun mrg_right_key :: "mrg list \<Rightarrow> bool list" where
  "mrg_right_key [] = []"
| "mrg_right_key (MLft # p) = mrg_right_key p"
| "mrg_right_key (MRgt # p) = False # mrg_right_key p"
| "mrg_right_key (MBth # p) = True # mrg_right_key p"

definition no_left :: "mrg list \<Rightarrow> bool" where
  "no_left p = list_all (\<lambda>m. m \<noteq> MLft) p"

fun mrg_swap :: "mrg \<Rightarrow> mrg" where
  "mrg_swap MLft = MRgt"
| "mrg_swap MRgt = MLft"
| "mrg_swap MBth = MBth"

subsubsection \<open>General join via an index\<close>

text \<open>
  One side is indexed by the shared columns and the other probes the index; a hit agrees on the
  shared columns, so the merge needs no test.
\<close>

fun emerge :: "mrg list \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "emerge [] xs ys = []"
| "emerge (MLft # p) (x # xs) ys = x # emerge p xs ys"
| "emerge (MRgt # p) xs (y # ys) = y # emerge p xs ys"
| "emerge (MBth # p) (x # xs) (y # ys) = x # emerge p xs ys"
| "emerge (m # p) xs ys = []"

definition gindex_step :: "bool list \<Rightarrow> 'b list \<Rightarrow>
    ('b list, 'b list list) mapping \<Rightarrow> ('b list, 'b list list) mapping" where
  "gindex_step msk b m = (let k = eproj msk b in
     (case Mapping.lookup m k of None \<Rightarrow> Mapping.update k [b] m
      | Some l \<Rightarrow> Mapping.update k (b # l) m))"

definition gindex :: "bool list \<Rightarrow> 'b :: ccompare list set \<Rightarrow>
    ('b list, 'b list list) mapping" where
  "gindex msk B = fold (gindex_step msk) (csl B) Mapping.empty"

definition gprobe_step :: "mrg list \<Rightarrow> bool list \<Rightarrow>
    ('b list, 'b list list) mapping \<Rightarrow> 'b list \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "gprobe_step p msk m a acc = (case Mapping.lookup m (eproj msk a) of
      None \<Rightarrow> acc
    | Some l \<Rightarrow> fold (\<lambda>b acc. Set.insert (emerge p a b) acc) l acc)"

definition gprobe_step_l :: "mrg list \<Rightarrow> bool list \<Rightarrow>
    ('b list, 'b list list) mapping \<Rightarrow> 'b list \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "gprobe_step_l p rk m y acc = (case Mapping.lookup m (eproj rk y) of
      None \<Rightarrow> acc
    | Some l \<Rightarrow> fold (\<lambda>x acc. Set.insert (emerge p x y) acc) l acc)"

definition ggen_join :: "mrg list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
    'b :: ccompare list set \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "ggen_join p lk rk A B =
     (if card A \<le> card B
      then (let m = gindex lk A in fold (gprobe_step_l p rk m) (csl B) {})
      else (let m = gindex rk B in fold (gprobe_step p lk m) (csl A) {}))"

definition bucket :: "(event_data tuple, event_data tuple list) mapping \<Rightarrow>
    event_data tuple \<Rightarrow> event_data tuple list" where
  "bucket m k = (case Mapping.lookup m k of None \<Rightarrow> [] | Some l \<Rightarrow> l)"

subsubsection \<open>Join plans\<close>

text \<open>
  A plan is computed once, at compile time; the kernel's @{const bin_join} redoes this case
  distinction on every call.
\<close>

datatype ejoin_plan =
    EJEq | EJEmp | EJSub "bool list" | EJSup "bool list"
  | EJGen "mrg list" "bool list" "bool list"

definition mk_djoin :: "cols \<Rightarrow> cols \<Rightarrow> ejoin_plan" where
  "mk_djoin cs1 cs2 = (if cs1 = cs2 then EJEq else if cs2 = [] then EJEmp
     else (let p = mrg_plan cs1 cs2 in
       if no_right p then EJSub (mrg_left_key p)
       else if no_left p then EJSup (mrg_right_key p)
       else EJGen p (mrg_left_key p) (mrg_right_key p)))"

fun gbin_join0 :: "ejoin_plan \<Rightarrow> 'b :: ccompare list set \<Rightarrow> bool \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "gbin_join0 EJEq A pos B = (if pos then A \<inter> B else A - B)"
| "gbin_join0 EJEmp A pos B = (if pos = ([] \<in> B) then A else {})"
| "gbin_join0 (EJSub msk) A pos B = esemi msk pos A B"
| "gbin_join0 (EJSup msk) A pos B = (if pos then Set.filter (\<lambda>b. eproj msk b \<in> A) B else A)"
| "gbin_join0 (EJGen p lk rk) A pos B = (if pos then ggen_join p lk rk A B else A)"

definition gbin_join :: "ejoin_plan \<Rightarrow> 'b :: ccompare list set \<Rightarrow> bool \<Rightarrow> 'b list set \<Rightarrow>
    'b list set" where
  "gbin_join pl A pos B = (if Set.is_empty A then {}
     else if Set.is_empty B then (if pos then {} else A)
     else gbin_join0 pl A pos B)"

subsection \<open>Multi-way join\<close>

text \<open>
  The kernel's @{const mmulti_join} picks a strategy at run time; the executable one joins left to
  right along a plan list computed once.
\<close>

fun eands_plans :: "cols \<Rightarrow> cols list \<Rightarrow> ejoin_plan list" where
  "eands_plans acc [] = []"
| "eands_plans acc (c # cs) = mk_djoin acc c # eands_plans (merge_cols acc c) cs"

fun eands_cols :: "cols \<Rightarrow> cols list \<Rightarrow> cols" where
  "eands_cols acc [] = acc"
| "eands_cols acc (c # cs) = eands_cols (merge_cols acc c) cs"

fun gands_pos :: "ejoin_plan list \<Rightarrow> 'b :: ccompare list set \<Rightarrow> 'b list set list \<Rightarrow>
    'b list set" where
  "gands_pos [] t us = t"
| "gands_pos (p # ps) t [] = t"
| "gands_pos (p # ps) t (u # us) = gands_pos ps (gbin_join p t True u) us"

fun gands_neg :: "ejoin_plan list \<Rightarrow> 'b :: ccompare list set \<Rightarrow> 'b list set list \<Rightarrow>
    'b list set" where
  "gands_neg [] t us = t"
| "gands_neg (p # ps) t [] = t"
| "gands_neg (p # ps) t (u # us) = gands_neg ps (gbin_join p t False u) us"

fun kands_cols :: "cols \<Rightarrow> cols list \<Rightarrow> cols" where
  "kands_cols acc [] = acc"
| "kands_cols acc (k # ks) = kands_cols (cols_union acc k) ks"

fun kands_pos :: "cols \<Rightarrow> 'a table \<Rightarrow> (cols \<times> 'a table) list \<Rightarrow> 'a table" where
  "kands_pos acc t [] = t"
| "kands_pos acc t ((k, u) # us) = kands_pos (cols_union acc k) (join acc t True k u) us"

fun kands_neg :: "cols \<Rightarrow> 'a table \<Rightarrow> (cols \<times> 'a table) list \<Rightarrow> 'a table" where
  "kands_neg acc t [] = t"
| "kands_neg acc t ((k, u) # us) = kands_neg acc (join acc t False k u) us"

definition wf_operand :: "cols \<Rightarrow> cols \<Rightarrow> event_data table \<Rightarrow> bool" where
  "wf_operand k c U \<longleftrightarrow> eframe k c \<and> table k U \<and> finite U"

subsection \<open>Aggregation\<close>

subsubsection \<open>Reindexed terms\<close>

fun col_pos :: "cols \<Rightarrow> nat \<Rightarrow> nat" where
  "col_pos [] x = 0"
| "col_pos (c # cs) x = (if c = x then 0 else Suc (col_pos cs x))"

fun reindex_trm :: "cols \<Rightarrow> Formula.trm \<Rightarrow> Formula.trm" where
  "reindex_trm cs (Formula.Var x) = Formula.Var (col_pos cs x)"
| "reindex_trm cs (Formula.Const c) = Formula.Const c"
| "reindex_trm cs (Formula.Plus a b) = Formula.Plus (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.Minus a b) = Formula.Minus (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.UMinus a) = Formula.UMinus (reindex_trm cs a)"
| "reindex_trm cs (Formula.Mult a b) = Formula.Mult (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.Div a b) = Formula.Div (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.Mod a b) = Formula.Mod (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.F2i a) = Formula.F2i (reindex_trm cs a)"
| "reindex_trm cs (Formula.I2f a) = Formula.I2f (reindex_trm cs a)"

lemma col_pos_nth: "c \<in> set cs \<Longrightarrow> map f cs ! col_pos cs c = f c"
  by (induct cs) auto

lemma umeval_trm_reindex:
  "Formula.fv_trm t \<subseteq> set cs' \<Longrightarrow> umeval_trm (reindex_trm cs' t) (restrict cs' cs x) = meval_trm cs t x"
  by (induct t) (auto simp: restrict_map col_pos_nth)

subsubsection \<open>Group key as a suffix\<close>

text \<open>
  The bound variables are the bottom columns, so the ascending columns are @{term "[0..<m]"}
  followed by the shifted group columns, and the group key is @{term "drop m"} of the short tuple.
\<close>

abbreviation agg_cols :: "nat \<Rightarrow> cols \<Rightarrow> cols" where
  "agg_cols m gcols \<equiv> [0..<m] @ map (\<lambda>c. c + m) gcols"

lemma agg_cols_sortedD: "sorted_wrt (<) (agg_cols m gcols) \<Longrightarrow> sorted_wrt (<) gcols"
  by (auto simp: sorted_wrt_append sorted_wrt_map)

lemma set_shift_agg_cols:
  "set cs = set (agg_cols m gcols) \<Longrightarrow> set (shift_cols m cs) = set gcols"
  by (force simp: set_shift_cols image_iff)

lemma eframe_shift_cols:
  assumes "eframe cs (agg_cols m gcols)"
  shows "eframe (shift_cols m cs) gcols"
  using eframeD(1,2)[OF assms] set_shift_agg_cols[OF eframeD(3)[OF assms, symmetric]]
  unfolding eframe_def by (simp add: distinct_shift_cols agg_cols_sortedD)

lemma tup_get_agg_key_shift:
  assumes "c \<in> set cs" "k \<le> c"
  shows "tup_get (shift_cols k cs) (agg_key k cs x) (c - k) = tup_get cs x c"
proof -
  have "tup_get (shift_cols k cs) (agg_key k cs x) (c - k) =
      tup_get (filter (\<lambda>x. k \<le> x) cs) (agg_key k cs x) c"
    unfolding shift_cols_def using assms by (intro tup_get_map) (auto simp: inj_on_def)
  also have "\<dots> = tup_get cs x c"
    unfolding agg_key_def using assms by (simp add: tup_get_restrict)
  finally show ?thesis .
qed

lemma wf_tuple_agg_key_shift: "wf_tuple (shift_cols k cs) (agg_key k cs x)"
  by (simp add: agg_key_def shift_cols_def wf_tuple_def)

lemma drop_restrict_agg:
  assumes "set (agg_cols m gcols) \<subseteq> set cs"
  shows "drop m (restrict (agg_cols m gcols) cs x) = restrict gcols (shift_cols m cs) (agg_key m cs x)"
proof -
  have "drop m (restrict (agg_cols m gcols) cs x) = map (\<lambda>c. tup_get cs x (c + m)) gcols"
    by (simp add: restrict_map)
  also have "\<dots> = restrict gcols (shift_cols m cs) (agg_key m cs x)"
    unfolding restrict_map
  proof (rule map_cong[OF refl])
    fix c assume "c \<in> set gcols"
    then have "c + m \<in> set cs" using assms by auto
    then show "tup_get cs x (c + m) = tup_get (shift_cols m cs) (agg_key m cs x) c"
      using tup_get_agg_key_shift[of "c + m" cs m x] by simp
  qed
  finally show ?thesis .
qed

subsubsection \<open>Inserting the aggregate\<close>

definition ins_pos :: "cols \<Rightarrow> nat \<Rightarrow> nat" where
  "ins_pos cs y = length (filter (\<lambda>c. c < y) cs)"

lemma merge_cols_single:
  "sorted_wrt (<) cs \<Longrightarrow> y \<notin> set cs \<Longrightarrow>
     merge_cols cs [y] = take (ins_pos cs y) cs @ y # drop (ins_pos cs y) cs"
proof (induct cs)
  case (Cons c cs)
  show ?case
  proof (cases "c < y")
    case True
    then show ?thesis using Cons by (simp add: ins_pos_def)
  next
    case False
    then have yc: "y < c" using Cons(3) by auto
    then have "filter (\<lambda>d. d < y) (c # cs) = []" using Cons(2)
      by (force simp: filter_empty_conv)
    then show ?thesis using yc False by (simp add: ins_pos_def merge_cols_Nil2)
  qed
qed (simp add: ins_pos_def)

lemma restrict_merge_single:
  assumes s: "sorted_wrt (<) gcols" and yg: "y \<notin> set gcols"
  shows "restrict (merge_cols gcols [y]) (y # ks) (v # k)
       = take (ins_pos gcols y) (restrict gcols ks k) @ v # drop (ins_pos gcols y) (restrict gcols ks k)"
proof -
  let ?p = "ins_pos gcols y"
  have upd: "tup_get (y # ks) (v # k) c = tup_get ks k c" if "c \<in> set gcols" for c
    using that yg by (auto simp: tup_get_Cons)
  have "restrict (merge_cols gcols [y]) (y # ks) (v # k)
      = map (tup_get (y # ks) (v # k)) (take ?p gcols @ y # drop ?p gcols)"
    by (simp add: restrict_map merge_cols_single[OF s yg])
  also have "\<dots> = map (tup_get ks k) (take ?p gcols) @ v # map (tup_get ks k) (drop ?p gcols)"
  proof -
    have t: "map (tup_get (y # ks) (v # k)) (take ?p gcols) = map (tup_get ks k) (take ?p gcols)"
      by (rule map_cong[OF refl]) (auto dest: in_set_takeD intro!: upd)
    have d: "map (tup_get (y # ks) (v # k)) (drop ?p gcols) = map (tup_get ks k) (drop ?p gcols)"
      by (rule map_cong[OF refl]) (auto dest: in_set_dropD intro!: upd)
    show ?thesis using t d by (simp add: tup_get_Cons)
  qed
  also have "\<dots> = take ?p (restrict gcols ks k) @ v # drop ?p (restrict gcols ks k)"
    by (simp add: restrict_map take_map drop_map)
  finally show ?thesis .
qed

lemma drop_restrict_agg_eq_iff:
  assumes f: "eframe cs (agg_cols m gcols)"
  shows "(drop m (restrict (agg_cols m gcols) cs x) = drop m (restrict (agg_cols m gcols) cs x'))
       = (agg_key m cs x = agg_key m cs x')"
proof -
  have sub: "set (agg_cols m gcols) \<subseteq> set cs" using eframeD(3)[OF f] by simp
  note i = inj_on_restrict[OF eframe_shift_cols[OF f]]
  show ?thesis
    unfolding drop_restrict_agg[OF sub]
  proof
    assume "restrict gcols (shift_cols m cs) (agg_key m cs x) = restrict gcols (shift_cols m cs) (agg_key m cs x')"
    then show "agg_key m cs x = agg_key m cs x'"
      by (rule inj_onD[OF i]) (simp_all add: wf_tuple_agg_key_shift)
  qed simp
qed

lemma etabc_agg_group:
  assumes f: "eframe cs (agg_cols m gcols)"
  shows "Set.filter (\<lambda>z. drop m z = drop m (restrict (agg_cols m gcols) cs x0))
           (etabc cs (agg_cols m gcols) rel)
       = etabc cs (agg_cols m gcols) (Set.filter (\<lambda>x. agg_key m cs x = agg_key m cs x0) rel)"
  unfolding etabc_def using drop_restrict_agg_eq_iff[OF f] by auto

lemma uagg_values_etabc:
  assumes f: "eframe cs (agg_cols m gcols)" and tG: "table cs G"
    and fv: "Formula.fv_trm f \<subseteq> set cs"
  shows "uagg_values (reindex_trm (agg_cols m gcols) f) (etabc cs (agg_cols m gcols) G)
       = (\<lambda>v. (v, ecard (Set.filter (\<lambda>x. meval_trm cs f x = v) G))) ` meval_trm cs f ` G"
proof -
  let ?cc = "agg_cols m gcols"
  let ?r = "restrict ?cc cs"
  let ?g = "reindex_trm ?cc f"
  have ev: "umeval_trm ?g (?r x) = meval_trm cs f x" for x
    using fv eframeD(3)[OF f] by (intro umeval_trm_reindex) simp
  have inj: "inj_on ?r G"
    by (rule inj_on_subset[OF inj_on_restrict[OF f]]) (use tG in \<open>auto simp: table_def\<close>)
  have img: "umeval_trm ?g ` ?r ` G = meval_trm cs f ` G"
    unfolding image_image by (intro image_cong[OF refl] ev)
  show ?thesis
    unfolding uagg_values etabc_def img
  proof (intro image_cong[OF refl])
    fix v :: event_data
    have fil: "Set.filter (\<lambda>z. umeval_trm ?g z = v) (?r ` G) = ?r ` Set.filter (\<lambda>x. meval_trm cs f x = v) G"
      by (auto simp: ev)
    have inj': "inj_on ?r (Set.filter (\<lambda>x. meval_trm cs f x = v) G)"
      by (rule inj_on_subset[OF inj]) auto
    show "(v, ecard (Set.filter (\<lambda>z. umeval_trm ?g z = v) (?r ` G)))
        = (v, ecard (Set.filter (\<lambda>x. meval_trm cs f x = v) G))"
      unfolding fil ecard_image[OF inj'] by (rule refl)
  qed
qed

theorem uagg_eval_agg:
  assumes f: "eframe cs (agg_cols (length tys) gcols)" and t: "table cs rel"
    and fv: "Formula.fv_trm f \<subseteq> set cs" and yg: "y \<notin> set gcols"
    and g0: "g0 \<Longrightarrow> gcols = []"
  shows "uagg g0 \<omega> (reindex_trm (agg_cols (length tys) gcols) f) (length tys) (ins_pos gcols y)
           (etabc cs (agg_cols (length tys) gcols) rel)
       = etabc (y # shift_cols (length tys) cs) (merge_cols gcols [y]) (eval_agg cs g0 \<omega> tys f rel)"
proof -
  let ?m = "length tys"
  let ?cc = "agg_cols ?m gcols"
  let ?r = "restrict ?cc cs"
  let ?S = "shift_cols ?m cs"
  let ?g = "reindex_trm ?cc f"
  let ?p = "ins_pos gcols y"
  let ?A = "\<lambda>x. eval_agg_op \<omega> ((\<lambda>x''. (meval_trm cs f x'', ecard (Set.filter
      (\<lambda>x'. meval_trm cs f x' = meval_trm cs f x'')
      (Set.filter (\<lambda>x'. agg_key ?m cs x' = agg_key ?m cs x) rel)))) `
      Set.filter (\<lambda>x'. agg_key ?m cs x' = agg_key ?m cs x) rel)"
  have sg: "sorted_wrt (<) gcols" using eframeD(2)[OF f] by (rule agg_cols_sortedD)
  have sub: "set ?cc \<subseteq> set cs" using eframeD(3)[OF f] by simp
  show ?thesis
  proof (cases "g0 \<and> rel = empty_table")
    case True
    then have e: "rel = {}" and g: "g0" by (auto simp: empty_table_def)
    have mc: "merge_cols gcols [y] = [y]" using g0[OF g] by simp
    show ?thesis
      using True e g by (simp add: uagg_def eval_agg_def etabc_def singleton_table_def mc
          restrict_map tup_get_Cons empty_table_def)
  next
    case False
    then have ne: "\<not> (g0 \<and> Set.is_empty (?r ` rel))"
      by (auto simp: empty_table_def)
    have "uagg g0 \<omega> ?g ?m ?p (etabc cs ?cc rel)
        = (\<lambda>k. take ?p k @ eval_agg_op \<omega>
          (uagg_values ?g (Set.filter (\<lambda>z. drop ?m z = k) (?r ` rel))) # drop ?p k)
          ` (drop ?m ` ?r ` rel)"
      unfolding uagg_def etabc_def Let_def keys_cluster using ne
      by (auto simp: lookup_cluster_Some intro!: image_cong)
    also have "\<dots> = (\<lambda>x. restrict (merge_cols gcols [y]) (y # ?S) (?A x # agg_key ?m cs x)) ` rel"
      unfolding image_image
    proof (intro image_cong[OF refl])
      fix x assume x: "x \<in> rel"
      let ?gr = "Set.filter (\<lambda>x'. agg_key ?m cs x' = agg_key ?m cs x) rel"
      have k: "drop ?m (?r x) = restrict gcols ?S (agg_key ?m cs x)"
        by (rule drop_restrict_agg[OF sub])
      have grp: "Set.filter (\<lambda>z. drop ?m z = drop ?m (?r x)) (?r ` rel) = ?r ` ?gr"
        using etabc_agg_group[OF f, of x rel] unfolding etabc_def .
      have tgr: "table cs ?gr" using t by (auto simp: table_def)
      have av: "uagg_values ?g (?r ` ?gr) = (\<lambda>v. (v, ecard (Set.filter (\<lambda>x'. meval_trm cs f x' = v) ?gr)))
          ` meval_trm cs f ` ?gr"
        using uagg_values_etabc[OF f tgr fv] unfolding etabc_def .
      show "take ?p (drop ?m (?r x)) @ eval_agg_op \<omega>
              (uagg_values ?g (Set.filter (\<lambda>z. drop ?m z = drop ?m (?r x)) (?r ` rel)))
              # drop ?p (drop ?m (?r x))
          = restrict (merge_cols gcols [y]) (y # ?S) (?A x # agg_key ?m cs x)"
        unfolding grp av unfolding restrict_merge_single[OF sg yg] k image_image by (rule refl)
    qed
    also have "\<dots> = etabc (y # ?S) (merge_cols gcols [y]) (eval_agg cs g0 \<omega> tys f rel)"
      unfolding etabc_def eval_agg_def Let_def if_not_P[OF False] by (simp add: image_image)
    finally show ?thesis .
  qed
qed

subsection \<open>Predicates and the existential\<close>

definition set_cols :: "nat set \<Rightarrow> cols" where
  "set_cols A = csorted_list_of_set A"

text \<open>If a predicate's arguments are distinct variables in ascending order, its database tuples
  are already short tuples.\<close>

fun smp_cols :: "Formula.trm list \<Rightarrow> cols" where
  "smp_cols [] = []"
| "smp_cols (Formula.Var y # ts) = y # smp_cols ts"
| "smp_cols (t # ts) = []"

text \<open>Over ascending columns, variable @{term 0} can only be the head column, so the existential
  drops the head or nothing.\<close>

definition ex_drop0 :: "cols \<Rightarrow> bool" where
  "ex_drop0 ccs = (case ccs of [] \<Rightarrow> False | c # _ \<Rightarrow> c = 0)"

definition eex_cols :: "cols \<Rightarrow> cols" where
  "eex_cols ccs = map (\<lambda>c. c - Suc 0) (if ex_drop0 ccs then tl ccs else ccs)"

subsection \<open>Temporal operators\<close>

text \<open>
  All that @{locale msaux} and @{locale muaux} do to their auxiliary lists commutes with the
  reordering, so the verified structures run unchanged over ascending columns.
\<close>

definition eargs :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> args" where
  "eargs cs_R cs_L args = init_args (args_ivl args) (length cs_R) cs_L cs_R (args_pos args) None"

lemma eargs_simps[simp]:
  "args_ivl (eargs cs_R cs_L args) = args_ivl args"
  "args_n (eargs cs_R cs_L args) = length cs_R"
  "args_L (eargs cs_R cs_L args) = cs_L"
  "args_R (eargs cs_R cs_L args) = cs_R"
  "args_pos (eargs cs_R cs_L args) = args_pos args"
  "args_agg (eargs cs_R cs_L args) = None"
  by (simp_all add: eargs_def init_args_def)

lemma eval_args_agg_None[simp]: "args_agg args = None \<Longrightarrow> eval_args_agg args X = X"
  by (simp add: eval_args_agg_def)

definition eauxlist :: "cols \<Rightarrow> cols \<Rightarrow> (ts \<times> 'b list set) list \<Rightarrow> (ts \<times> 'b list set) list" where
  "eauxlist ks cs aux = map (\<lambda>(t, rel). (t, etabc ks cs rel)) aux"

definition eauxlist3 :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow>
    (ts \<times> 'b list set \<times> 'b list set) list" where
  "eauxlist3 kL cL kR cR aux = map (\<lambda>(t, a1, a2). (t, etabc kL cL a1, etabc kR cR a2)) aux"

lemma length_map2_map[simp]: "length hs = length buf \<Longrightarrow> length (map2 map hs buf) = length buf"
  by simp

lemma etabc_empty_table[simp]: "etabc ks cs empty_table = empty_table"
  by (simp add: empty_table_def)

subsection \<open>Multi-way join of the evaluator\<close>

definition gmulti_join :: "ejoin_plan list \<Rightarrow> ejoin_plan list \<Rightarrow> 'b :: ccompare list set list \<Rightarrow>
    'b list set" where
  "gmulti_join ps ns us = (case us of [] \<Rightarrow> {}
     | t # r \<Rightarrow> gands_neg ns (gands_pos ps t (take (length ps) r)) (drop (length ps) r))"

lemma length_eands_plans[simp]: "length (eands_plans acc css) = length css"
  by (induct css arbitrary: acc) auto

subsection \<open>Constraints\<close>

definition reindex_constraint ::
    "cols \<Rightarrow> Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow>
     Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm" where
  "reindex_constraint cs conf = (case conf of (t1, p, c, t2) \<Rightarrow>
     (reindex_trm cs t1, p, c, reindex_trm cs t2))"

subsection \<open>Embedding plans and time points\<close>

definition emb_plan :: "cols \<Rightarrow> cols \<Rightarrow> nat option list" where
  "emb_plan cs_R cs_L = map (\<lambda>c. if c \<in> set cs_L then Some (col_pos cs_L c) else None) cs_R"

definition mtrm_ecols :: "mtrm \<Rightarrow> cols" where
  "mtrm_ecols mt = (case mt of MVar v \<Rightarrow> [v] | MConst c \<Rightarrow> [])"

lemma length_eauxlist3[simp]: "length (eauxlist3 kL cL kR cR auxlist) = length auxlist"
  by (simp add: eauxlist3_def)

subsection \<open>Index for the semi-join\<close>

text \<open>
  Over ascending columns the probe table is the key set, so the index clusters the stored table
  by its key projection and a probe restricts the mapping.
\<close>

definition eidx :: "bool list \<Rightarrow> 'b list set \<Rightarrow> ('b list, 'b list set) mapping" where
  "eidx msk T = cluster (Some \<circ> eproj msk) T"

definition esemi_idx :: "bool list \<Rightarrow> bool \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow> 'b list set \<Rightarrow>
    'b list set" where
  "esemi_idx msk pos idx X = set_of_idx (Mapping.filter (\<lambda>k _. (k \<in> X) = pos) idx)"

lemma lookup_eidx: "Mapping.lookup (eidx msk T) k =
  (if k \<in> eproj msk ` T then Some {y \<in> T. eproj msk y = k} else None)"
  unfolding eidx_def by transfer auto

(*<*)
end
(*>*)

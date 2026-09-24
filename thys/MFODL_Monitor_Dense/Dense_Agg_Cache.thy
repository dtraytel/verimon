(*<*)
theory Dense_Agg_Cache
  imports Dense_Unbox_UAgg
begin
(*>*)

section \<open>The window's aggregate with its result table\<close>

text \<open>
  A fused aggregation over a past window (@{const usa_result}) reads its result at every time
  point, and the read builds the table of all groups afresh from the aggregate's mapping, one
  insertion per group.  From one time point to the next only the groups of the tuples entering
  and leaving the window can change -- and for MIN and MAX few of those do.  This theory keeps the
  result table next to the aggregate and updates it at the touched groups only.

  The aggregate and its result are kept together in the type @{text ucache}, whose invariant is
  that the table is the (filtered) result of the aggregate, so that reading it off is correct on
  every value of the type and no invariant has to be carried through the evaluator.  The table is
  built for one node, its key: a structure built for a different constraint or aggregation is
  rebuilt by the first step.  The window over it, @{text uswaggc}, is the window of
  @{theory MFODL_Monitor_Dense.Dense_Unbox_Eval} with the count set and the aggregate moved into
  the new type, and it projects onto that window (@{text ucs}) with every operation commuting.

  The per-group reading rests on the result tuple of a group, @{text mkr}: the group with the
  aggregate inserted at the result's position, which determines the group and the value
  (@{text mkr_eq_iff}), so a group's old tuple can be removed without touching another group's.
\<close>

subsection \<open>The result, group by group\<close>

definition mkr :: "nat \<Rightarrow> 'b list \<Rightarrow> 'b \<Rightarrow> 'b list" where
  "mkr p g v = take p g @ v # drop p g"

lemma length_mkr[simp]: "length (mkr p g v) = Suc (length g)"
  by (simp add: mkr_def)

lemma mkr_eq_iff: "mkr p g v = mkr p g' v' \<longleftrightarrow> g = g' \<and> v = v'"
proof
  assume eq: "mkr p g v = mkr p g' v'"
  then have len: "length g = length g'" using length_mkr[of p g v] length_mkr[of p g' v'] by simp
  then have "take p g = take p g' \<and> v # drop p g = v' # drop p g'"
    using eq unfolding mkr_def by (subst (asm) append_eq_append_conv) auto
  then show "g = g' \<and> v = v'" by (metis append_take_drop_id list.inject)
qed simp

fun gval :: "ty Formula.agg_op \<Rightarrow> 'b gagg \<Rightarrow> 'b list \<Rightarrow> event_data option" where
  "gval \<omega> (GCnt m) g = map_option (\<lambda>k. EInt (integer_of_int k)) (Mapping.lookup m g)"
| "gval \<omega> (GSum m) g = (case fst \<omega> of
       Formula.Agg_Sum \<Rightarrow> map_option (\<lambda>k. EInt (snd k)) (Mapping.lookup m g)
     | Formula.Agg_Avg \<Rightarrow> map_option
         (\<lambda>k. EFloat (double_of_event_data (EInt (snd k)) / double_of_int (fst k))) (Mapping.lookup m g)
     | _ \<Rightarrow> None)"
| "gval \<omega> (GRank m ty) g = (case fst \<omega> of
       Formula.Agg_Min \<Rightarrow> map_option (\<lambda>k. get_edata_list k 0) (Mapping.lookup m g)
     | Formula.Agg_Max \<Rightarrow> map_option (\<lambda>k. get_edata_list k (get_length k - 1)) (Mapping.lookup m g)
     | Formula.Agg_Med \<Rightarrow> map_option (\<lambda>k. let u = get_length k; u' = u div 2;
         aggval = (if even u
           then (double_of_event_data_agg (get_edata_list k (u' - 1))
                 + double_of_event_data_agg (get_edata_list k u')) / double_of_int 2
           else double_of_event_data_agg (get_edata_list k u'))
         in EFloat aggval) (Mapping.lookup m g)
     | _ \<Rightarrow> None)"

definition gvset :: "ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> event_data gagg \<Rightarrow> event_data list set" where
  "gvset \<omega> p a = {mkr p g v | g v. gval \<omega> a g = Some v}"

lemma gmr_mkr: "gmr p (\<lambda>x. x) f m = {mkr p g v | g v. map_option f (Mapping.lookup m g) = Some v}"
  unfolding gmr_def mkr_def[symmetric]
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> (\<lambda>g. case Mapping.lookup m g of Some i \<Rightarrow> mkr p g (f i) | None \<Rightarrow> g) ` Mapping.keys m"
  then obtain g i where "Mapping.lookup m g = Some i" "x = mkr p g (f i)"
    by (auto simp: Mapping.keys_dom_lookup)
  then show "x \<in> {mkr p g v |g v. map_option f (Mapping.lookup m g) = Some v}" by auto
next
  fix x
  assume "x \<in> {mkr p g v |g v. map_option f (Mapping.lookup m g) = Some v}"
  then obtain g i where g: "Mapping.lookup m g = Some i" "x = mkr p g (f i)" by auto
  then have "g \<in> Mapping.keys m" by (simp add: Mapping.keys_dom_lookup domI)
  with g show "x \<in> (\<lambda>g. case Mapping.lookup m g of Some i \<Rightarrow> mkr p g (f i) | None \<Rightarrow> g) ` Mapping.keys m"
    by (auto intro!: rev_image_eqI[of g])
qed

lemma gres_gvset: "gres g0 \<omega> p (\<lambda>x. x) a =
    (if g0 \<and> gkeys a = {} then {[eval_agg_op \<omega> {}]} else gvset \<omega> p a)"
  by (cases a) (auto simp: gvset_def gmr_mkr split: Formula.agg_type.splits)


lemma gval_gstep_ins: "gstep_ins k ev t (Some a) = Some a' \<Longrightarrow> h \<noteq> drop k t \<Longrightarrow>
    gval \<omega> a' h = gval \<omega> a h"
  by (cases a) (auto simp: gstep_ins_def Let_def lookup_update' split: prod.splits option.splits
      if_splits event_data.splits type.splits list_aux.splits Formula.agg_type.splits)

lemma gval_gstep_del: "gstep_del k ev t (Some a) = Some a' \<Longrightarrow> h \<noteq> drop k t \<Longrightarrow>
    gval \<omega> a' h = gval \<omega> a h"
  by (cases a) (auto simp: gstep_del_def Let_def lookup_update' lookup_delete split: prod.splits
      option.splits if_splits event_data.splits type.splits list_aux.splits Formula.agg_type.splits)

definition cupd :: "(event_data list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> event_data list \<Rightarrow> event_data option \<Rightarrow>
    event_data option \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "cupd Q p g ov nv C = (if ov = nv then C else
     (let C' = (case ov of Some v \<Rightarrow> if Q (mkr p g v) then Set.remove (mkr p g v) C else C
                | None \<Rightarrow> C) in
      case nv of Some v \<Rightarrow> if Q (mkr p g v) then Set.insert (mkr p g v) C' else C' | None \<Rightarrow> C'))"

lemma cupd_upd: "cupd Q p g (F g) y (Set.filter Q {mkr p h v | h v. F h = Some v}) =
    Set.filter Q {mkr p h v | h v. fun_upd F g y h = Some v}"
proof -
  have split: "{mkr p h v | h v. G h = Some v} =
      {mkr p h v | h v. h \<noteq> g \<and> F h = Some v} \<union> (case G g of Some v \<Rightarrow> {mkr p g v} | None \<Rightarrow> {})"
    if G: "\<And>h. h \<noteq> g \<Longrightarrow> G h = F h" for G
  proof (intro set_eqI iffI)
    fix x
    assume "x \<in> {mkr p h v | h v. G h = Some v}"
    then obtain h v where x: "x = mkr p h v" "G h = Some v" by blast
    then show "x \<in> {mkr p h v | h v. h \<noteq> g \<and> F h = Some v} \<union>
        (case G g of Some v \<Rightarrow> {mkr p g v} | None \<Rightarrow> {})"
      using G by (cases "h = g") auto
  next
    fix x
    assume "x \<in> {mkr p h v | h v. h \<noteq> g \<and> F h = Some v} \<union>
        (case G g of Some v \<Rightarrow> {mkr p g v} | None \<Rightarrow> {})"
    then show "x \<in> {mkr p h v | h v. G h = Some v}"
      using G by (auto simp: mkr_eq_iff split: option.splits)
  qed
  have out: "mkr p g v \<notin> {mkr p h v | h v. h \<noteq> g \<and> F h = Some v}" for v
    by (auto simp: mkr_eq_iff)
  show ?thesis
    unfolding split[of F, OF refl] split[of "fun_upd F g y", simplified]
    using out by (auto simp: cupd_def Let_def mkr_eq_iff split: option.splits if_splits)
qed

lemma cupd_gvset:
  assumes "\<And>h. h \<noteq> g \<Longrightarrow> gval \<omega> a' h = gval \<omega> a h"
  shows "cupd Q p g (gval \<omega> a g) (gval \<omega> a' g) (Set.filter Q (gvset \<omega> p a)) =
    Set.filter Q (gvset \<omega> p a')"
proof -
  have eq: "gval \<omega> a' = fun_upd (gval \<omega> a) g (gval \<omega> a' g)"
    using assms by (auto simp: fun_eq_iff)
  have "cupd Q p g (gval \<omega> a g) (gval \<omega> a' g) (Set.filter Q (gvset \<omega> p a)) =
      Set.filter Q {mkr p h v | h v. fun_upd (gval \<omega> a) g (gval \<omega> a' g) h = Some v}"
    unfolding gvset_def by (rule cupd_upd)
  also have "\<dots> = Set.filter Q (gvset \<omega> p a')"
    unfolding gvset_def eq[symmetric] ..
  finally show ?thesis .
qed


subsection \<open>The counts and the aggregate, in one pass\<close>

text \<open>When a time point's table enters the window or leaves it, the node updates the count of
  every tuple in the window and the aggregate, which sees only the tuples that newly enter or
  finally leave.  The tuples of a table are distinct, so each one's count can be read and updated
  in the same pass as the aggregate without seeing another tuple's update: @{text cnt_ins_fold}
  and @{text cnt_del_fold} are that pass (formerly of @{text Dense_Agg_Upkeep}).\<close>

definition cnt_ins_fold :: "(event_data list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> event_data list list \<Rightarrow> ucnt \<Rightarrow> 'b \<Rightarrow>
    ucnt \<times> 'b" where
  "cnt_ins_fold F xs c b = fold (\<lambda>t (c, acc). case Mapping.lookup c t of
       None \<Rightarrow> (Mapping.update t 1 c, F t acc)
     | Some k \<Rightarrow> (Mapping.update t (k + 1) c, acc)) xs (c, b)"

definition cnt_del_fold :: "(event_data list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> event_data list list \<Rightarrow> ucnt \<Rightarrow> 'b \<Rightarrow>
    ucnt \<times> 'b" where
  "cnt_del_fold F xs c b = fold (\<lambda>t (c, acc). case Mapping.lookup c t of
       None \<Rightarrow> (c, acc)
     | Some k \<Rightarrow> (if k \<le> 1 then (Mapping.delete t c, if k = 1 then F t acc else acc)
                 else (Mapping.update t (k - 1) c, acc))) xs (c, b)"

lemma lookup_ucnt_add1_other: "u \<noteq> t \<Longrightarrow> Mapping.lookup (ucnt_add1 t c) u = Mapping.lookup c u"
  by (simp add: ucnt_add1_def lookup_update' split: option.splits)

lemma lookup_ucnt_del1_other: "u \<noteq> t \<Longrightarrow> Mapping.lookup (ucnt_del1 t c) u = Mapping.lookup c u"
  by (simp add: ucnt_del1_def lookup_update' lookup_delete split: option.splits)

lemma fold_filter_if: "fold F (filter P xs) b = fold (\<lambda>t acc. if P t then F t acc else acc) xs b"
  by (induct xs arbitrary: b) simp_all

lemma cnt_ins_fold_eq:
  "distinct xs \<Longrightarrow> cnt_ins_fold F xs c b =
     (fold ucnt_add1 xs c, fold F (filter (\<lambda>t. Mapping.lookup c t = None) xs) b)"
proof (induct xs arbitrary: c b)
  case (Cons t xs)
  have same: "\<And>b'. fold (\<lambda>u acc. if Mapping.lookup (ucnt_add1 t c) u = None then F u acc else acc) xs b'
      = fold (\<lambda>u acc. if Mapping.lookup c u = None then F u acc else acc) xs b'"
    using Cons.prems by (intro fold_cong refl) (metis distinct.simps(2) lookup_ucnt_add1_other)
  show ?case
    using Cons same
    by (auto simp: cnt_ins_fold_def ucnt_add1_def fold_filter_if split: option.splits)
qed (simp add: cnt_ins_fold_def)

lemma cnt_del_fold_eq:
  "distinct xs \<Longrightarrow> cnt_del_fold F xs c b =
     (fold ucnt_del1 xs c, fold F (filter (\<lambda>t. Mapping.lookup c t = Some 1) xs) b)"
proof (induct xs arbitrary: c b)
  case (Cons t xs)
  have same: "\<And>b'. fold (\<lambda>u acc. if Mapping.lookup (ucnt_del1 t c) u = Some 1 then F u acc else acc) xs b'
      = fold (\<lambda>u acc. if Mapping.lookup c u = Some 1 then F u acc else acc) xs b'"
    using Cons.prems by (intro fold_cong refl) (metis distinct.simps(2) lookup_ucnt_del1_other)
  show ?case
    using Cons same
    by (auto simp: cnt_del_fold_def ucnt_del1_def fold_filter_if split: option.splits)
qed (simp add: cnt_del_fold_def)

lemma distinct_csl_edl: "distinct (csl (X :: event_data list set))"
proof (cases "finite X")
  case True
  then show ?thesis
    using Dense_Unbox.ID_ccompare_ed by (simp add: csl_finite) (subst csorted_list_of_set_split, auto)
qed (simp add: csl_infinite)


subsection \<open>The aggregate with its result\<close>

definition gcache :: "uconstr option \<Rightarrow> daggp \<Rightarrow> ugagg \<Rightarrow> event_data list set" where
  "gcache q p a = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> Set.filter (uqok q) (gvset \<omega> pos a))"

lemma gcache_ugres: "gcache q p a = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> ugres (uqok q) False \<omega> pos a)"
  by (simp add: gcache_def ugres_def gres_gvset split: prod.splits)

text \<open>The table pays where a group's aggregate rarely changes with a tuple, which is MIN and MAX:
  for them a tuple changes its group's value only when it is the group's extreme.  The count, the
  sum and the average change with every tuple, and keeping the table then costs more than building
  it; for those the structure keeps no table, and the read builds it as before.\<close>

definition cachedp :: "daggp \<Rightarrow> bool" where
  "cachedp p = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> fst \<omega> = Formula.Agg_Min \<or> fst \<omega> = Formula.Agg_Max)"

typedef ucache = "{x :: (uconstr option \<times> daggp) \<times> ucnt \<times> ugagg option \<times> event_data list set.
    case x of (k, c, ax, C) \<Rightarrow> cachedp (snd k) \<longrightarrow> (\<forall>a. ax = Some a \<longrightarrow> C = gcache (fst k) (snd k) a)}"
  by (rule exI[of _ "(undefined, Mapping.empty, None, {})"]) simp

lifting_forget mapping.lifting

setup_lifting type_definition_ucache

lift_definition uc_key :: "ucache \<Rightarrow> uconstr option \<times> daggp" is "\<lambda>(k, c, ax, C). k" .
lift_definition uc_cnt :: "ucache \<Rightarrow> ucnt" is "\<lambda>(k, c, ax, C). c" .
lift_definition uc_ax :: "ucache \<Rightarrow> ugagg option" is "\<lambda>(k, c, ax, C). ax" .
lift_definition uc_set :: "ucache \<Rightarrow> event_data list set" is "\<lambda>(k, c, ax, C). C" .

lemma uc_set_gcache: "cachedp (snd (uc_key x)) \<Longrightarrow> uc_ax x = Some a \<Longrightarrow>
    uc_set x = gcache (fst (uc_key x)) (snd (uc_key x)) a"
  by transfer auto

definition cset :: "uconstr option \<Rightarrow> daggp \<Rightarrow> ugagg option \<Rightarrow> event_data list set" where
  "cset q p ax = (case ax of None \<Rightarrow> {} | Some a \<Rightarrow> gcache q p a)"

lift_definition uc_mk :: "uconstr option \<Rightarrow> daggp \<Rightarrow> ucnt \<Rightarrow> ugagg option \<Rightarrow> ucache" is
  "\<lambda>q p c ax. ((q, p), c, ax, cset q p ax)"
  by (simp add: cset_def)

lemma uc_mk[simp]: "uc_cnt (uc_mk q p c ax) = c" "uc_ax (uc_mk q p c ax) = ax"
  by (transfer; simp)+

text \<open>A tuple's step, on the aggregate and its result together: the result changes only at the
  tuple's group, from the group's value before the step to its value after.\<close>

definition cstep :: "(nat \<Rightarrow> (event_data list \<Rightarrow> event_data) \<Rightarrow> event_data list \<Rightarrow> ugagg option \<Rightarrow>
    ugagg option) \<Rightarrow> uconstr option \<Rightarrow> daggp \<Rightarrow> event_data list \<Rightarrow>
    ugagg option \<times> event_data list set \<Rightarrow> ugagg option \<times> event_data list set" where
  "cstep S q p t axC = (case axC of (ax, C) \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     (case ax of None \<Rightarrow> (None, C)
      | Some a \<Rightarrow> (case S k (umeval_trm f) t (Some a) of None \<Rightarrow> (None, C)
         | Some a' \<Rightarrow> (Some a', cupd (uqok q) pos (drop k t) (gval \<omega> a (drop k t))
              (gval \<omega> a' (drop k t)) C)))))"

definition cinv :: "uconstr option \<Rightarrow> daggp \<Rightarrow> ugagg option \<times> event_data list set \<Rightarrow> bool" where
  "cinv q p axC = (\<forall>a. fst axC = Some a \<longrightarrow> snd axC = gcache q p a)"

lemma cstep_fst: "fst (cstep S q p t axC) = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
    (case fst axC of None \<Rightarrow> None | Some a \<Rightarrow> S k (umeval_trm f) t (Some a)))"
  by (auto simp: cstep_def split: prod.splits option.splits)

lemma cstep_cinv:
  assumes loc: "\<And>\<omega> k ev t a a' h. S k ev t (Some a) = Some a' \<Longrightarrow> h \<noteq> drop k t \<Longrightarrow>
      gval \<omega> a' h = gval \<omega> a h"
    and inv: "cinv q p axC"
  shows "cinv q p (cstep S q p t axC)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  obtain ax C where axC: "axC = (ax, C)" by (cases axC)
  show ?thesis
  proof (cases ax)
    case None
    then show ?thesis by (simp add: cstep_def cinv_def p axC)
  next
    case (Some a)
    then have C: "C = gcache q p a" using inv by (simp add: cinv_def axC)
    show ?thesis
    proof (cases "S k (umeval_trm f) t (Some a)")
      case None
      then show ?thesis using Some by (simp add: cstep_def cinv_def p axC)
    next
      case (Some a')
      then show ?thesis using \<open>ax = Some a\<close> C cupd_gvset[OF loc[OF Some], where Q = "uqok q" and p = pos]
        by (simp add: cstep_def cinv_def p axC gcache_def)
    qed
  qed
qed

lemma gstep_ins_None[simp]: "gstep_ins k ev t None = None"
  by (simp add: gstep_ins_def)

lemma gstep_del_None[simp]: "gstep_del k ev t None = None"
  by (simp add: gstep_del_def)

lemma cstep_ins_fst: "fst (cstep gstep_ins q p t axC) =
    (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gstep_ins k (umeval_trm f) t (fst axC))"
  by (simp add: cstep_fst split: prod.splits option.splits)

lemma cstep_del_fst: "fst (cstep gstep_del q p t axC) =
    (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gstep_del k (umeval_trm f) t (fst axC))"
  by (simp add: cstep_fst split: prod.splits option.splits)

lemma cstep_ins_cinv: "cinv q p axC \<Longrightarrow> cinv q p (cstep gstep_ins q p t axC)"
  by (rule cstep_cinv) (auto intro: gval_gstep_ins)

lemma cstep_del_cinv: "cinv q p axC \<Longrightarrow> cinv q p (cstep gstep_del q p t axC)"
  by (rule cstep_cinv) (auto intro: gval_gstep_del)


lemma fold_cstep_fst:
  "(\<And>t axC. fst (S t axC) = G t (fst axC)) \<Longrightarrow> fst (fold S xs axC) = fold G xs (fst axC)"
  by (induct xs arbitrary: axC) simp_all

lemma fold_cstep_cinv:
  "(\<And>t axC. cinv q p axC \<Longrightarrow> cinv q p (S t axC)) \<Longrightarrow> cinv q p axC \<Longrightarrow> cinv q p (fold S xs axC)"
  by (induct xs arbitrary: axC) simp_all

lemma cinv_cset: "cinv q p (ax, cset q p ax)"
  by (simp add: cinv_def cset_def)

lemma fst_fold_cstep_ins: "fst (fold (cstep gstep_ins q p) xs axC) =
    (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gins k (umeval_trm f) xs (fst axC))"
  by (cases p) (simp add: gins_def fold_cstep_fst[where G = "gstep_ins _ _"] cstep_ins_fst)

lemma fst_fold_cstep_del: "fst (fold (cstep gstep_del q p) xs axC) =
    (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gdel k (umeval_trm f) xs (fst axC))"
  by (cases p) (simp add: gdel_def fold_cstep_fst[where G = "gstep_del _ _"] cstep_del_fst)

text \<open>The window's two steps on the counts, the aggregate and its result, in one pass each.  A
  structure built for another node (its key differs) is rebuilt instead.\<close>

lemma cnt_ins_fold_cinv:
  assumes "\<forall>a. ax = Some a \<longrightarrow> C = gcache q p a"
    and "cnt_ins_fold (cstep gstep_ins q p) (csl X) c (ax, C) = (c', ax', C')"
  shows "\<forall>a. ax' = Some a \<longrightarrow> C' = gcache q p a"
proof -
  have c0: "cinv q p (ax, C)" using assms(1) by (simp add: cinv_def)
  have f: "cinv q p (fold (cstep gstep_ins q p) xs (ax, C))" for xs
    using fold_cstep_cinv[OF cstep_ins_cinv c0] .
  from assms(2) have "fold (cstep gstep_ins q p) (filter (\<lambda>t. Mapping.lookup c t = None) (csl X)) (ax, C) =
      (ax', C')"
    by (simp add: cnt_ins_fold_eq[OF distinct_csl_edl])
  with f[of "filter (\<lambda>t. Mapping.lookup c t = None) (csl X)"] show ?thesis by (simp add: cinv_def)
qed

lemma cnt_del_fold_cinv:
  assumes "\<forall>a. ax = Some a \<longrightarrow> C = gcache q p a"
    and "cnt_del_fold (cstep gstep_del q p) (csl X) c (ax, C) = (c', ax', C')"
  shows "\<forall>a. ax' = Some a \<longrightarrow> C' = gcache q p a"
proof -
  have c0: "cinv q p (ax, C)" using assms(1) by (simp add: cinv_def)
  have f: "cinv q p (fold (cstep gstep_del q p) xs (ax, C))" for xs
    using fold_cstep_cinv[OF cstep_del_cinv c0] .
  from assms(2) have "fold (cstep gstep_del q p) (filter (\<lambda>t. Mapping.lookup c t = Some 1) (csl X)) (ax, C) =
      (ax', C')"
    by (simp add: cnt_del_fold_eq[OF distinct_csl_edl])
  with f[of "filter (\<lambda>t. Mapping.lookup c t = Some 1) (csl X)"] show ?thesis by (simp add: cinv_def)
qed

lemma cset_gcache: "ax = Some a \<Longrightarrow> cset q p ax = gcache q p a"
  by (simp add: cset_def)

lift_definition uc_step_ins :: "uconstr option \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
    ucache \<Rightarrow> ucache" is
  "\<lambda>q p w X x. case x of (key, c, ax, C) \<Rightarrow> (if cachedp p then (if key = (q, p)
     then (case cnt_ins_fold (cstep gstep_ins q p) (csl X) c (ax, C) of (c', axC') \<Rightarrow> (key, c', axC'))
     else ((q, p), ucnt_add X c, uag_ins p w X c ax, cset q p (uag_ins p w X c ax)))
     else (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
       (case cnt_ins_fold (gstep_ins k (umeval_trm f)) (csl X) c ax of (c', ax') \<Rightarrow> ((q, p), c', ax', C))))"
  by (auto split: prod.splits dest: cnt_ins_fold_cinv simp: cset_gcache)

lift_definition uc_step_del :: "uconstr option \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
    ucache \<Rightarrow> ucache" is
  "\<lambda>q p w X x. case x of (key, c, ax, C) \<Rightarrow> (if cachedp p then (if key = (q, p)
     then (case cnt_del_fold (cstep gstep_del q p) (csl X) c (ax, C) of (c', axC') \<Rightarrow> (key, c', axC'))
     else ((q, p), ucnt_del X c, uag_del p w X c ax, cset q p (uag_del p w X c ax)))
     else (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
       (case cnt_del_fold (gstep_del k (umeval_trm f)) (csl X) c ax of (c', ax') \<Rightarrow> ((q, p), c', ax', C))))"
  by (auto split: prod.splits dest: cnt_del_fold_cinv simp: cset_gcache)

lemma uc_step_ins_cnt[simp]: "uc_cnt (uc_step_ins q p w X x) = ucnt_add X (uc_cnt x)"
proof -
  obtain key c ax C where r: "Rep_ucache x = (key, c, ax, C)" by (cases "Rep_ucache x")
  show ?thesis
    by (simp add: uc_cnt.rep_eq uc_step_ins.rep_eq r cnt_ins_fold_eq[OF distinct_csl_edl] ucnt_add_def
        split: prod.splits)
qed

lemma uc_step_ins_ax[simp]: "uc_ax (uc_step_ins q p w X x) = uag_ins p w X (uc_cnt x) (uc_ax x)"
proof -
  obtain key c ax C where r: "Rep_ucache x = (key, c, ax, C)" by (cases "Rep_ucache x")
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  have h1: "fst (fold (cstep gstep_ins q p) (filter (\<lambda>t. Mapping.lookup c t = None) (csl X)) (ax, C)) =
      uag_ins p w X c ax"
    by (simp add: fst_fold_cstep_ins uag_ins_def)
  have h2: "fold (gstep_ins k (umeval_trm f)) (filter (\<lambda>t. Mapping.lookup c t = None) (csl X)) ax =
      uag_ins p w X c ax"
    by (simp add: p uag_ins_def gins_def)
  show ?thesis
  proof (cases "cachedp p")
    case True
    with h1 show ?thesis
      by (simp add: uc_ax.rep_eq uc_cnt.rep_eq uc_step_ins.rep_eq r cnt_ins_fold_eq[OF distinct_csl_edl]
          split: prod.splits) (metis fst_conv)
  next
    case False
    with h2 show ?thesis
      by (simp add: uc_ax.rep_eq uc_cnt.rep_eq uc_step_ins.rep_eq r p cnt_ins_fold_eq[OF distinct_csl_edl]
          split: prod.splits)
  qed
qed

lemma uc_step_del_cnt[simp]: "uc_cnt (uc_step_del q p w X x) = ucnt_del X (uc_cnt x)"
proof -
  obtain key c ax C where r: "Rep_ucache x = (key, c, ax, C)" by (cases "Rep_ucache x")
  show ?thesis
    by (simp add: uc_cnt.rep_eq uc_step_del.rep_eq r cnt_del_fold_eq[OF distinct_csl_edl] ucnt_del_def
        split: prod.splits)
qed

lemma uc_step_del_ax[simp]: "uc_ax (uc_step_del q p w X x) = uag_del p w X (uc_cnt x) (uc_ax x)"
proof -
  obtain key c ax C where r: "Rep_ucache x = (key, c, ax, C)" by (cases "Rep_ucache x")
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  have h1: "fst (fold (cstep gstep_del q p) (filter (\<lambda>t. Mapping.lookup c t = Some 1) (csl X)) (ax, C)) =
      uag_del p w X c ax"
    by (simp add: fst_fold_cstep_del uag_del_def)
  have h2: "fold (gstep_del k (umeval_trm f)) (filter (\<lambda>t. Mapping.lookup c t = Some 1) (csl X)) ax =
      uag_del p w X c ax"
    by (simp add: p uag_del_def gdel_def)
  show ?thesis
  proof (cases "cachedp p")
    case True
    with h1 show ?thesis
      by (simp add: uc_ax.rep_eq uc_cnt.rep_eq uc_step_del.rep_eq r cnt_del_fold_eq[OF distinct_csl_edl]
          split: prod.splits) (metis fst_conv)
  next
    case False
    with h2 show ?thesis
      by (simp add: uc_ax.rep_eq uc_cnt.rep_eq uc_step_del.rep_eq r p cnt_del_fold_eq[OF distinct_csl_edl]
          split: prod.splits)
  qed
qed



lifting_update mapping.lifting

subsection \<open>The result, read off\<close>

fun gempty :: "'b gagg \<Rightarrow> bool" where
  "gempty (GCnt m) = Mapping.is_empty m"
| "gempty (GSum m) = Mapping.is_empty m"
| "gempty (GRank m ty) = Mapping.is_empty m"

lemma gempty_gkeys: "gempty a \<longleftrightarrow> gkeys a = {}"
  by (cases a) (simp_all add: Mapping.is_empty_def)

definition uc_res :: "uconstr option \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> ucache \<Rightarrow> event_data list set" where
  "uc_res q p w x = (case uc_ax x of
     None \<Rightarrow> ufilt q (udagg_p p (Mapping.keys (uc_cnt x)))
   | Some a \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> if uc_key x = (q, p) \<and> cachedp p
       then (if g0 \<and> gempty a then ufilt q {[eval_agg_op \<omega> {}]} else uc_set x)
       else ugres (uqok q) g0 \<omega> pos a))"

lemma uc_res: "uc_res q p w x = uag_res q p w (uc_cnt x) (uc_ax x)"
  by (auto simp: uc_res_def uag_res_code ugres_def gres_gvset ufilt_def uc_set_gcache gcache_def
      gempty_gkeys split: option.splits prod.splits)

subsection \<open>The window over it\<close>

type_synonym uswaggc = "(ts \<times> (ts \<times> event_data list set) queue \<times> (ts \<times> event_data list set) queue) \<times>
  ucache"

fun ucs :: "uswaggc \<Rightarrow> uswagg" where
  "ucs ((t, pend, win), x) = ((t, pend, win, uc_cnt x), uc_ax x)"

function usc_move :: "args \<Rightarrow> daggp \<Rightarrow> uconstr option \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data list set) queue \<Rightarrow>
    (ts \<times> event_data list set) queue \<Rightarrow> ucache \<Rightarrow>
    (ts \<times> event_data list set) queue \<times> (ts \<times> event_data list set) queue \<times> ucache" where
  "usc_move args p q nt pend win x =
     (case safe_hd pend of
        (None, pend') \<Rightarrow> (pend', win, x)
      | (Some e, pend') \<Rightarrow>
        (if memL (args_ivl args) (nt - fst e)
         then (if memR (args_ivl args) (nt - fst e)
               then usc_move args p q nt (tl_queue pend') (append_queue e win)
                      (uc_step_ins q p (args_n args) (snd e) x)
               else usc_move args p q nt (tl_queue pend') win x)
         else (pend', win, x)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, p, q, nt, pend, win, x). length (linearize pend))")
     (fastforce split: prod.splits)+

declare usc_move.simps[simp del]

function usc_expire :: "args \<Rightarrow> daggp \<Rightarrow> uconstr option \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data list set) queue \<Rightarrow>
    ucache \<Rightarrow> (ts \<times> event_data list set) queue \<times> ucache" where
  "usc_expire args p q nt win x =
     (case safe_hd win of
        (None, win') \<Rightarrow> (win', x)
      | (Some e, win') \<Rightarrow>
        (if memR (args_ivl args) (nt - fst e) then (win', x)
         else usc_expire args p q nt (tl_queue win') (uc_step_del q p (args_n args) (snd e) x)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, p, q, nt, win, x). length (linearize win))")
     (fastforce split: prod.splits)+

declare usc_expire.simps[simp del]

lemma usc_move: "usa_move args p nt pend win (uc_cnt x) (uc_ax x) =
    (case usc_move args p q nt pend win x of (pend', win', x') \<Rightarrow> (pend', win', uc_cnt x', uc_ax x'))"
proof (induct args p q nt pend win x rule: usc_move.induct)
  case (1 args p q nt pend win x)
  obtain h pend' where hd: "safe_hd pend = (h, pend')" by (cases "safe_hd pend")
  show ?case
  proof (cases h)
    case None
    then show ?thesis by (subst usa_move.simps, subst usc_move.simps) (simp add: hd)
  next
    case (Some e)
    have IH1: "memL (args_ivl args) (nt - fst e) \<Longrightarrow> memR (args_ivl args) (nt - fst e) \<Longrightarrow>
        usa_move args p nt (tl_queue pend') (append_queue e win)
          (uc_cnt (uc_step_ins q p (args_n args) (snd e) x)) (uc_ax (uc_step_ins q p (args_n args) (snd e) x)) =
        (case usc_move args p q nt (tl_queue pend') (append_queue e win) (uc_step_ins q p (args_n args) (snd e) x)
         of (pend', win', x') \<Rightarrow> (pend', win', uc_cnt x', uc_ax x'))"
      using 1(1)[OF hd[symmetric] Some] by blast
    have IH2: "memL (args_ivl args) (nt - fst e) \<Longrightarrow> \<not> memR (args_ivl args) (nt - fst e) \<Longrightarrow>
        usa_move args p nt (tl_queue pend') win (uc_cnt x) (uc_ax x) =
        (case usc_move args p q nt (tl_queue pend') win x of (pend', win', x') \<Rightarrow> (pend', win', uc_cnt x', uc_ax x'))"
      using 1(2)[OF hd[symmetric] Some] by blast
    show ?thesis
      using IH1 IH2 by (subst usa_move.simps, subst usc_move.simps) (simp add: hd Some)
  qed
qed

lemma usc_expire: "usa_expire args p nt win (uc_cnt x) (uc_ax x) =
    (case usc_expire args p q nt win x of (win', x') \<Rightarrow> (win', uc_cnt x', uc_ax x'))"
proof (induct args p q nt win x rule: usc_expire.induct)
  case (1 args p q nt win x)
  obtain h win' where hd: "safe_hd win = (h, win')" by (cases "safe_hd win")
  show ?case
  proof (cases h)
    case None
    then show ?thesis by (subst usa_expire.simps, subst usc_expire.simps) (simp add: hd)
  next
    case (Some e)
    have IH: "\<not> memR (args_ivl args) (nt - fst e) \<Longrightarrow>
        usa_expire args p nt (tl_queue win') (uc_cnt (uc_step_del q p (args_n args) (snd e) x))
          (uc_ax (uc_step_del q p (args_n args) (snd e) x)) =
        (case usc_expire args p q nt (tl_queue win') (uc_step_del q p (args_n args) (snd e) x)
         of (win', x') \<Rightarrow> (win', uc_cnt x', uc_ax x'))"
      using 1[OF hd[symmetric] Some] by blast
    show ?thesis
      using IH by (subst usa_expire.simps, subst usc_expire.simps) (simp add: hd Some)
  qed
qed

definition usc_init :: "args \<Rightarrow> daggp \<Rightarrow> uconstr option \<Rightarrow> uswaggc" where
  "usc_init args p q = ((0, empty_queue, empty_queue), uc_mk q p Mapping.empty (ag_init p (args_n args)))"

definition usc_add_new_ts :: "args \<Rightarrow> daggp \<Rightarrow> uconstr option \<Rightarrow> ts \<Rightarrow> uswaggc \<Rightarrow> uswaggc" where
  "usc_add_new_ts args p q nt aux = (case aux of ((t, pend, win), x) \<Rightarrow>
     (case usc_move args p q nt pend win x of (pend', win', x') \<Rightarrow>
      (case usc_expire args p q nt win' x' of (win'', x'') \<Rightarrow> ((nt, pend', win''), x''))))"

definition usc_join :: "args \<Rightarrow> daggp \<Rightarrow> uconstr option \<Rightarrow> event_data list set \<Rightarrow> uswaggc \<Rightarrow> uswaggc" where
  "usc_join args p q X aux = (case aux of ((t, pend, win), x) \<Rightarrow>
     (if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then aux
      else ((t, empty_queue, empty_queue), uc_mk q p Mapping.empty (ag_init p (args_n args)))))"

definition usc_add_new_table :: "args \<Rightarrow> daggp \<Rightarrow> uconstr option \<Rightarrow> event_data list set \<Rightarrow>
    uswaggc \<Rightarrow> uswaggc" where
  "usc_add_new_table args p q X aux = (case aux of ((t, pend, win), x) \<Rightarrow>
     (if memL (args_ivl args) 0
      then ((t, pend, append_queue (t, X) win), uc_step_ins q p (args_n args) X x)
      else ((t, append_queue (t, X) pend, win), x)))"

definition usc_result :: "uconstr option \<Rightarrow> args \<Rightarrow> daggp \<Rightarrow> uswaggc \<Rightarrow> event_data list set" where
  "usc_result q args p aux = (case aux of ((t, pend, win), x) \<Rightarrow> uc_res q p (args_n args) x)"

lemma usc_init_ucs: "ucs (usc_init args p q) = usa_init args p"
  by (simp add: usc_init_def usa_init_def usw_init_def)

lemma usc_add_new_ts_ucs: "ucs (usc_add_new_ts args p q nt aux) = usa_add_new_ts args p nt (ucs aux)"
proof -
  obtain t pend win x where aux: "aux = ((t, pend, win), x)" by (cases aux) auto
  obtain pend' win' x' where m: "usc_move args p q nt pend win x = (pend', win', x')"
    by (cases "usc_move args p q nt pend win x") auto
  obtain win'' x'' where e: "usc_expire args p q nt win' x' = (win'', x'')"
    by (cases "usc_expire args p q nt win' x'") auto
  have "usa_move args p nt pend win (uc_cnt x) (uc_ax x) = (pend', win', uc_cnt x', uc_ax x')"
    using usc_move[of args p nt pend win x q] m by simp
  moreover have "usa_expire args p nt win' (uc_cnt x') (uc_ax x') = (win'', uc_cnt x'', uc_ax x'')"
    using usc_expire[of args p nt win' x' q] e by simp
  ultimately show ?thesis
    by (simp add: aux m e usc_add_new_ts_def usa_add_new_ts_def)
qed

lemma usc_join_ucs: "ucs (usc_join args p q X aux) = usa_join args p X (ucs aux)"
  by (cases aux) (auto simp: usc_join_def usa_join_def usw_join_def)

lemma usc_add_new_table_ucs:
  "ucs (usc_add_new_table args p q X aux) = usa_add_new_table args p X (ucs aux)"
  by (cases aux) (auto simp: usc_add_new_table_def usa_add_new_table_def)

lemma usc_result_ucs: "usc_result q args p aux = usa_result q args p (ucs aux)"
  by (cases aux) (auto simp: usc_result_def usa_result_def uc_res)

(*<*)
end
(*>*)

(*<*)
theory Agg_Cache
  imports Until_Agg
begin
(*>*)



section \<open>The window's aggregate with its result table\<close>

text \<open>
  A fused aggregation over a past window (@{const sa_result}) reads its result at every time
  point, and the read builds the table of all groups afresh from the aggregate's mapping, one
  insertion per group.  From one time point to the next only the groups of the tuples entering
  and leaving the window can change -- and for MIN and MAX few of those do.  This theory keeps the
  result table next to the aggregate and updates it at the touched groups only.

  The aggregate and its result are kept together in the type @{text ucache}, whose invariant is
  that the table is the (filtered) result of the aggregate, so that reading it off is correct on
  every value of the type and no invariant has to be carried through the evaluator.  The table is
  built for one node, its key: a structure built for a different constraint or aggregation is
  rebuilt by the first step.  The window over it, @{text uswaggc}, is the window of
  @{theory MFODL_Monitor_Exec.Since_Agg} with the count set over a mapping
  (Section ``The executable fused Since window'' of @{theory MFODL_Monitor_Exec.Since_Agg}) and the aggregate moved into the new type, and
  it maps onto that window (@{text rsc}) with every operation commuting.

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
  and @{text cnt_del_fold} are that pass.\<close>

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
    using ID_ccompare_ed by (simp add: csl_finite) (subst csorted_list_of_set_split, auto)
qed (simp add: csl_infinite)

subsection \<open>The aggregate with its result\<close>

definition gcache :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> ugagg \<Rightarrow> event_data list set" where
  "gcache q p a = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> Set.filter (uqok q) (gvset \<omega> pos a))"

lemma gcache_ugres: "gcache q p a = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> ugres (uqok q) False \<omega> pos a)"
  by (simp add: gcache_def ugres_def gres_gvset split: prod.splits)

text \<open>The table pays where a group's aggregate rarely changes with a tuple, which is MIN and MAX:
  for them a tuple changes its group's value only when it is the group's extreme.  The count, the
  sum and the average change with every tuple, and keeping the table then costs more than building
  it; for those the structure keeps no table, and the read builds it as before.\<close>

definition cachedp :: "eaggp \<Rightarrow> bool" where
  "cachedp p = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> fst \<omega> = Formula.Agg_Min \<or> fst \<omega> = Formula.Agg_Max)"

subsection \<open>The count set, by group\<close>

text \<open>For a count or a sum, the count set can be kept split by group: an outer map from each group
  to its summary (the count or the count and the sum) together with the count set of the group's
  tuples.  A tuple's step then descends the outer map once and the group's small map once, where
  the flat representation descends the count set and the aggregate's map separately.  The flat
  count set and the aggregate are the projections @{text nflat} and @{text nsumm}.\<close>

type_synonym 'a nmap = "(event_data list, 'a \<times> ucnt) mapping"

definition nflat :: "nat \<Rightarrow> 'a nmap \<Rightarrow> ucnt" where
  "nflat k M = Mapping.Mapping (\<lambda>t. case Mapping.lookup M (drop k t) of None \<Rightarrow> None
     | Some aI \<Rightarrow> Mapping.lookup (snd aI) t)"

lemma lookup_nflat: "Mapping.lookup (nflat k M) t = (case Mapping.lookup M (drop k t) of None \<Rightarrow> None
     | Some aI \<Rightarrow> Mapping.lookup (snd aI) t)"
  unfolding nflat_def by (simp add: Mapping.lookup.abs_eq)

definition nsumm :: "'a nmap \<Rightarrow> (event_data list, 'a) mapping" where
  "nsumm M = Mapping.map_values (\<lambda>_ v. fst v) M"

lemma lookup_nsumm: "Mapping.lookup (nsumm M) g = map_option fst (Mapping.lookup M g)"
  by (simp add: nsumm_def lookup_map_values)

text \<open>A tuple entering: its count, and the summary of its group when it is new.\<close>

definition nins :: "nat \<Rightarrow> (event_data list \<Rightarrow> 'a) \<Rightarrow> (event_data list \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    event_data list \<Rightarrow> 'a nmap \<Rightarrow> 'a nmap" where
  "nins k si su t M = (let g = drop k t in case Mapping.lookup M g of
     None \<Rightarrow> Mapping.update g (si t, Mapping.update t 1 Mapping.empty) M
   | Some (a, I) \<Rightarrow> (case Mapping.lookup I t of
       None \<Rightarrow> Mapping.update g (su t a, Mapping.update t 1 I) M
     | Some m \<Rightarrow> Mapping.update g (a, Mapping.update t (m + 1) I) M))"

definition ndel :: "nat \<Rightarrow> (event_data list \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> event_data list \<Rightarrow> 'a nmap \<Rightarrow> 'a nmap" where
  "ndel k sd t M = (let g = drop k t in case Mapping.lookup M g of
     None \<Rightarrow> M
   | Some (a, I) \<Rightarrow> (case Mapping.lookup I t of
       None \<Rightarrow> M
     | Some m \<Rightarrow> (if m \<le> 1 then (let I' = Mapping.delete t I in
          if Mapping.is_empty I' then Mapping.delete g M else Mapping.update g (sd t a, I') M)
        else Mapping.update g (a, Mapping.update t (m - 1) I) M)))"

lemma nflat_nins: "nflat k (nins k si su t M) = ucnt_add1 t (nflat k M)"
  by (rule mapping_eqI)
    (auto simp: lookup_nflat nins_def ucnt_add1_def Let_def lookup_update'
      split: option.splits prod.splits)

definition gupd :: "nat \<Rightarrow> (event_data list \<Rightarrow> 'a) \<Rightarrow> (event_data list \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    event_data list \<Rightarrow> (event_data list, 'a) mapping \<Rightarrow> (event_data list, 'a) mapping" where
  "gupd k si su t m = (let g = drop k t in case Mapping.lookup m g of
     None \<Rightarrow> Mapping.update g (si t) m | Some a \<Rightarrow> Mapping.update g (su t a) m)"

lemma nsumm_nins: "nsumm (nins k si su t M) =
    (if Mapping.lookup (nflat k M) t = None then gupd k si su t (nsumm M) else nsumm M)"
  by (rule mapping_eqI)
    (auto simp: lookup_nflat lookup_nsumm nins_def gupd_def Let_def lookup_update'
      split: option.splits prod.splits)

lemma nflat_ndel: "nflat k (ndel k sd t M) = ucnt_del1 t (nflat k M)"
proof (rule mapping_eqI)
  fix u
  show "Mapping.lookup (nflat k (ndel k sd t M)) u = Mapping.lookup (ucnt_del1 t (nflat k M)) u"
  proof (cases "Mapping.lookup M (drop k t)")
    case None
    then show ?thesis
      by (auto simp: lookup_nflat ndel_def ucnt_del1_def Let_def split: option.splits)
  next
    case (Some aI)
    obtain a I where aI: "aI = (a, I)" by (cases aI)
    show ?thesis
    proof (cases "Mapping.lookup I t")
      case None
      then show ?thesis using Some aI
        by (auto simp: lookup_nflat ndel_def ucnt_del1_def Let_def split: option.splits)
    next
      case (Some m)
      show ?thesis
      proof (cases "m \<le> 1")
        case True
        show ?thesis
        proof (cases "Mapping.is_empty (Mapping.delete t I)")
          case True
          then have "Mapping.lookup I u = None" if "u \<noteq> t"
          proof -
            have "Mapping.lookup (Mapping.delete t I) u = None"
              using True by (simp add: Mapping.is_empty_def Mapping.keys_dom_lookup)
            with that show ?thesis by (simp add: lookup_delete)
          qed
          then show ?thesis using \<open>Mapping.lookup M (drop k t) = Some aI\<close> aI Some \<open>m \<le> 1\<close> True
            by (auto simp: lookup_nflat ndel_def ucnt_del1_def Let_def lookup_delete lookup_update'
                split: option.splits)
        next
          case False
          then show ?thesis using \<open>Mapping.lookup M (drop k t) = Some aI\<close> aI Some \<open>m \<le> 1\<close>
            by (auto simp: lookup_nflat ndel_def ucnt_del1_def Let_def lookup_delete lookup_update'
                split: option.splits)
        qed
      next
        case False
        then show ?thesis using \<open>Mapping.lookup M (drop k t) = Some aI\<close> aI Some
          by (auto simp: lookup_nflat ndel_def ucnt_del1_def Let_def lookup_delete lookup_update'
              split: option.splits)
      qed
    qed
  qed
qed

text \<open>The summary of a group, when its tuples leave: the step of the aggregate's deletion.  Its
  agreement with the summaries rests on the invariant: every tuple lies in its own group, every
  count is positive, and a summary counts its group's tuples.\<close>

definition gdn :: "nat \<Rightarrow> (event_data list \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow>
    event_data list \<Rightarrow> (event_data list, 'a) mapping \<Rightarrow> (event_data list, 'a) mapping" where
  "gdn k sd nc t m = (let g = drop k t in case Mapping.lookup m g of
     None \<Rightarrow> m | Some a \<Rightarrow> if nc a = 1 then Mapping.delete g m else Mapping.update g (sd t a) m)"

definition ninv :: "nat \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a nmap \<Rightarrow> bool" where
  "ninv k nc M = (finite (Mapping.keys M) \<and> (\<forall>g a I. Mapping.lookup M g = Some (a, I) \<longrightarrow>
     (\<forall>t \<in> Mapping.keys I. drop k t = g) \<and> finite (Mapping.keys I) \<and>
     nc a = card (Mapping.keys I) \<and> (\<forall>t m. Mapping.lookup I t = Some m \<longrightarrow> 1 \<le> m)))"

lemma ninv_empty[simp]: "ninv k nc Mapping.empty"
  by (simp add: ninv_def)

lemma keys_lookup_Some: "Mapping.lookup I t = Some m \<Longrightarrow> t \<in> Mapping.keys I"
  by (simp add: Mapping.keys_dom_lookup domI)

lemma is_empty_delete_iff:
  assumes "finite (Mapping.keys I)" "t \<in> Mapping.keys I"
  shows "Mapping.is_empty (Mapping.delete t I) \<longleftrightarrow> card (Mapping.keys I) = 1"
proof -
  have "Mapping.keys (Mapping.delete t I) = Mapping.keys I - {t}" by simp
  then show ?thesis using assms
    by (auto simp: Mapping.is_empty_def card_Suc_eq card_1_singleton_iff)
qed

lemma nsumm_ndel:
  assumes inv: "ninv k nc M"
  shows "nsumm (ndel k sd t M) =
    (if Mapping.lookup (nflat k M) t = Some 1 then gdn k sd nc t (nsumm M) else nsumm M)"
proof (cases "Mapping.lookup M (drop k t)")
  case None
  then show ?thesis by (simp add: ndel_def lookup_nflat)
next
  case (Some aI)
  obtain a I where aI: "aI = (a, I)" by (cases aI)
  have MI: "Mapping.lookup M (drop k t) = Some (a, I)" using Some aI by simp
  have fin: "finite (Mapping.keys I)" and cnt: "nc a = card (Mapping.keys I)"
    and pos: "\<And>u m. Mapping.lookup I u = Some m \<Longrightarrow> 1 \<le> m"
    using inv MI unfolding ninv_def by blast+
  show ?thesis
  proof (cases "Mapping.lookup I t")
    case None
    then show ?thesis using MI by (simp add: ndel_def lookup_nflat)
  next
    case (Some m)
    have tI: "t \<in> Mapping.keys I" using Some by (rule keys_lookup_Some)
    show ?thesis
    proof (cases "m \<le> 1")
      case True
      then have m1: "m = 1" using pos[OF Some] by simp
      have e: "Mapping.is_empty (Mapping.delete t I) \<longleftrightarrow> nc a = 1"
        using is_empty_delete_iff[OF fin tI] cnt by simp
      show ?thesis
        by (rule mapping_eqI)
          (use MI Some m1 e in \<open>auto simp: ndel_def lookup_nflat gdn_def lookup_nsumm Let_def
            lookup_delete lookup_update' split: option.splits\<close>)
    next
      case False
      then show ?thesis
        by (intro mapping_eqI)
          (use MI Some in \<open>auto simp: ndel_def lookup_nflat lookup_nsumm lookup_update'\<close>)
    qed
  qed
qed

lemma ninv_nins:
  assumes inv: "ninv k nc M" and si: "nc (si t) = 1" and su: "\<And>a. nc (su t a) = Suc (nc a)"
  shows "ninv k nc (nins k si su t M)"
  unfolding ninv_def
proof (rule conjI)
  show "finite (Mapping.keys (nins k si su t M))"
    using inv by (auto simp: ninv_def nins_def Let_def split: option.splits prod.splits)
next
  show "\<forall>g a I. Mapping.lookup (nins k si su t M) g = Some (a, I) \<longrightarrow>
     (\<forall>t \<in> Mapping.keys I. drop k t = g) \<and> finite (Mapping.keys I) \<and>
     nc a = card (Mapping.keys I) \<and> (\<forall>t m. Mapping.lookup I t = Some m \<longrightarrow> 1 \<le> m)"
  proof (intro allI impI)
  fix g a' I'
  assume L: "Mapping.lookup (nins k si su t M) g = Some (a', I')"
  show "(\<forall>u \<in> Mapping.keys I'. drop k u = g) \<and> finite (Mapping.keys I') \<and>
      nc a' = card (Mapping.keys I') \<and> (\<forall>u m. Mapping.lookup I' u = Some m \<longrightarrow> 1 \<le> m)"
  proof (cases "g = drop k t")
    case False
    then have "Mapping.lookup M g = Some (a', I')"
      using L by (auto simp: nins_def Let_def lookup_update' split: option.splits)
    then show ?thesis using inv unfolding ninv_def by blast
  next
    case gt: True
    show ?thesis
    proof (cases "Mapping.lookup M g")
      case None
      then show ?thesis using L gt si by (auto simp: nins_def Let_def lookup_update' split: if_splits)
    next
      case (Some aI)
      obtain a I where aI: "aI = (a, I)" by (cases aI)
      have MI: "Mapping.lookup M g = Some (a, I)" using Some aI by simp
      have grp: "\<forall>u \<in> Mapping.keys I. drop k u = g" and fin: "finite (Mapping.keys I)"
        and cnt: "nc a = card (Mapping.keys I)" and pos: "\<And>u m. Mapping.lookup I u = Some m \<Longrightarrow> 1 \<le> m"
        using inv MI unfolding ninv_def by blast+
      show ?thesis
      proof (cases "Mapping.lookup I t")
        case None
        then have "t \<notin> Mapping.keys I" by (simp add: Mapping.keys_dom_lookup domIff)
        then show ?thesis using L gt MI None grp fin cnt pos su
          by (auto simp: nins_def Let_def lookup_update' split: if_splits)
      next
        case (Some m)
        have tI: "t \<in> Mapping.keys I" using Some by (rule keys_lookup_Some)
        have aI': "a' = a" "I' = Mapping.update t (m + 1) I"
          using L gt MI Some by (auto simp: nins_def Let_def lookup_update')
        have ks: "Mapping.keys I' = Mapping.keys I" using tI by (auto simp: aI')
        show ?thesis
          unfolding ks using grp fin cnt pos aI' by (auto simp: lookup_update' split: if_splits)
      qed
    qed
  qed
qed
qed

lemma ninv_ndel:
  assumes inv: "ninv k nc M" and sd: "\<And>a. nc (sd t a) = nc a - 1"
  shows "ninv k nc (ndel k sd t M)"
  unfolding ninv_def
proof (rule conjI)
  show "finite (Mapping.keys (ndel k sd t M))"
    using inv by (auto simp: ninv_def ndel_def Let_def split: option.splits prod.splits)
next
  show "\<forall>g a I. Mapping.lookup (ndel k sd t M) g = Some (a, I) \<longrightarrow>
     (\<forall>t \<in> Mapping.keys I. drop k t = g) \<and> finite (Mapping.keys I) \<and>
     nc a = card (Mapping.keys I) \<and> (\<forall>t m. Mapping.lookup I t = Some m \<longrightarrow> 1 \<le> m)"
  proof (intro allI impI)
  fix g a' I'
  assume L: "Mapping.lookup (ndel k sd t M) g = Some (a', I')"
  show "(\<forall>u \<in> Mapping.keys I'. drop k u = g) \<and> finite (Mapping.keys I') \<and>
      nc a' = card (Mapping.keys I') \<and> (\<forall>u m. Mapping.lookup I' u = Some m \<longrightarrow> 1 \<le> m)"
  proof (cases "g = drop k t")
    case False
    then have "Mapping.lookup M g = Some (a', I')"
      using L by (auto simp: ndel_def Let_def lookup_update' lookup_delete split: option.splits if_splits)
    then show ?thesis using inv unfolding ninv_def by blast
  next
    case gt: True
    show ?thesis
    proof (cases "Mapping.lookup M g")
      case None
      then show ?thesis using L gt by (simp add: ndel_def)
    next
      case (Some aI)
      obtain a I where aI: "aI = (a, I)" by (cases aI)
      have MI: "Mapping.lookup M g = Some (a, I)" using Some aI by simp
      have grp: "\<forall>u \<in> Mapping.keys I. drop k u = g" and fin: "finite (Mapping.keys I)"
        and cnt: "nc a = card (Mapping.keys I)" and pos: "\<And>u m. Mapping.lookup I u = Some m \<Longrightarrow> 1 \<le> m"
        using inv MI unfolding ninv_def by blast+
      show ?thesis
      proof (cases "Mapping.lookup I t")
        case None
        then show ?thesis using L gt MI grp fin cnt pos by (simp add: ndel_def)
      next
        case (Some m)
        have tI: "t \<in> Mapping.keys I" using Some by (rule keys_lookup_Some)
        show ?thesis
        proof (cases "m \<le> 1")
          case True
          have ne: "\<not> Mapping.is_empty (Mapping.delete t I)"
            using L gt MI Some True by (auto simp: ndel_def Let_def lookup_delete split: if_splits)
          then have aI': "a' = sd t a" "I' = Mapping.delete t I"
            using L gt MI Some True by (auto simp: ndel_def Let_def lookup_update')
          have ks: "Mapping.keys I' = Mapping.keys I - {t}" by (simp add: aI')
          show ?thesis
            unfolding ks
            using grp fin cnt pos tI sd[of a] aI'
            by (auto simp: card_Diff_singleton lookup_delete split: if_splits)
        next
          case False
          then have aI': "a' = a" "I' = Mapping.update t (m - 1) I"
            using L gt MI Some by (auto simp: ndel_def Let_def lookup_update')
          have ks: "Mapping.keys I' = Mapping.keys I" using tI by (auto simp: aI')
          show ?thesis
            unfolding ks
            using grp fin cnt pos False aI' by (auto simp: lookup_update' split: if_splits)
        qed
      qed
    qed
  qed
qed
qed

text \<open>The count set read off in full, for the rare step that has to go back to the flat
  structure: every group's tuples, inserted one by one.\<close>

definition nflat_x :: "'a nmap \<Rightarrow> ucnt" where
  "nflat_x M = fold (\<lambda>g c. case Mapping.lookup M g of None \<Rightarrow> c
     | Some aI \<Rightarrow> fold (\<lambda>t c. case Mapping.lookup (snd aI) t of None \<Rightarrow> c
         | Some n \<Rightarrow> Mapping.update t n c) (csl (Mapping.keys (snd aI))) c)
     (csl (Mapping.keys M)) Mapping.empty"

lemma lookup_fold_inner:
  "Mapping.lookup (fold (\<lambda>t c. case Mapping.lookup I t of None \<Rightarrow> c
     | Some n \<Rightarrow> Mapping.update t n c) xs c) u =
   (if u \<in> set xs \<and> Mapping.lookup I u \<noteq> None then Mapping.lookup I u else Mapping.lookup c u)"
  by (induct xs arbitrary: c) (auto simp: lookup_update' split: option.splits)

lemma in_keys_lookup: "u \<in> Mapping.keys m \<longleftrightarrow> Mapping.lookup m u \<noteq> None"
  by (simp add: Mapping.keys_dom_lookup domIff)

lemma lookup_fold_outer:
  fixes M :: "'x nmap"
  assumes grp: "\<And>g a I u. Mapping.lookup M g = Some (a, I) \<Longrightarrow> u \<in> Mapping.keys I \<Longrightarrow> drop k u = g"
    and fin: "\<And>g a I. Mapping.lookup M g = Some (a, I) \<Longrightarrow> finite (Mapping.keys I)"
  shows "Mapping.lookup (fold (\<lambda>g c. case Mapping.lookup M g of None \<Rightarrow> c
     | Some aI \<Rightarrow> fold (\<lambda>t c. case Mapping.lookup (snd aI) t of None \<Rightarrow> c
         | Some n \<Rightarrow> Mapping.update t n c) (csl (Mapping.keys (snd aI))) c) gs c) u =
   (if drop k u \<in> set gs then (case Mapping.lookup M (drop k u) of None \<Rightarrow> Mapping.lookup c u
      | Some aI \<Rightarrow> (if Mapping.lookup (snd aI) u \<noteq> None then Mapping.lookup (snd aI) u
         else Mapping.lookup c u)) else Mapping.lookup c u)"
proof (induct gs arbitrary: c)
  case (Cons g gs)
  show ?case
  proof (cases "Mapping.lookup M g")
    case None
    then show ?thesis using Cons by (auto split: option.splits)
  next
    case (Some aI)
    obtain a I where aI: "aI = (a, I)" by (cases aI)
    have finI: "finite (Mapping.keys I)" using fin[of g a I] Some aI by simp
    have ks: "set (csl (Mapping.keys I)) = Mapping.keys I" by (rule set_csl_ed[OF finI])
    have other: "Mapping.lookup I u = None" if "drop k u \<noteq> g"
    proof (rule ccontr)
      assume "Mapping.lookup I u \<noteq> None"
      then have "u \<in> Mapping.keys I" by (simp add: in_keys_lookup)
      with grp[of g a I u] Some aI that show False by simp
    qed
    have c': "\<And>c. Mapping.lookup (fold (\<lambda>t c. case Mapping.lookup I t of None \<Rightarrow> c
        | Some n \<Rightarrow> Mapping.update t n c) (csl (Mapping.keys I)) c) u =
      (if Mapping.lookup I u \<noteq> None then Mapping.lookup I u else Mapping.lookup c u)"
      unfolding lookup_fold_inner ks by (simp add: in_keys_lookup)
    show ?thesis
      using Cons.hyps other Some aI c' by (cases "drop k u = g") (auto split: option.splits)
  qed
qed simp

lemma nflat_x:
  assumes "ninv k nc M"
  shows "nflat_x M = nflat k M"
proof (rule mapping_eqI)
  fix u
  have finM: "finite (Mapping.keys M)" using assms by (simp add: ninv_def)
  have grp: "\<And>g a I u. Mapping.lookup M g = Some (a, I) \<Longrightarrow> u \<in> Mapping.keys I \<Longrightarrow> drop k u = g"
    and fin: "\<And>g a I. Mapping.lookup M g = Some (a, I) \<Longrightarrow> finite (Mapping.keys I)"
    using assms unfolding ninv_def by blast+
  have "Mapping.lookup (nflat_x M) u =
    (if drop k u \<in> set (csl (Mapping.keys M)) then (case Mapping.lookup M (drop k u) of
        None \<Rightarrow> Mapping.lookup Mapping.empty u
      | Some aI \<Rightarrow> (if Mapping.lookup (snd aI) u \<noteq> None then Mapping.lookup (snd aI) u
         else Mapping.lookup Mapping.empty u)) else Mapping.lookup Mapping.empty u)"
    unfolding nflat_x_def by (rule lookup_fold_outer[OF grp fin])
  then show "Mapping.lookup (nflat_x M) u = Mapping.lookup (nflat k M) u"
    by (auto simp: set_csl_ed[OF finM] lookup_nflat in_keys_lookup
        split: option.splits)
qed

subsection \<open>The two instances: the count and the count with the sum\<close>

definition cins :: "(event_data list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> event_data list \<Rightarrow> ucnt \<times> 'b \<Rightarrow> ucnt \<times> 'b" where
  "cins F t ca = (case ca of (c, acc) \<Rightarrow> (case Mapping.lookup c t of
       None \<Rightarrow> (Mapping.update t 1 c, F t acc)
     | Some k \<Rightarrow> (Mapping.update t (k + 1) c, acc)))"

definition cdel :: "(event_data list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> event_data list \<Rightarrow> ucnt \<times> 'b \<Rightarrow> ucnt \<times> 'b" where
  "cdel F t ca = (case ca of (c, acc) \<Rightarrow> (case Mapping.lookup c t of
       None \<Rightarrow> (c, acc)
     | Some k \<Rightarrow> (if k \<le> 1 then (Mapping.delete t c, if k = 1 then F t acc else acc)
                 else (Mapping.update t (k - 1) c, acc))))"

lemma cins_eq: "cins F t (c, acc) = (ucnt_add1 t c, if Mapping.lookup c t = None then F t acc else acc)"
  by (simp add: cins_def ucnt_add1_def split: option.splits)

lemma cdel_eq: "cdel F t (c, acc) = (ucnt_del1 t c, if Mapping.lookup c t = Some 1 then F t acc else acc)"
  by (auto simp: cdel_def ucnt_del1_def split: option.splits)

definition ival :: "event_data \<Rightarrow> integer" where
  "ival e = (case e of EInt i \<Rightarrow> i | _ \<Rightarrow> 0)"

definition is_eint :: "event_data \<Rightarrow> bool" where
  "is_eint e = (case e of EInt i \<Rightarrow> True | _ \<Rightarrow> False)"

lemma gstep_ins_GCnt: "gstep_ins k ev t (Some (GCnt m)) = Some (GCnt (gupd k (\<lambda>_. 1) (\<lambda>_ a. Suc a) t m))"
  by (simp add: gstep_ins_def gupd_def Let_def split: option.splits)

lemma gstep_del_GCnt: "gstep_del k ev t (Some (GCnt m)) = Some (GCnt (gdn k (\<lambda>_ a. a - 1) id t m))"
  by (simp add: gstep_del_def gdn_def Let_def split: option.splits)

lemma gstep_ins_GSum: "gstep_ins k ev t (Some (GSum m)) = (if is_eint (ev t)
    then Some (GSum (gupd k (\<lambda>t. (1, ival (ev t))) (\<lambda>t a. (Suc (fst a), snd a + ival (ev t))) t m))
    else None)"
  by (auto simp: gstep_ins_def gupd_def Let_def is_eint_def ival_def split: option.splits event_data.splits)

lemma gstep_del_GSum: "Mapping.lookup m (drop k t) \<noteq> None \<Longrightarrow>
  gstep_del k ev t (Some (GSum m)) = (if is_eint (ev t)
    then Some (GSum (gdn k (\<lambda>t a. (fst a - 1, snd a - ival (ev t))) fst t m))
    else None)"
  by (auto simp: gstep_del_def gdn_def Let_def is_eint_def ival_def split: option.splits event_data.splits)

subsection \<open>The representation: flat, or grouped for a count or a sum\<close>

text \<open>The representation of the count set and the aggregate: flat, the count set next to the
  aggregate, or grouped, for a count (@{text UNCnt}, the group's count of tuples) or a sum
  (@{text UNSum}, the group's count and sum).  A grouped representation is made only for an empty
  window (@{text urmk}); a sum whose value is not an integer goes back to the flat one, as the flat
  aggregate does then.  The projections @{text rcnt} and @{text rax} give the flat pair.\<close>

datatype ucrep = UFlat ucnt "ugagg option" | UNCnt "nat nmap" | UNSum "(nat \<times> integer) nmap"

fun rcnt :: "nat \<Rightarrow> ucrep \<Rightarrow> ucnt" where
  "rcnt k (UFlat c ax) = c"
| "rcnt k (UNCnt M) = nflat k M"
| "rcnt k (UNSum M) = nflat k M"

fun rax :: "ucrep \<Rightarrow> ugagg option" where
  "rax (UFlat c ax) = ax"
| "rax (UNCnt M) = Some (GCnt (nsumm M))"
| "rax (UNSum M) = Some (GSum (nsumm M))"

fun rinv :: "nat \<Rightarrow> ucrep \<Rightarrow> bool" where
  "rinv k (UFlat c ax) = True"
| "rinv k (UNCnt M) = ninv k id M"
| "rinv k (UNSum M) = ninv k fst M"

fun rflat_x :: "ucrep \<Rightarrow> ucnt" where
  "rflat_x (UFlat c ax) = c"
| "rflat_x (UNCnt M) = nflat_x M"
| "rflat_x (UNSum M) = nflat_x M"

lemma rflat_x: "rinv k R \<Longrightarrow> rflat_x R = rcnt k R"
  by (cases R) (simp_all add: nflat_x)

fun rins :: "nat \<Rightarrow> (event_data list \<Rightarrow> event_data) \<Rightarrow> event_data list \<Rightarrow> ucrep \<Rightarrow> ucrep" where
  "rins k ev t (UFlat c ax) = (case cins (gstep_ins k ev) t (c, ax) of (c', ax') \<Rightarrow> UFlat c' ax')"
| "rins k ev t (UNCnt M) = UNCnt (nins k (\<lambda>_. 1) (\<lambda>_ a. Suc a) t M)"
| "rins k ev t (UNSum M) = (if is_eint (ev t) \<or> Mapping.lookup (nflat k M) t \<noteq> None
     then UNSum (nins k (\<lambda>t. (1, ival (ev t))) (\<lambda>t a. (Suc (fst a), snd a + ival (ev t))) t M)
     else UFlat (ucnt_add1 t (nflat_x M)) None)"

fun rdel :: "nat \<Rightarrow> (event_data list \<Rightarrow> event_data) \<Rightarrow> event_data list \<Rightarrow> ucrep \<Rightarrow> ucrep" where
  "rdel k ev t (UFlat c ax) = (case cdel (gstep_del k ev) t (c, ax) of (c', ax') \<Rightarrow> UFlat c' ax')"
| "rdel k ev t (UNCnt M) = UNCnt (ndel k (\<lambda>_ a. a - 1) t M)"
| "rdel k ev t (UNSum M) = (if is_eint (ev t) \<or> Mapping.lookup (nflat k M) t \<noteq> Some 1
     then UNSum (ndel k (\<lambda>t a. (fst a - 1, snd a - ival (ev t))) t M)
     else UFlat (ucnt_del1 t (nflat_x M)) None)"

lemma rins:
  assumes "rinv k R"
  shows "(rcnt k (rins k ev t R), rax (rins k ev t R)) = cins (gstep_ins k ev) t (rcnt k R, rax R)"
    and "rinv k (rins k ev t R)"
proof -
  have "(rcnt k (rins k ev t R), rax (rins k ev t R)) = cins (gstep_ins k ev) t (rcnt k R, rax R) \<and>
      rinv k (rins k ev t R)"
  proof (cases R)
    case (UFlat c ax)
    then show ?thesis by (simp split: prod.splits)
  next
    case (UNCnt M)
    have inv: "ninv k id M" using assms UNCnt by simp
    show ?thesis
      using UNCnt ninv_nins[OF inv, of "\<lambda>_. 1" t "\<lambda>_ a. Suc a"]
      by (simp add: cins_eq nflat_nins nsumm_nins gstep_ins_GCnt)
  next
    case (UNSum M)
    have inv: "ninv k fst M" using assms UNSum by simp
    show ?thesis
    proof (cases "is_eint (ev t) \<or> Mapping.lookup (nflat k M) t \<noteq> None")
      case True
      then show ?thesis
        using UNSum ninv_nins[OF inv, of "\<lambda>t. (1, ival (ev t))" t "\<lambda>t a. (Suc (fst a), snd a + ival (ev t))"]
        by (auto simp: cins_eq nflat_nins nsumm_nins gstep_ins_GSum)
    next
      case False
      then show ?thesis using UNSum by (simp add: cins_eq nflat_x[OF inv] gstep_ins_GSum)
    qed
  qed
  then show "(rcnt k (rins k ev t R), rax (rins k ev t R)) = cins (gstep_ins k ev) t (rcnt k R, rax R)"
    and "rinv k (rins k ev t R)" by simp_all
qed

lemma lookup_nsumm_nflat: "Mapping.lookup (nflat k M) t \<noteq> None \<Longrightarrow> Mapping.lookup (nsumm M) (drop k t) \<noteq> None"
  by (auto simp: lookup_nflat lookup_nsumm split: option.splits)

lemma rdel:
  assumes "rinv k R"
  shows "(rcnt k (rdel k ev t R), rax (rdel k ev t R)) = cdel (gstep_del k ev) t (rcnt k R, rax R)"
    and "rinv k (rdel k ev t R)"
proof -
  have "(rcnt k (rdel k ev t R), rax (rdel k ev t R)) = cdel (gstep_del k ev) t (rcnt k R, rax R) \<and>
      rinv k (rdel k ev t R)"
  proof (cases R)
    case (UFlat c ax)
    then show ?thesis by (simp split: prod.splits)
  next
    case (UNCnt M)
    have inv: "ninv k id M" using assms UNCnt by simp
    show ?thesis
      using UNCnt ninv_ndel[OF inv, of "\<lambda>_ a. a - 1" t]
      by (simp add: cdel_eq nflat_ndel nsumm_ndel[OF inv] gstep_del_GCnt)
  next
    case (UNSum M)
    have inv: "ninv k fst M" using assms UNSum by simp
    show ?thesis
    proof (cases "is_eint (ev t) \<or> Mapping.lookup (nflat k M) t \<noteq> Some 1")
      case True
      then show ?thesis
        using UNSum ninv_ndel[OF inv, of "\<lambda>t a. (fst a - 1, snd a - ival (ev t))" t]
          lookup_nsumm_nflat[of k M t]
        by (auto simp: cdel_eq nflat_ndel nsumm_ndel[OF inv] gstep_del_GSum)
    next
      case False
      then show ?thesis using UNSum lookup_nsumm_nflat[of k M t]
        by (simp add: cdel_eq nflat_x[OF inv] gstep_del_GSum)
    qed
  qed
  then show "(rcnt k (rdel k ev t R), rax (rdel k ev t R)) = cdel (gstep_del k ev) t (rcnt k R, rax R)"
    and "rinv k (rdel k ev t R)" by simp_all
qed

lemma fold_rins:
  "rinv k R \<Longrightarrow> (rcnt k (fold (rins k ev) xs R), rax (fold (rins k ev) xs R)) =
     fold (cins (gstep_ins k ev)) xs (rcnt k R, rax R) \<and> rinv k (fold (rins k ev) xs R)"
proof (induct xs arbitrary: R)
  case (Cons t xs)
  show ?case using Cons.hyps[OF rins(2)[OF Cons.prems]] rins(1)[OF Cons.prems] by simp
qed simp

lemma fold_rdel:
  "rinv k R \<Longrightarrow> (rcnt k (fold (rdel k ev) xs R), rax (fold (rdel k ev) xs R)) =
     fold (cdel (gstep_del k ev)) xs (rcnt k R, rax R) \<and> rinv k (fold (rdel k ev) xs R)"
proof (induct xs arbitrary: R)
  case (Cons t xs)
  show ?case using Cons.hyps[OF rdel(2)[OF Cons.prems]] rdel(1)[OF Cons.prems] by simp
qed simp

definition ek :: "eaggp \<Rightarrow> nat" where
  "ek p = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> k)"

lemma nflat_empty[simp]: "nflat k Mapping.empty = Mapping.empty"
  by (rule mapping_eqI) (simp add: lookup_nflat)

lemma nsumm_empty[simp]: "nsumm Mapping.empty = Mapping.empty"
  by (rule mapping_eqI) (simp add: lookup_nsumm)

lemma is_empty_eq_empty: "Mapping.is_empty m \<longleftrightarrow> m = Mapping.empty"
  by (metis Mapping.is_empty_empty Mapping.keys_empty Mapping.is_empty_def mapping_eqI
      in_keys_lookup ex_in_conv)

definition urmk :: "eaggp \<Rightarrow> ucnt \<Rightarrow> ugagg option \<Rightarrow> ucrep" where
  "urmk p c ax = (if \<not> cachedp p \<and> Mapping.is_empty c then (case ax of
      Some (GCnt m) \<Rightarrow> if Mapping.is_empty m then UNCnt Mapping.empty else UFlat c ax
    | Some (GSum m) \<Rightarrow> if Mapping.is_empty m then UNSum Mapping.empty else UFlat c ax
    | _ \<Rightarrow> UFlat c ax) else UFlat c ax)"

lemma urmk: "rcnt k (urmk p c ax) = c" "rax (urmk p c ax) = ax" "rinv k (urmk p c ax)"
  by (auto simp: urmk_def is_empty_eq_empty split: option.splits gagg.splits)

text \<open>The cache: its key (the constraint and the aggregation it was made for), the
  representation and the result table.  The representation is grouped at the key's group arity
  (@{text ek}).  A step of an aggregation that keeps no table keeps the grouped representation
  whenever the arity agrees, whatever the rest of the key: the representation does not depend on
  it, and the constraint on the result is pushed into the node after the cache is made, so that
  comparing the whole key would lose the grouping at the first step.\<close>

typedef ucache = "{x :: (uconstr option \<times> eaggp) \<times> ucrep \<times> event_data list set.
    case x of (key, R, C) \<Rightarrow> rinv (ek (snd key)) R \<and>
      (cachedp (snd key) \<longrightarrow> (\<forall>a. rax R = Some a \<longrightarrow> C = gcache (fst key) (snd key) a))}"
  by (rule exI[of _ "(undefined, UFlat Mapping.empty None, {})"]) simp

lifting_forget mapping.lifting

setup_lifting type_definition_ucache

lift_definition uc_key :: "ucache \<Rightarrow> uconstr option \<times> eaggp" is "\<lambda>(k, R, C). k" .
lift_definition uc_cnt :: "ucache \<Rightarrow> ucnt" is "\<lambda>(k, R, C). rcnt (ek (snd k)) R" .
lift_definition uc_ax :: "ucache \<Rightarrow> ugagg option" is "\<lambda>(k, R, C). rax R" .
lift_definition uc_set :: "ucache \<Rightarrow> event_data list set" is "\<lambda>(k, R, C). C" .
lift_definition uc_rep :: "ucache \<Rightarrow> ucrep" is "\<lambda>(k, R, C). R" .

definition cset :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> ugagg option \<Rightarrow> event_data list set" where
  "cset q p ax = (case ax of None \<Rightarrow> {} | Some a \<Rightarrow> gcache q p a)"

lift_definition uc_mk :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> ucnt \<Rightarrow> ugagg option \<Rightarrow> ucache" is
  "\<lambda>q p c ax. ((q, p), urmk p c ax, cset q p ax)"
  by (simp add: cset_def urmk)

text \<open>A tuple's step, on the aggregate and its result together: the result changes only at the
  tuple's group, from the group's value before the step to its value after.\<close>

definition cstep :: "(nat \<Rightarrow> (event_data list \<Rightarrow> event_data) \<Rightarrow> event_data list \<Rightarrow> ugagg option \<Rightarrow>
    ugagg option) \<Rightarrow> uconstr option \<Rightarrow> eaggp \<Rightarrow> event_data list \<Rightarrow>
    ugagg option \<times> event_data list set \<Rightarrow> ugagg option \<times> event_data list set" where
  "cstep S q p t axC = (case axC of (ax, C) \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     (case ax of None \<Rightarrow> (None, C)
      | Some a \<Rightarrow> (case S k (umeval_trm f) t (Some a) of None \<Rightarrow> (None, C)
         | Some a' \<Rightarrow> (Some a', cupd (uqok q) pos (drop k t) (gval \<omega> a (drop k t))
              (gval \<omega> a' (drop k t)) C)))))"

definition cinv :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> ugagg option \<times> event_data list set \<Rightarrow> bool" where
  "cinv q p axC = (\<forall>a. fst axC = Some a \<longrightarrow> snd axC = gcache q p a)"

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

lemma cstep_ins_cinv: "cinv q p axC \<Longrightarrow> cinv q p (cstep gstep_ins q p t axC)"
  by (rule cstep_cinv) (auto intro: gval_gstep_ins)

lemma cstep_del_cinv: "cinv q p axC \<Longrightarrow> cinv q p (cstep gstep_del q p t axC)"
  by (rule cstep_cinv) (auto intro: gval_gstep_del)

lemma fold_cstep_cinv:
  "(\<And>t axC. cinv q p axC \<Longrightarrow> cinv q p (S t axC)) \<Longrightarrow> cinv q p axC \<Longrightarrow> cinv q p (fold S xs axC)"
  by (induct xs arbitrary: axC) simp_all

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

lift_definition uc_step_ins :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
    ucache \<Rightarrow> ucache" is
  "\<lambda>q p w X x. case x of (key, R, C) \<Rightarrow> (if cachedp p then (if key = (q, p)
     then (case cnt_ins_fold (cstep gstep_ins q p) (csl X) (rflat_x R) (rax R, C) of
       (c', ax', C') \<Rightarrow> (key, UFlat c' ax', C'))
     else ((q, p), UFlat (ucnt_add X (rflat_x R)) (uag_ins p w X (rflat_x R) (rax R)),
       cset q p (uag_ins p w X (rflat_x R) (rax R))))
     else (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> if ek (snd key) = k
       then ((q, p), fold (rins k (umeval_trm f)) (csl X) R, C)
       else (case cnt_ins_fold (gstep_ins k (umeval_trm f)) (csl X) (rflat_x R) (rax R) of
         (c', ax') \<Rightarrow> ((q, p), UFlat c' ax', C))))"
  subgoal premises inv for q p w X x
  proof -
    obtain key R C where x: "x = (key, R, C)" by (cases x) auto
    obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
    have R: "rinv (ek (snd key)) R"
      and C: "cachedp (snd key) \<Longrightarrow> rax R = Some a \<Longrightarrow> C = gcache (fst key) (snd key) a" for a
      using inv by (simp_all add: x)
    show ?thesis
    proof (cases "cachedp p")
      case cp: True
      show ?thesis
      proof (cases "key = (q, p)")
        case True
        obtain c' ax' C' where
          c: "cnt_ins_fold (cstep gstep_ins q p) (csl X) (rflat_x R) (rax R, C) = (c', ax', C')"
          by (metis prod.collapse)
        have "\<forall>a. rax R = Some a \<longrightarrow> C = gcache q p a" using C cp True by simp
        then have "\<forall>a. ax' = Some a \<longrightarrow> C' = gcache q p a" by (rule cnt_ins_fold_cinv[OF _ c])
        then show ?thesis using cp True by (simp add: x c)
      next
        case False
        then show ?thesis using cp by (simp add: x cset_gcache)
      qed
    next
      case ncp: False
      show ?thesis
      proof (cases "ek (snd key) = k")
        case True
        then show ?thesis using ncp R fold_rins[of k R "umeval_trm f" "csl X"]
          by (simp add: x p ek_def)
      next
        case False
        obtain c' ax' where
          c: "cnt_ins_fold (gstep_ins k (umeval_trm f)) (csl X) (rflat_x R) (rax R) = (c', ax')"
          by (metis prod.collapse)
        show ?thesis using ncp False by (simp add: x p c)
      qed
    qed
  qed
  done

lemma uc_rep_inv: "rinv (ek (snd (uc_key x))) (uc_rep x)"
  by transfer auto

lemma uc_cnt_rep: "uc_cnt x = rcnt (ek (snd (uc_key x))) (uc_rep x)"
  by transfer auto

lemma uc_ax_rep: "uc_ax x = rax (uc_rep x)"
  by transfer auto

lift_definition uc_step_del :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
    ucache \<Rightarrow> ucache" is
  "\<lambda>q p w X x. case x of (key, R, C) \<Rightarrow> (if cachedp p then (if key = (q, p)
     then (case cnt_del_fold (cstep gstep_del q p) (csl X) (rflat_x R) (rax R, C) of
       (c', ax', C') \<Rightarrow> (key, UFlat c' ax', C'))
     else ((q, p), UFlat (ucnt_del X (rflat_x R)) (uag_del p w X (rflat_x R) (rax R)),
       cset q p (uag_del p w X (rflat_x R) (rax R))))
     else (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> if ek (snd key) = k
       then ((q, p), fold (rdel k (umeval_trm f)) (csl X) R, C)
       else (case cnt_del_fold (gstep_del k (umeval_trm f)) (csl X) (rflat_x R) (rax R) of
         (c', ax') \<Rightarrow> ((q, p), UFlat c' ax', C))))"
  subgoal premises inv for q p w X x
  proof -
    obtain key R C where x: "x = (key, R, C)" by (cases x) auto
    obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
    have R: "rinv (ek (snd key)) R"
      and C: "cachedp (snd key) \<Longrightarrow> rax R = Some a \<Longrightarrow> C = gcache (fst key) (snd key) a" for a
      using inv by (simp_all add: x)
    show ?thesis
    proof (cases "cachedp p")
      case cp: True
      show ?thesis
      proof (cases "key = (q, p)")
        case True
        obtain c' ax' C' where
          c: "cnt_del_fold (cstep gstep_del q p) (csl X) (rflat_x R) (rax R, C) = (c', ax', C')"
          by (metis prod.collapse)
        have "\<forall>a. rax R = Some a \<longrightarrow> C = gcache q p a" using C cp True by simp
        then have "\<forall>a. ax' = Some a \<longrightarrow> C' = gcache q p a" by (rule cnt_del_fold_cinv[OF _ c])
        then show ?thesis using cp True by (simp add: x c)
      next
        case False
        then show ?thesis using cp by (simp add: x cset_gcache)
      qed
    next
      case ncp: False
      show ?thesis
      proof (cases "ek (snd key) = k")
        case True
        then show ?thesis using ncp R fold_rdel[of k R "umeval_trm f" "csl X"]
          by (simp add: x p ek_def)
      next
        case False
        obtain c' ax' where
          c: "cnt_del_fold (gstep_del k (umeval_trm f)) (csl X) (rflat_x R) (rax R) = (c', ax')"
          by (metis prod.collapse)
        show ?thesis using ncp False by (simp add: x p c)
      qed
    qed
  qed
  done


lifting_update mapping.lifting

subsection \<open>The result, read off\<close>

fun gempty :: "'b gagg \<Rightarrow> bool" where
  "gempty (GCnt m) = Mapping.is_empty m"
| "gempty (GSum m) = Mapping.is_empty m"
| "gempty (GRank m ty) = Mapping.is_empty m"

definition uc_res :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> ucache \<Rightarrow> event_data list set" where
  "uc_res q p w x = (case uc_ax x of
     None \<Rightarrow> ufilt q (eagg_p p (Mapping.keys (uc_cnt x)))
   | Some a \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> if uc_key x = (q, p) \<and> cachedp p
       then (if g0 \<and> gempty a then ufilt q {[eval_agg_op \<omega> {}]} else uc_set x)
       else ugres (uqok q) g0 \<omega> pos a))"

text \<open>The result read off the grouped representation directly, without the projection.\<close>

definition nis_empty :: "'a nmap \<Rightarrow> bool" where
  "nis_empty M = Mapping.is_empty M"

lemma ugmr_map_values: "ugmr q p f (Mapping.map_values (\<lambda>_ v. g v) m) = ugmr q p (\<lambda>v. f (g v)) m"
  unfolding ugmr_def gmr_def keys_map_values lookup_map_values
  by (rule arg_cong[where f = "Set.filter q"], rule image_cong) (auto split: option.splits)

lemma is_empty_nsumm[simp]: "Mapping.is_empty (nsumm M) \<longleftrightarrow> Mapping.is_empty M"
  by (simp add: nsumm_def Mapping.is_empty_def)

definition ugres_nc :: "uconstr option \<Rightarrow> bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> nat nmap \<Rightarrow>
    event_data list set" where
  "ugres_nc q g0 \<omega> p M = ugres (uqok q) g0 \<omega> p (GCnt (nsumm M))"

definition ugres_ns :: "uconstr option \<Rightarrow> bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> (nat \<times> integer) nmap \<Rightarrow>
    event_data list set" where
  "ugres_ns q g0 \<omega> p M = ugres (uqok q) g0 \<omega> p (GSum (nsumm M))"

lemma ugres_nc_code[code]: "ugres_nc q g0 \<omega> p M =
    (if g0 \<and> nis_empty M then Set.filter (uqok q) {[eval_agg_op \<omega> {}]}
     else ugmr (uqok q) p (\<lambda>v. EInt (integer_of_int (fst v))) M)"
  by (simp add: nis_empty_def ugres_nc_def ugres_code nsumm_def ugmr_map_values)

lemma ugres_ns_code[code]: "ugres_ns q g0 \<omega> p M =
    (if g0 \<and> nis_empty M then Set.filter (uqok q) {[eval_agg_op \<omega> {}]}
     else (case fst \<omega> of
       Formula.Agg_Sum \<Rightarrow> ugmr (uqok q) p (\<lambda>v. EInt (snd (fst v))) M
     | Formula.Agg_Avg \<Rightarrow> ugmr (uqok q) p
         (\<lambda>v. EFloat (double_of_event_data (EInt (snd (fst v))) / double_of_int (fst (fst v)))) M
     | _ \<Rightarrow> {}))"
  by (simp add: nis_empty_def ugres_ns_def ugres_code nsumm_def ugmr_map_values split: Formula.agg_type.splits)

lemma uc_res_code[code]: "uc_res q p w x = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> (case uc_rep x of
     UFlat c ax \<Rightarrow> (case ax of
       None \<Rightarrow> ufilt q (eagg_p p (Mapping.keys c))
     | Some a \<Rightarrow> if uc_key x = (q, p) \<and> cachedp p
       then (if g0 \<and> gempty a then ufilt q {[eval_agg_op \<omega> {}]} else uc_set x)
       else ugres (uqok q) g0 \<omega> pos a)
   | UNCnt M \<Rightarrow> if uc_key x = (q, p) \<and> cachedp p
       then (if g0 \<and> nis_empty M then ufilt q {[eval_agg_op \<omega> {}]} else uc_set x)
       else ugres_nc q g0 \<omega> pos M
   | UNSum M \<Rightarrow> if uc_key x = (q, p) \<and> cachedp p
       then (if g0 \<and> nis_empty M then ufilt q {[eval_agg_op \<omega> {}]} else uc_set x)
       else ugres_ns q g0 \<omega> pos M))"
  by (auto simp: uc_res_def uc_ax_rep uc_cnt_rep ugres_nc_def ugres_ns_def nis_empty_def
      split: ucrep.splits prod.splits option.splits)

text \<open>The code reads the count set through the executable flattening, and a tuple's count through
  its group's map; the projection @{const nflat} itself is a lookup function, not a tree.\<close>

lemma uc_cnt_code[code]: "uc_cnt x = rflat_x (uc_rep x)"
  using rflat_x[OF uc_rep_inv[of x]] by (simp add: uc_cnt_rep)

definition nlk :: "nat \<Rightarrow> 'a nmap \<Rightarrow> event_data list \<Rightarrow> nat option" where
  "nlk k M t = (case Mapping.lookup M (drop k t) of None \<Rightarrow> None | Some aI \<Rightarrow> Mapping.lookup (snd aI) t)"

lemma lookup_nflat_nlk[code_unfold]: "Mapping.lookup (nflat k M) t = nlk k M t"
  by (simp add: lookup_nflat nlk_def)

subsection \<open>The window over it\<close>

type_synonym uswaggc = "(ts \<times> (ts \<times> event_data list set) queue \<times> (ts \<times> event_data list set) queue) \<times>
  ucache"

fun rsc :: "uswaggc \<Rightarrow> swagg" where
  "rsc ((t, pend, win), x) = ((t, pend, win, ucc (uc_cnt x)), uc_ax x)"

function usc_move :: "args \<Rightarrow> eaggp \<Rightarrow> uconstr option \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data list set) queue \<Rightarrow>
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

function usc_expire :: "args \<Rightarrow> eaggp \<Rightarrow> uconstr option \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data list set) queue \<Rightarrow>
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

definition usc_init :: "args \<Rightarrow> eaggp \<Rightarrow> uconstr option \<Rightarrow> uswaggc" where
  "usc_init args p q = ((0, empty_queue, empty_queue), uc_mk q p Mapping.empty (ag_init p (args_n args)))"

definition usc_add_new_ts :: "args \<Rightarrow> eaggp \<Rightarrow> uconstr option \<Rightarrow> ts \<Rightarrow> uswaggc \<Rightarrow> uswaggc" where
  "usc_add_new_ts args p q nt aux = (case aux of ((t, pend, win), x) \<Rightarrow>
     (case usc_move args p q nt pend win x of (pend', win', x') \<Rightarrow>
      (case usc_expire args p q nt win' x' of (win'', x'') \<Rightarrow> ((nt, pend', win''), x''))))"

definition usc_join :: "args \<Rightarrow> eaggp \<Rightarrow> uconstr option \<Rightarrow> event_data list set \<Rightarrow> uswaggc \<Rightarrow> uswaggc" where
  "usc_join args p q X aux = (case aux of ((t, pend, win), x) \<Rightarrow>
     (if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then aux
      else ((t, empty_queue, empty_queue), uc_mk q p Mapping.empty (ag_init p (args_n args)))))"

definition usc_add_new_table :: "args \<Rightarrow> eaggp \<Rightarrow> uconstr option \<Rightarrow> event_data list set \<Rightarrow>
    uswaggc \<Rightarrow> uswaggc" where
  "usc_add_new_table args p q X aux = (case aux of ((t, pend, win), x) \<Rightarrow>
     (if memL (args_ivl args) 0
      then ((t, pend, append_queue (t, X) win), uc_step_ins q p (args_n args) X x)
      else ((t, append_queue (t, X) pend, win), x)))"

definition usc_result :: "uconstr option \<Rightarrow> args \<Rightarrow> eaggp \<Rightarrow> uswaggc \<Rightarrow> event_data list set" where
  "usc_result q args p aux = (case aux of ((t, pend, win), x) \<Rightarrow> uc_res q p (args_n args) x)"

end
(*>*)

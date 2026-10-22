(*<*)
theory Agg_Cache_Proof
  imports "Monitor_Exec.Agg_Cache" Until_Agg_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma mkr_eq_iff: "mkr p g v = mkr p g' v' \<longleftrightarrow> g = g' \<and> v = v'"
proof
  assume eq: "mkr p g v = mkr p g' v'"
  then have len: "length g = length g'" using length_mkr[of p g v] length_mkr[of p g' v'] by simp
  then have "take p g = take p g' \<and> v # drop p g = v' # drop p g'"
    using eq unfolding mkr_def by (subst (asm) append_eq_append_conv) auto
  then show "g = g' \<and> v = v'" by (metis append_take_drop_id list.inject)
qed simp

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

lemma gcache_ugres: "gcache q p a = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> ugres (uqok q) False \<omega> pos a)"
  by (simp add: gcache_def ugres_def gres_gvset split: prod.splits)

lemma lookup_nflat: "Mapping.lookup (nflat k M) t = (case Mapping.lookup M (drop k t) of None \<Rightarrow> None
     | Some aI \<Rightarrow> Mapping.lookup (snd aI) t)"
  unfolding nflat_def by (simp add: Mapping.lookup.abs_eq)

lemma nflat_nins: "nflat k (nins k si su t M) = ucnt_add1 t (nflat k M)"
  by (rule mapping_eqI)
    (auto simp: lookup_nflat nins_def ucnt_add1_def Let_def lookup_update'
      split: option.splits prod.splits)

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

lemma cnt_ins_fold_cins: "cnt_ins_fold F xs c b = fold (cins F) xs (c, b)"
  unfolding cnt_ins_fold_def cins_def by (rule arg_cong[where f = "\<lambda>f. fold f xs (c, b)"]) (auto simp: fun_eq_iff)

lemma cnt_del_fold_cdel: "cnt_del_fold F xs c b = fold (cdel F) xs (c, b)"
  unfolding cnt_del_fold_def cdel_def by (rule arg_cong[where f = "\<lambda>f. fold f xs (c, b)"]) (auto simp: fun_eq_iff)

lemma cins_eq: "cins F t (c, acc) = (ucnt_add1 t c, if Mapping.lookup c t = None then F t acc else acc)"
  by (simp add: cins_def ucnt_add1_def split: option.splits)

lemma cdel_eq: "cdel F t (c, acc) = (ucnt_del1 t c, if Mapping.lookup c t = Some 1 then F t acc else acc)"
  by (auto simp: cdel_def ucnt_del1_def split: option.splits)

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

lemma rflat_x: "rinv k R \<Longrightarrow> rflat_x R = rcnt k R"
  by (cases R) (simp_all add: nflat_x)

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

lemma nflat_empty[simp]: "nflat k Mapping.empty = Mapping.empty"
  by (rule mapping_eqI) (simp add: lookup_nflat)

lemma is_empty_eq_empty: "Mapping.is_empty m \<longleftrightarrow> m = Mapping.empty"
  by (metis Mapping.is_empty_empty Mapping.keys_empty Mapping.is_empty_def mapping_eqI
      in_keys_lookup ex_in_conv)

lemma urmk: "rcnt k (urmk p c ax) = c" "rax (urmk p c ax) = ax" "rinv k (urmk p c ax)"
  by (auto simp: urmk_def is_empty_eq_empty split: option.splits gagg.splits)

lemma uc_set_gcache: "cachedp (snd (uc_key x)) \<Longrightarrow> uc_ax x = Some a \<Longrightarrow>
    uc_set x = gcache (fst (uc_key x)) (snd (uc_key x)) a"
  by transfer auto

lemma uc_mk[simp]: "uc_cnt (uc_mk q p c ax) = c" "uc_ax (uc_mk q p c ax) = ax"
  by (transfer; simp add: urmk)+

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

lemma fst_fold_cstep_ins: "fst (fold (cstep gstep_ins q p) xs axC) =
    (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gins k (umeval_trm f) xs (fst axC))"
  by (cases p) (simp add: gins_def fold_cstep_fst[where G = "gstep_ins _ _"] cstep_ins_fst)

lemma fst_fold_cstep_del: "fst (fold (cstep gstep_del q p) xs axC) =
    (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gdel k (umeval_trm f) xs (fst axC))"
  by (cases p) (simp add: gdel_def fold_cstep_fst[where G = "gstep_del _ _"] cstep_del_fst)

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

lemma uc_rep_inv: "rinv (ek (snd (uc_key x))) (uc_rep x)"
  by transfer auto

lemma uc_cnt_rep: "uc_cnt x = rcnt (ek (snd (uc_key x))) (uc_rep x)"
  by transfer auto

lemma uc_ax_rep: "uc_ax x = rax (uc_rep x)"
  by transfer auto

lemma uc_step_ins_nc:
  assumes "\<not> cachedp p" "p = (g0, \<omega>, f, k, pos)"
  shows "(uc_cnt (uc_step_ins q p w X x), uc_ax (uc_step_ins q p w X x)) =
    cnt_ins_fold (gstep_ins k (umeval_trm f)) (csl X) (uc_cnt x) (uc_ax x)"
proof -
  obtain key R C where r: "Rep_ucache x = (key, R, C)" by (cases "Rep_ucache x")
  have inv: "rinv (ek (snd key)) R" using uc_rep_inv[of x] by (simp add: uc_key.rep_eq uc_rep.rep_eq r)
  have c: "uc_cnt x = rcnt (ek (snd key)) R" "uc_ax x = rax R"
    by (simp_all add: uc_cnt.rep_eq uc_ax.rep_eq r)
  show ?thesis
  proof (cases "ek (snd key) = k")
    case True
    then have "rinv k R" using inv by simp
    from fold_rins[OF this, of "umeval_trm f" "csl X"] True show ?thesis using assms
      by (simp add: uc_cnt.rep_eq uc_ax.rep_eq uc_step_ins.rep_eq r c ek_def cnt_ins_fold_cins)
  next
    case False
    then show ?thesis using assms rflat_x[OF inv]
      by (simp add: uc_cnt.rep_eq uc_ax.rep_eq uc_step_ins.rep_eq r c ek_def split: prod.splits)
  qed
qed

lemma uc_step_ins_c:
  assumes "cachedp p"
  shows "uc_cnt (uc_step_ins q p w X x) = fold ucnt_add1 (csl X) (uc_cnt x)"
    "uc_ax (uc_step_ins q p w X x) = uag_ins p w X (uc_cnt x) (uc_ax x)"
proof -
  obtain key R C where r: "Rep_ucache x = (key, R, C)" by (cases "Rep_ucache x")
  have inv: "rinv (ek (snd key)) R" using uc_rep_inv[of x] by (simp add: uc_key.rep_eq uc_rep.rep_eq r)
  have c: "uc_cnt x = rflat_x R" "uc_ax x = rax R"
    by (simp_all add: uc_cnt.rep_eq uc_ax.rep_eq r rflat_x[OF inv])
  have h1: "fst (fold (cstep gstep_ins q p) (filter (\<lambda>t. Mapping.lookup (rflat_x R) t = None) (csl X))
      (rax R, C)) = uag_ins p w X (rflat_x R) (rax R)"
    by (simp add: fst_fold_cstep_ins uag_ins_def)
  show "uc_cnt (uc_step_ins q p w X x) = fold ucnt_add1 (csl X) (uc_cnt x)"
    using assms by (simp add: uc_cnt.rep_eq uc_step_ins.rep_eq r c cnt_ins_fold_eq[OF distinct_csl_edl]
        ucnt_add_def rflat_x[OF inv] split: prod.splits)
  show "uc_ax (uc_step_ins q p w X x) = uag_ins p w X (uc_cnt x) (uc_ax x)"
    using assms h1 by (simp add: uc_ax.rep_eq uc_step_ins.rep_eq r c cnt_ins_fold_eq[OF distinct_csl_edl]
        split: prod.splits) (metis fst_conv)
qed

lemma uc_step_ins_cnt[simp]: "uc_cnt (uc_step_ins q p w X x) = ucnt_add X (uc_cnt x)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  show ?thesis
  proof (cases "cachedp p")
    case True
    then show ?thesis by (simp add: uc_step_ins_c ucnt_add_def)
  next
    case False
    from uc_step_ins_nc[OF False p, of q w X x] show ?thesis
      by (simp add: cnt_ins_fold_eq[OF distinct_csl_edl] ucnt_add_def)
  qed
qed

lemma uc_step_ins_ax[simp]: "uc_ax (uc_step_ins q p w X x) = uag_ins p w X (uc_cnt x) (uc_ax x)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  show ?thesis
  proof (cases "cachedp p")
    case True
    then show ?thesis by (simp add: uc_step_ins_c)
  next
    case False
    from uc_step_ins_nc[OF False p, of q w X x] show ?thesis
      by (simp add: cnt_ins_fold_eq[OF distinct_csl_edl] p uag_ins_def gins_def)
  qed
qed

lemma uc_step_del_nc:
  assumes "\<not> cachedp p" "p = (g0, \<omega>, f, k, pos)"
  shows "(uc_cnt (uc_step_del q p w X x), uc_ax (uc_step_del q p w X x)) =
    cnt_del_fold (gstep_del k (umeval_trm f)) (csl X) (uc_cnt x) (uc_ax x)"
proof -
  obtain key R C where r: "Rep_ucache x = (key, R, C)" by (cases "Rep_ucache x")
  have inv: "rinv (ek (snd key)) R" using uc_rep_inv[of x] by (simp add: uc_key.rep_eq uc_rep.rep_eq r)
  have c: "uc_cnt x = rcnt (ek (snd key)) R" "uc_ax x = rax R"
    by (simp_all add: uc_cnt.rep_eq uc_ax.rep_eq r)
  show ?thesis
  proof (cases "ek (snd key) = k")
    case True
    then have "rinv k R" using inv by simp
    from fold_rdel[OF this, of "umeval_trm f" "csl X"] True show ?thesis using assms
      by (simp add: uc_cnt.rep_eq uc_ax.rep_eq uc_step_del.rep_eq r c ek_def cnt_del_fold_cdel)
  next
    case False
    then show ?thesis using assms rflat_x[OF inv]
      by (simp add: uc_cnt.rep_eq uc_ax.rep_eq uc_step_del.rep_eq r c ek_def split: prod.splits)
  qed
qed

lemma uc_step_del_c:
  assumes "cachedp p"
  shows "uc_cnt (uc_step_del q p w X x) = fold ucnt_del1 (csl X) (uc_cnt x)"
    "uc_ax (uc_step_del q p w X x) = uag_del p w X (uc_cnt x) (uc_ax x)"
proof -
  obtain key R C where r: "Rep_ucache x = (key, R, C)" by (cases "Rep_ucache x")
  have inv: "rinv (ek (snd key)) R" using uc_rep_inv[of x] by (simp add: uc_key.rep_eq uc_rep.rep_eq r)
  have c: "uc_cnt x = rflat_x R" "uc_ax x = rax R"
    by (simp_all add: uc_cnt.rep_eq uc_ax.rep_eq r rflat_x[OF inv])
  have h1: "fst (fold (cstep gstep_del q p) (filter (\<lambda>t. Mapping.lookup (rflat_x R) t = Some 1) (csl X))
      (rax R, C)) = uag_del p w X (rflat_x R) (rax R)"
    by (simp add: fst_fold_cstep_del uag_del_def)
  show "uc_cnt (uc_step_del q p w X x) = fold ucnt_del1 (csl X) (uc_cnt x)"
    using assms by (simp add: uc_cnt.rep_eq uc_step_del.rep_eq r c cnt_del_fold_eq[OF distinct_csl_edl]
        ucnt_del_def rflat_x[OF inv] split: prod.splits)
  show "uc_ax (uc_step_del q p w X x) = uag_del p w X (uc_cnt x) (uc_ax x)"
    using assms h1 by (simp add: uc_ax.rep_eq uc_step_del.rep_eq r c cnt_del_fold_eq[OF distinct_csl_edl]
        split: prod.splits) (metis fst_conv)
qed

lemma uc_step_del_cnt[simp]: "uc_cnt (uc_step_del q p w X x) = ucnt_del X (uc_cnt x)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  show ?thesis
  proof (cases "cachedp p")
    case True
    then show ?thesis by (simp add: uc_step_del_c ucnt_del_def)
  next
    case False
    from uc_step_del_nc[OF False p, of q w X x] show ?thesis
      by (simp add: cnt_del_fold_eq[OF distinct_csl_edl] ucnt_del_def)
  qed
qed

lemma uc_step_del_ax[simp]: "uc_ax (uc_step_del q p w X x) = uag_del p w X (uc_cnt x) (uc_ax x)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  show ?thesis
  proof (cases "cachedp p")
    case True
    then show ?thesis by (simp add: uc_step_del_c)
  next
    case False
    from uc_step_del_nc[OF False p, of q w X x] show ?thesis
      by (simp add: cnt_del_fold_eq[OF distinct_csl_edl] p uag_del_def gdel_def)
  qed
qed

lifting_update mapping.lifting

lemma gempty_gkeys: "gempty a \<longleftrightarrow> gkeys a = {}"
  by (cases a) (simp_all add: Mapping.is_empty_def)

lemma uc_res: "uc_res q p w x = uag_res q p w (uc_cnt x) (uc_ax x)"
  by (auto simp: uc_res_def uag_res_code ugres_def gres_gvset ufilt_def uc_set_gcache gcache_def
      gempty_gkeys split: option.splits prod.splits)

lemma ugmr_map_values: "ugmr q p f (Mapping.map_values (\<lambda>_ v. g v) m) = ugmr q p (\<lambda>v. f (g v)) m"
  unfolding ugmr_def gmr_def keys_map_values lookup_map_values
  by (rule arg_cong[where f = "Set.filter q"], rule image_cong) (auto split: option.splits)

lemma sa_move_rsc: "sa_move args p nt pend win (ucc (uc_cnt x)) (uc_ax x) =
    (case usc_move args p q nt pend win x of (pend', win', x') \<Rightarrow> (pend', win', ucc (uc_cnt x'), uc_ax x'))"
proof (induct args p q nt pend win x rule: usc_move.induct)
  case (1 args p q nt pend win x)
  obtain h pend' where hd: "safe_hd pend = (h, pend')" by (cases "safe_hd pend")
  show ?case
  proof (cases h)
    case None
    then show ?thesis by (subst sa_move.simps, subst usc_move.simps) (simp add: hd)
  next
    case (Some e)
    note IH = 1[OF hd[symmetric] Some]
    show ?thesis
      using IH by (subst sa_move.simps, subst usc_move.simps) (simp add: hd Some)
  qed
qed

lemma sa_expire_rsc: "sa_expire args p nt win (ucc (uc_cnt x)) (uc_ax x) =
    (case usc_expire args p q nt win x of (win', x') \<Rightarrow> (win', ucc (uc_cnt x'), uc_ax x'))"
proof (induct args p q nt win x rule: usc_expire.induct)
  case (1 args p q nt win x)
  obtain h win' where hd: "safe_hd win = (h, win')" by (cases "safe_hd win")
  show ?case
  proof (cases h)
    case None
    then show ?thesis by (subst sa_expire.simps, subst usc_expire.simps) (simp add: hd)
  next
    case (Some e)
    note IH = 1[OF hd[symmetric] Some]
    show ?thesis
      using IH by (subst sa_expire.simps, subst usc_expire.simps) (simp add: hd Some)
  qed
qed

lemma sa_init_rsc: "sa_init args p = rsc (usc_init args p q)"
  by (simp add: sa_init_def usc_init_def sw_init_def ucc.simps)

lemma sa_add_new_ts_rsc: "sa_add_new_ts args p nt (rsc aux) = rsc (usc_add_new_ts args p q nt aux)"
proof -
  obtain t pend win x where aux: "aux = ((t, pend, win), x)" by (cases aux) auto
  obtain pend' win' x' where m: "usc_move args p q nt pend win x = (pend', win', x')"
    by (cases "usc_move args p q nt pend win x") auto
  obtain win'' x'' where e: "usc_expire args p q nt win' x' = (win'', x'')"
    by (cases "usc_expire args p q nt win' x'") auto
  show ?thesis
    using sa_move_rsc[of args p nt pend win x q] sa_expire_rsc[of args p nt win' x' q]
    by (simp add: aux m e sa_add_new_ts_def usc_add_new_ts_def)
qed

lemma sa_join_rsc: "sa_join args p X (rsc aux) = rsc (usc_join args p q X aux)"
  by (cases aux) (auto simp: sa_join_def sw_join_def usc_join_def ucc.simps)

lemma sa_add_new_table_rsc: "sa_add_new_table args p X (rsc aux) = rsc (usc_add_new_table args p q X aux)"
  by (cases aux) (auto simp: sa_add_new_table_def usc_add_new_table_def)

lemma sa_result_rsc: "ufilt q (sa_result args p (rsc aux)) = usc_result q args p aux"
  by (cases aux) (auto simp: sa_result_def usc_result_def uc_res ag_res_ucc simp del: ag_res_ucc_None)

(*<*)
end
(*>*)

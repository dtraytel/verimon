(*<*)
theory Correct_Regex
  imports
    Progress
    "Monitor_Algorithm.Monitor"
    Correct_Binary_Ops
begin
(*>*)


section \<open> Correctness of regular expressions \<close>


subsection \<open> Translation of regular expressions \<close>

lemma from_mregex_cong: "ok m mr \<Longrightarrow> (\<forall>i < m. xs ! i = ys ! i) \<Longrightarrow> from_mregex mr xs = from_mregex mr ys"
  by (induct mr) auto

lemmas to_mregex_safe_atms =
  to_mregex_ok[THEN conjunct1, THEN equalityD1, THEN set_mp, rotated]

lemma from_mregex_shift: "from_mregex (shift r (length xs)) (xs @ ys) = from_mregex r ys"
  by (induct r) (auto simp: nth_append)

lemma from_mregex_to_mregex: "Regex.safe_regex fv rgx_safe_pred m g r 
  \<Longrightarrow> case_prod from_mregex (to_mregex r) = r"
  by (induct r rule: safe_regex.induct) 
      (auto dest: to_mregex_ok intro!: from_mregex_cong simp: nth_append from_mregex_shift case_Neg_iff
      split: prod.splits modality.splits if_splits)

lemma from_mregex_eq: "Regex.safe_regex fv rgx_safe_pred m g r 
  \<Longrightarrow> to_mregex r = (mr, \<phi>s) \<Longrightarrow> from_mregex mr \<phi>s = r"
  using from_mregex_to_mregex[of m g r] by auto

lemma fv_regex_from_mregex:
  "ok (length \<phi>s) mr \<Longrightarrow> fv_regex (from_mregex mr \<phi>s) \<subseteq> (\<Union>\<phi> \<in> set \<phi>s. fv \<phi>)"
  by (induct mr) (auto simp: Bex_def in_set_conv_nth)+


subsection \<open> Safety of right derivatives \<close>

lemma RPD_fv_regex_le:
  "ms \<in> RPD mr \<Longrightarrow> fv_regex (from_mregex ms \<phi>s) \<subseteq> fv_regex (from_mregex mr \<phi>s)"
  by (induct mr arbitrary: ms) (auto simp: MTimesL_def split: nat.splits)+

lemma RPD_safe: "Regex.safe_regex fv rgx_safe_pred Past g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPD mr \<Longrightarrow> Regex.safe_regex fv rgx_safe_pred Past g (from_mregex ms \<phi>s)"
proof (induct Past g "from_mregex mr \<phi>s" arbitrary: mr ms rule: safe_regex_induct)
  case Skip
  then show ?case
    by (cases mr) (auto split: nat.splits)
next
  case (Test g \<phi>)
  then show ?case
    by (cases mr) auto
next
  case (Plus g r s mrs)
  then show ?case
  proof (cases mrs)
    case (MPlus mr ms)
    with Plus(3-5) show ?thesis
      by (auto dest!: Plus(1,2))
  qed auto
next
  case (TimesP g r s mrs)
  then show ?case
  proof (cases mrs)
    case (MTimes mr ms)
    with TimesP(3-5) show ?thesis
      by (cases g) (auto 0 4 simp: MTimesL_def dest: RPD_fv_regex_le TimesP(1,2))
  qed auto
next
  case (Star g r)
  then show ?case
  proof (cases mr)
    case (MStar x6)
    with Star(2-4) show ?thesis
      by (cases g) (auto 0 4 simp: MTimesL_def dest: RPD_fv_regex_le
          elim!: safe_cosafe[rotated] dest!: Star(1))
  qed auto
qed

lemma RPDi_safe: "Regex.safe_regex fv rgx_safe_pred Past g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPDi n mr ==> Regex.safe_regex fv rgx_safe_pred Past g (from_mregex ms \<phi>s)"
  by (induct n arbitrary: ms mr) (auto dest: RPD_safe)

lemma RPDs_safe: "Regex.safe_regex fv rgx_safe_pred Past g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPDs mr ==> Regex.safe_regex fv rgx_safe_pred Past g (from_mregex ms \<phi>s)"
  unfolding RPDs_def by (auto dest: RPDi_safe)

lemma RPD_safe_fv_regex: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPD mr \<Longrightarrow> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
proof (induct Past Strict "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
  case (Skip n)
  then show ?case
    by (cases mr) (auto split: nat.splits)
next
  case (Test \<phi>)
  then show ?case
    by (cases mr) auto
next
  case (Plus r s)
  then show ?case
    by (cases mr) auto
next
  case (TimesP r s)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesL_def dest: RPD_fv_regex_le split: modality.splits)
next
  case (Star r)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesL_def dest: RPD_fv_regex_le)
qed

lemma RPDi_safe_fv_regex: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPDi n mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  by (induct n arbitrary: ms mr) (auto 5 0 dest: RPD_safe_fv_regex RPD_safe)

lemma RPDs_safe_fv_regex: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPDs mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  unfolding RPDs_def by (auto dest: RPDi_safe_fv_regex)

lemma RPD_ok: "ok m mr \<Longrightarrow> ms \<in> RPD mr \<Longrightarrow> ok m ms"
proof (induct mr arbitrary: ms)
  case (MPlus mr1 mr2)
  from MPlus(3,4) show ?case
    by (auto elim: MPlus(1,2))
next
  case (MTimes mr1 mr2)
  from MTimes(3,4) show ?case
    by (auto elim: MTimes(1,2) simp: MTimesL_def)
next
  case (MStar mr)
  from MStar(2,3) show ?case
    by (auto elim: MStar(1) simp: MTimesL_def)
qed (auto split: nat.splits)

lemma RPDi_ok: "ok m mr \<Longrightarrow> ms \<in> RPDi n mr \<Longrightarrow> ok m ms"
  by (induct n arbitrary: ms mr) (auto intro: RPD_ok)

lemma RPDs_ok: "ok m mr \<Longrightarrow> ms \<in> RPDs mr \<Longrightarrow> ok m ms"
  unfolding RPDs_def by (auto intro: RPDi_ok)


subsection \<open> Safety of left derivatives \<close>

lemma LPD_fv_regex_le:
  "ms \<in> LPD mr \<Longrightarrow> fv_regex (from_mregex ms \<phi>s) \<subseteq> fv_regex (from_mregex mr \<phi>s)"
  by (induct mr arbitrary: ms) (auto simp: MTimesR_def split: nat.splits)+

lemma LPD_safe: "Regex.safe_regex fv rgx_safe_pred Futu g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPD mr \<Longrightarrow> Regex.safe_regex fv rgx_safe_pred Futu g (from_mregex ms \<phi>s)"
proof (induct Futu g "from_mregex mr \<phi>s" arbitrary: mr ms rule: safe_regex_induct)
  case Skip
  then show ?case
    by (cases mr) (auto split: nat.splits)
next
  case (Test g \<phi>)
  then show ?case
    by (cases mr) auto
next
  case (Plus g r s mrs)
  then show ?case
  proof (cases mrs)
    case (MPlus mr ms)
    with Plus(3-5) show ?thesis
      by (auto dest!: Plus(1,2))
  qed auto
next
  case (TimesF g r s mrs)
  then show ?case
  proof (cases mrs)
    case (MTimes mr ms)
    with TimesF(3-5) show ?thesis
      by (cases g) 
        (auto 0 4 simp: MTimesR_def dest: LPD_fv_regex_le 
          split: modality.splits dest: TimesF(1,2))
  qed auto
next
  case (Star g r)
  then show ?case
  proof (cases mr)
    case (MStar x6)
    with Star(2-4) show ?thesis
      by (cases g) (auto 0 4 simp: MTimesR_def dest: LPD_fv_regex_le
          elim!: safe_cosafe[rotated] dest!: Star(1))
  qed auto
qed

lemma LPDi_safe: "Regex.safe_regex fv rgx_safe_pred Futu g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPDi n mr ==> Regex.safe_regex fv rgx_safe_pred Futu g (from_mregex ms \<phi>s)"
  by (induct n arbitrary: ms mr) (auto dest: LPD_safe)

lemma LPDs_safe: "Regex.safe_regex fv rgx_safe_pred Futu g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPDs mr ==> Regex.safe_regex fv rgx_safe_pred Futu g (from_mregex ms \<phi>s)"
  unfolding LPDs_def by (auto dest: LPDi_safe)

lemma LPD_safe_fv_regex: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPD mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
proof (induct Futu Strict "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
  case Skip
  then show ?case
    by (cases mr) (auto split: nat.splits)
next
  case (Test \<phi>)
  then show ?case
    by (cases mr) auto
next
  case (Plus r s)
  then show ?case
    by (cases mr) auto
next
  case (TimesF r s)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesR_def dest: LPD_fv_regex_le split: modality.splits)
next
  case (Star r)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesR_def dest: LPD_fv_regex_le)
qed

lemma LPDi_safe_fv_regex: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPDi n mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  by (induct n arbitrary: ms mr) (auto 5 0 dest: LPD_safe_fv_regex LPD_safe)

lemma LPDs_safe_fv_regex: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPDs mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  unfolding LPDs_def by (auto dest: LPDi_safe_fv_regex)

lemma LPD_ok: "ok m mr \<Longrightarrow> ms \<in> LPD mr \<Longrightarrow> ok m ms"
proof (induct mr arbitrary: ms)
  case (MPlus mr1 mr2)
  from MPlus(3,4) show ?case
    by (auto elim: MPlus(1,2))
next
  case (MTimes mr1 mr2)
  from MTimes(3,4) show ?case
    by (auto elim: MTimes(1,2) simp: MTimesR_def)
next
  case (MStar mr)
  from MStar(2,3) show ?case
    by (auto elim: MStar(1) simp: MTimesR_def)
qed (auto split: nat.splits)

lemma LPDi_ok: "ok m mr \<Longrightarrow> ms \<in> LPDi n mr \<Longrightarrow> ok m ms"
  by (induct n arbitrary: ms mr) (auto intro: LPD_ok)

lemma LPDs_ok: "ok m mr \<Longrightarrow> ms \<in> LPDs mr \<Longrightarrow> ok m ms"
  unfolding LPDs_def by (auto intro: LPDi_ok)


subsection \<open> Progress \<close>

lemma ok_0_atms: "ok 0 mr \<Longrightarrow> regex.atms (from_mregex mr []) = {}"
  by (induct mr) auto

lemma ok_0_progress: "ok 0 mr \<Longrightarrow> progress_regex \<sigma> P (from_mregex mr []) j = j"
  by (drule ok_0_atms) (auto simp: progress_regex_def)

lemma atms_empty_progress: "Regex.safe_regex fv rgx_safe_pred m g r \<Longrightarrow> safe_atms r = {} 
  \<Longrightarrow> progress_regex \<sigma> P r j = j"
  by (drule atms_empty_safe_atms) (auto simp: progress_regex_def)

lemma to_mregex_empty_progress: "Regex.safe_regex fv rgx_safe_pred m g r 
  \<Longrightarrow> to_mregex r = (mr, []) \<Longrightarrow> progress_regex \<sigma> P r j = j"
  using from_mregex_eq ok_0_progress to_mregex_ok atms_empty_safe_atms by fastforce

lemma atms_nonempty_progress:
  "Regex.safe_regex fv rgx_safe_pred m g r \<Longrightarrow> safe_atms r \<noteq> {} 
  \<Longrightarrow> (\<lambda>\<phi>. progress \<sigma> P \<phi> j) ` safe_atms r = (\<lambda>\<phi>. progress \<sigma> P \<phi> j) ` regex.atms r"
proof -
  assume safe: "Regex.safe_regex fv rgx_safe_pred m g r"
  let ?f = "\<lambda>\<phi>. progress \<sigma> P \<phi> j"
  have safe_sub: "?f \<phi> \<in> ?f ` regex.atms r" if "\<phi> \<in> safe_atms r" for \<phi>
  proof -
    from that obtain \<psi> where "\<psi> \<in> regex.atms r" and "safe_formula \<psi> \<and> \<phi> = \<psi> \<or> \<psi> = Formula.Neg \<phi>"
      by (auto simp: safe_atms_def case_Neg_in_iff split: if_splits)
    then show ?thesis
      by (auto intro: rev_image_eqI)
  qed
  have atms_sub: "?f \<psi> \<in> ?f ` safe_atms r" if \<psi>: "\<psi> \<in> regex.atms r" for \<psi>
  proof (cases "safe_formula \<psi>")
    case True
    with \<psi> have "\<psi> \<in> safe_atms r"
      by (auto simp: safe_atms_def)
    then show ?thesis
      by (rule imageI)
  next
    case False
    with safe_regex_safe_formula[OF safe \<psi>] obtain \<psi>' where \<psi>': "\<psi> = Formula.Neg \<psi>'"
      by blast
    have "\<psi>' \<in> safe_atms r"
      unfolding safe_atms_def
    proof (rule UN_I[OF \<psi>])
      show "\<psi>' \<in> (if safe_formula \<psi> then {\<psi>} else case \<psi> of Formula.Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"
        unfolding if_not_P[OF False] case_Neg_in_iff by (rule \<psi>')
    qed
    with \<psi>' show ?thesis
      by (auto intro: rev_image_eqI)
  qed
  show ?thesis
    by (intro equalityI image_subsetI safe_sub atms_sub)
qed

lemma to_mregex_nonempty_progress: "Regex.safe_regex fv rgx_safe_pred m g r 
  \<Longrightarrow> to_mregex r = (mr, \<phi>s) \<Longrightarrow> \<phi>s \<noteq> [] 
  \<Longrightarrow> progress_regex \<sigma> P r j = (MIN \<phi>\<in>set \<phi>s. progress \<sigma> P \<phi> j)"
  using atms_nonempty_progress[of m g r \<sigma> P] to_mregex_ok[of r mr \<phi>s]
  unfolding progress_regex_def by fastforce

lemma to_mregex_progress: "Regex.safe_regex fv rgx_safe_pred m g r \<Longrightarrow> to_mregex r = (mr, \<phi>s) \<Longrightarrow>
  progress_regex \<sigma> P r j = (if \<phi>s = [] then j else (MIN \<phi>\<in>set \<phi>s. progress \<sigma> P \<phi> j))"
  using to_mregex_nonempty_progress[of m g r mr \<phi>s \<sigma> P] to_mregex_empty_progress[of m g r mr \<sigma> P]
  unfolding progress_regex_def by auto


subsection \<open> N-ary buffers \<close>

definition wf_mbufn :: "nat \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> event_data table \<Rightarrow> bool) list \<Rightarrow> event_data mbufn \<Rightarrow> bool" where
  "wf_mbufn i js Ps buf \<longleftrightarrow> list_all3 (\<lambda>P j xs. i \<le> j \<and> list_all2 P [i..<j] xs) Ps js buf"

lemma wf_mbufn_add:
  assumes "wf_mbufn i js Ps buf"
    and "list_all3 list_all2 Ps (List.map2 (\<lambda>j j'. [j..<j']) js js') xss"
    and "list_all2 (\<le>) js js'"
  shows "wf_mbufn i js' Ps (mbufn_add xss buf)"
  unfolding wf_mbufn_def list_all3_conv_all_nth
proof safe
  show "length Ps = length js'" "length js' = length (mbufn_add xss buf)"
    using assms unfolding wf_mbufn_def list_all3_conv_all_nth list_all2_conv_all_nth by auto
next
  fix k assume k: "k < length Ps"
  then show "i \<le> js' ! k"
    using assms unfolding wf_mbufn_def list_all3_conv_all_nth list_all2_conv_all_nth
    by (auto 0 4 dest: spec[of _ i])
  from k have " [i..<js' ! k] =  [i..<js ! k] @ [js ! k ..<js' ! k]" and
    "length [i..<js ! k] = length (buf ! k)"
    using assms(1,3) unfolding wf_mbufn_def list_all3_conv_all_nth list_all2_conv_all_nth
    by (auto simp: upt_append)
  with k show "list_all2 (Ps ! k) [i..<js' ! k] (mbufn_add xss buf ! k)"
    using assms[unfolded wf_mbufn_def list_all3_conv_all_nth]
    by (auto simp add: list_all2_append)
qed

lemma wf_mbufn_notin_set:
  assumes "wf_mbufn i js Ps buf"
  shows "[] \<notin> set buf \<Longrightarrow> j \<in> set js \<Longrightarrow> i < j"
  using assms unfolding wf_mbufn_def list_all3_conv_all_nth
  by (cases "i \<in> set js") (auto intro: le_neq_implies_less simp: in_set_conv_nth)

lemma wf_mbufn_map_tl:
  "wf_mbufn i js Ps buf \<Longrightarrow> [] \<notin> set buf \<Longrightarrow> wf_mbufn (Suc i) js Ps (map tl buf)"
  by (auto simp: wf_mbufn_def list_all3_map Suc_le_eq
      dest: rel_funD[OF tl_transfer]  elim!: list_all3_mono_strong le_neq_implies_less)

definition Mini where
  "Mini i js = (if js = [] then i else Min (set js))"

lemma wf_mbufn_in_set_Mini:
  assumes "wf_mbufn i js Ps buf"
  shows "[] \<in> set buf \<Longrightarrow> Mini i js = i"
  unfolding in_set_conv_nth
proof (elim exE conjE)
  fix k
  have "i \<le> j" if "j \<in> set js" for j
    using that assms unfolding wf_mbufn_def list_all3_conv_all_nth in_set_conv_nth by auto
  moreover assume "k < length buf" "buf ! k = []"
  ultimately show ?thesis using assms
    unfolding Mini_def wf_mbufn_def list_all3_conv_all_nth
    by (auto 0 4 dest!: spec[of _ k] intro: Min_eqI simp: in_set_conv_nth)
qed

lemma mbufnt_take_nt:
  assumes "mbufnt_take f z buf t nts = (z', buf', nt, nts')"
  shows "nt = hd (nts' @ rev nts @ [t])"
  using assms
  by (induction f z buf t nts arbitrary: z' buf' nt nts' rule: mbufnt_take.induct)
     (auto simp add: hd_append split: list.splits if_splits)

lemma mbufnt_take_eqD:
  assumes "mbufnt_take f z buf t nts = (z', buf', nt, nts')"
    and "wf_mbufn i js Ps buf"
    and "list_all2 R [i..<j] nts"
    and "\<And>k. k \<in> set js \<Longrightarrow> k \<le> j"
    and "k = Mini (i + length nts) js"
  shows "wf_mbufn k js Ps buf'"
    and "list_all2 R [k..<j] nts'"
  using assms(1-4) unfolding assms(5)
proof (induction f z buf t nts arbitrary: i z' buf' nt nts' rule: mbufnt_take.induct)
  case IH: (1 f z buf t nts)
  note mbufnt_take.simps[simp del]
  case 1
  then have *: "list_all2 R [Suc i..<j] (tl nts)"
    by (auto simp: list.rel_sel[of R "[i..<j]" nts, simplified])
  from 1 show ?case
    using wf_mbufn_in_set_Mini[OF 1(2)]
    by (subst (asm) mbufnt_take.simps)
      (force simp: Mini_def wf_mbufn_def split: if_splits prod.splits elim!: list_all3_mono_strong
        dest!: IH(1)[rotated, OF _ wf_mbufn_map_tl[OF 1(2)] *])
  case 2
  then have *: "list_all2 R [Suc i..<j] (tl nts)"
    by (auto simp: list.rel_sel[of R "[i..<j]" nts, simplified])
  have [simp]: "Suc (i + (length nts - Suc 0)) = i + length nts" if "nts \<noteq> []"
    using that by (fastforce simp flip: length_greater_0_conv)
  with 2 show ?case
    using wf_mbufn_in_set_Mini[OF 2(2)] wf_mbufn_notin_set[OF 2(2)]
    by (subst (asm) mbufnt_take.simps) (force simp: Mini_def wf_mbufn_def
        dest!: IH(2)[rotated, OF _ wf_mbufn_map_tl[OF 2(2)] *]
        split: if_splits prod.splits)
qed

definition wf_mbufn' :: "Formula.trace \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat 
  \<Rightarrow> event_data list set \<Rightarrow> ty Formula.formula Regex.regex 
  \<Rightarrow> event_data mbufn \<Rightarrow> bool" 
  where "wf_mbufn' \<sigma>  P V j n R r buf 
  \<longleftrightarrow> (case to_mregex r of (mr, \<phi>s) \<Rightarrow>
    wf_mbufn (progress_regex \<sigma> P r j) (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) \<phi>s)
    (map (\<lambda>\<phi> i r. sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> r) \<phi>s)
    buf)"

lemma wf_mbufn'_0: "to_mregex r = (mr, \<phi>s) \<Longrightarrow> pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow> wf_mbufn' \<sigma> P V 0 n R r (replicate (length \<phi>s) [])"
  unfolding wf_mbufn'_def wf_mbufn_def map_replicate_const[symmetric]
  by (auto simp: list_all3_map intro: list_all3_refl simp: Min_eq_iff progress_regex_def)

definition wf_ts_regex :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> ty Formula.formula Regex.regex \<Rightarrow> ts list \<Rightarrow> bool" 
  where "wf_ts_regex \<sigma> P j r ts \<longleftrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> P r j..<j] ts"

lemma wf_ts_regex_0: "wf_ts_regex \<sigma> P 0 r []"
  unfolding wf_ts_regex_def by simp

lemma mbufnt_take_add':
  assumes eq: "mbufnt_take f z (mbufn_add xss buf) t nts = (z', buf', nt, nts')"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and rm: "rel_mapping (\<le>) P P'"
    and safe: "Regex.safe_regex fv rgx_safe_pred m g r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and pre_buf: "wf_mbufn' \<sigma> P V j n R r buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> P r j..<j'] nts"
    and xss: "list_all3 list_all2
     (map (\<lambda>\<phi> i r. sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> r) \<phi>s)
     (map2 upt (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) \<phi>s) (map (\<lambda>\<phi>. progress \<sigma> P' \<phi> j') \<phi>s)) xss"
    and "j \<le> j'"
  shows "wf_mbufn' \<sigma> P' V j' n R r buf'"
    and "wf_ts_regex \<sigma> P' j' r nts'"
  using pre_buf pre_nts bounded rm mr safe xss \<open>j \<le> j'\<close>  unfolding wf_mbufn'_def wf_ts_regex_def
  using atms_empty_progress[of m g r] to_mregex_ok[OF mr]
  by (auto 0 3 simp: list.rel_map to_mregex_empty_progress to_mregex_nonempty_progress Mini_def
      intro: progress_mono_gen[OF \<open>j \<le> j'\<close> bounded rm] list.rel_refl_strong progress_le_gen
      dest: list_all2_lengthD elim!: mbufnt_take_eqD[OF eq wf_mbufn_add])

lemma mbufnt_take_induct[consumes 5, case_names base step]:
  assumes "mbufnt_take f z buf t nts = (z', buf', nt, nts')"
    and "wf_mbufn i js Ps buf"
    and "list_all2 R [i..<j] nts"
    and "\<And>k. k \<in> set js \<Longrightarrow> k \<le> j"
    and "U i z"
    and "\<And>k xs t z. i \<le> k \<Longrightarrow> Suc k \<le> Mini j js \<Longrightarrow>
      list_all2 (\<lambda>P x. P k x) Ps xs \<Longrightarrow> R k t \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f xs t z)"
  shows "U (Mini (i + length nts) js) z'"
  using assms
proof (induction f z buf t nts arbitrary: i z' buf' nt nts' rule: mbufnt_take.induct)
  case (1 f z buf t nts)
  then have *: "list_all2 R [Suc i..<j] (tl nts)"
    by (auto simp: list.rel_sel[of R "[i..<j]" nts, simplified])
  note mbufnt_take.simps[simp del]
  from 1(2-6) have "i = Min (set js)" if "js \<noteq> []" "nts = []"
    using that unfolding wf_mbufn_def using wf_mbufn_in_set_Mini[OF 1(3)]
    by (fastforce simp: Mini_def list_all3_Cons neq_Nil_conv)
  with 1(2-7) list_all2_hdD[OF 1(4)] show ?case
    unfolding wf_mbufn_def using wf_mbufn_in_set_Mini[OF 1(3)] wf_mbufn_notin_set[OF 1(3)]
    by (subst (asm) mbufnt_take.simps)
      (auto simp add: Mini_def list.rel_map Suc_le_eq
        elim!: arg_cong2[of _ _ _ _ U, OF _ refl, THEN iffD1, rotated]
        list_all3_mono_strong[THEN list_all3_list_all2I[of _ _ js]] list_all2_hdD
        dest!: 1(1)[rotated, OF _ wf_mbufn_map_tl[OF 1(3)] * _ 1(7)] split: prod.split if_splits)
qed

lemma mbufnt_take_add_induct'[consumes 6, case_names base step]:
  assumes eq: "mbufnt_take f z (mbufn_add xss buf) t nts = (z', buf', nt, nts')"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and rm: "rel_mapping (\<le>) P P'"
    and safe: "Regex.safe_regex fv rgx_safe_pred m g r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and pre_buf: "wf_mbufn' \<sigma> P V j n R r buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> P r j..<j'] nts"
    and xss: "list_all3 list_all2
     (map (\<lambda>\<phi> i r. sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> r) \<phi>s)
     (map2 upt (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) \<phi>s) (map (\<lambda>\<phi>. progress \<sigma> P' \<phi> j') \<phi>s)) xss"
    and "j \<le> j'"
    and base: "U (progress_regex \<sigma> P r j) z"
    and step: "\<And>k Xs z. progress_regex \<sigma> P r j \<le> k \<Longrightarrow> Suc k \<le> progress_regex \<sigma> P' r j' \<Longrightarrow>
      list_all2 (\<lambda>\<phi> r. sat_table \<sigma> V n R (Formula.fv_list \<phi>) k \<phi> r) \<phi>s Xs \<Longrightarrow>
      U k z \<Longrightarrow> U (Suc k) (f Xs (\<tau> \<sigma> k) z)"
  shows "U (progress_regex \<sigma> P' r j') z'"
  using pre_buf pre_nts bounded rm \<open>j \<le> j'\<close> to_mregex_progress[OF safe mr, of \<sigma> P' j'] 
    to_mregex_empty_progress[OF safe, of mr \<sigma> P j] base
  unfolding wf_mbufn'_def mr prod.case
  by (fastforce dest!: mbufnt_take_induct[OF eq wf_mbufn_add[OF _ xss] pre_nts, of U]
      simp: list.rel_map le_imp_diff_is_add ac_simps Mini_def
      intro: progress_mono_gen[OF \<open>j \<le> j'\<close> bounded rm] list.rel_refl_strong progress_le_gen
      intro!: base step  dest: list_all2_lengthD split: if_splits)

lemma wf_mbufn_take:
  assumes "mbufn_take f z buf = (z', buf')"
    and "wf_mbufn i js Ps buf"
  shows "wf_mbufn (Mini i js) js Ps buf'"
  using assms unfolding wf_mbufn_def
proof (induction f z buf arbitrary: i z' buf' rule: mbufn_take.induct)
  case rec: (1 f z buf)
  show ?case proof (cases "buf = []")
    case True
    with rec.prems show ?thesis by simp
  next
    case nonempty: False
    show ?thesis proof (cases "[] \<in> set buf")
      case True
      from rec.prems(2) have "\<forall>j\<in>set js. i \<le> j"
        by (auto simp: in_set_conv_nth list_all3_conv_all_nth)
      moreover from True rec.prems(2) have "i \<in> set js"
        by (fastforce simp: in_set_conv_nth list_all3_conv_all_nth list_all2_iff)
      ultimately have "Mini i js = i"
        unfolding Mini_def
        by (auto intro!: antisym[OF Min.coboundedI Min.boundedI])
      with rec.prems nonempty True show ?thesis by simp
    next
      case False
      from nonempty rec.prems(2) have "Mini i js = Mini (Suc i) js"
        unfolding Mini_def by auto
      show ?thesis
        unfolding \<open>Mini i js = Mini (Suc i) js\<close>
      proof (rule rec.IH)
        show "\<not> (buf = [] \<or> [] \<in> set buf)" using nonempty False by simp
        show "list_all3 (\<lambda>P j xs. Suc i \<le> j \<and> list_all2 P [Suc i..<j] xs) Ps js (map tl buf)"
          using False rec.prems(2)
          by (auto simp: list_all3_map elim!: list_all3_mono_strong dest: list.rel_sel[THEN iffD1])
        show "mbufn_take f (f (map hd buf) z) (map tl buf) = (z', buf')"
          using nonempty False rec.prems(1) by simp
      qed
    qed
  qed
qed

lemma mbufn_take_induct[consumes 3, case_names base step]:
  assumes "mbufn_take f z buf = (z', buf')"
    and "wf_mbufn i js Ps buf"
    and "U i z"
    and "\<And>k xs z. i \<le> k \<Longrightarrow> Suc k \<le> Mini i js \<Longrightarrow>
      list_all2 (\<lambda>P x. P k x) Ps xs \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f xs z)"
  shows "U (Mini i js) z'"
  using assms unfolding wf_mbufn_def
proof (induction f z buf arbitrary: i z' buf' rule: mbufn_take.induct)
  case rec: (1 f z buf)
  show ?case proof (cases "buf = []")
    case True
    with rec.prems show ?thesis unfolding Mini_def by simp
  next
    case nonempty: False
    show ?thesis proof (cases "[] \<in> set buf")
      case True
      from rec.prems(2) have "\<forall>j\<in>set js. i \<le> j"
        by (auto simp: in_set_conv_nth list_all3_conv_all_nth)
      moreover from True rec.prems(2) have "i \<in> set js"
        by (fastforce simp: in_set_conv_nth list_all3_conv_all_nth list_all2_iff)
      ultimately have "Mini i js = i"
        unfolding Mini_def
        by (auto intro!: antisym[OF Min.coboundedI Min.boundedI])
      with rec.prems nonempty True show ?thesis by simp
    next
      case False
      with nonempty rec.prems(2) have more: "Suc i \<le> Mini i js"
        using diff_is_0_eq not_le unfolding Mini_def
        by (fastforce simp: in_set_conv_nth list_all3_conv_all_nth list_all2_iff)
      then have "Mini i js = Mini (Suc i) js" unfolding Mini_def by auto
      show ?thesis
        unfolding \<open>Mini i js = Mini (Suc i) js\<close>
      proof (rule rec.IH)
        show "\<not> (buf = [] \<or> [] \<in> set buf)" using nonempty False by simp
        show "mbufn_take f (f (map hd buf) z) (map tl buf) = (z', buf')"
          using nonempty False rec.prems by simp
        show "list_all3 (\<lambda>P j xs. Suc i \<le> j \<and> list_all2 P [Suc i..<j] xs) Ps js (map tl buf)"
          using False rec.prems
          by (auto simp: list_all3_map elim!: list_all3_mono_strong dest: list.rel_sel[THEN iffD1])
        show "U (Suc i) (f (map hd buf) z)"
          using more False rec.prems
          by (auto 0 4 simp: list_all3_map intro!: rec.prems(4) list_all3_list_all2I
              elim!: list_all3_mono_strong dest: list.rel_sel[THEN iffD1])
        show "\<And>k xs z. Suc i \<le> k \<Longrightarrow> Suc k \<le> Mini (Suc i) js \<Longrightarrow>
          list_all2 (\<lambda>P. P k) Ps xs \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f xs z)"
          by (rule rec.prems(4)) (auto simp: Mini_def)
      qed
    qed
  qed
qed


subsection \<open> Tables of empty matches \<close>

lemma qtable_\<epsilon>_lax:
  assumes "ok (length \<phi>s) mr"
    and "list_all2 (\<lambda>\<phi> rel. sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> rel) \<phi>s rels"
    and "fv_regex (from_mregex mr \<phi>s) \<subseteq> set A" and "distinct A"
    and "qtable A (mem_restr R A) Q guard"
  shows "qtable A (mem_restr R A)
   (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (val n A v)) i (from_mregex mr \<phi>s) \<and> Q v)
   (\<epsilon>_lax A (map Formula.fv_list \<phi>s) guard rels mr)"
  using assms
proof (induct mr)
  case (MSkip m)
  then show ?case
    by (cases "m = 0") (simp_all add: qtable_empty_iff)
next
  case (MTestPos k)
  from MTestPos(1,2) have rel: "sat_table \<sigma> V n R (Formula.fv_list (\<phi>s ! k)) i (\<phi>s ! k) (rels ! k)"
    by (simp add: list_all2_conv_all_nth)
  from MTestPos(3) have "Formula.fv (\<phi>s ! k) \<subseteq> set A"
    by simp
  moreover from MTestPos(1) have "k < length \<phi>s"
    by simp
  ultimately show ?case
    unfolding \<epsilon>_lax.simps
    by (subst nth_map) (auto intro!: qtable_join_sub[OF MTestPos(5) rel MTestPos(4)] simp: sat_restrict)
next
  case (MTestNeg k)
  from MTestNeg(1,2) have rel: "sat_table \<sigma> V n R (Formula.fv_list (\<phi>s ! k)) i (\<phi>s ! k) (rels ! k)"
    by (simp add: list_all2_conv_all_nth)
  from MTestNeg(3) have "Formula.fv (\<phi>s ! k) \<subseteq> set A"
    by (simp split: if_splits)
  moreover from MTestNeg(1) have "k < length \<phi>s"
    by simp
  ultimately show ?case
    unfolding \<epsilon>_lax.simps
    by (subst nth_map) (auto intro!: qtable_join_sub[OF MTestNeg(5) rel MTestNeg(4)] simp: sat_restrict)
next
  case (MPlus mr1 mr2)
  from MPlus(3-7) show ?case
    by (auto intro!: qtable_union[OF MPlus(1,2)])
next
  case (MTimes mr1 mr2)
  then have "fv_regex (from_mregex mr1 \<phi>s) \<subseteq> set A" "fv_regex (from_mregex mr2 \<phi>s) \<subseteq> set A"
    using fv_regex_from_mregex[of \<phi>s mr1] fv_regex_from_mregex[of \<phi>s mr2] by (auto simp: subset_eq)
  with MTimes(3-7) show ?case
    by (auto simp: restrict_idle intro!: qtable_join_sub[OF MTimes(1,2)])
next
  case (MStar mr)
  then show ?case
    by simp
qed

lemma qtable_r\<epsilon>_strict:
  assumes "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<phi>s)" "ok (length \<phi>s) mr"
    and "set A = fv_regex (from_mregex mr \<phi>s)" "distinct A"
    and "list_all2 (\<lambda>\<phi> rel. sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> rel) \<phi>s rels"
  shows "qtable A (mem_restr R A) (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (val n A v)) i (from_mregex mr \<phi>s))
    (r\<epsilon>_strict A (map Formula.fv_list \<phi>s) rels mr)"
  using assms
proof (induct Past Strict "from_mregex mr \<phi>s" arbitrary: mr A rule: safe_regex_induct)
  case (Skip n)
  then have "A = []"
    by (cases mr) (auto split: if_splits)
  with Skip show ?case
    by (cases mr) (auto simp: qtable_empty_iff qtable_unit_table split: if_splits)
next
  case (Test \<phi>)
  from Test.hyps Test.prems(2) obtain k where k: "k < length \<phi>s"
    and mr: "mr = MTestPos k \<or> mr = MTestNeg k"
    by (cases mr) auto
  from Test.prems(5) k have rel: "sat_table \<sigma> V n R (Formula.fv_list (\<phi>s ! k)) i (\<phi>s ! k) (rels ! k)"
    by (simp add: list_all2_conv_all_nth)
  from mr show ?case
  proof
    assume mr: "mr = MTestPos k"
    with Test.prems(3) have A: "set A = set (Formula.fv_list (\<phi>s ! k))"
      by simp
    show ?case
      unfolding mr r\<epsilon>_strict.simps from_mregex.simps nth_map[OF k]
      by (rule qtable_reorder_mem_restr[OF rel Test.prems(4) distinct_fvi_list A])
        (simp add: sat_restrict)
  next
    assume mr: "mr = MTestNeg k"
    with Test.hyps Test.prems(1,3) have A: "A = []" and "Formula.fv (\<phi>s ! k) = {}"
      by (auto split: if_splits)
    then have "Formula.fv_list (\<phi>s ! k) = []"
      by (metis set_empty set_fvi_list)
    with rel have rel': "sat_table \<sigma> V n R [] i (\<phi>s ! k) (rels ! k)"
      by simp
    show ?case
    proof (cases "rels ! k = empty_table")
      case True
      with rel' have "qtable [] (mem_restr R []) (\<lambda>v. \<not> Formula.sat \<sigma> V (val n [] v) i (\<phi>s ! k)) unit_table"
        by (intro qtable_empty_unit_table) simp
      with True show ?thesis
        unfolding mr A r\<epsilon>_strict.simps
        by (auto elim!: qtable_cong)
    next
      case False
      then obtain x where "x \<in> rels ! k"
        by (auto simp: empty_table_def)
      from qtable_nonempty_empty_table[OF rel' this] False show ?thesis
        unfolding mr A r\<epsilon>_strict.simps
        by (auto elim!: qtable_cong)
    qed
  qed
next
  case (Plus r s)
  from Plus(3) obtain mr1 mr2 where mr: "mr = MPlus mr1 mr2"
    and r: "r = from_mregex mr1 \<phi>s" and s: "s = from_mregex mr2 \<phi>s"
    by (cases mr) (simp_all split: if_splits)
  from Plus.prems have safe1: "Regex.safe_regex fv rgx_safe_pred Past Strict r"
    and safe2: "Regex.safe_regex fv rgx_safe_pred Past Strict s"
    and fv: "fv_regex s = fv_regex r" and ok1: "ok (length \<phi>s) mr1" and ok2: "ok (length \<phi>s) mr2"
    by (simp_all add: mr r s)
  have fv_mr: "fv_regex (from_mregex mr \<phi>s) = fv_regex r"
    using fv by (simp add: mr r s)
  have IH1: "qtable A (mem_restr R A)
    (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (val n A v)) i r) (r\<epsilon>_strict A (map Formula.fv_list \<phi>s) rels mr1)"
    using Plus(1)[of mr1 A] safe1 ok1 Plus.prems fv_mr by (simp add: r)
  have IH2: "qtable A (mem_restr R A)
    (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (val n A v)) i s) (r\<epsilon>_strict A (map Formula.fv_list \<phi>s) rels mr2)"
    using Plus(2)[of mr2 A] safe2 ok2 Plus.prems fv_mr fv by (simp add: s)
  show ?case
    unfolding mr r\<epsilon>_strict.simps
    by (rule qtable_union[OF IH1 IH2]) (simp add: r s)
next
  case (TimesP r s)
  from TimesP.hyps(2) obtain mr1 mr2 where mr: "mr = MTimes mr1 mr2"
    and r: "r = from_mregex mr1 \<phi>s" and s: "s = from_mregex mr2 \<phi>s"
    by (cases mr) (simp_all split: if_splits)
  from TimesP.prems have safe1: "Regex.safe_regex fv rgx_safe_pred Past Strict r"
    and fv: "fv_regex s \<subseteq> fv_regex r" and ok1: "ok (length \<phi>s) mr1" and ok2: "ok (length \<phi>s) mr2"
    by (simp_all add: mr r s)
  have fv_mr: "fv_regex (from_mregex mr \<phi>s) = fv_regex r"
    using fv by (auto simp: mr r s)
  have IH: "qtable A (mem_restr R A)
    (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (val n A v)) i r) (r\<epsilon>_strict A (map Formula.fv_list \<phi>s) rels mr1)"
    using TimesP(1)[of mr1 A] safe1 ok1 TimesP.prems fv_mr by (simp add: r)
  have fv2: "fv_regex (from_mregex mr2 \<phi>s) \<subseteq> set A"
    using TimesP.prems(3) fv_mr fv by (simp add: s)
  show ?case
    unfolding mr r\<epsilon>_strict.simps
    by (rule qtable_cong[OF qtable_\<epsilon>_lax[OF ok2 TimesP.prems(5) fv2 TimesP.prems(4) IH]])
      (auto simp: r s)
next
  case (Star r)
  then have "A = []"
    by (cases mr) (auto split: if_splits)
  with Star show ?case
    by (cases mr) (auto simp: qtable_unit_table split: if_splits)
qed

lemma qtable_l\<epsilon>_strict:
  assumes "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<phi>s)" "ok (length \<phi>s) mr"
    and "set A = fv_regex (from_mregex mr \<phi>s)" "distinct A"
    and "list_all2 (\<lambda>\<phi> rel. sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> rel) \<phi>s rels"
  shows "qtable A (mem_restr R A) (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (val n A v)) i (from_mregex mr \<phi>s))
    (l\<epsilon>_strict A (map Formula.fv_list \<phi>s) rels mr)"
  using assms
proof (induct Futu Strict "from_mregex mr \<phi>s" arbitrary: mr A rule: safe_regex_induct)
  case (Skip n)
  then have "A = []"
    by (cases mr) (auto split: if_splits)
  with Skip show ?case
    by (cases mr) (auto simp: qtable_empty_iff qtable_unit_table split: if_splits)
next
  case (Test \<phi>)
  from Test.hyps Test.prems(2) obtain k where k: "k < length \<phi>s"
    and mr: "mr = MTestPos k \<or> mr = MTestNeg k"
    by (cases mr) auto
  from Test.prems(5) k have rel: "sat_table \<sigma> V n R (Formula.fv_list (\<phi>s ! k)) i (\<phi>s ! k) (rels ! k)"
    by (simp add: list_all2_conv_all_nth)
  from mr show ?case
  proof
    assume mr: "mr = MTestPos k"
    with Test.prems(3) have A: "set A = set (Formula.fv_list (\<phi>s ! k))"
      by simp
    show ?case
      unfolding mr l\<epsilon>_strict.simps from_mregex.simps nth_map[OF k]
      by (rule qtable_reorder_mem_restr[OF rel Test.prems(4) distinct_fvi_list A])
        (simp add: sat_restrict)
  next
    assume mr: "mr = MTestNeg k"
    with Test.hyps Test.prems(1,3) have A: "A = []" and "Formula.fv (\<phi>s ! k) = {}"
      by (auto split: if_splits)
    then have "Formula.fv_list (\<phi>s ! k) = []"
      by (metis set_empty set_fvi_list)
    with rel have rel': "sat_table \<sigma> V n R [] i (\<phi>s ! k) (rels ! k)"
      by simp
    show ?case
    proof (cases "rels ! k = empty_table")
      case True
      with rel' have "qtable [] (mem_restr R []) (\<lambda>v. \<not> Formula.sat \<sigma> V (val n [] v) i (\<phi>s ! k)) unit_table"
        by (intro qtable_empty_unit_table) simp
      with True show ?thesis
        unfolding mr A l\<epsilon>_strict.simps
        by (auto elim!: qtable_cong)
    next
      case False
      then obtain x where "x \<in> rels ! k"
        by (auto simp: empty_table_def)
      from qtable_nonempty_empty_table[OF rel' this] False show ?thesis
        unfolding mr A l\<epsilon>_strict.simps
        by (auto elim!: qtable_cong)
    qed
  qed
next
  case (Plus r s)
  from Plus(3) obtain mr1 mr2 where mr: "mr = MPlus mr1 mr2"
    and r: "r = from_mregex mr1 \<phi>s" and s: "s = from_mregex mr2 \<phi>s"
    by (cases mr) (simp_all split: if_splits)
  from Plus.prems have safe1: "Regex.safe_regex fv rgx_safe_pred Futu Strict r"
    and safe2: "Regex.safe_regex fv rgx_safe_pred Futu Strict s"
    and fv: "fv_regex s = fv_regex r" and ok1: "ok (length \<phi>s) mr1" and ok2: "ok (length \<phi>s) mr2"
    by (simp_all add: mr r s)
  have fv_mr: "fv_regex (from_mregex mr \<phi>s) = fv_regex r"
    using fv by (simp add: mr r s)
  have IH1: "qtable A (mem_restr R A)
    (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (val n A v)) i r) (l\<epsilon>_strict A (map Formula.fv_list \<phi>s) rels mr1)"
    using Plus(1)[of mr1 A] safe1 ok1 Plus.prems fv_mr by (simp add: r)
  have IH2: "qtable A (mem_restr R A)
    (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (val n A v)) i s) (l\<epsilon>_strict A (map Formula.fv_list \<phi>s) rels mr2)"
    using Plus(2)[of mr2 A] safe2 ok2 Plus.prems fv_mr fv by (simp add: s)
  show ?case
    unfolding mr l\<epsilon>_strict.simps
    by (rule qtable_union[OF IH1 IH2]) (simp add: r s)
next
  case (TimesF r s)
  from TimesF.hyps(2) obtain mr1 mr2 where mr: "mr = MTimes mr1 mr2"
    and r: "r = from_mregex mr1 \<phi>s" and s: "s = from_mregex mr2 \<phi>s"
    by (cases mr) (simp_all split: if_splits)
  from TimesF.prems have safe2: "Regex.safe_regex fv rgx_safe_pred Futu Strict s"
    and fv: "fv_regex r \<subseteq> fv_regex s" and ok1: "ok (length \<phi>s) mr1" and ok2: "ok (length \<phi>s) mr2"
    by (simp_all add: mr r s)
  have fv_mr: "fv_regex (from_mregex mr \<phi>s) = fv_regex s"
    using fv by (auto simp: mr r s)
  have IH: "qtable A (mem_restr R A)
    (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (val n A v)) i s) (l\<epsilon>_strict A (map Formula.fv_list \<phi>s) rels mr2)"
    using TimesF(1)[of mr2 A] safe2 ok2 TimesF.prems fv_mr by (simp add: s)
  have fv1: "fv_regex (from_mregex mr1 \<phi>s) \<subseteq> set A"
    using TimesF.prems(3) fv_mr fv by (simp add: r)
  show ?case
    unfolding mr l\<epsilon>_strict.simps
    by (rule qtable_cong[OF qtable_\<epsilon>_lax[OF ok1 TimesF.prems(5) fv1 TimesF.prems(4) IH]])
      (auto simp: r s)
next
  case (Star r)
  then have "A = []"
    by (cases mr) (auto split: if_splits)
  with Star show ?case
    by (cases mr) (auto simp: qtable_unit_table split: if_splits)
qed


subsection \<open> Tables of derivatives \<close>

inductive ok_rctxt for \<phi>s where
  "ok_rctxt \<phi>s id id"
| "ok_rctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> ok_rctxt \<phi>s (\<lambda>t. \<kappa> (MTimes mr t)) (\<lambda>t. \<kappa>' (Regex.Times (from_mregex mr \<phi>s) t))"

lemma ok_rctxt_swap: "ok_rctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> from_mregex (\<kappa> mr) \<phi>s = \<kappa>' (from_mregex mr \<phi>s)"
  by (induct \<kappa> \<kappa>' arbitrary: mr rule: ok_rctxt.induct) auto

lemma ok_rctxt_cong: "ok_rctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> Regex.match (Formula.sat \<sigma> V v) r = Regex.match (Formula.sat \<sigma> V v) s \<Longrightarrow>
  Regex.match (Formula.sat \<sigma> V v) (\<kappa>' r) i j = Regex.match (Formula.sat \<sigma> V v) (\<kappa>' s) i j"
  by (induct \<kappa> \<kappa>' arbitrary: r s rule: ok_rctxt.induct) simp_all

lemma qtable_r\<delta>\<kappa>:
  assumes "ok (length \<phi>s) mr" "fv_regex (from_mregex mr \<phi>s) \<subseteq> set A"
    and "list_all2 (\<lambda>\<phi> rel. sat_table \<sigma> V n R (Formula.fv_list \<phi>) j \<phi> rel) \<phi>s rels"
    and "ok_rctxt \<phi>s \<kappa> \<kappa>'"
    and "\<forall>ms \<in> \<kappa> ` RPD mr. qtable A (mem_restr R A) (\<lambda>v. Q (val n A v) (from_mregex ms \<phi>s)) (lookup rel ms)"
    and "distinct A"
  shows "qtable A (mem_restr R A)
  (\<lambda>v. \<exists>s \<in> Regex.rpd\<kappa> \<kappa>' (Formula.sat \<sigma> V (val n A v)) j (from_mregex mr \<phi>s). Q (val n A v) s)
  (r\<delta> A (map Formula.fv_list \<phi>s) \<kappa> rel rels mr)"
  using assms
proof (induct mr arbitrary: \<kappa> \<kappa>')
  case MSkip
  then show ?case
    by (auto simp: rtranclp_False ok_rctxt_swap qtable_empty_iff
        elim!: qtable_cong[OF _ _ ok_rctxt_cong[of _ \<kappa> \<kappa>']] split: nat.splits)
next
  case (MPlus mr1 mr2)
  from MPlus(3-8) show ?case
    by (auto intro!: qtable_union[OF MPlus(1,2)])
next
  case (MTimes mr1 mr2)
  from MTimes(3-8) show ?case
    by (auto intro!: qtable_union[OF MTimes(2) qtable_\<epsilon>_lax[OF _ _ _ _ MTimes(1)]]
        elim!: ok_rctxt.intros(2) simp: MTimesL_def Ball_def)
next
  case (MStar mr)
  from MStar(2-7) show ?case
    by (auto intro!: qtable_cong[OF MStar(1)] intro: ok_rctxt.intros simp: MTimesL_def Ball_def)
qed (auto simp: qtable_empty_iff)

lemmas qtable_r\<delta> = qtable_r\<delta>\<kappa>[OF _ _ _ ok_rctxt.intros(1), unfolded rpd\<kappa>_rpd image_id id_apply]

inductive ok_lctxt for \<phi>s where
  "ok_lctxt \<phi>s id id"
| "ok_lctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> ok_lctxt \<phi>s (\<lambda>t. \<kappa> (MTimes t mr)) (\<lambda>t. \<kappa>' (Regex.Times t (from_mregex mr \<phi>s)))"

lemma ok_lctxt_swap: "ok_lctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> from_mregex (\<kappa> mr) \<phi>s = \<kappa>' (from_mregex mr \<phi>s)"
  by (induct \<kappa> \<kappa>' arbitrary: mr rule: ok_lctxt.induct) auto

lemma qtable_l\<delta>\<kappa>:
  assumes "ok (length \<phi>s) mr" "fv_regex (from_mregex mr \<phi>s) \<subseteq> set A"
    and "list_all2 (\<lambda>\<phi> rel. sat_table \<sigma> V n R (Formula.fv_list \<phi>) j \<phi> rel) \<phi>s rels"
    and "ok_lctxt \<phi>s \<kappa> \<kappa>'"
    and "\<forall>ms \<in> \<kappa> ` LPD mr. qtable A (mem_restr R A) (\<lambda>v. Q (val n A v) (from_mregex ms \<phi>s)) (lookup rel ms)"
    and "distinct A"
  shows "qtable A (mem_restr R A)
  (\<lambda>v. \<exists>s \<in> Regex.lpd\<kappa> \<kappa>' (Formula.sat \<sigma> V (val n A v)) j (from_mregex mr \<phi>s). Q (val n A v) s)
  (l\<delta> A (map Formula.fv_list \<phi>s) \<kappa> rel rels mr)"
  using assms
proof (induct mr arbitrary: \<kappa> \<kappa>')
  case MSkip
  then show ?case
    by (auto simp: rtranclp_False ok_lctxt_swap qtable_empty_iff
        elim!: qtable_cong[OF _ _ ok_rctxt_cong[of _ \<kappa> \<kappa>']] split: nat.splits)
next
  case (MPlus mr1 mr2)
  from MPlus(3-8) show ?case
    by (auto intro!: qtable_union[OF MPlus(1,2)])
next
  case (MTimes mr1 mr2)
  from MTimes(3-8) show ?case
    by (auto intro!: qtable_union[OF MTimes(1) qtable_\<epsilon>_lax[OF _ _ _ _ MTimes(2)]]
        elim!: ok_lctxt.intros(2) simp: MTimesR_def Ball_def)
next
  case (MStar mr)
  from MStar(2-7) show ?case
    by (auto intro!: qtable_cong[OF MStar(1)] intro: ok_lctxt.intros simp: MTimesR_def Ball_def)
qed (auto simp: qtable_empty_iff)

lemmas qtable_l\<delta> = qtable_l\<delta>\<kappa>[OF _ _ _ ok_lctxt.intros(1), unfolded lpd\<kappa>_lpd image_id id_apply]


subsection \<open> Invariants of the auxiliary states \<close>

definition wf_matchP_aux :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
    \<I> \<Rightarrow> ty Formula.formula Regex.regex \<Rightarrow> event_data mr\<delta>aux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_matchP_aux \<sigma> V n R I r aux ne \<longleftrightarrow> sorted_wrt (\<lambda>x y. fst x > fst y) aux \<and>
    (\<forall>t X. (t, X) \<in> set aux \<longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> memR I (\<tau> \<sigma> (ne-1) - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
      (case to_mregex r of (mr, \<phi>s) \<Rightarrow>
      (\<forall>ms \<in> RPDs mr. sat_table \<sigma> V n R (regex_cols r) (ne-1)
         (Formula.MatchP (point (\<tau> \<sigma> (ne-1) - t)) (from_mregex ms \<phi>s))
         (lookup X ms)))) \<and>
    (\<forall>t. ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> memR I (\<tau> \<sigma> (ne-1) - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<longrightarrow>
      (\<exists>X. (t, X) \<in> set aux))"

lemma wf_matchP_aux_Nil: "wf_matchP_aux \<sigma> V n R I r [] 0"
  unfolding wf_matchP_aux_def by simp

definition wf_matchF_aux :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
    \<I> \<Rightarrow> ty Formula.formula Regex.regex \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_matchF_aux \<sigma> V n R I r aux ne k \<longleftrightarrow> (case to_mregex r of (mr, \<phi>s) \<Rightarrow>
      list_all2 (\<lambda>x i. case x of (t, rels, rel) \<Rightarrow> t = \<tau> \<sigma> i \<and>
        list_all2 (\<lambda>\<phi>. sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi>) \<phi>s rels \<and>
        qtable (regex_cols r) (mem_restr R (regex_cols r)) (\<lambda>v. (\<exists>j. i \<le> j \<and> j < ne + length aux + k \<and>
          mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and> Regex.match (Formula.sat \<sigma> V (val n (regex_cols r) v)) r i j)) rel)
    aux [ne..<ne+length aux])"

lemma wf_matchF_aux_Nil: "wf_matchF_aux \<sigma> V n R I r [] 0 k"
  unfolding wf_matchF_aux_def by simp

lemma wf_matchF_aux_Cons: "wf_matchF_aux \<sigma> V n R I r (entry # aux) ne i \<Longrightarrow>
  wf_matchF_aux \<sigma> V n R I r aux (Suc ne) i"
  unfolding wf_matchF_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc cong: if_cong split: prod.splits)

definition wf_matchF_invar where
  "wf_matchF_invar \<sigma> V n R I r st i =
     (case st of (aux, Y) \<Rightarrow> aux \<noteq> [] \<and> wf_matchF_aux \<sigma> V n R I r aux i 0 \<and>
     (case to_mregex r of (mr, \<phi>s) \<Rightarrow> \<forall>ms \<in> LPDs mr.
       qtable (regex_cols r) (mem_restr R (regex_cols r)) (\<lambda>v.
         Regex.match (Formula.sat \<sigma> V (val n (regex_cols r) v)) (from_mregex ms \<phi>s) i (i + length aux - 1))
         (lookup Y ms)))"

lemma lookup_tabulate:
  "distinct xs \<Longrightarrow> lookup (mrtabulate xs f) x = (if x \<in> set xs then f x else empty_table)"
  unfolding lookup_default_def lookup_def
  by transfer (auto simp: Let_def map_filter_def map_of_eq_None_iff o_def image_image dest!: map_of_SomeD
      split: if_splits option.splits)


subsection \<open> Update for MatchP \<close>

lemma update_matchP:
  assumes pre: "wf_matchP_aux \<sigma> V n R I r aux ne"
    and safe: "Regex.safe_regex fv rgx_safe_pred Past Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (RPDs mr)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. sat_table \<sigma> V n R (Formula.fv_list \<phi>) ne \<phi> rel) \<phi>s rels"
    and result_eq: "(rel, aux') = update_matchP (regex_cols r) (map Formula.fv_list \<phi>s) I mr mrs rels (\<tau> \<sigma> ne) aux"
  shows "wf_matchP_aux \<sigma> V n R I r aux' (Suc ne)"
    and "sat_table \<sigma> V n R (regex_cols r) ne (Formula.MatchP I r) rel"
proof -
  let ?cs = "regex_cols r"
  let ?dss = "map Formula.fv_list \<phi>s"
  let ?update = "\<lambda>rel t. mrtabulate mrs (\<lambda>mr.
    r\<delta> ?cs ?dss id rel rels mr \<union> (if t = \<tau> \<sigma> ne then r\<epsilon>_strict ?cs ?dss rels mr else {}))"
  note sat.simps[simp del]

  define aux0 where "aux0 = [(t, ?update rel t). (t, rel) \<leftarrow> aux, memR I (\<tau> \<sigma> ne - t)]"
  have sorted_aux0: "sorted_wrt (\<lambda>x y. fst x > fst y) aux0"
    using pre[unfolded wf_matchP_aux_def, THEN conjunct1]
    unfolding aux0_def
    by (induction aux) (auto simp add: sorted_wrt_append)
  have safe_mr: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<phi>s)"
    using safe by (simp only: from_mregex_eq[OF safe mr])
  { fix ms
    assume ms: "ms \<in> RPDs mr"
    have fv_ms: "fv_regex (from_mregex ms \<phi>s) = fv_regex r"
      using RPDs_safe_fv_regex[OF safe_mr ms] by (simp only: from_mregex_eq[OF safe mr])
    have safe_ms: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex ms \<phi>s)"
      using safe_mr ms by (rule RPDs_safe)
    have ok_ms: "ok (length \<phi>s) ms"
      using conjunct2[OF to_mregex_ok[OF mr]] ms by (rule RPDs_ok)
    have RPD_ms: "RPD ms \<subseteq> RPDs mr"
      using RPDs_trans[OF _ ms] by (rule subsetI)
    note fv_ms safe_ms ok_ms RPD_ms
  } note * = this
  have in_aux0_1: "(t, X) \<in> set aux0 \<Longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> ne \<and> memR I (\<tau> \<sigma> ne - t) \<and>
      (\<exists>i. \<tau> \<sigma> i = t) \<and>
      (\<forall>ms\<in>RPDs mr. sat_table \<sigma> V n R ?cs ne
         (Formula.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s)) (lookup X ms))" for t X
  proof -
    assume "(t, X) \<in> set aux0"
    then obtain Y where tY: "(t, Y) \<in> set aux" and memR: "memR I (\<tau> \<sigma> ne - t)"
      and X: "X = ?update Y t"
      unfolding aux0_def by (auto simp: id_def)
    from pre[unfolded wf_matchP_aux_def mr prod.case] tY
    have ne: "ne \<noteq> 0" and t_le: "t \<le> \<tau> \<sigma> (ne - 1)" and i: "\<exists>i. \<tau> \<sigma> i = t"
      and Y: "\<forall>ms\<in>RPDs mr. sat_table \<sigma> V n R ?cs (ne - 1)
         (Formula.MatchP (point (\<tau> \<sigma> (ne - 1) - t)) (from_mregex ms \<phi>s)) (lookup Y ms)"
      by blast+
    have \<tau>_le: "\<tau> \<sigma> (ne - 1) \<le> \<tau> \<sigma> ne"
      by (rule \<tau>_mono) simp
    have t_le': "t \<le> \<tau> \<sigma> ne"
      using t_le \<tau>_le by (rule order_trans)
    have "sat_table \<sigma> V n R ?cs ne
         (Formula.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s)) (lookup X ms)"
      if ms: "ms \<in> RPDs mr" for ms
    proof -
      have lookup: "lookup X ms = r\<delta> ?cs ?dss (\<lambda>x. x) Y rels ms \<union>
        (if t = \<tau> \<sigma> ne then r\<epsilon>_strict ?cs ?dss rels ms else {})"
        using ms unfolding X mrs by (simp add: lookup_tabulate finite_RPDs id_def)
      have r\<delta>: "qtable ?cs (mem_restr R ?cs) (\<lambda>v. \<exists>s \<in> Regex.rpd (Formula.sat \<sigma> V (val n ?cs v)) ne
          (from_mregex ms \<phi>s). Formula.sat \<sigma> V (val n ?cs v) (ne - 1) (Formula.MatchP (point (\<tau> \<sigma> (ne - 1) - t)) s))
          (r\<delta> ?cs ?dss (\<lambda>x. x) Y rels ms)"
      proof (rule qtable_r\<delta>[where Q = "\<lambda>v s. Formula.sat \<sigma> V v (ne - 1) (Formula.MatchP (point (\<tau> \<sigma> (ne - 1) - t)) s)",
            OF *(3)[OF ms] _ qtables])
        show "fv_regex (from_mregex ms \<phi>s) \<subseteq> set ?cs"
          using *(1)[OF ms] by simp
        show "\<forall>ms'\<in>RPD ms. sat_table \<sigma> V n R ?cs (ne - 1)
          (Formula.MatchP (point (\<tau> \<sigma> (ne - 1) - t)) (from_mregex ms' \<phi>s)) (lookup Y ms')"
          using Y *(4)[OF ms] by blast
      qed simp
      have d: "\<tau> \<sigma> ne - t - (\<tau> \<sigma> ne - \<tau> \<sigma> (ne - 1)) = \<tau> \<sigma> (ne - 1) - t"
        using t_le \<tau>_le by linarith
      have memL0: "\<tau> \<sigma> ne - t \<le> 0 \<longleftrightarrow> t = \<tau> \<sigma> ne"
        using t_le' by linarith
      have memR\<Delta>: "\<tau> \<sigma> ne - \<tau> \<sigma> (ne - 1) \<le> \<tau> \<sigma> ne - t"
        using t_le by linarith
      have sat_iff: "Formula.sat \<sigma> V v ne (Formula.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s)) \<longleftrightarrow>
          t = \<tau> \<sigma> ne \<and> Regex.eps (Formula.sat \<sigma> V v) ne (from_mregex ms \<phi>s) \<or>
          (\<exists>s \<in> Regex.rpd (Formula.sat \<sigma> V v) ne (from_mregex ms \<phi>s).
            Formula.sat \<sigma> V v (ne - 1) (Formula.MatchP (point (\<tau> \<sigma> (ne - 1) - t)) s))" for v
        unfolding sat_MatchP_rec[of \<sigma> V v ne] subtract_simps(2) point_simps d memL0
        using ne memR\<Delta> by simp
      show ?thesis
      proof (cases "t = \<tau> \<sigma> ne")
        case True
        have r\<epsilon>: "qtable ?cs (mem_restr R ?cs)
          (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (val n ?cs v)) ne (from_mregex ms \<phi>s)) (r\<epsilon>_strict ?cs ?dss rels ms)"
          by (rule qtable_r\<epsilon>_strict[OF *(2)[OF ms] *(3)[OF ms] _ distinct_regex_cols qtables])
            (simp add: *(1)[OF ms])
        show ?thesis
          unfolding lookup if_P[OF True] sat_iff
          by (rule qtable_union[OF r\<delta> r\<epsilon>]) (simp add: True disj_commute)
      next
        case False
        show ?thesis
          unfolding lookup if_not_P[OF False] Un_empty_right sat_iff
          by (rule qtable_cong[OF r\<delta> refl]) (simp add: False)
      qed
    qed
    with ne t_le' memR i show ?thesis
      by blast
  qed
  then have in_aux0_le_\<tau>: "(t, X) \<in> set aux0 \<Longrightarrow> t \<le> \<tau> \<sigma> ne" for t X
    by (meson \<tau>_mono diff_le_self le_trans)
  have in_aux0_2: "ne \<noteq> 0 \<Longrightarrow> t \<le> \<tau> \<sigma> (ne-1) \<Longrightarrow> memR I (\<tau> \<sigma> ne - t) \<Longrightarrow> \<exists>i. \<tau> \<sigma> i = t \<Longrightarrow>
    \<exists>X. (t, X) \<in> set aux0" for t
  proof -
    fix t
    assume "ne \<noteq> 0" "t \<le> \<tau> \<sigma> (ne-1)" "memR I (\<tau> \<sigma> ne - t)" "\<exists>i. \<tau> \<sigma> i = t"
    then obtain X where "(t, X) \<in> set aux"
      by (atomize_elim, intro assms(1)[unfolded wf_matchP_aux_def, THEN conjunct2, THEN conjunct2, rule_format])
        (auto simp: gr0_conv_Suc elim!: order_trans[rotated] intro!: diff_le_mono \<tau>_mono)
    with \<open>memR I (\<tau> \<sigma> ne - t)\<close> have "(t, ?update X t) \<in> set aux0"
      unfolding aux0_def by (auto simp: id_def elim!: bexI[rotated] intro!: exI[of _ X])
    then show "\<exists>X. (t, X) \<in> set aux0"
      by blast
  qed
  have aux0_Nil: "aux0 = [] \<Longrightarrow> ne = 0 \<or> ne \<noteq> 0 \<and> (\<forall>t. t \<le> \<tau> \<sigma> (ne-1) \<and> memR I (\<tau> \<sigma> ne - t) \<longrightarrow>
        (\<nexists>i. \<tau> \<sigma> i = t))"
    using in_aux0_2 by (cases "ne = 0") (auto)
  have r\<epsilon>_base: "sat_table \<sigma> V n R ?cs ne
      (Formula.MatchP (point 0) (from_mregex ms \<phi>s)) (lookup (mrtabulate mrs (r\<epsilon>_strict ?cs ?dss rels)) ms)"
    if ms: "ms \<in> RPDs mr" and fresh: "\<forall>x \<in> set aux0. fst x \<noteq> \<tau> \<sigma> ne" for ms
  proof -
    have ne: "ne = 0 \<or> \<tau> \<sigma> (ne - 1) < \<tau> \<sigma> ne"
    proof (rule ccontr)
      assume "\<not> (ne = 0 \<or> \<tau> \<sigma> (ne - 1) < \<tau> \<sigma> ne)"
      then have "ne \<noteq> 0" and nlt: "\<not> \<tau> \<sigma> (ne - 1) < \<tau> \<sigma> ne"
        by simp_all
      moreover have "\<tau> \<sigma> (ne - 1) \<le> \<tau> \<sigma> ne"
        by (rule \<tau>_mono) simp
      with nlt have "\<tau> \<sigma> (ne - 1) = \<tau> \<sigma> ne"
        by linarith
      ultimately obtain X where "(\<tau> \<sigma> ne, X) \<in> set aux0"
        using in_aux0_2[of "\<tau> \<sigma> ne"] by auto
      with fresh show False
        by auto
    qed
    show ?thesis
      unfolding mrs lookup_tabulate[OF distinct_sorted_list_of_set] set_sorted_list_of_set[OF finite_RPDs]
      using ms ne by (auto simp: zero_enat_def[symmetric] sat_MatchP_rec[where i=ne] *(1)[OF ms]
          intro!: qtable_cong[OF qtable_r\<epsilon>_strict[OF *(2)[OF ms] *(3)[OF ms] _ distinct_regex_cols qtables]])
  qed

  have aux'_eq: "aux' = (case aux0 of
      [] \<Rightarrow> [(\<tau> \<sigma> ne, mrtabulate mrs (r\<epsilon>_strict ?cs ?dss rels))]
    | x # aux' \<Rightarrow> (if fst x = \<tau> \<sigma> ne then x # aux'
       else (\<tau> \<sigma> ne, mrtabulate mrs (r\<epsilon>_strict ?cs ?dss rels)) # x # aux'))"
    using result_eq unfolding aux0_def update_matchP_def Let_def by simp
  have sorted_aux': "sorted_wrt (\<lambda>x y. fst x > fst y) aux'"
    unfolding aux'_eq
    using sorted_aux0 in_aux0_le_\<tau> by (cases aux0) (fastforce)+

  have in_aux'_1: "t \<le> \<tau> \<sigma> ne \<and> memR I (\<tau> \<sigma> ne - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
     (\<forall>ms\<in>RPDs mr. sat_table \<sigma> V n R ?cs ne
        (Formula.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s)) (lookup X ms))"
    if aux': "(t, X) \<in> set aux'" for t X
  proof (cases aux0)
    case Nil
    with aux' show ?thesis
      unfolding aux'_eq using r\<epsilon>_base[unfolded Nil]
      by (auto intro: exI[of _ ne])
  next
    case (Cons a as)
    show ?thesis
    proof (cases "t = \<tau> \<sigma> ne")
      case t: True
      show ?thesis
      proof (cases "fst a = \<tau> \<sigma> ne")
        case True
        with aux' Cons t have "X = snd a"
          unfolding aux'_eq using sorted_aux0 by auto
        moreover from in_aux0_1[of "fst a" "snd a"] Cons have "ne \<noteq> 0"
          "fst a \<le> \<tau> \<sigma> ne" "memR I (\<tau> \<sigma> ne - fst a)" "\<exists>i. \<tau> \<sigma> i = fst a"
          "\<forall>ms \<in> RPDs mr. sat_table \<sigma> V n R ?cs ne
            (Formula.MatchP (point (\<tau> \<sigma> ne - fst a)) (from_mregex ms \<phi>s)) (lookup (snd a) ms)"
          by auto
        ultimately show ?thesis using t True
          by auto
      next
        case False
        with aux' Cons t have "X = mrtabulate mrs (r\<epsilon>_strict ?cs ?dss rels)"
          unfolding aux'_eq using sorted_aux0 in_aux0_le_\<tau>[of "fst a" "snd a"] by auto
        moreover have "\<forall>x \<in> set aux0. fst x \<noteq> \<tau> \<sigma> ne"
          using False sorted_aux0 in_aux0_le_\<tau>[of "fst a" "snd a"] unfolding Cons
          by fastforce
        ultimately show ?thesis
          using t r\<epsilon>_base by (auto intro: exI[of _ ne])
      qed
    next
      case False
      with aux' Cons have "(t, X) \<in> set aux0"
        unfolding aux'_eq by (auto split: if_splits)
      then have "ne \<noteq> 0" "t \<le> \<tau> \<sigma> ne" "memR I (\<tau> \<sigma> ne - t)" "\<exists>i. \<tau> \<sigma> i = t"
        "\<forall>ms \<in> RPDs mr. sat_table \<sigma> V n R ?cs ne
          (Formula.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s)) (lookup X ms)"
        using in_aux0_1 by blast+
      with False aux' Cons show ?thesis
        unfolding aux'_eq by auto
    qed
  qed

  have in_aux'_2: "\<exists>X. (t, X) \<in> set aux'" if "t \<le> \<tau> \<sigma> ne" "memR I (\<tau> \<sigma> ne - t)" "\<exists>i. \<tau> \<sigma> i = t" for t
  proof (cases "t = \<tau> \<sigma> ne")
    case True
    then show ?thesis
    proof (cases aux0)
      case Nil
      with True show ?thesis unfolding aux'_eq by simp
    next
      case (Cons a as)
      with True show ?thesis unfolding aux'_eq using eq_fst_iff[of t a]
        by (cases "fst a = \<tau> \<sigma> ne") auto
    qed
  next
    case False
    with that have "ne \<noteq> 0"
      using le_\<tau>_less neq0_conv by blast
    moreover from False that have  "t \<le> \<tau> \<sigma> (ne-1)"
      by (metis One_nat_def Suc_leI Suc_pred \<tau>_mono diff_is_0_eq' order.antisym neq0_conv not_le)
    ultimately obtain X where "(t, X) \<in> set aux0" using \<open>memR I (\<tau> \<sigma> ne - t)\<close> \<open>\<exists>i. \<tau> \<sigma> i = t\<close>
      by atomize_elim (auto intro!: in_aux0_2)
    then show ?thesis unfolding aux'_eq using False
      by (auto intro: exI[of _ X] split: list.split)
  qed

  show "wf_matchP_aux \<sigma> V n R I r aux' (Suc ne)"
    unfolding wf_matchP_aux_def using mr
    by (auto dest: in_aux'_1 intro: sorted_aux' in_aux'_2)

  have rel_eq: "rel = foldr (\<union>) [lookup rel mr. (t, rel) \<leftarrow> aux', memL I (\<tau> \<sigma> ne - t)] {}"
    unfolding aux'_eq aux0_def
    using result_eq by (simp add: update_matchP_def Let_def)
  have rel_alt: "rel = (\<Union>(t, rel) \<in> set aux'. if memL I (\<tau> \<sigma> ne - t) then lookup rel mr else empty_table)"
    unfolding rel_eq foldr_union
    by (auto simp add: prod.case_eq_if)
  show "sat_table \<sigma> V n R ?cs ne (Formula.MatchP I r) rel"
    unfolding rel_alt
  proof (rule qtable_Union[where Qi="\<lambda>(t, X) v.
    memL I (\<tau> \<sigma> ne - t) \<and> Formula.sat \<sigma> V (val n ?cs v) ne (Formula.MatchP (point (\<tau> \<sigma> ne - t)) r)"],
        goal_cases finite qtable equiv)
    case (equiv v)
    show ?case
    proof (rule iffI, erule sat_MatchP_point, goal_cases left right)
      case (left j)
      then show ?case using in_aux'_2[of "\<tau> \<sigma> j", OF _ _ exI, OF _ _ refl] by auto
    next
      case right
      then show ?case by (auto elim!: sat_MatchP_pointD dest: in_aux'_1)
    qed
  qed (auto dest!: in_aux'_1 intro!: qtable_empty dest!: bspec[OF _ RPDs_refl]
      simp: from_mregex_eq[OF safe mr])
qed


subsection \<open> Update for MatchF \<close>

lemma length_update_matchF_base:
  "length (fst (update_matchF_base cs dss I mr mrs rels nt)) = Suc 0"
  by (auto simp: Let_def update_matchF_base_def)

lemma length_update_matchF_step:
  "length (fst (update_matchF_step cs dss I mr mrs nt entry st)) = Suc (length (fst st))"
  by (auto simp: Let_def update_matchF_step_def split: prod.splits)

lemma length_foldr_update_matchF_step:
  "length (fst (foldr (update_matchF_step cs dss I mr mrs nt) aux base)) = length aux + length (fst base)"
  by (induct aux arbitrary: base) (auto simp: Let_def length_update_matchF_step)

lemma length_update_matchF: "length (update_matchF cs dss I mr mrs rels nt aux) = Suc (length aux)"
  unfolding update_matchF_def update_matchF_base_def length_foldr_update_matchF_step
  by (auto simp: Let_def)

lemma wf_update_matchF_base_invar:
  assumes safe: "Regex.safe_regex fv rgx_safe_pred Futu Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. sat_table \<sigma> V n R (Formula.fv_list \<phi>) j \<phi> rel) \<phi>s rels"
  shows "wf_matchF_invar \<sigma> V n R I r
    (update_matchF_base (regex_cols r) (map Formula.fv_list \<phi>s) I mr mrs rels (\<tau> \<sigma> j)) j"
proof -
  have from_mregex: "from_mregex mr \<phi>s = r"
    using safe mr using from_mregex_eq by blast
  from safe have safe_mr: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<phi>s)"
    by (simp only: from_mregex)
  { fix ms
    assume ms: "ms \<in> LPDs mr"
    have fv_ms: "fv_regex (from_mregex ms \<phi>s) = fv_regex r"
      using LPDs_safe_fv_regex[OF safe_mr ms] by (simp only: from_mregex)
    have safe_ms: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex ms \<phi>s)"
      using safe_mr ms by (rule LPDs_safe)
    have ok_ms: "ok (length \<phi>s) ms"
      using conjunct2[OF to_mregex_ok[OF mr]] ms by (rule LPDs_ok)
    have LPD_ms: "LPD ms \<subseteq> LPDs mr"
      using LPDs_trans[OF _ ms] by (rule subsetI)
    note fv_ms safe_ms ok_ms LPD_ms
  } note * = this
  show ?thesis
    unfolding wf_matchF_invar_def wf_matchF_aux_def update_matchF_base_def mr prod.case Let_def mrs
    using safe
    by (auto simp: * from_mregex qtables qtable_empty_iff zero_enat_def[symmetric]
        lookup_tabulate finite_LPDs eps_match less_Suc_eq LPDs_refl
        intro!: qtable_cong[OF qtable_l\<epsilon>_strict[where \<phi>s=\<phi>s]] intro: qtables exI[of _ j]
        split: option.splits)
qed

lemma wf_matchF_invar_step:
  assumes wf: "wf_matchF_invar \<sigma> V n R I r st (Suc i)"
    and safe: "Regex.safe_regex fv rgx_safe_pred Futu Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> rel) \<phi>s rels"
    and rel: "qtable (regex_cols r) (mem_restr R (regex_cols r)) (\<lambda>v. (\<exists>j. i \<le> j \<and> j < i + length (fst st) \<and>
          mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and> Regex.match (Formula.sat \<sigma> V (val n (regex_cols r) v)) r i j)) rel"
    and entry: "entry = (\<tau> \<sigma> i, rels, rel)"
    and nt: "nt = \<tau> \<sigma> (i + length (fst st))"
  shows "wf_matchF_invar \<sigma> V n R I r
    (update_matchF_step (regex_cols r) (map Formula.fv_list \<phi>s) I mr mrs nt entry st) i"
proof -
  have from_mregex: "from_mregex mr \<phi>s = r"
    using safe mr using from_mregex_eq by blast
  from safe have safe_mr: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<phi>s)"
    by (simp only: from_mregex)
  { fix ms
    assume ms: "ms \<in> LPDs mr"
    have fv_ms: "fv_regex (from_mregex ms \<phi>s) = fv_regex r"
      using LPDs_safe_fv_regex[OF safe_mr ms] by (simp only: from_mregex)
    have safe_ms: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex ms \<phi>s)"
      using safe_mr ms by (rule LPDs_safe)
    have ok_ms: "ok (length \<phi>s) ms"
      using conjunct2[OF to_mregex_ok[OF mr]] ms by (rule LPDs_ok)
    have LPD_ms: "LPD ms \<subseteq> LPDs mr"
      using LPDs_trans[OF _ ms] by (rule subsetI)
    note fv_ms safe_ms ok_ms LPD_ms
  } note * = this
  { fix aux X ms
    assume "st = (aux, X)" "ms \<in> LPDs mr"
    with wf mr have "qtable (regex_cols r) (mem_restr R (regex_cols r))
      (\<lambda>v. Regex.match (Formula.sat \<sigma> V (val n (regex_cols r) v)) (from_mregex ms \<phi>s) i (i + length aux))
      (l\<delta> (regex_cols r) (map Formula.fv_list \<phi>s) (\<lambda>x. x) X rels ms)"
      by (intro qtable_cong[OF qtable_l\<delta>[where \<phi>s=\<phi>s and A="regex_cols r" and
              Q="\<lambda>v r. Regex.match (Formula.sat \<sigma> V v) r (Suc i) (i + length aux)", OF _ _ qtables]])
        (auto simp: wf_matchF_invar_def * LPDs_trans lpd_match[of i] elim!: bspec)
  } note l\<delta> = this
  have "lookup (mrtabulate mrs f) ms = f ms" if "ms \<in> LPDs mr" for ms and f :: "mregex \<Rightarrow> 'a table"
    using that mrs  by (fastforce simp: lookup_tabulate finite_LPDs split: option.splits)+
  then show ?thesis
    using wf mr mrs entry nt LPDs_trans
    by (auto 0 3 simp: Let_def wf_matchF_invar_def update_matchF_step_def wf_matchF_aux_def mr * LPDs_refl
        list_all2_Cons1 append_eq_Cons_conv upt_eq_Cons_conv Suc_le_eq qtables
        lookup_tabulate finite_LPDs id_def l\<delta> from_mregex less_Suc_eq
        intro!: qtable_union[OF rel l\<delta>] qtable_cong[OF rel]
        intro: exI[of _ "i + length _"]
        split: if_splits prod.splits)
qed

lemma wf_update_matchF_invar:
  assumes pre: "wf_matchF_aux \<sigma> V n R I r aux ne (length (fst st) - 1)"
    and wf: "wf_matchF_invar \<sigma> V n R I r st (ne + length aux)"
    and safe: "Regex.safe_regex fv rgx_safe_pred Futu Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and j: "j = ne + length aux + length (fst st) - 1"
  shows "wf_matchF_invar \<sigma> V n R I r
    (foldr (update_matchF_step (regex_cols r) (map Formula.fv_list \<phi>s) I mr mrs (\<tau> \<sigma> j)) aux st) ne"
  using pre wf unfolding j
proof (induct aux arbitrary: ne)
  case (Cons entry aux)
  obtain t rels rel where entry: "entry = (t, rels, rel)"
    by (cases entry)
  from Cons(3) obtain k where k: "length (fst st) = Suc k"
    by (auto simp: wf_matchF_invar_def neq_Nil_conv split: prod.splits)
  from Cons(2) have t: "t = \<tau> \<sigma> ne"
    and qtables: "list_all2 (\<lambda>\<phi>. sat_table \<sigma> V n R (Formula.fv_list \<phi>) ne \<phi>) \<phi>s rels"
    and rel: "qtable (regex_cols r) (mem_restr R (regex_cols r)) (\<lambda>v. \<exists>j. ne \<le> j \<and>
      j < ne + length (entry # aux) + k \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> ne) \<and>
      Regex.match (Formula.sat \<sigma> V (val n (regex_cols r) v)) r ne j) rel"
    and aux: "wf_matchF_aux \<sigma> V n R I r aux (Suc ne) k"
    by (simp_all add: wf_matchF_aux_def mr entry k upt_conv_Cons del: upt_Suc)
  have wf: "wf_matchF_invar \<sigma> V n R I r
    (foldr (update_matchF_step (regex_cols r) (map Formula.fv_list \<phi>s) I mr mrs
      (\<tau> \<sigma> (ne + length (entry # aux) + length (fst st) - 1))) aux st) (Suc ne)"
    using Cons(1)[of "Suc ne"] aux Cons(3) by (simp add: k)
  show ?case
    unfolding foldr.simps o_apply
    using rel t
    by (intro wf_matchF_invar_step[OF wf safe mr mrs qtables])
      (simp_all add: entry k length_foldr_update_matchF_step add.assoc)
qed simp

lemma wf_update_matchF:
  assumes pre: "wf_matchF_aux \<sigma> V n R I r aux ne 0"
    and safe: "Regex.safe_regex fv rgx_safe_pred Futu Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and nt: "nt = \<tau> \<sigma> (ne + length aux)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. sat_table \<sigma> V n R (Formula.fv_list \<phi>) (ne + length aux) \<phi> rel) \<phi>s rels"
  shows "wf_matchF_aux \<sigma> V n R I r
    (update_matchF (regex_cols r) (map Formula.fv_list \<phi>s) I mr mrs rels nt aux) ne 0"
  unfolding update_matchF_def using wf_update_matchF_base_invar[OF safe mr mrs qtables, of I]
  unfolding nt
  by (intro wf_update_matchF_invar[OF _ _ safe mr mrs, unfolded wf_matchF_invar_def split_beta, THEN conjunct2, THEN conjunct1])
    (auto simp: length_update_matchF_base wf_matchF_invar_def update_matchF_base_def Let_def pre)

lemma wf_matchF_aux_Cons1: "wf_matchF_aux \<sigma> V n R I r ((t, rels, rel) # aux) ne i \<Longrightarrow> t = \<tau> \<sigma> ne"
  unfolding wf_matchF_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc split: prod.splits)

lemma wf_matchF_aux_Cons3: "wf_matchF_aux \<sigma> V n R I r ((t, rels, rel) # aux) ne i \<Longrightarrow>
  qtable (regex_cols r) (mem_restr R (regex_cols r)) (\<lambda>v. (\<exists>j. ne \<le> j \<and> j < Suc (ne + length aux + i) \<and>
    mem I ((\<tau> \<sigma> j - \<tau> \<sigma> ne)) \<and> Regex.match (Formula.sat \<sigma> V (val n (regex_cols r) v)) r ne j)) rel"
  unfolding wf_matchF_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc split: prod.splits)

(*<*)
end
(*>*)
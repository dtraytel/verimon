(*<*)
theory Safe_Finite
  imports
    Safety
begin
(*>*)

section \<open> Finite @{term safe_formula} \<close>

text \<open>A safe and future-bounded formula has finitely many satisfying valuations at every time-point,
  provided that the trace's databases and the interpretations of the predicates in the
  environment are finite (@{text safe_formula_finite} and @{text safe_formula_finite_dense}).\<close>

unbundle MFODL_notation \<comment> \<open> enable notation \<close>


subsection \<open> Partial valuations \<close>

text \<open>The finiteness argument works with partial valuations: lists of optional values of length
  @{term n} that are defined exactly at a set of variables.  They are not the monitor's tuples,
  which list the values at their columns only; @{text safe_formula_finite_dense} below transfers
  the result to those.\<close>

definition pwf_tuple :: "nat \<Rightarrow> nat set \<Rightarrow> 'a option list \<Rightarrow> bool" where
  "pwf_tuple n V x \<longleftrightarrow> length x = n \<and> (\<forall>i<n. x!i = None \<longleftrightarrow> i \<notin> V)"

lemma pwf_tuple_length: "pwf_tuple n V x \<Longrightarrow> length x = n"
  unfolding pwf_tuple_def by simp

lemma pwf_tuple_Nil[simp]: "pwf_tuple n A [] = (n = 0)"
  unfolding pwf_tuple_def by auto

lemma Suc_pred_case: "Suc (x - Suc 0) = (case x of 0 \<Rightarrow> Suc 0 | _ \<Rightarrow> x)"
  by (auto split: nat.splits)

lemma pwf_tuple_Cons[simp]:
  "pwf_tuple n A (x # xs) \<longleftrightarrow> ((if x = None then 0 \<notin> A else 0 \<in> A) \<and>
   (\<exists>m. n = Suc m \<and> pwf_tuple m ((\<lambda>x. x - 1) ` (A - {0})) xs))"
  unfolding pwf_tuple_def
  by (auto 0 3 simp: nth_Cons image_iff Ball_def gr0_conv_Suc Suc_pred_case split: nat.splits)

lemma pwf_tuple_empty_iff: "pwf_tuple n {} v \<longleftrightarrow> v = replicate n None"
  by (auto simp: pwf_tuple_def intro!: nth_equalityI)

definition "unit_ptable n = {replicate n None}"

lemma in_unit_ptable: "v \<in> unit_ptable n \<longleftrightarrow> pwf_tuple n {} v"
  unfolding unit_ptable_def pwf_tuple_def by (auto intro!: nth_equalityI)

definition prestrict :: "nat set \<Rightarrow> 'a option list \<Rightarrow> 'a option list" where
  "prestrict A v = map (\<lambda>i. if i \<in> A then v ! i else None) [0 ..< length v]"

lemma prestrict_Nil[simp]: "prestrict A [] = []"
  unfolding prestrict_def by auto

lemma prestrict_Cons[simp]: "prestrict A (x # xs) =
  (if 0 \<in> A then x # prestrict ((\<lambda>x. x - 1) ` (A - {0})) xs else None # prestrict ((\<lambda>x. x - 1) ` A) xs)"
  unfolding prestrict_def
  by (auto simp: map_upt_Suc image_iff Suc_pred_case Ball_def simp del: upt_Suc split: nat.splits)

lemma prestrict_prestrict: "prestrict A (prestrict B v) = prestrict (A \<inter> B) v"
  by (simp add: prestrict_def)

lemma prestrict_idle: "pwf_tuple n A v \<Longrightarrow> prestrict A v = v"
  by (induct v arbitrary: n A) (auto split: if_splits)

lemma length_prestrict[simp]: "length (prestrict A v) = length v"
  unfolding prestrict_def by auto

lemma map_the_prestrict: "i \<in> A \<Longrightarrow> map the (prestrict A v) ! i = map the v ! i"
  by (induct v arbitrary: A i) (auto simp: nth_Cons' gr0_conv_Suc split: option.splits)

lemma pwf_tuple_prestrict: "pwf_tuple n B v \<Longrightarrow> A \<inter> B = C \<Longrightarrow> pwf_tuple n C (prestrict A v)"
  unfolding prestrict_def pwf_tuple_def by auto

lemma pwf_tuple_prestrict_simple: "pwf_tuple n B v \<Longrightarrow> A \<subseteq> B \<Longrightarrow> pwf_tuple n A (prestrict A v)"
  unfolding prestrict_def pwf_tuple_def by auto

lemma prestrict_eq_Nil[simp]: "prestrict A v = [] \<longleftrightarrow> v = []"
  unfolding prestrict_def by auto

fun pjoin1 :: "'a option list \<times> 'a option list \<Rightarrow> 'a option list option" where
  "pjoin1 ([], []) = Some []"
| "pjoin1 (None # xs, None # ys) = map_option (Cons None) (pjoin1 (xs, ys))"
| "pjoin1 (Some x # xs, None # ys) = map_option (Cons (Some x)) (pjoin1 (xs, ys))"
| "pjoin1 (None # xs, Some y # ys) = map_option (Cons (Some y)) (pjoin1 (xs, ys))"
| "pjoin1 (Some x # xs, Some y # ys) = (if x = y
    then map_option (Cons (Some x)) (pjoin1 (xs, ys))
    else None)"
| "pjoin1 _ = None"

lemma pjoin1_Some_prestrict:
  fixes x y :: "'a option list"
  assumes "pwf_tuple n A x" "pwf_tuple n B y"
  shows "pjoin1 (x, y) = Some z \<longleftrightarrow> pwf_tuple n (A \<union> B) z \<and> prestrict A z = x \<and> prestrict B z = y"
  using assms
proof (induct "(x, y)" arbitrary: n x y z A B rule: pjoin1.induct)
  case (2 xs ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
next
  case (3 x xs ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
next
  case (4 xs y ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
next
  case (5 x xs y ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
qed auto

definition pjoin :: "'a option list set \<Rightarrow> bool \<Rightarrow> 'a option list set \<Rightarrow> 'a option list set" where
  "pjoin A pos B = (if pos then Option.these (pjoin1 ` (A \<times> B))
    else A - Option.these (pjoin1 ` (A \<times> B)))"

lemma pjoin_prestrict:
  fixes X Y :: "'a option list set"
  assumes "\<And>v. v \<in> X \<Longrightarrow> pwf_tuple n A v" "\<And>v. v \<in> Y \<Longrightarrow> pwf_tuple n B v" "\<not> b \<Longrightarrow> B \<subseteq> A"
  shows "v \<in> pjoin X b Y \<longleftrightarrow>
    pwf_tuple n (A \<union> B) v \<and> prestrict A v \<in> X \<and> (if b then prestrict B v \<in> Y else prestrict B v \<notin> Y)"
  by (auto 4 4 simp: pjoin_def Option.these_def image_iff assms pwf_tuple_prestrict sup_absorb1 prestrict_idle
    prestrict_idle[OF assms(1)] elim: assms
    dest: pjoin1_Some_prestrict[OF assms(1,2), THEN iffD1, rotated -1]
    dest!: spec[of _ "Some v"]
    intro!: exI[of _ "Some v"] pjoin1_Some_prestrict[THEN iffD2, symmetric] bexI[rotated])

lemma finite_listset: "(\<And>A. A \<in> set xs \<Longrightarrow> finite A) \<Longrightarrow> finite (listset xs)"
  by (induct xs) (simp_all add: set_Cons_def finite_image_set2)

fun pjoinN :: "'a option list list \<Rightarrow> 'a option list option" where
"pjoinN [] = Some []"
|"pjoinN (a#b#cs) =  (case (pjoin1 (a, b)) of None \<Rightarrow> None| Some x \<Rightarrow> pjoinN (x#cs))"
|"pjoinN (a#[]) = Some a"

lemma in_listset_conv_list_all2: "xs \<in> listset ys \<longleftrightarrow> list_all2 (\<in>) xs ys"
  by (induct ys arbitrary: xs) (auto simp: set_Cons_def list_all2_Cons2)

lemma pjoinN_Some_prestrict:
  fixes as :: "'a option list list"
  fixes bs :: "nat set list"
  assumes "list_all2 (pwf_tuple n) bs as"
  assumes "as\<noteq>[]"
  shows "pjoinN (as) = Some z \<longleftrightarrow> pwf_tuple n (\<Union> (set bs)) z \<and> list_all2 (\<lambda>b a. prestrict b z = a) bs as"
  using assms
proof (induct "as" arbitrary: n bs z rule: pjoinN.induct)
  case 1
  then show ?case
    by(auto)
next
  case (2 a b cs)
  from "2.prems"(1) obtain A B Cs where bs: "bs = A # B # Cs"
    and wf: "pwf_tuple n A a" "pwf_tuple n B b" "list_all2 (pwf_tuple n) Cs cs"
    by (auto simp: list_all2_Cons2)
  \<comment> \<open>the prestriction of @{term z} to @{term "A \<union> B"} is the only candidate for the pjoin of a and b\<close>
  have pjoin_prestrict: "pjoin1 (a, b) = Some (prestrict (A \<union> B) z) \<longleftrightarrow> prestrict A z = a \<and> prestrict B z = b"
    if "pwf_tuple n (\<Union> (set bs)) z"
  proof -
    have "pwf_tuple n (A \<union> B) (prestrict (A \<union> B) z)"
      using that by (auto simp: bs intro: pwf_tuple_prestrict_simple)
    then show ?thesis
      using pjoin1_Some_prestrict[OF wf(1,2)] by (simp add: prestrict_prestrict)
  qed
  show ?case
  proof (cases "pjoin1 (a, b)")
    case None
    then have "pjoinN (a # b # cs) \<noteq> Some z"
      by simp
    moreover have "\<not> (pwf_tuple n (\<Union> (set bs)) z \<and> list_all2 (\<lambda>b a. prestrict b z = a) bs (a # b # cs))"
      using pjoin_prestrict None by (auto simp: bs)
    ultimately show ?thesis
      by blast
  next
    case (Some c)
    with pjoin1_Some_prestrict[OF wf(1,2), of c] have c: "pwf_tuple n (A \<union> B) c"
      by simp
    have IH: "pjoinN (c # cs) = Some z \<longleftrightarrow> pwf_tuple n (A \<union> B \<union> \<Union> (set Cs)) z
      \<and> prestrict (A \<union> B) z = c \<and> list_all2 (\<lambda>b a. prestrict b z = a) Cs cs"
      using "2.hyps"[of c n "(A \<union> B) # Cs" z] Some c wf(3) by simp
    have "prestrict (A \<union> B) z = c \<longleftrightarrow> prestrict A z = a \<and> prestrict B z = b"
      if "pwf_tuple n (\<Union> (set bs)) z"
      using pjoin_prestrict[OF that] Some by auto
    with Some IH show ?thesis
      by (auto simp: bs Un_assoc)
  qed
next
  case (3 a)
  from "3.prems"(1) obtain b where bs: "bs = [b]" and wf: "pwf_tuple n b a"
    by (metis list_all2_Cons2 list_all2_Nil2)
  show ?case
  proof
    assume "pjoinN [a] = Some z"
    then have "z = a"
      by simp
    with wf show "pwf_tuple n (\<Union> (set bs)) z \<and> list_all2 (\<lambda>b a. prestrict b z = a) bs [a]"
      by (simp add: bs prestrict_idle)
  next
    assume "pwf_tuple n (\<Union> (set bs)) z \<and> list_all2 (\<lambda>b a. prestrict b z = a) bs [a]"
    then have "pwf_tuple n b z" and "prestrict b z = a"
      by (simp_all add: bs)
    then show "pjoinN [a] = Some z"
      by (simp add: prestrict_idle)
  qed
qed

lemma Collect_singleton_tuple_eq_image: "i < n \<Longrightarrow> {v. pwf_tuple n {i} v \<and> P (map the v ! i)} =
  (\<lambda>x. (replicate n None)[i := Some x]) ` Collect P"
  unfolding pwf_tuple_def
  by (auto simp add: list_eq_iff_nth_eq nth_list_update intro: rev_image_eqI)


subsection \<open> Finiteness of the satisfying valuations \<close>

lemma sat_the_prestrict: "fv \<phi> \<subseteq> A \<Longrightarrow>
  Formula.sat \<sigma> V (map the (prestrict A v)) i \<phi> = Formula.sat \<sigma> V (map the v) i \<phi>"
  by (rule sat_fv_cong) (auto intro!: map_the_prestrict)

lemma inj_eval: " \<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow>
    inj_on (\<lambda>v. map (Formula.eval_trm (map the v)) ts) {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v}"
proof (intro inj_onI)
  fix x y
  assume vars: "\<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t"
    and x: "x \<in> {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v}"
    and y: "y \<in> {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v}"
    and eq: "map (Formula.eval_trm (map the x)) ts = map (Formula.eval_trm (map the y)) ts"
  show "x = y"
  proof (rule nth_equalityI)
    show "length x = length y"
      using x y by (simp add: pwf_tuple_def)
  next
    fix i
    assume "i < length x"
    with x y have i: "i < n" "i < length y"
      by (simp_all add: pwf_tuple_def)
    show "x ! i = y ! i"
    proof (cases "i \<in> \<Union> (fv_trm ` set ts)")
      case True
      with vars have "\<^bold>v i \<in> set ts"
        by (auto simp: Formula.is_Var_def Formula.is_Const_def)
      moreover from eq have "\<forall>t\<in>set ts. Formula.eval_trm (map the x) t = Formula.eval_trm (map the y) t"
        by simp
      ultimately have "map the x ! i = map the y ! i"
        by fastforce
      with \<open>i < length x\<close> i have "the (x ! i) = the (y ! i)"
        by simp
      moreover have "x ! i \<noteq> None" "y ! i \<noteq> None"
        using True x y i by (simp_all add: pwf_tuple_def)
      ultimately show ?thesis
        by (metis option.expand)
    next
      case False
      with x y i have "x ! i = None" "y ! i = None"
        by (auto simp: pwf_tuple_def)
      then show ?thesis
        by simp
    qed
  qed
qed

lemma inj_eval2: " \<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow>
    inj_on (\<lambda>v. (e, map (Formula.eval_trm (map the v)) ts)) {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v}"
  using inj_eval[of ts n] by (simp add: inj_on_def)

lemma finite_letpast:
  assumes fv: "{0..<Formula.nfv \<phi>} \<subseteq> fv \<phi>"
  assumes V: "\<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i}"
  assumes IH: "\<And>V i.
    \<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i} \<Longrightarrow>
    finite {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  shows "finite {v. length v = Formula.nfv \<phi> \<and>
    letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>) v i}"
proof (induction i rule: less_induct)
  case (less i)
  let ?F = "\<lambda>X u k. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>"
  define X where "X = (\<lambda>w j. j < i \<and> letpast_sat ?F w j)"
  let ?V = "V((p, Formula.nfv \<phi>) \<mapsto> X)"
  have "\<forall>pn\<in>dom ?V. \<forall>k. finite {v. length v = snd pn \<and> the (?V pn) v k}"
  proof (intro ballI allI)
    fix pn k
    assume "pn \<in> dom ?V"
    show "finite {v. length v = snd pn \<and> the (?V pn) v k}"
    proof (cases "pn = (p, Formula.nfv \<phi>)")
      case True
      then show ?thesis
        using less[of k] by (cases "k < i") (simp_all add: X_def fun_upd_same del: fun_upd_apply)
    next
      case False
      with \<open>pn \<in> dom ?V\<close> V show ?thesis
        by simp
    qed
  qed
  then have "finite {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> ?V (map the v) i \<phi>}"
    by (rule IH)
  moreover have "{v. length v = Formula.nfv \<phi> \<and> letpast_sat ?F v i}
    \<subseteq> map the ` {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> ?V (map the v) i \<phi>}"
  proof
    fix v
    assume "v \<in> {v. length v = Formula.nfv \<phi> \<and> letpast_sat ?F v i}"
    then have len: "length v = Formula.nfv \<phi>" and "letpast_sat ?F v i"
      by simp_all
    then have "Formula.sat \<sigma> ?V v i \<phi>"
      unfolding X_def by (subst (asm) letpast_sat.simps)
    moreover have "pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) (map Some v)"
      using fv len by (auto simp: pwf_tuple_def)
    ultimately show "v \<in> map the ` {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> ?V (map the v) i \<phi>}"
      by (intro image_eqI[where x = "map Some v"]) simp_all
  qed
  ultimately show ?case
    by (rule finite_surj)
qed

lemma safe_regex_Past_finite: "Regex.safe_regex fv rgx_safe_pred Past Strict r \<Longrightarrow>
  (\<And>i \<phi>. \<phi> \<in> safe_atms r \<Longrightarrow> finite {v. pwf_tuple n (fv \<phi>) v \<and> test v i \<phi>}) \<Longrightarrow>
  finite {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>i. Regex.match (test v) r j i)}"
proof (induct Past Strict r arbitrary: i rule: safe_regex_induct)
  case (Skip k)
  have "{v. pwf_tuple n (fv_regex (Regex.Skip k)) v \<and> (\<exists>j\<le>i. Regex.match (test v) (Regex.Skip k) j i)}
    \<subseteq> unit_ptable n"
    by (auto simp flip: in_unit_ptable)
  then show ?case
    by (rule finite_subset) (simp add: unit_ptable_def)
next
  case (Test \<phi>)
  then have "\<phi> \<in> safe_atms (Regex.Test \<phi>)"
    by simp
  moreover have "{v. pwf_tuple n (fv_regex (Regex.Test \<phi>)) v \<and> (\<exists>j\<le>i. Regex.match (test v) (Regex.Test \<phi>) j i)}
    = {v. pwf_tuple n (fv \<phi>) v \<and> test v i \<phi>}"
    by auto
  ultimately show ?case
    using Test(2) by simp
next
  case (Plus r s)
  have "finite {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>i. Regex.match (test v) r j i)}"
    by (rule Plus.hyps(1)) (use Plus.prems in auto)
  moreover have "finite {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<le>i. Regex.match (test v) s j i)}"
    by (rule Plus.hyps(2)) (use Plus.prems in auto)
  moreover have "{v. pwf_tuple n (fv_regex (Regex.Plus r s)) v \<and> (\<exists>j\<le>i. Regex.match (test v) (Regex.Plus r s) j i)}
    \<subseteq> {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>i. Regex.match (test v) r j i)}
      \<union> {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<le>i. Regex.match (test v) s j i)}"
    using Plus.prems(1) by auto
  ultimately show ?case
    by (simp add: finite_subset)
next
  case (TimesP r s)
  have fv: "fv_regex (Regex.Times r s) = fv_regex r"
    using TimesP.prems(1) by auto
  have r: "finite {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>k. Regex.match (test v) r j k)}" for k
    by (rule TimesP.hyps) (use TimesP.prems in auto)
  have "{v. pwf_tuple n (fv_regex (Regex.Times r s)) v \<and> (\<exists>j\<le>i. Regex.match (test v) (Regex.Times r s) j i)}
    \<subseteq> (\<Union>k\<in>{0..i}. {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>k. Regex.match (test v) r j k)})"
  proof
    fix v
    assume "v \<in> {v. pwf_tuple n (fv_regex (Regex.Times r s)) v \<and> (\<exists>j\<le>i. Regex.match (test v) (Regex.Times r s) j i)}"
    then obtain j k where "pwf_tuple n (fv_regex r) v" "j \<le> i"
      "Regex.match (test v) r j k" "Regex.match (test v) s k i"
      unfolding fv by auto
    moreover from \<open>Regex.match (test v) s k i\<close> have "k \<le> i"
      by (rule match_le)
    ultimately show "v \<in> (\<Union>k\<in>{0..i}. {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>k. Regex.match (test v) r j k)})"
      using match_le by fastforce
  qed
  moreover have "finite (\<Union>k\<in>{0..i}. {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>k. Regex.match (test v) r j k)})"
    using r by simp
  ultimately show ?case
    by (rule finite_subset)
next
  case (Star r)
  then have "{v. pwf_tuple n (fv_regex (Regex.Star r)) v \<and> (\<exists>j\<le>i. Regex.match (test v) (Regex.Star r) j i)}
    \<subseteq> unit_ptable n"
    by (auto simp flip: in_unit_ptable)
  then show ?case
    by (rule finite_subset) (simp add: unit_ptable_def)
qed

lemma safe_regex_Future_finite: "Regex.safe_regex fv rgx_safe_pred Futu Strict r \<Longrightarrow>
  (\<And>i \<phi>. \<phi> \<in> safe_atms r \<Longrightarrow> finite {v. pwf_tuple n (fv \<phi>) v \<and> test v i \<phi>}) \<Longrightarrow>
  finite {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) r i j)}"
proof (induct Futu Strict r arbitrary: i rule: safe_regex_induct)
  case (Skip k)
  have "{v. pwf_tuple n (fv_regex (Regex.Skip k)) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) (Regex.Skip k) i j)}
    \<subseteq> unit_ptable n"
    by (auto simp flip: in_unit_ptable)
  then show ?case
    by (rule finite_subset) (simp add: unit_ptable_def)
next
  case (Test \<phi>)
  then have "\<phi> \<in> safe_atms (Regex.Test \<phi>)"
    by simp
  moreover have "{v. pwf_tuple n (fv_regex (Regex.Test \<phi>)) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) (Regex.Test \<phi>) i j)}
    \<subseteq> {v. pwf_tuple n (fv \<phi>) v \<and> test v i \<phi>}"
    by auto
  ultimately show ?case
    using Test(2) by (blast intro: finite_subset)
next
  case (Plus r s)
  have "finite {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) r i j)}"
    by (rule Plus.hyps(1)) (use Plus.prems in auto)
  moreover have "finite {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) s i j)}"
    by (rule Plus.hyps(2)) (use Plus.prems in auto)
  moreover have "{v. pwf_tuple n (fv_regex (Regex.Plus r s)) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) (Regex.Plus r s) i j)}
    \<subseteq> {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) r i j)}
      \<union> {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) s i j)}"
    using Plus.prems(1) by auto
  ultimately show ?case
    by (simp add: finite_subset)
next
  case (TimesF r s)
  have fv: "fv_regex (Regex.Times r s) = fv_regex s"
    using TimesF.prems(1) by auto
  have s: "finite {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<in>{k..thr}. Regex.match (test v) s k j)}" for k
    by (rule TimesF.hyps) (use TimesF.prems in auto)
  have "{v. pwf_tuple n (fv_regex (Regex.Times r s)) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) (Regex.Times r s) i j)}
    \<subseteq> (\<Union>k\<in>{i..thr}. {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<in>{k..thr}. Regex.match (test v) s k j)})"
  proof
    fix v
    assume "v \<in> {v. pwf_tuple n (fv_regex (Regex.Times r s)) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) (Regex.Times r s) i j)}"
    then obtain j k where "pwf_tuple n (fv_regex s) v" "j \<le> thr"
      "Regex.match (test v) r i k" "Regex.match (test v) s k j"
      unfolding fv by auto
    moreover from this(3,4) have "i \<le> k" "k \<le> j"
      by (simp_all add: match_le)
    ultimately show "v \<in> (\<Union>k\<in>{i..thr}. {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<in>{k..thr}. Regex.match (test v) s k j)})"
      by fastforce
  qed
  moreover have "finite (\<Union>k\<in>{i..thr}. {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<in>{k..thr}. Regex.match (test v) s k j)})"
    using s by simp
  ultimately show ?case
    by (rule finite_subset)
next
  case (Star r)
  then have "{v. pwf_tuple n (fv_regex (Regex.Star r)) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) (Regex.Star r) i j)}
    \<subseteq> unit_ptable n"
    by (auto simp flip: in_unit_ptable)
  then show ?case
    by (rule finite_subset) (simp add: unit_ptable_def)
qed

lemma safe_formula_finite: "safe_formula \<phi> \<Longrightarrow> Safety.future_bounded \<phi> \<Longrightarrow> n\<ge> (Formula.nfv \<phi>) \<Longrightarrow> \<forall> i. finite (\<Gamma> \<sigma> i) \<Longrightarrow>
  \<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i} \<Longrightarrow>
  finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
proof(induct \<phi> arbitrary: i n V rule: safe_formula_induct)
  case (Eq_Const c d)
  then show ?case
    by(simp flip: in_unit_ptable add: unit_ptable_def)
next
  case (Eq_Var1 c x)
  then have "x < n"
    by (simp add: Formula.nfv_def)
  then show ?case
    using Collect_singleton_tuple_eq_image[of x n "\<lambda>y. c = y"] by simp
next
  case (Eq_Var2 c x)
  then have "x < n"
    by (simp add: Formula.nfv_def)
  then show ?case
    using Collect_singleton_tuple_eq_image[of x n "\<lambda>y. y = c"] by simp
next
  case (Pred e ts)
  then have vars: "\<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t"
    by simp
  show ?case
  proof (cases "V (e, length ts)")
    case None
    then have "{v. pwf_tuple n (fv (e \<dagger> ts)) v \<and> Formula.sat \<sigma> V (map the v) i (e \<dagger> ts)}
      = (\<lambda>v. (e, map (Formula.eval_trm (map the v)) ts)) -` \<Gamma> \<sigma> i
        \<inter> {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v}"
      by auto
    moreover have "finite ((\<lambda>v. (e, map (Formula.eval_trm (map the v)) ts)) -` \<Gamma> \<sigma> i
        \<inter> {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v})"
      using Pred.prems inj_eval2[OF vars] by (intro finite_vimage_IntI) simp_all
    ultimately show ?thesis
      by simp
  next
    case (Some a)
    then have "{v. pwf_tuple n (fv (e \<dagger> ts)) v \<and> Formula.sat \<sigma> V (map the v) i (e \<dagger> ts)}
      = (\<lambda>v. map (Formula.eval_trm (map the v)) ts) -` {v. length v = length ts \<and> a v i}
        \<inter> {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v}"
      by auto
    moreover from Pred.prems Some have "finite {v. length v = length ts \<and> a v i}"
      by (auto dest!: bspec[OF _ domI])
    then have "finite ((\<lambda>v. map (Formula.eval_trm (map the v)) ts) -` {v. length v = length ts \<and> a v i}
        \<inter> {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v})"
      using inj_eval[OF vars] by (rule finite_vimage_IntI)
    ultimately show ?thesis
      by simp
  qed
next
  case (Let p \<phi> \<psi>)
  let ?V = "V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>)"
  have "{v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v j \<phi>}
    = map the ` {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) j \<phi>}" for j
    using Let.hyps(1) by (auto simp: pwf_tuple_def intro!: image_eqI[where x="map Some _"])
  moreover have "finite {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) j \<phi>}" for j
    using Let by auto
  ultimately have "\<forall>pn\<in>dom ?V. \<forall>j. finite {v. length v = snd pn \<and> the (?V pn) v j}"
    using Let.prems by simp
  then have "finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> ?V (map the v) i \<psi>}"
    using Let by auto
  then show ?case
    by simp
next
  case (Frz p \<phi> \<psi>)
  let ?V = "V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w i \<phi>)"
  have "{v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v i \<phi>}
    = map the ` {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    using Frz.hyps(1) by (auto simp: pwf_tuple_def intro!: image_eqI[where x="map Some _"])
  moreover have "finite {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    using Frz by auto
  ultimately have "\<forall>pn\<in>dom ?V. \<forall>j. finite {v. length v = snd pn \<and> the (?V pn) v j}"
    using Frz.prems by simp
  then have "finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> ?V (map the v) i \<psi>}"
    using Frz by auto
  then show ?case
    by simp
next
  case (LetPast p \<phi> \<psi>)
  let ?F = "\<lambda>X u k. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>"
  let ?V = "V((p, Formula.nfv \<phi>) \<mapsto> letpast_sat ?F)"
  have dom_V: "\<forall>pn\<in>dom ?V. \<forall>j. finite {v. length v = snd pn \<and> the (?V pn) v j}"
  proof (intro ballI allI)
    fix pn j
    assume "pn \<in> dom ?V"
    show "finite {v. length v = snd pn \<and> the (?V pn) v j}"
    proof (cases "pn = (p, Formula.nfv \<phi>)")
      case True
      have "finite {v. length v = Formula.nfv \<phi> \<and> letpast_sat ?F v j}"
      proof (rule finite_letpast)
        show "{0..<Formula.nfv \<phi>} \<subseteq> fv \<phi>" "\<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i}"
          using LetPast by auto
        show "finite {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V' (map the v) k \<phi>}"
          if "\<forall>pn\<in>dom V'. \<forall>i. finite {v. length v = snd pn \<and> the (V' pn) v i}" for V' k
          using LetPast that by (intro LetPast.hyps(5)) auto
      qed
      with True show ?thesis
        by simp
    next
      case False
      with \<open>pn \<in> dom ?V\<close> LetPast.prems show ?thesis
        by auto
    qed
  qed
  have "finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> ?V (map the v) i \<psi>}"
    by (rule LetPast.hyps(6)[OF _ _ _ dom_V]) (use LetPast.prems in \<open>simp_all add: Formula.nfv_def\<close>)
  then show ?case
    by (simp add: Let_def)
next
  case (And_assign \<phi> \<psi>)
  then have IH: " finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by simp
  have fv_\<psi>_n: "\<forall>z\<in>fv \<psi>. z < n"
    using fvi_less_nfv[of \<psi>] And_assign(5) by fastforce
  \<comment> \<open>assigning a variable @{term x} that does not occur in @{term \<phi>} the value of a term over
    the variables of @{term \<phi>} is injective on the tuples satisfying @{term \<phi>}\<close>
  have assign: ?case
    if x: "x < n" "x \<notin> fv \<phi>" and t: "fv_trm t \<subseteq> fv \<phi>" and fv_\<psi>: "fv \<psi> = insert x (fv_trm t)"
      and sat_\<psi>: "\<And>v. Formula.sat \<sigma> V v i \<psi> \<longleftrightarrow> v ! x = Formula.eval_trm v t" for x t
  proof (rule finite_subset)
    let ?f = "\<lambda>v. v[x := Some (Formula.eval_trm (map the v) t)]"
    let ?A = "{v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    show "finite (?f ` ?A)"
      using IH by (rule finite_imageI)
    show "{v. pwf_tuple n (fv (\<phi> \<and>\<^sub>F \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<phi> \<and>\<^sub>F \<psi>)} \<subseteq> ?f ` ?A"
    proof
      fix v
      assume "v \<in> {v. pwf_tuple n (fv (\<phi> \<and>\<^sub>F \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<phi> \<and>\<^sub>F \<psi>)}"
      with t fv_\<psi> sat_\<psi> have wf: "pwf_tuple n (insert x (fv \<phi>)) v"
        and sat: "Formula.sat \<sigma> V (map the v) i \<phi>" and eq: "map the v ! x = Formula.eval_trm (map the v) t"
        by (simp_all add: Un_absorb2)
      let ?u = "v[x := None]"
      from wf x have "pwf_tuple n (fv \<phi>) ?u"
        by (auto simp: pwf_tuple_def nth_list_update)
      moreover from sat x(2) have "Formula.sat \<sigma> V (map the ?u) i \<phi>"
        by (simp add: sat_the_update)
      ultimately have "?u \<in> ?A"
        by simp
      moreover have "v = ?f ?u"
      proof (rule sym)
        from x(2) t have "\<forall>z\<in>fv_trm t. map the ?u ! z = map the v ! z"
          by (auto simp: map_update intro!: nth_list_update_neq)
        then have "Formula.eval_trm (map the ?u) t = Formula.eval_trm (map the v) t"
          by (rule eval_trm_fv_cong)
        moreover from wf x(1) have "v ! x = Some (map the v ! x)"
          by (auto simp: pwf_tuple_def)
        ultimately show "?f ?u = v"
          using eq x(1) pwf_tuple_length[OF wf] by (simp add: list_update_same_conv)
      qed
      ultimately show "v \<in> ?f ` ?A"
        by (rule rev_image_eqI)
    qed
  qed
  consider x y where "\<psi> = \<^bold>v x =\<^sub>F (\<^bold>v y)" and  "(x \<notin> fv \<phi> \<longleftrightarrow> y \<in> fv \<phi>)"
    |x t where "\<psi> = \<^bold>v x =\<^sub>F t" and "\<not> Formula.is_Var t" and "(x \<notin> fv \<phi> \<and> fv_trm t \<subseteq> fv \<phi>)"
    |x t where "\<psi> = t =\<^sub>F (\<^bold>v x)" and "\<not> Formula.is_Var t" and "(x \<notin> fv \<phi> \<and> fv_trm t \<subseteq> fv \<phi>)"
    using And_assign(2)
    by(simp add: safe_assignment_def Formula.is_Var_def split: Formula.formula.splits trm.splits)
  then show ?case
  proof cases
    case 1
    with fv_\<psi>_n have "x < n" "y < n"
      by simp_all
    show ?thesis
    proof (cases "x \<in> fv \<phi>")
      case True
      with 1 \<open>y < n\<close> show ?thesis
        by (intro assign[of y "\<^bold>v x"]) auto
    next
      case False
      with 1 \<open>x < n\<close> show ?thesis
        by (intro assign[of x "\<^bold>v y"]) auto
    qed
  next
    case 2
    with fv_\<psi>_n show ?thesis
      by (intro assign[of x t]) auto
  next
    case 3
    with fv_\<psi>_n show ?thesis
      by (intro assign[of x t]) auto
  qed
next
  case (And_safe \<phi> \<psi>)
  let ?A = "\<lambda>\<phi>. {v | v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  let ?p = "\<lambda>v. (prestrict (fv \<phi>) v, prestrict (fv \<psi>) v)"
  let ?test = "(?A \<phi> \<times> ?A \<psi>)"
  have "finite (?A \<phi>)" and "finite (?A \<psi>)" using And_safe by auto
  then have "finite (?A \<phi> \<times> ?A \<psi>)" ..
  then have "finite (Option.these (pjoin1 ` (?A \<phi> \<times> ?A \<psi>)))"
    by (auto simp: Option.these_def)
  moreover have "{v. pwf_tuple n (fv \<phi> \<union> fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi> \<and> Formula.sat \<sigma> V (map the v) i \<psi>}
      \<subseteq> Option.these (pjoin1 ` (?A \<phi> \<times> ?A \<psi>))" (is "?B \<subseteq> ?B'")
  proof
    fix v
    assume "v \<in> ?B"
    then have wf: "pwf_tuple n (fv \<phi> \<union> fv \<psi>) v"
      by simp
    from \<open>v \<in> ?B\<close> have "(prestrict (fv \<phi>) v, prestrict (fv \<psi>) v) \<in> ?A \<phi> \<times> ?A \<psi>"
      by (auto simp: pwf_tuple_prestrict_simple sat_the_prestrict)
    moreover have "pjoin1 (prestrict (fv \<phi>) v, prestrict (fv \<psi>) v) = Some v"
    proof -
      from wf have "pwf_tuple n (fv \<phi>) (prestrict (fv \<phi>) v)" "pwf_tuple n (fv \<psi>) (prestrict (fv \<psi>) v)"
        by (auto intro: pwf_tuple_prestrict_simple)
      with wf show ?thesis
        by (simp add: pjoin1_Some_prestrict)
    qed
    ultimately have "Some v \<in> pjoin1 ` (?A \<phi> \<times> ?A \<psi>)"
      by (rule rev_image_eqI[OF _ sym])
    then show "v \<in> ?B'"
      by (simp add: in_these_eq)
  qed
  ultimately show ?case
    by (auto elim!: finite_subset)
next
  case (And_constraint \<phi> \<psi>)
  then have fin: "finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by simp
  have "fv (\<phi> \<and>\<^sub>F \<psi>) = fv \<phi>"
    using And_constraint.hyps(4) by (simp add: Un_absorb2)
  then have "{v. pwf_tuple n (fv (\<phi> \<and>\<^sub>F \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<phi> \<and>\<^sub>F \<psi>)}
    \<subseteq> {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by (simp add: Collect_mono_iff)
  from this fin show ?case
    by (rule finite_subset)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  hence obs: "finite {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>}"
    by simp
  have "FV (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>T I \<psi>')) = FV \<phi>"
    using And_Trigger.hyps(4) by (simp add: Un_absorb2)
  then have "{v. pwf_tuple n (FV (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>T I \<psi>'))) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>T I \<psi>'))}
    \<subseteq> {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>}"
    by (simp add: Collect_mono_iff)
  from this obs show ?case
    by (rule finite_subset)
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  hence obs: "finite {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>}"
    by simp
  have "FV (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>R I \<psi>')) = FV \<phi>"
    using And_Release.hyps(7) by (simp add: Un_absorb2)
  then have "{v. pwf_tuple n (FV (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>R I \<psi>'))) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>R I \<psi>'))}
    \<subseteq> {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>}"
    by (simp add: Collect_mono_iff)
  from this obs show ?case
    by (rule finite_subset)
next
  case (And_Not \<phi> \<psi>)
  then have fin: "finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by simp
  have "fv (\<phi> \<and>\<^sub>F \<not>\<^sub>F \<psi>) = fv \<phi>"
    using And_Not.hyps(4) by (simp add: Un_absorb2)
  then have "{v. pwf_tuple n (fv (\<phi> \<and>\<^sub>F \<not>\<^sub>F \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<phi> \<and>\<^sub>F \<not>\<^sub>F \<psi>)}
    \<subseteq> {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by (simp add: Collect_mono_iff)
  from this fin show ?case
    by (rule finite_subset)
next
  case (Ands l pos neg)
  let ?A = "\<lambda>\<phi>. {v | v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  let ?p = "\<lambda>v. (map (\<lambda> \<phi>.(prestrict (fv \<phi>) v)) pos)"
  let ?A_list = "listset (map (\<lambda> \<phi>. ?A \<phi>) pos)"
  from Ands.hyps(1) have pos: "set pos = {\<phi> \<in> set l. safe_formula \<phi>}"
    by simp
  have "finite (?A \<phi>)" if "\<phi> \<in> set pos" for \<phi>
  proof -
    from that pos have "\<phi> \<in> set l"
      by simp
    with Ands.prems(1) have "Safety.future_bounded \<phi>"
      by (simp add: list_all_iff)
    moreover from \<open>\<phi> \<in> set l\<close> Ands.prems(2) have "Formula.nfv \<phi> \<le> n"
      by (simp add: Max_ge_iff)
    ultimately show ?thesis
      using that Ands.hyps(6) Ands.prems(3,4) by (simp add: list_all_iff)
  qed
  then have "finite (?A_list)"
    by (intro finite_listset) auto
  then have "finite (Option.these (pjoinN ` (?A_list)))"
    by(auto simp: Option.these_def)
  moreover have "{v. pwf_tuple n (\<Union> (fv ` set l)) v \<and> (\<forall>x\<in>set l. Formula.sat \<sigma> V (map the v) i x)}
      \<subseteq> (Option.these (pjoinN ` (?A_list)))" (is "?B \<subseteq> ?B'")
  proof
    fix v
    assume "v \<in> ?B"
    then have wf: "pwf_tuple n (\<Union> (fv ` set l)) v"
      by simp
    from \<open>v \<in> ?B\<close> have "?p v \<in> ?A_list"
      using Ands(1)
      by (auto simp: sat_the_prestrict in_listset_conv_list_all2 list.rel_map intro!: list.rel_refl_strong pwf_tuple_prestrict_simple)
    moreover have "pjoinN (?p v) = Some v"
    proof -
      have "set l = set pos \<union> set neg"
        using Ands.hyps(1) by auto
      with Ands.hyps(5) have fv_pos: "\<Union> (fv ` set pos) = \<Union> (fv ` set l)"
        by blast
      with wf have all2: "list_all2 (pwf_tuple n) (map fv pos) (?p v)"
        by (auto simp: list.rel_map intro!: list.rel_refl_strong pwf_tuple_prestrict_simple)
      from Ands.hyps(2) have "?p v \<noteq> []"
        by simp
      with wf fv_pos show ?thesis
        by (auto simp: pjoinN_Some_prestrict[OF all2] list.rel_map intro!: list.rel_refl_strong)
    qed
    ultimately have "Some v \<in> pjoinN ` ?A_list"
      by (rule rev_image_eqI[OF _ sym])
    then show "v \<in> ?B'"
      by (simp add: in_these_eq)
  qed
  ultimately show ?case
    by (auto elim!: finite_subset)
next
  case (Neg \<phi>)
  then show ?case
   by(simp flip: in_unit_ptable add: unit_ptable_def)
next
  case (Or \<phi> \<psi>)
  then have "finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(simp)
  moreover from Or have "finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<psi>}"
    by(simp)
  ultimately have "finite ({v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>} \<union> {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<psi>})"
    (is "finite ?AB")
    by(simp)
  moreover have "{v. pwf_tuple n (fv (\<phi> \<or>\<^sub>F \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<phi> \<or>\<^sub>F \<psi>)} \<subseteq> ?AB"
    using Or.hyps(1) by auto
  ultimately show ?case
    by (rule finite_subset[rotated])
next
  case (Exists t \<phi>)
  from Exists have IH: "finite {v. pwf_tuple (Suc n) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(simp add: Formula.nfv_def fvi_Suc_bound Suc_le_eq)
  have "{v. pwf_tuple n (fv (\<exists>\<^sub>F:t. \<phi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<exists>\<^sub>F:t. \<phi>)}
    \<subseteq> tl ` {v. pwf_tuple (Suc n) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  proof
    fix v
    assume "v \<in> {v. pwf_tuple n (fv (\<exists>\<^sub>F:t. \<phi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<exists>\<^sub>F:t. \<phi>)}"
    then obtain z where wf: "pwf_tuple n (Formula.fvi (Suc 0) \<phi>) v"
      and sat: "Formula.sat \<sigma> V (z # map the v) i \<phi>"
      by auto
    \<comment> \<open>the bound variable 0 occurs in @{term \<phi>}, so it gets a defined value\<close>
    from wf Exists.hyps(2) have "pwf_tuple (Suc n) (fv \<phi>) (Some z # v)"
      by (simp add: pwf_tuple_def All_less_Suc2 fvi_Suc)
    moreover from sat have "Formula.sat \<sigma> V (map the (Some z # v)) i \<phi>"
      by simp
    ultimately have "Some z # v \<in> {v. pwf_tuple (Suc n) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
      by simp
    then show "v \<in> tl ` {v. pwf_tuple (Suc n) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
      by (rule rev_image_eqI) simp
  qed
  from this finite_imageI[OF IH] show ?case
    by (rule finite_subset)
next
  case (Agg y \<omega> tys f \<phi>)
  define b where [simp]: "b= length tys"
  from Agg have IH: "finite {v. pwf_tuple (n+b) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(auto 0 4 simp add: Suc_le_eq ball_Un Formula.nfv_def intro!: Agg(5)[where ?n="n+(length tys)"] dest!: fvi_plus_bound[where b=0 and c=b, simplified])
  then have IH_alt: "finite (drop b`{v. pwf_tuple (n+b) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>})"
    by(auto)
  have drop_b: "finite (drop b`{v. pwf_tuple (n+b) (fv \<phi>) v \<and> fv \<phi> = {0..<b}})"
  proof (rule finite_subset)
    show "drop b`{v. pwf_tuple (n+b) (fv \<phi>) v \<and> fv \<phi> = {0..<b}} \<subseteq> {replicate n None}"
      by (auto simp add: pwf_tuple_def list_eq_iff_nth_eq[where ?ys="replicate n None"])
  qed simp
  have final_subset: "finite (drop b`{v. pwf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})})"
    using drop_b IH_alt
    by (simp add: conj_disj_distribL Collect_disj_eq image_Un)
  \<comment> \<open>the variable @{term y} does not occur in @{term \<phi>} (shifted by @{term b})\<close>
  have upd_eq: "(zs @ map the (x[y := None])) ! j = (zs @ map the x) ! j"
    if "length zs = b" and "j \<in> fv \<phi>" for x and zs :: Formula.env and j
  proof (cases "j < b")
    case True
    with that(1) show ?thesis
      by (simp add: nth_append)
  next
    case False
    with that Agg.hyps(1) have "y \<noteq> j - b"
      by auto
    with False that(1) show ?thesis
      by (simp add: nth_append map_update)
  qed
  have sat_eq: "Formula.sat \<sigma> V (zs @ map the (x[y := None])) i \<phi> = Formula.sat \<sigma> V (zs @ map the (x)) i \<phi>" if "length zs = b" for x zs
    using that by (intro sat_fv_cong) (simp add: upd_eq)
  have eval_trm_eq: "Formula.eval_trm (zs @ map the (x[y := None])) f = Formula.eval_trm (zs @ map the (x)) f" if "length zs = b" for x zs
    using upd_eq[OF that] Agg.hyps(3) by (intro eval_trm_fv_cong) blast
  let ?M = "\<lambda>u. {(x, ecard Zs) | x Zs. Zs = {zs. length zs = b \<and> Formula.sat \<sigma> V (zs @ u) i \<phi> \<and> Formula.eval_trm (zs @ u) f = x} \<and> Zs \<noteq> {}}"
  have sat_Agg: "Formula.sat \<sigma> V u i (Formula.Agg y \<omega> tys f \<phi>) \<longleftrightarrow>
    (?M u = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b}) \<and> u ! y = eval_agg_op \<omega> (?M u)" for u
    by (simp only: Formula.sat.simps Let_def b_def)
  have M_upd: "?M (map the (v[y := None])) = ?M (map the v)" for v
    by (simp only: sat_eq eval_trm_eq cong: conj_cong)
  have fv_Agg: "fv (Formula.Agg y \<omega> tys f \<phi>) = insert y (Formula.fvi b \<phi>)"
    using Agg.hyps(3) by (auto simp: fvi_iff_fv[of _ "length tys"] fvi_trm_iff_fv_trm[of _ "length tys"])
  have y_notin: "y \<notin> Formula.fvi b \<phi>"
    using Agg.hyps(1) by (simp add: fvi_iff_fv[of _ "length tys"])
  have "y < n"
    using fvi_less_nfv[of "Formula.Agg y \<omega> tys f \<phi>"] Agg.prems(2) fv_Agg by fastforce
  \<comment> \<open>a satisfying tuple is determined by its group, i.e., the values of all other variables\<close>
  let ?G = "{w. pwf_tuple n (Formula.fvi b \<phi>) w \<and> (?M (map the w) = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b})}"
  let ?g = "\<lambda>w. w[y := Some (eval_agg_op \<omega> (?M (map the w)))]"
  have S_sub: "{v. pwf_tuple n (fv (Formula.Agg y \<omega> tys f \<phi>)) v \<and> Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> tys f \<phi>)}
    \<subseteq> ?g ` ?G"
  proof
    fix v
    assume "v \<in> {v. pwf_tuple n (fv (Formula.Agg y \<omega> tys f \<phi>)) v \<and> Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> tys f \<phi>)}"
    then have wf: "pwf_tuple n (insert y (Formula.fvi b \<phi>)) v"
      and sat: "(?M (map the v) = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b}) \<and> map the v ! y = eval_agg_op \<omega> (?M (map the v))"
      unfolding mem_Collect_eq fv_Agg sat_Agg by blast+
    let ?w = "v[y := None]"
    from wf y_notin \<open>y < n\<close> have "pwf_tuple n (Formula.fvi b \<phi>) ?w"
      by (auto simp: pwf_tuple_def nth_list_update)
    moreover from sat have "?M (map the ?w) = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b}"
      unfolding M_upd by blast
    ultimately have "?w \<in> ?G"
      by blast
    moreover have "?g ?w = v"
    proof -
      from wf \<open>y < n\<close> have "v ! y \<noteq> None"
        by (simp add: pwf_tuple_def)
      with sat pwf_tuple_length[OF wf] \<open>y < n\<close> have vy: "v ! y = Some (eval_agg_op \<omega> (?M (map the v)))"
        by (cases "v ! y") auto
      have "?g ?w = v[y := Some (eval_agg_op \<omega> (?M (map the v)))]"
        by (simp only: list_update_overwrite M_upd)
      also have "\<dots> = v"
        using vy pwf_tuple_length[OF wf] \<open>y < n\<close> by (simp add: list_update_same_conv)
      finally show ?thesis .
    qed
    ultimately show "v \<in> ?g ` ?G"
      by (rule rev_image_eqI[OF _ sym])
  qed
  \<comment> \<open>every group extends to a satisfying tuple of @{term \<phi>}, unless @{term \<phi>} only has the bound variables\<close>
  have G_sub: "?G \<subseteq> drop b`{v. pwf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})}"
  proof
    fix w
    assume "w \<in> ?G"
    then have wf: "pwf_tuple n (Formula.fvi b \<phi>) w" and M: "?M (map the w) = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b}"
      unfolding mem_Collect_eq by blast+
    show "w \<in> drop b`{v. pwf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})}"
    proof (cases "?M (map the w) = {}")
      case False
      then obtain zs where zs: "length zs = b" "Formula.sat \<sigma> V (zs @ map the w) i \<phi>"
        by auto
      let ?u = "map2 (\<lambda>j z. if j \<in> fv \<phi> then Some z else None) [0..<b] zs @ w"
      have "pwf_tuple (n+b) (fv \<phi>) ?u"
        unfolding pwf_tuple_def
      proof (intro conjI allI impI)
        show "length ?u = n + b"
          using zs(1) pwf_tuple_length[OF wf] by simp
        fix j
        assume "j < n + b"
        show "?u ! j = None \<longleftrightarrow> j \<notin> fv \<phi>"
        proof (cases "j < b")
          case True
          with zs(1) show ?thesis
            by (simp add: nth_append)
        next
          case False
          with \<open>j < n + b\<close> wf have "w ! (j - b) = None \<longleftrightarrow> j - b \<notin> Formula.fvi b \<phi>"
            by (simp add: pwf_tuple_def)
          with False zs(1) show ?thesis
            by (simp add: nth_append fvi_iff_fv[of _ "length tys"])
        qed
      qed
      moreover have "Formula.sat \<sigma> V (map the ?u) i \<phi>"
      proof -
        have "\<forall>j\<in>fv \<phi>. map the ?u ! j = (zs @ map the w) ! j"
          using zs(1) by (auto simp: nth_append)
        then have "Formula.sat \<sigma> V (map the ?u) i \<phi> = Formula.sat \<sigma> V (zs @ map the w) i \<phi>"
          by (rule sat_fv_cong)
        with zs(2) show ?thesis
          by simp
      qed
      ultimately have "?u \<in> {v. pwf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})}"
        by blast
      moreover have "drop b ?u = w"
        using zs(1) by simp
      ultimately show ?thesis
        by (rule rev_image_eqI[OF _ sym])
    next
      case True
      with M Agg.hyps(2) have fv_\<phi>: "fv \<phi> = {0..<b}"
        by auto
      then have "Formula.fvi b \<phi> = {}"
        by (auto simp: fvi_iff_fv[of _ "length tys"])
      with wf have w: "w = replicate n None"
        by (simp add: pwf_tuple_empty_iff)
      let ?u = "replicate b (Some undefined) @ w"
      have "pwf_tuple (n+b) (fv \<phi>) ?u"
        using w fv_\<phi> by (auto simp: pwf_tuple_def nth_append)
      with fv_\<phi> have "?u \<in> {v. pwf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})}"
        by blast
      moreover have "drop b ?u = w"
        by simp
      ultimately show ?thesis
        by (rule rev_image_eqI[OF _ sym])
    qed
  qed
  from G_sub final_subset have "finite ?G"
    by (rule finite_subset)
  then have "finite (?g ` ?G)"
    by (rule finite_imageI)
  with S_sub show ?case
    by (rule finite_subset)
next
  case (Prev I \<phi>)
  then have fin: "finite
            {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) (i-1) \<phi>}"
    by simp
  have "{v. pwf_tuple n (fv (Formula.Prev I \<phi>)) v \<and> Formula.sat \<sigma> V (map the v) i (Formula.Prev I \<phi>)}
    \<subseteq> {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) (i-1) \<phi>}"
    by (cases i) auto
  from this fin show ?case
    by (rule finite_subset)
next
  case (Next I \<phi>)
  then have fin: "finite
     {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) (Suc i) \<phi>}"
    by simp
  have "{v. pwf_tuple n (fv (Formula.Next I \<phi>)) v \<and> Formula.sat \<sigma> V (map the v) i (Formula.Next I \<phi>)}
    \<subseteq> {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) (Suc i) \<phi>}"
    by auto
  from this fin show ?case
    by (rule finite_subset)
next
  case (Since \<phi> I \<psi>)
  then have "\<forall> j. finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have fin: "finite (\<Union> j\<le>i. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>})"
    by(auto)
  have "fv (Formula.Since \<phi> I \<psi>) = fv \<psi>"
    using Since.hyps(1) by (simp add: Un_absorb1)
  then have "{v. pwf_tuple n (fv (Formula.Since \<phi> I \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (Formula.Since \<phi> I \<psi>)}
    \<subseteq> (\<Union> j\<le>i. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>})"
    by auto
  from this fin show ?case
    by (rule finite_subset)
next
  case (Not_Since \<phi> I \<psi>)
  then have "\<forall> j. finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have fin: "finite (\<Union> j\<le>i. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>})"
    by(auto)
  have "fv (Formula.Since (Formula.Neg \<phi>) I \<psi>) = fv \<psi>"
    using Not_Since.hyps(1) by (simp add: Un_absorb1)
  then have "{v. pwf_tuple n (fv (Formula.Since (Formula.Neg \<phi>) I \<psi>)) v
      \<and> Formula.sat \<sigma> V (map the v) i (Formula.Since (Formula.Neg \<phi>) I \<psi>)}
    \<subseteq> (\<Union> j\<le>i. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>})"
    by auto
  from this fin show ?case
    by (rule finite_subset)
next
  case (Until \<phi> I \<psi>)
  from Until.prems(1) obtain m where m: "\<not> memR I m"
    by (auto simp: bounded_memR)
  obtain j where j: "m + \<tau> \<sigma> i \<le> \<tau> \<sigma> j"
    using ex_le_\<tau> by blast
  \<comment> \<open>after @{term j}, the interval has been left\<close>
  have j2_le: "j2 \<le> j" if "memR I (\<tau> \<sigma> j2 - \<tau> \<sigma> i)" for j2
  proof (rule ccontr)
    assume "\<not> j2 \<le> j"
    then have "\<tau> \<sigma> j \<le> \<tau> \<sigma> j2"
      by (intro \<tau>_mono) simp
    with j have "m \<le> \<tau> \<sigma> j2 - \<tau> \<sigma> i"
      by linarith
    with that m show False
      using memR_antimono by blast
  qed
  from Until have "\<forall> j. finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have fin: "finite (\<Union> j'\<le>j. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j' \<psi>})"
    by(auto)
  have "fv (Formula.Until \<phi> I \<psi>) = fv \<psi>"
    using Until.hyps(1) by (simp add: Un_absorb1)
  then have "{v. pwf_tuple n (fv (Formula.Until \<phi> I \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (Formula.Until \<phi> I \<psi>)}
    \<subseteq> (\<Union> j'\<le>j. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j' \<psi>})"
    using j2_le by auto
  from this fin show ?case
    by (rule finite_subset)
next
  case (Not_Until \<phi> I \<psi>)
  from Not_Until.prems(1) obtain m where m: "\<not> memR I m"
    by (auto simp: bounded_memR)
  obtain j where j: "m + \<tau> \<sigma> i \<le> \<tau> \<sigma> j"
    using ex_le_\<tau> by blast
  \<comment> \<open>after @{term j}, the interval has been left\<close>
  have j2_le: "j2 \<le> j" if "memR I (\<tau> \<sigma> j2 - \<tau> \<sigma> i)" for j2
  proof (rule ccontr)
    assume "\<not> j2 \<le> j"
    then have "\<tau> \<sigma> j \<le> \<tau> \<sigma> j2"
      by (intro \<tau>_mono) simp
    with j have "m \<le> \<tau> \<sigma> j2 - \<tau> \<sigma> i"
      by linarith
    with that m show False
      using memR_antimono by blast
  qed
  from Not_Until have "\<forall> j. finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have fin: "finite (\<Union> j'\<le>j. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j' \<psi>})"
    by(auto)
  have "fv (Formula.Until (Formula.Neg \<phi>) I \<psi>) = fv \<psi>"
    using Not_Until.hyps(1) by (simp add: Un_absorb1)
  then have "{v. pwf_tuple n (fv (Formula.Until (Formula.Neg \<phi>) I \<psi>)) v
      \<and> Formula.sat \<sigma> V (map the v) i (Formula.Until (Formula.Neg \<phi>) I \<psi>)}
    \<subseteq> (\<Union> j'\<le>j. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j' \<psi>})"
    using j2_le by auto
  from this fin show ?case
    by (rule finite_subset)
next
  case (Trigger \<phi> I \<psi>) (* notice the False at the end *)
  let ?sats = "{v. pwf_tuple n (FV (\<phi> \<^bold>T I \<psi>)) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi> \<^bold>T I \<psi>}"
  have "finite (unit_ptable n)"
    by (auto simp: unit_ptable_def)
  have psi_prptys: "Safety.future_bounded \<psi>" "Formula.nfv \<psi> \<le> n"
    using Trigger.prems
    by (auto simp: Formula.nfv_def)
  have phi_prptys: "Safety.future_bounded \<phi>" "Formula.nfv \<phi> \<le> n"
    using Trigger.prems
    by (auto simp: Formula.nfv_def)
  hence "finite {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}" 
    and "finite {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<phi>}" 
    for j
    using Trigger.hyps(6)[OF phi_prptys Trigger.prems(3,4)]
    Trigger.hyps(7)[OF psi_prptys Trigger.prems(3,4)]
    by auto
  hence "finite ((\<Union>j\<le>i. {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}) \<union> 
    (\<Union>j\<le>i. {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<phi>}))" (is "finite ?bigU")
    by auto
  have False
    using Trigger(1) .
  thus ?case
    by blast
next
  case (Trigger_0 \<phi> I \<psi>)
  have psi_prptys: "Safety.future_bounded \<psi>" "Formula.nfv \<psi> \<le> n"
    using Trigger_0.prems
    by (auto simp: Formula.nfv_def)
  hence "finite {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}" for j
    using Trigger_0.hyps(5)[OF psi_prptys Trigger_0.prems(3,4)]
    by force
  hence "finite (\<Union>j\<le>i. {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>})"
    by auto
  moreover have "{v. pwf_tuple n (FV (\<phi> \<^bold>T I \<psi>)) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi> \<^bold>T I \<psi>}
    \<subseteq> (\<Union>j\<le>i. {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>})"
    using Trigger_0.hyps
    by (auto simp add: Un_absorb1)
  ultimately show ?case 
    by (elim finite_subset[rotated])
next
  case (Release \<phi> I \<psi>) (* notice the False at the end *)
  let ?sats = "{v. pwf_tuple n (FV (\<phi> \<^bold>R I \<psi>)) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi> \<^bold>R I \<psi>}"
  have "finite (unit_ptable n)"
    by (auto simp: unit_ptable_def)
  have psi_prptys: "Safety.future_bounded \<psi>" "Formula.nfv \<psi> \<le> n"
    using Release.prems
    by (auto simp: Formula.nfv_def)
  have phi_prptys: "Safety.future_bounded \<phi>" "Formula.nfv \<phi> \<le> n"
    using Release.prems
    by (auto simp: Formula.nfv_def)
  hence "finite {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}" 
    and "finite {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<phi>}" 
    for j
    using Release.hyps(6)[OF phi_prptys Release.prems(3,4)]
    Release.hyps(7)[OF psi_prptys Release.prems(3,4)]
    by auto
  hence "finite ((\<Union>j\<le>i. {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}) \<union> 
    (\<Union>j\<le>i. {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<phi>}))" (is "finite ?bigU")
    by auto
  have False
    using Release(1) .
  thus ?case
    by blast
next
  case (Release_0 \<phi> I \<psi>)
  \<comment> \<open>with 0 in the interval, the release implies its right operand\<close>
  from Release_0 have fin: "finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<psi>}"
    by (simp add: Formula.nfv_def)
  have "fv (Formula.Release \<phi> I \<psi>) = fv \<psi>"
    using Release_0.hyps(4) by (simp add: Un_absorb1)
  then have "{v. pwf_tuple n (fv (Formula.Release \<phi> I \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (Formula.Release \<phi> I \<psi>)}
    \<subseteq> {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<psi>}"
    using Release_0.hyps(1) by auto
  from this fin show ?case
    by (rule finite_subset)
next
  case (MatchP I r)
  have IH: "finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) k \<phi>}"
    if "\<phi> \<in> safe_atms r" for k \<phi>
  proof -
    \<comment> \<open>@{term \<phi>} is an atom of @{term r} or the negation of @{term \<phi>} is one\<close>
    from that obtain \<psi> where \<psi>: "\<psi> \<in> Regex.atms r"
      and \<phi>\<psi>: "\<phi> \<in> (if safe_formula \<psi> then {\<psi>} else case \<psi> of Formula.Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"
      unfolding safe_atms_def by blast
    from \<phi>\<psi> have "\<phi> = \<psi> \<or> \<psi> = Formula.Neg \<phi>"
      by (cases \<psi> rule: Formula.formula.exhaust) (simp_all split: if_splits)
    then have fv: "fv \<phi> = fv \<psi>" and fb: "Safety.future_bounded \<phi> = Safety.future_bounded \<psi>"
      by auto
    from MatchP.prems(1) \<psi> fb have "Safety.future_bounded \<phi>"
      by (simp add: regex.pred_set)
    moreover have "Formula.nfv \<phi> \<le> n"
    proof -
      have "\<forall>x\<in>fv \<phi>. x < n"
        using fvi_less_nfv_regex[of r] MatchP.prems(2) \<psi> fv by (fastforce simp: fv_regex_alt)
      then show ?thesis
        by (simp add: Formula.nfv_def Suc_le_eq)
    qed
    ultimately show ?thesis
      using MatchP.prems(3,4) by (intro MatchP.hyps(2)[rule_format, OF that]) simp_all
  qed
  from MatchP(3-) show ?case
    by (intro finite_subset[OF _ safe_regex_Past_finite[OF MatchP(1) IH, of i]]) auto
next
  case (MatchF I r)
  from MatchF.prems(1) obtain m where m: "\<not> memR I m"
    by (auto simp: bounded_memR)
  obtain j where j: "m + \<tau> \<sigma> i \<le> \<tau> \<sigma> j"
    using ex_le_\<tau> by blast
  \<comment> \<open>after @{term j}, the interval has been left\<close>
  have j2_le: "j2 \<le> j" if "memR I (\<tau> \<sigma> j2 - \<tau> \<sigma> i)" for j2
  proof (rule ccontr)
    assume "\<not> j2 \<le> j"
    then have "\<tau> \<sigma> j \<le> \<tau> \<sigma> j2"
      by (intro \<tau>_mono) simp
    with j have "m \<le> \<tau> \<sigma> j2 - \<tau> \<sigma> i"
      by linarith
    with that m show False
      using memR_antimono by blast
  qed
  have IH: "finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) k \<phi>}"
    if "\<phi> \<in> safe_atms r" for k \<phi>
  proof -
    \<comment> \<open>@{term \<phi>} is an atom of @{term r} or the negation of @{term \<phi>} is one\<close>
    from that obtain \<psi> where \<psi>: "\<psi> \<in> Regex.atms r"
      and \<phi>\<psi>: "\<phi> \<in> (if safe_formula \<psi> then {\<psi>} else case \<psi> of Formula.Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"
      unfolding safe_atms_def by blast
    from \<phi>\<psi> have "\<phi> = \<psi> \<or> \<psi> = Formula.Neg \<phi>"
      by (cases \<psi> rule: Formula.formula.exhaust) (simp_all split: if_splits)
    then have fv: "fv \<phi> = fv \<psi>" and fb: "Safety.future_bounded \<phi> = Safety.future_bounded \<psi>"
      by auto
    from MatchF.prems(1) \<psi> fb have "Safety.future_bounded \<phi>"
      by (simp add: regex.pred_set)
    moreover have "Formula.nfv \<phi> \<le> n"
    proof -
      have "\<forall>x\<in>fv \<phi>. x < n"
        using fvi_less_nfv_regex[of r] MatchF.prems(2) \<psi> fv by (fastforce simp: fv_regex_alt)
      then show ?thesis
        by (simp add: Formula.nfv_def Suc_le_eq)
    qed
    ultimately show ?thesis
      using MatchF.prems(3,4) by (intro MatchF.hyps(2)[rule_format, OF that]) simp_all
  qed
  from MatchF(3-) show ?case
    using j2_le by (intro finite_subset[OF _ safe_regex_Future_finite[OF MatchF(1) IH, of i j]]) auto
next
  case (TP t)
  then show ?case
    unfolding Formula.is_Var_def Formula.is_Const_def Formula.nfv_def 
    by (auto simp add: pwf_tuple_empty_iff Collect_singleton_tuple_eq_image[where P="\<lambda>x. x = _"])
next
  case (TS t)
  then show ?case
    unfolding Formula.is_Var_def Formula.is_Const_def Formula.nfv_def
    by (auto simp add: pwf_tuple_empty_iff Collect_singleton_tuple_eq_image[where P="\<lambda>x. x = _"])
qed

text \<open>The same for the monitor's tuples, over any list of the free variables.\<close>

lemma safe_formula_finite_dense:
  assumes "safe_formula \<phi>" "Safety.future_bounded \<phi>" "n \<ge> Formula.nfv \<phi>" "\<forall>i. finite (\<Gamma> \<sigma> i)"
    "\<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i}"
    and cs: "distinct cs" "set cs = fv \<phi>"
  shows "finite {v. wf_tuple cs v \<and> Formula.sat \<sigma> V (val n cs v) i \<phi>}"
    (is "finite ?D")
proof -
  let ?P = "{v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  let ?p = "\<lambda>v. map (\<lambda>x. if x \<in> set cs then Some (tup_get cs v x) else None) [0..<n]"
  have lt: "x < n" if "x \<in> set cs" for x
    using that assms(3) cs(2) fvi_less_nfv[of \<phi>] by fastforce
  have "?p v \<in> ?P" if "v \<in> ?D" for v
  proof -
    have "pwf_tuple n (fv \<phi>) (?p v)"
      using cs(2) by (auto simp: pwf_tuple_def)
    moreover have "Formula.sat \<sigma> V (map the (?p v)) i \<phi> \<longleftrightarrow> Formula.sat \<sigma> V (val n cs v) i \<phi>"
      by (rule sat_fv_cong) (use cs(2) lt in auto)
    ultimately show ?thesis
      using that by simp
  qed
  moreover have "inj_on ?p ?D"
  proof (rule inj_onI)
    fix v w
    assume v: "v \<in> ?D" and w: "w \<in> ?D" and eq: "?p v = ?p w"
    have "tup_get cs v c = tup_get cs w c" if "c \<in> set cs" for c
      using arg_cong[OF eq, of "\<lambda>u. u ! c"] lt[OF that] that by simp
    with v w cs(1) show "v = w"
      by (auto intro: wf_tuple_cong)
  qed
  ultimately show ?thesis
    using inj_on_finite[of ?p ?D ?P] safe_formula_finite[OF assms(1-5)] by blast
qed

unbundle MFODL_no_notation \<comment> \<open> disable notation \<close>


(*<*)
end
(*>*)

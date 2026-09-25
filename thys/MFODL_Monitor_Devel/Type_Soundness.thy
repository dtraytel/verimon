theory Type_Soundness
  imports Typing
begin


subsection \<open> Type soundness \<close>

context sat_general
begin

lemma safe_neg_eq: 
  "safe_formula (Formula.Neg (Formula.Eq x1 x2)) \<Longrightarrow> safe_formula  (Formula.Eq x1 x2) \<or>
  (Formula.sat \<sigma> V v i  (Formula.Neg (Formula.Eq x1 x2)) \<longleftrightarrow> sat' \<sigma> V v i  (Formula.Neg (Formula.Eq x1 x2))) "
  by (cases x1; cases x2) auto

lemma foldl_sound:
  assumes  " \<forall>x\<in>set (x22). ty_of x = t" "ty_of x21 = t" 
  shows
    "foldl undef_min x21 x22 = foldl min x21 x22"
    "foldl undef_max x21 x22 = foldl max x21 x22"
    "t \<in> numeric_ty \<Longrightarrow> foldl undef_plus x21 x22 = foldl (+) x21 x22 \<and> ty_of (foldl (+) x21 x22 ) = t"
  
proof -
  from assms(1-2) 
  have minmax:"foldl undef_min x21 x22 = foldl min x21 x22 \<and> foldl undef_max x21 x22 = foldl max x21 x22"
  proof (induction x22 arbitrary: x21 t)
    case (Cons a x22)
    then show ?case using undef_less_eq_sound   
      by (cases x21; cases a; simp add: min_def undef_min_def max_def undef_max_def) fastforce+ 
  qed auto
  from this show "foldl undef_min x21 x22 = foldl min x21 x22" by auto
  from minmax show "foldl undef_max x21 x22 = foldl max x21 x22" by auto
next
  assume "t \<in> numeric_ty"
  from this assms show "foldl undef_plus x21 x22 = foldl (+) x21 x22 \<and> ty_of (foldl (+) x21 x22 ) = t"
  proof (induction x22 arbitrary: x21)
    case (Cons a x22)
    have num: "t \<in> numeric_ty" and ty_x21: "ty_of x21 = t" and ty_a: "ty_of a = t"
      using Cons.prems by simp_all
    have "undef_plus x21 a = x21 + a"
      using num ty_x21 ty_a
      by (cases x21; cases a) (simp_all add: numeric_ty_def undef_plus_sound)
    moreover have "ty_of (x21 + a) = t"
      using ty_x21 ty_a num by (rule ty_of_plus)
    ultimately show ?case
      using Cons.IH[of "x21 + a"] Cons.prems by simp
  qed simp
qed

lemma eval_agg_op_sound: 
  assumes 
    "M={(x, ecard Zs) | x Zs. Zs =
      {zs. length zs = length tys \<and> Formula.sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}"
    "S, E \<turnstile> formula.Agg y (agg_op,d) tys f \<phi> " 
    "wty_envs S \<sigma> V"
    "fv_trm f \<subseteq> fv \<phi>"
    "safe_formula \<phi>" 
  shows "eval_agg_op (agg_op,d) M = eval_agg_op' (agg_op,d) M"
proof -
  from assms(2) obtain t where t_def: "agg_env E tys  \<turnstile> f :: t" and t_wty:"t \<in> agg_trm_type agg_op"
    and phi_wty: "S, agg_env E tys \<turnstile> \<phi>" by cases auto
  let ?Zs = "\<lambda>x. {zs. length zs = length tys \<and> Formula.sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x}"
  have fv_wty: "y\<in>fv_trm f \<Longrightarrow> length zs = length tys \<Longrightarrow> Formula.sat \<sigma> V (zs @ v) i \<phi> \<Longrightarrow> ty_of ((zs @ v) ! y) = agg_env E tys y" for y zs
    using ty_of_sat_safe[OF assms(5) phi_wty assms(3)] assms(4) by blast
  then have wty_M: "\<forall>(x,card) \<in>  M . ty_of x = t" 
    using assms(1) t_def by (auto dest!: ty_of_eval_trm)
  have "finite_multiset M \<Longrightarrow>set (flatten_multiset M) \<subseteq> fst ` M" 
  proof -
    assume "finite_multiset M"
    moreover have "{(x, ecard (?Zs x)) | x. ?Zs x \<noteq> {}} = M"
      unfolding assms(1) by blast
    ultimately have "finite {(x, ecard (?Zs x)) | x. ?Zs x \<noteq> {}}"
      by (simp add: finite_multiset_def)
    then have "finite {x. ?Zs x \<noteq> {}}"
      by (rule finite_fst)
    then show ?thesis
      by (rule set_of_flatten_multiset[OF assms(1)])
  qed
  then have wty_flatten: "finite_multiset M \<Longrightarrow> \<forall>x \<in> set (flatten_multiset M). ty_of x = t" 
    using wty_M by fastforce
  have dbl: "undef_double_of_event_data_agg z = double_of_event_data_agg z" if "ty_of z \<in> numeric_ty" for z
    using that by (cases z) (simp_all add: numeric_ty_def undef_double_of_event_data_agg_sound)
  show ?thesis
  proof (cases "finite_multiset M")
    case False
    then show ?thesis by (cases agg_op) (simp_all add: Let_def split: list.split)
  next
    case True
    then have wty: "\<forall>z \<in> set (flatten_multiset M). ty_of z = t"
      by (rule wty_flatten)
    show ?thesis
    proof (cases "flatten_multiset M")
      case Nil
      then show ?thesis by (cases agg_op) simp_all
    next
      case (Cons x xs)
      then have ty_x: "ty_of x = t" and ty_xs: "\<forall>z\<in>set xs. ty_of z = t"
        using wty by simp_all
      show ?thesis
      proof (cases agg_op)
        case Agg_Cnt
        then show ?thesis using True Cons by simp
      next
        case Agg_Min
        then show ?thesis using True Cons foldl_sound(1)[OF ty_xs ty_x] by simp
      next
        case Agg_Max
        then show ?thesis using True Cons foldl_sound(2)[OF ty_xs ty_x] by simp
      next
        case Agg_Sum
        then have "t \<in> numeric_ty" using t_wty by simp
        then show ?thesis using True Cons Agg_Sum foldl_sound(3)[OF ty_xs ty_x] by simp
      next
        case Agg_Avg
        then have "t \<in> numeric_ty" using t_wty by simp
        then have "foldl undef_plus x xs = foldl (+) x xs" and "ty_of (foldl (+) x xs) \<in> numeric_ty"
          using foldl_sound(3)[OF ty_xs ty_x] by simp_all
        then show ?thesis using True Cons Agg_Avg dbl by simp
      next
        case Agg_Med
        then have num: "t \<in> numeric_ty" using t_wty by simp
        have med: "undef_double_of_event_data_agg ((x # xs) ! k) = double_of_event_data_agg ((x # xs) ! k)"
          if "k < length (x # xs)" for k
        proof (rule dbl)
          from that have "(x # xs) ! k \<in> set (flatten_multiset M)"
            unfolding Cons by (rule nth_mem)
          with wty num show "ty_of ((x # xs) ! k) \<in> numeric_ty" by simp
        qed
        define u where "u = length (x # xs)"
        define u' where "u' = u div 2"
        have "u' < u" "u' - 1 < u"
          unfolding u_def u'_def by simp_all
        then have e: "undef_double_of_event_data_agg ((x # xs) ! u') = double_of_event_data_agg ((x # xs) ! u')"
          "undef_double_of_event_data_agg ((x # xs) ! (u' - 1)) = double_of_event_data_agg ((x # xs) ! (u' - 1))"
          unfolding u_def by (simp_all add: med)
        have "eval_agg_op (agg_op, d) M = EFloat (if even u
          then (double_of_event_data_agg ((x # xs) ! (u' - 1)) + double_of_event_data_agg ((x # xs) ! u')) / double_of_int 2
          else double_of_event_data_agg ((x # xs) ! u'))"
          using True Cons Agg_Med by (simp add: u_def u'_def Let_def)
        also have "\<dots> = EFloat (if even u
          then (undef_double_of_event_data_agg ((x # xs) ! (u' - 1)) + undef_double_of_event_data_agg ((x # xs) ! u')) / double_of_int 2
          else undef_double_of_event_data_agg ((x # xs) ! u'))"
          by (simp only: e)
        also have "\<dots> = eval_agg_op' (agg_op, d) M"
          using True Cons Agg_Med by (simp add: u_def u'_def Let_def)
        finally show ?thesis .
      qed
    qed
  qed
qed 

(* TODO: move to formula *)
lemma sat_trigger_mem0_iff: "mem I 0 \<Longrightarrow> Formula.sat \<sigma> V v i (formula.Trigger \<phi> I \<psi>) 
  \<longleftrightarrow> (\<forall>j \<le> i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k\<in>{j<..i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> k) \<and> Formula.sat \<sigma> V v k (formula.And \<phi> \<psi>)))"
  using sat_trigger_rewrite_0_mem[of I _ _ _ i \<phi> \<psi>]
  by auto

lemma sat_release_mem0_iff: "mem I 0 \<Longrightarrow> Formula.sat \<sigma> V v i (formula.Release \<phi> I \<psi>) 
  \<longleftrightarrow> (\<forall>j \<ge> i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k\<in>{i..<j}. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v k (formula.And \<phi> \<psi>)))"
  using sat_release_rewrite_0_mem[of I _ _ _ i \<phi> \<psi>]
  by auto


subsubsection \<open> Results for sat' from sat \<close>

lemma sat'_until_true:
  assumes "\<not>mem I 0"
  shows "sat' \<sigma> V v i (Formula.Until \<phi> I Formula.TT) = sat' \<sigma> V v i (Formula.Until \<phi> I (Formula.Prev all \<phi>))"
proof (rule iffI)
  assume "sat' \<sigma> V v i (Formula.Until \<phi> I Formula.TT)"
  then obtain j where j_props: "j\<ge>i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<forall>k\<in>{i..<j}. sat' \<sigma> V v k \<phi>" by auto
  {
    assume "j=i"
    then have "False" using j_props assms by auto
  }
  then have "j>i" using j_props(1) using le_eq_less_or_eq by blast
  then show "sat' \<sigma> V v i (Formula.Until \<phi> I (Formula.Prev all \<phi>))"
    using j_props interval_all
    by (auto split: nat.split intro!: exI[of _ j])
next
  assume "sat' \<sigma> V v i (Formula.Until \<phi> I (Formula.Prev all \<phi>))"
  then show "sat' \<sigma> V v i (Formula.Until \<phi> I Formula.TT)" by auto
qed

lemma sat'_always_rewrite_bounded:
  fixes I1 :: \<I>
  assumes "bounded I1" (* [a, b] *)
  shows "sat' \<sigma> V v i (Formula.And (eventually I1 \<phi>) (always I1 \<phi>)) = sat' \<sigma> V v i (always_safe_bounded I1 \<phi>)"
proof (rule iffI)
  assume "sat' \<sigma> V v i (Formula.And (eventually I1 \<phi>) (always I1 \<phi>))"
  then show "sat' \<sigma> V v i (always_safe_bounded I1 \<phi>)"
    using assms always_safe_bounded_def
    by (simp add: always_safe_bounded_def)
next
  define I2 where "I2 = int_remove_lower_bound I1"
  assume "sat' \<sigma> V v i (always_safe_bounded I1 \<phi>)"
  then have rewrite: "sat' \<sigma> V v i (Formula.And (eventually I1 \<phi>) (Formula.Neg (eventually I1 (Formula.And (Formula.Or (once I2 \<phi>) (eventually I2 \<phi>)) (Formula.Neg \<phi>)))))"
    using assms I2_def always_safe_bounded_def
    by (simp add: always_safe_bounded_def)
  then obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat' \<sigma> V v j \<phi>" by auto
  have j_geq_i_sat: "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> (sat' \<sigma> V v j (Formula.Neg (once I2 \<phi>)) \<and> sat' \<sigma> V v j (Formula.Neg (eventually I2 \<phi>))) \<or> sat' \<sigma> V v j \<phi>"
    using rewrite
    by auto
  {
    fix k
    assume k_props: "k\<ge>i" "mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
    then have "(sat' \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> sat' \<sigma> V v k (Formula.Neg (eventually I2 \<phi>))) \<or> sat' \<sigma> V v k \<phi>"
      using j_geq_i_sat by auto
    moreover {
      assume assm: "(sat' \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> sat' \<sigma> V v k (Formula.Neg (eventually I2 \<phi>)))"
      then have leq_k_sat: "\<forall>j\<le>k. mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j) \<longrightarrow> \<not>sat' \<sigma> V v j \<phi>" 
        by (auto simp: once_def)
      have geq_k_sat: "\<forall>j\<ge>k. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k) \<longrightarrow> \<not>sat' \<sigma> V v j \<phi>" using assm by auto
      have j_int: "memL I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "memR I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)"
          using j_props assms
          by auto
      have k_int: "memL I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)" "memR I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
          using k_props assms
          by auto
      {
        assume k_geq_j: "k\<ge>j"
        then have "memR I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def interval_geq j_props(1)
          by (metis forall_finite(1) int_remove_lower_bound.rep_eq memL.rep_eq memR.rep_eq not_le_imp_less prod.sel(1-2))
        then have "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms leq_k_sat j_props k_geq_j by auto
      }
      moreover {
        assume k_less_j: "\<not>(k\<ge>j)"
        then have "memR I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)"
          using j_int k_int assms I2_def j_props(1) k_props(1) interval_geq
          by (metis forall_finite(1) int_remove_lower_bound.rep_eq memL.rep_eq memR.rep_eq not_le_imp_less prod.sel(1-2))
        then have "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)" using assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms geq_k_sat j_props k_less_j by auto
      }
      ultimately have "False" by blast
    }
    ultimately have "sat' \<sigma> V v k \<phi>" by auto
  }
  then have "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v j \<phi>" by auto
  then show "sat' \<sigma> V v i (Formula.And (eventually I1 \<phi>) (always I1 \<phi>))"
    using rewrite
    by auto
qed

lemma sat'_release_rewrite:
  fixes I1 I2 :: \<I>
  assumes "bounded I1" "\<not>mem I1 0" (* [a, b] *)
shows "sat' \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>)) = sat' \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume release: "sat' \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>))"
  {
    assume "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v j \<psi>"
    then have all: "sat' \<sigma> V v i (always I1 \<psi>)" by auto
    obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" using release by auto
    then have "sat' \<sigma> V v i (always_safe_bounded I1 \<psi>)"
      using assms sat'_always_rewrite_bounded[of I1 \<sigma> V v i \<psi>] all
      by auto
    then have "sat' \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      by auto
  }
  moreover {
    assume "\<exists>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> \<not>sat' \<sigma> V v j \<psi>"
    then obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<not>sat' \<sigma> V v j \<psi>" by auto
    define A where "A = {k. k \<in>{i ..< j} \<and> sat' \<sigma> V v k \<phi>}"
    define k where k_def: "k = Min A"
    have "(\<exists>k \<in> {i ..< j}. sat' \<sigma> V v k \<phi>)" using j_props release by auto
    then have A_props: "A \<noteq> {}" "finite A" using A_def by auto
    then have "k \<in> A" using k_def by auto
    then have k_props: "k \<in>{i ..< j}" "sat' \<sigma> V v k \<phi>" using A_def by auto
    {
      fix x
      assume x_props: "x\<le>j" "\<not>mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
      {
        assume k_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
        have "\<tau> \<sigma> x \<le> \<tau> \<sigma> j" using x_props by auto
        then have "\<tau> \<sigma> x - \<tau> \<sigma> i \<le> \<tau> \<sigma> j - \<tau> \<sigma> i" by linarith
        moreover have "memR I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" using assms j_props by auto 
        ultimately have "memR I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using memR_antimono by blast
        moreover have "memL I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
          using k_not_mem_1 x_props assms I2_def
          by (metis flip_int_less_lower.rep_eq memL.rep_eq memR.rep_eq prod.sel(1) prod.sel(2))
        ultimately have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using assms by auto
        then have "False" using k_not_mem_1 by auto
      }
      then have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" by auto
    }
    then have geq_j_mem: "\<forall>x\<le>j. \<not>mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" by auto
    {
      assume "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have "sat' \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
        using k_props
        by auto
    }
    moreover {
      assume k_not_mem_2: "\<not>mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have k_mem: "mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)" using geq_j_mem k_props by auto
      then have "sat' \<sigma> V v k \<psi> \<or> (\<exists>k \<in> {i ..< k}. sat' \<sigma> V v k \<phi>)" using release k_props by auto
      moreover {
        assume "(\<exists>k \<in> {i ..< k}. sat' \<sigma> V v k \<phi>)"
        then obtain l where l_props: "l \<in> {i ..< k}" "sat' \<sigma> V v l \<phi>" by blast
        then have "l \<in> A" using A_def k_props l_props by auto
        then have "False" using A_props l_props k_def by auto
      }
      ultimately have "sat' \<sigma> V v k \<psi>" by auto
      then have k_sat: "sat' \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_props by auto
      then have k_until: "sat' \<sigma> V v k (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
        using assms int_remove_lower_bound.rep_eq memL.rep_eq prod.sel(1)
        by auto
      {
        assume "k=i"
        then have "sat' \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          using k_sat sat_once[of \<sigma> V v i I2 \<phi>] using assms k_mem by auto
      }
      moreover {
        assume k_neq_i: "\<not>(k=i)"
        then have k_pred_geq_i: "k-1\<ge>i" using k_props by auto
        {
          fix x
          assume x_props: "x \<in> {i..<k}" "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
          then have "sat' \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {i ..< x}. sat' \<sigma> V v k \<phi>)" using release by auto
          moreover {
            assume "\<exists>k \<in> {i ..< x}. sat' \<sigma> V v k \<phi>"
            then obtain l where l_props: "l \<in> {i ..< x}" "sat' \<sigma> V v l \<phi>" by blast
            then have "l \<in> A" using A_def x_props k_props by auto
            then have "l \<ge> k" using k_def A_props by auto
            then have "False" using l_props x_props by auto
          }
          ultimately have "sat' \<sigma> V v x \<psi>" by auto
        }
        then have k_greater_sat: "\<forall>x\<in>{i..<k}. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v x \<psi>" by auto
        {
          assume k_suc_mem: "mem I2 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)"
          moreover have "sat' \<sigma> V v (k-1) (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
            using k_pred_geq_i k_until interval_all k_neq_i
            by auto
          ultimately have "(\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat' \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            using k_pred_geq_i
            by blast
          then have "sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            by auto
        }
        moreover {
          define B where "B = {l. l\<in>{i..<k} \<and> mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i) \<and> sat' \<sigma> V v l \<psi>}"
          define c where "c = Min B"
          assume "\<not>mem I2 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)"
          then have k_suc_mem: "mem I1 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)" using geq_j_mem k_props by auto
          then have "sat' \<sigma> V v (k-1) \<psi> \<or> (\<exists>x \<in> {i ..< k-1}. sat' \<sigma> V v x \<phi>)"
            using release k_pred_geq_i
            by auto
          moreover {
            assume "\<exists>x \<in> {i ..< k-1}. sat' \<sigma> V v x \<phi>"
            then obtain x where x_props: "x \<in> {i ..< k-1} \<and> sat' \<sigma> V v x \<phi>" by blast
            then have "x \<in> A" using A_def k_props by auto
            then have "x \<ge> k" using A_props k_def by auto
            then have "False" using x_props by auto
          }
          ultimately have "sat' \<sigma> V v (k-1) \<psi>" by auto
          then have B_props: "B \<noteq> {} \<and> finite B"
            using B_def k_pred_geq_i k_suc_mem k_props k_neq_i
            by auto
          then have "c \<in> B" using c_def by auto
          then have c_props: "c\<in>{i..<k}" "mem I1 (\<tau> \<sigma> c - \<tau> \<sigma> i)" "sat' \<sigma> V v c \<psi>" using B_def by auto
          then have k_cond: "k\<ge>c" "sat' \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_sat by auto
          {
            assume "c=0"
            then have "False" using c_props assms by auto
          }
          then have c_pos: "c\<noteq>0" by auto
          {
            fix x
            assume x_props: "x\<in>{c..<k}"
            then have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> c" by auto
            then have lower: "(\<tau> \<sigma> x - \<tau> \<sigma> i) \<ge> (\<tau> \<sigma> c - \<tau> \<sigma> i)" by auto
            have "\<tau> \<sigma> x \<le> \<tau> \<sigma> k" using x_props by auto
            then have upper: "(\<tau> \<sigma> x - \<tau> \<sigma> i) \<le> (\<tau> \<sigma> k - \<tau> \<sigma> i)" by auto
            then have "memR I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
              using k_mem memR_antimono by blast
            then have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using assms c_props lower by auto
            then have "sat' \<sigma> V v x \<psi>" using k_greater_sat x_props c_props by auto
          }
          then have "\<forall>x\<in>{c..<k}. sat' \<sigma> V v x \<psi>" by auto
          moreover have "mem (int_remove_lower_bound I1) (\<tau> \<sigma> k - \<tau> \<sigma> c)"
            using k_mem c_props
            by (metis atLeastLessThan_iff int_remove_lower_bound.rep_eq interval_geq less_or_eq_imp_le memL.rep_eq memR.rep_eq prod.sel(1) prod.sel(2))
          ultimately have c_sat: "sat' \<sigma> V v c (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
            using assms k_cond
            by auto
          {
            assume "(c-1) \<in> B"
            then have "c-1\<ge>c" using c_def B_props by auto
            moreover have "c-1 < c" using c_pos by auto
            ultimately have "False" by auto
          }
          then have "(c-1) \<notin> B" by blast
          then have disj: "(c-1)\<notin>{i..<k} \<or> \<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<or> \<not>sat' \<sigma> V v (c-1) \<psi>" using B_def by blast
          {
            assume "(c-1)\<notin>{i..<k}"
            then have "False" using assms c_props by auto
          }
          moreover {
            assume "\<not>((c-1)\<notin>{i..<k})"
            then have c_pred_geq_i: "(c-1)\<in>{i..<k}" by auto
            then have disj: "\<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<or> \<not>sat' \<sigma> V v (c-1) \<psi>" using disj by auto
            {
              assume c_suc_mem: "mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
              then have "\<not>sat' \<sigma> V v (c-1) \<psi>" using disj by blast
              then have "False"
                using k_greater_sat c_pred_geq_i c_suc_mem
                by auto
            }
            moreover {
              assume c_pred_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
              {
                assume "\<not>mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
                then have upper: "\<not> memR I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
                  using c_pred_not_mem_1 assms geq_j_mem k_cond k_props
                  by auto
                have "\<tau> \<sigma> c \<ge> \<tau> \<sigma> (c-1)" by auto
                then have "\<tau> \<sigma> c - \<tau> \<sigma> i \<ge> \<tau> \<sigma> (c-1) - \<tau> \<sigma> i" using diff_le_mono by blast
                moreover have "memR I1 (\<tau> \<sigma> c - \<tau> \<sigma> i)" using c_props assms by auto
                ultimately have "memR I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" using memR_antimono by blast
                then have "False" using upper by auto
              }
              then have "mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" by blast
              then have "(c-1)\<ge>i" "mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" "sat' \<sigma> V v (c-1) (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
                using c_pred_geq_i c_sat interval_all c_pos
                by auto
              then have "sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
                using interval_all sat'_eventually
                by blast
            }
            ultimately have "sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by auto
          }
          ultimately have "sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by blast
        }
        ultimately have "sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
          by blast
        then have "sat' \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by simp
      }
      ultimately have "sat' \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by blast
    }
    ultimately have "sat' \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))" by blast
  }
  ultimately have "sat' \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using release
    by auto
  then show "sat' \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
    using assms I2_def
    by (simp add: release_safe_bounded_def) blast
next
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume "sat' \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
  then have assm: "sat' \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using assms I2_def
    by (auto simp: release_safe_bounded_def)
  then have eventually: "sat' \<sigma> V v i (eventually I1 Formula.TT)" by auto
  then have "sat' \<sigma> V v i (always_safe_bounded I1 \<psi>) \<or> sat' \<sigma> V v i (eventually I2 \<phi>) \<or> sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    using assm
    by auto
  moreover {
    assume "sat' \<sigma> V v i (always_safe_bounded I1 \<psi>)"
    then have "sat' \<sigma> V v i (always I1 \<psi>)"
      using assms sat'_always_rewrite_bounded[of I1 \<sigma> V v i \<psi>]
      by auto
    then have "sat' \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by auto
  }
  moreover {
    assume "sat' \<sigma> V v i (eventually I2 \<phi>)"
    then have "\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat' \<sigma> V v j \<phi>" by auto
    then obtain j where j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat' \<sigma> V v j \<phi>" by blast
    {
      fix x
      assume x_props: "x\<ge>i" "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
      {
        assume "x\<le>j"
        then have "\<tau> \<sigma> x \<le> \<tau> \<sigma> j" by auto
        then have "mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using j_props assms I2_def flip_int_less_lower_props
          by (meson diff_le_mono memL_mono memR_antimono memR_zero zero_le)
        then have "False" using x_props assms I2_def
          using flip_int_less_lower.rep_eq memR.rep_eq memR_zero
          by auto
      }
      then have "\<not>(x\<le>j)" by blast
      then have "x>j" by auto
    }
    then have "\<forall>x\<ge>i. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> x>j" by auto
    then have "sat' \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" using j_props by auto
  }
  moreover {
    assume until: "sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    then have "\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat' \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by auto
    then obtain j where j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat' \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by blast
    then have j_pred_sat: "sat' \<sigma> V v (j+1) (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))" by auto
    then have "\<exists>x\<ge>(j+1). sat' \<sigma> V v x (Formula.And \<phi> \<psi>) \<and> (\<forall>k\<in>{(j+1)..<x}. sat' \<sigma> V v k \<psi>)" by auto
    then obtain x where x_props: "x\<ge>(j+1)" "sat' \<sigma> V v x (Formula.And \<phi> \<psi>)" "\<forall>k\<in>{(j+1)..<x}. sat' \<sigma> V v k \<psi>" by blast
    {
      fix l
      assume l_props: "l\<ge>i"
      {
        assume "l>x"
        then have "\<exists>k \<in> {i ..< l}. sat' \<sigma> V v k \<phi>" using x_props j_props by auto
      }
      moreover {
        assume l_assms: "\<not>(l>x)" "mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)"
        then have l_props: "x\<ge>l" "l\<ge>i" "mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)" using l_props by auto
        {
          assume "l\<ge>(j+1)"
          then have "sat' \<sigma> V v l \<psi>" using x_props l_props by auto
        }
        moreover {
          assume "\<not>l\<ge>(j+1)"
          then have l_geq: "l\<le>(j+1)" by auto
          have j_suc_psi: "sat' \<sigma> V v (j+1) \<psi>" using j_pred_sat by auto
          {
            assume "l<(j+1)"
            then have "\<tau> \<sigma> l \<le> \<tau> \<sigma> j" by auto
            then have "mem I2 (\<tau> \<sigma> l - \<tau> \<sigma> i)" using assms I2_def j_props flip_int_less_lower_props
            by (meson diff_le_mono le0 memL_mono memR_antimono memR_zero)
            then have "\<not>mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)"
              using assms I2_def flip_int_less_lower.rep_eq memR.rep_eq memR_zero
              by auto
            then have "False" using l_assms by auto
          }
          then have "l=(j+1)" using l_geq le_eq_less_or_eq by blast
          then have "sat' \<sigma> V v l \<psi>" using j_suc_psi by blast
        }
        ultimately have "sat' \<sigma> V v l \<psi>" by blast
      }
      ultimately have "(mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v l \<psi>) \<or> (\<exists>k \<in> {i ..< l}. sat' \<sigma> V v k \<phi>)" by blast
    }
    then have "\<forall>x\<ge>i. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {i ..< x}. sat' \<sigma> V v k \<phi>)" by auto
    then have "sat' \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by auto
  }
  ultimately have "sat' \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by blast
  then show "sat' \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>))"
    using assm
    by auto
qed

lemma sat'_and_release_rewrite:
  assumes "bounded I" "\<not>mem I 0" (* [a, b] *)
  shows "sat' \<sigma> V v i (Formula.And \<phi> (Formula.Release \<phi>' I \<psi>')) = sat' \<sigma> V v i (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
proof (cases "\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)")
  case True
  then have eventually: "sat' \<sigma> V v i (eventually I Formula.TT)"
    by auto
  then have "sat' \<sigma> V v i (Formula.Release \<phi>' I \<psi>') = sat' \<sigma> V v i (release_safe_bounded \<phi>' I \<psi>')"
    using sat'_release_rewrite[OF assms, of \<sigma> V v i \<phi>' \<psi>']
    by auto
  moreover have "
    Formula.sat \<sigma> V v i (Formula.Or (Formula.And \<phi> (Formula.Neg (eventually I Formula.TT))) (Formula.And \<phi> (release_safe_bounded \<phi>' I \<psi>'))) =
    Formula.sat \<sigma> V v i (Formula.And \<phi> (release_safe_bounded \<phi>' I \<psi>'))"
    using eventually
    by auto
  ultimately show ?thesis
    unfolding and_release_safe_bounded_def
    by auto
qed (auto simp add: and_release_safe_bounded_def)

lemma sat'_release_rewrite_0_mem:
  fixes i j :: nat
  assumes mem: "mem I 0"
  assumes trigger: "sat' \<sigma> V v i (Formula.Release \<phi> I \<psi>)"
  assumes geq: "j\<ge>i"
  assumes mem_j: "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
  shows "sat' \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> sat' \<sigma> V v k (Formula.And \<phi> \<psi>))"
proof (cases "\<exists>k \<in> {i..<j}. sat' \<sigma> V v k \<phi>")
  case True
  define A where "A = {x \<in> {i..<j}. sat' \<sigma> V v x \<phi>}"
  define k where "k = Min A"
  have A_props: "A \<noteq> {}" "finite A" using True A_def by auto
  then have k_in_A: "k \<in> A" using k_def by auto
  then have k_props: "k \<in> {i..<j}" "sat' \<sigma> V v k \<phi>" by (auto simp: A_def)
  have "(\<forall>l<k. l \<notin> A)"
    using Min_le[OF A_props(2)]
    by (fastforce simp: k_def)
  moreover have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" using mem mem_j k_props interval_leq[of I 0 \<sigma> j i k] by auto
  ultimately show ?thesis using k_props mem trigger by (auto simp: A_def)
next
  case False
  then show ?thesis using assms by auto
qed

lemma sat'_always_rewrite_0:
  fixes I :: \<I>
  assumes "mem I 0" "bounded I"
  shows "sat' \<sigma> V v i (always I \<phi>) = sat' \<sigma> V v i (always_safe_0 I \<phi>)"
proof (rule iffI)
  assume all: "sat' \<sigma> V v i (always I \<phi>)"
  {
    define A where "A = {j. j\<ge>i \<and> mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)}"
    define j where "j = Inf A"
    assume "\<exists>j\<ge>i. mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    then have "A \<noteq> {}" using A_def by auto
    then have "j \<in> A" using j_def by (simp add: Inf_nat_def1)
    then have j_props: "j\<ge>i" "mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)" using A_def by auto
    {
      fix k
      assume k_props: "k \<in> {i..<j}"
      then have ineq: "\<tau> \<sigma> k - \<tau> \<sigma> i \<le> \<tau> \<sigma> j - \<tau> \<sigma> i" by (simp add: diff_le_mono)
      {
        assume "mem (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        then have "k \<in> A" using A_def k_props by auto
        then have "k \<ge> j" using j_def cInf_lower by auto
        then have "False" using k_props by auto
      }
      then have "\<not>mem (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)" by blast
      then have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        using j_props ineq assms(1) flip_int_double_upper_leq[of I "(\<tau> \<sigma> j - \<tau> \<sigma> i)" "(\<tau> \<sigma> k - \<tau> \<sigma> i)"]
        by auto 
      then have "sat' \<sigma> V v k \<phi>" using k_props all by auto
    }
    then have until_j: "\<forall>k\<in>{i..<j}. sat' \<sigma> V v k \<phi>" by blast
    have "\<not> mem (flip_int_double_upper I) 0"
      using assms
      by (simp add: flip_int_double_upper.rep_eq memL.rep_eq)
    then have "sat' \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>))"
      using j_props until_j sat'_until_true[of "(flip_int_double_upper I)" \<sigma> V v i \<phi>]
      by auto
  }
  moreover {
    define B where "B = {b. \<not>memR I b}"
    define b where "b = Inf B"
    define C where "C = {k. k\<ge>i \<and> b \<le> \<tau> \<sigma> k - \<tau> \<sigma> i}"
    define c where "c = Inf C"
    assume empty_int: "\<forall>j\<ge>i. \<not> mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)" (* [b+1, 2b] *)
    from assms(2) have "B \<noteq> {}" using B_def bounded_memR by auto
    then have "b \<in> B" using b_def by (simp add: Inf_nat_def1)
    then have b_props: "\<not>memR I b" using B_def by auto
   
    have exists_db: "\<And>x. \<exists>j\<ge>i. x \<le> \<tau> \<sigma> j - \<tau> \<sigma> i"
    proof -
      fix x
      show "\<exists>j\<ge>i. x \<le> \<tau> \<sigma> j - \<tau> \<sigma> i"
        using ex_le_\<tau>[of i "x + \<tau> \<sigma> i" \<sigma>]
        by auto
    qed
    then have "C \<noteq> {}" using C_def by auto
    then have "c \<in> C" using c_def by (simp add: Inf_nat_def1)
    then have c_props: "c\<ge>i" "b \<le> \<tau> \<sigma> c - \<tau> \<sigma> i" using C_def by auto
    {
      assume "b = 0"
      then have "False" using b_props by auto
    }
    then have b_pos: "b>0" by blast
    {
      assume "c = i"
      then have "False" using c_props b_pos by auto
    }
    then have c_ge_i: "c>i" using c_props using le_less by blast
    {
      assume "\<not>mem I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
      then have "\<not>memR I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" using assms(1) memL_mono by blast
      then have "(\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<in> B" using B_def by auto
      then have "(\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<ge> b" using b_def cInf_lower by auto
      then have "(c-1) \<in> C" using C_def c_ge_i by auto
      then have "c-1 \<ge> c" using c_def cInf_lower by auto
      then have "False" using c_ge_i by auto
    }
    then have c_pred_mem: "mem I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" by blast
    then have c_pred_sat: "sat' \<sigma> V v (c-1) \<phi>" using all c_ge_i by auto
    {
      assume "\<not>mem (flip_int I) (\<tau> \<sigma> c - \<tau> \<sigma> (c-1))" (* [b+1, \<infinity>] but attention, here 'b' = b+1 *)
      then have "memR I (\<tau> \<sigma> c - \<tau> \<sigma> (c-1))" using assms(1) bounded_memR int_flip_mem by blast
      then have c_dist: "(\<tau> \<sigma> c - \<tau> \<sigma> (c-1)) < b" using b_props memR_antimono not_le by blast
      from c_pred_mem have "memR I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" by auto
      then have "(\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) < b" using b_props memR_antimono not_le by blast
      then have b_ineq: "b \<le> (\<tau> \<sigma> c - \<tau> \<sigma> i)" "(\<tau> \<sigma> c - \<tau> \<sigma> i) \<le> 2 * (b-1)"
        using c_props c_dist
        by auto
      {
        assume "\<not>memR I (b-1)"
        then have "(b-1) \<in> B" using B_def by auto
        then have "(b-1) \<ge> b" using b_def cInf_lower by auto
        then have "False" using b_pos by linarith
      }
      then have "memR I (b-1)" by blast
      then have "(\<lambda>i. memR I ((div) i 2)) (2*(b-1))" by auto
      then have "(\<lambda>i. memR I ((div) i 2)) (\<tau> \<sigma> c - \<tau> \<sigma> i)" using b_ineq by auto
      then have "memR (flip_int_double_upper I) (\<tau> \<sigma> c - \<tau> \<sigma> i)"
        by (simp add: flip_int_double_upper.rep_eq memR.rep_eq)
      moreover have "memL (flip_int_double_upper I) (\<tau> \<sigma> c - \<tau> \<sigma> i)"
        using b_ineq b_props flip_int_double_upper.rep_eq memL.rep_eq memR_antimono
        by auto
      ultimately have "False" using empty_int c_props by auto
    }
    then have "mem (flip_int I) (\<tau> \<sigma> c - \<tau> \<sigma> (c-1))" by blast
    then have c_pred_sat: "sat' \<sigma> V v (c-1) (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
      using c_pred_sat c_ge_i
      by auto
    have "\<forall>j\<in>{i..<(c-1)}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
      by (meson \<tau>_mono assms(1) atLeastLessThan_iff c_pred_mem diff_le_mono le_eq_less_or_eq memL_mono memR_antimono zero_le)
    then have "\<forall>j\<in>{i..<(c-1)}. sat' \<sigma> V v j \<phi>" using all by auto
    then have
        "(c-1)\<ge>i"
        "mem I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
        "sat' \<sigma> V v (c-1) (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
        "(\<forall>k \<in> {i ..< (c-1)}. sat' \<sigma> V v k \<phi>)"
      using c_ge_i c_pred_mem c_pred_sat
      by auto
    then have "sat' \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))"
      by auto
  }
  ultimately have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>)) (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))))"
    by auto
  then show "sat' \<sigma> V v i (always_safe_0 I \<phi>)" using always_safe_0_def by metis
next
  assume "sat' \<sigma> V v i (always_safe_0 I \<phi>)"
  then have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>)) (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))))"
    using always_safe_0_def
    by metis
  then have "sat' \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) Formula.TT) \<or> sat' \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))" by auto
  moreover {
    assume "sat' \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) Formula.TT)"
    then obtain j where j_props:
      "j\<ge>i" "mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<forall>k\<in>{i..<j}. sat' \<sigma> V v k \<phi>"
      by auto
    then have "\<forall>k\<ge>i. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<longrightarrow> k<j"
      by (metis (no_types, lifting) assms flip_int_double_upper.rep_eq forall_finite(1) interval_leq leI memL.rep_eq prod.sel(1))
    then have "sat' \<sigma> V v i (always I \<phi>)" using j_props by auto
  }
  moreover {
    assume "sat' \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))"
    then obtain j where j_props:
      "j\<ge>i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat' \<sigma> V v j (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
      "\<forall>k\<in>{i..<j}. sat' \<sigma> V v k \<phi>"
      by auto
    then have phi_sat: "\<forall>k\<in>{i..j}. sat' \<sigma> V v k \<phi>" by auto
    {
      fix k
      assume k_props: "k>j" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have t_geq: "(\<tau> \<sigma> k - \<tau> \<sigma> i) \<ge> (\<tau> \<sigma> (j+1) - \<tau> \<sigma> i)" using diff_le_mono by auto
      from j_props have "mem (flip_int I) (\<tau> \<sigma> (j+1) - \<tau> \<sigma> j)" by auto
      then have "\<not>mem I (\<tau> \<sigma> (j+1) - \<tau> \<sigma> i)"
        by (metis \<tau>_mono assms(2) diff_le_mono2 flip_int.rep_eq j_props(1) memL.rep_eq memL_mono prod.sel(1))
      then have "\<not>memR I (\<tau> \<sigma> (j+1) - \<tau> \<sigma> i)" using assms memL_mono by blast
      then have "\<not>memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" using t_geq memR_antimono by blast
      then have "False" using k_props by auto
    }
    then have "\<forall>k>j. \<not>mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" by auto
    then have "sat' \<sigma> V v i (always I \<phi>)" using phi_sat by auto
  }
  ultimately show "sat' \<sigma> V v i (always I \<phi>)" by blast
qed

lemma sat'_release_rewrite_0:
  assumes mem: "mem I 0" "bounded I"
shows "sat' \<sigma> V v i (Formula.Release \<phi> I \<psi>) = sat' \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
proof (rule iffI)
  assume release: "sat' \<sigma> V v i (Formula.Release \<phi> I \<psi>)"
  {
    assume "\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>))"
    then have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))" by auto
  }
  moreover {
    assume "\<not>(\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>)))"
    then obtain j' where j'_props: "j' \<ge> i" "mem I (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "\<not>sat' \<sigma> V v j' (Formula.And \<psi> (Formula.Neg \<phi>))" by blast
    define A where "A = {j. j \<in> {i..<j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat' \<sigma> V v j (Formula.And \<phi> \<psi>)}"
    define j where "j = Min A"
    from j'_props have "\<not>sat' \<sigma> V v j' \<psi> \<or> sat' \<sigma> V v j' \<phi>" by simp
    moreover {
      assume "\<not>sat' \<sigma> V v j' \<psi>"
      then have "\<exists>k \<in> {i..<j'}. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> sat' \<sigma> V v k (Formula.And \<phi> \<psi>)"
      using j'_props assms release sat'_release_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> j']
      by auto
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "j \<in> A" using j_def by auto
    then have j_props: "j \<in> {i..<j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat' \<sigma> V v j (Formula.And \<phi> \<psi>)"
      using A_def
      by auto
    {
      assume "\<not>(\<forall>k \<in> {i..<j}. sat' \<sigma> V v k \<psi>)"
      then obtain k where k_props: "k \<in> {i..<j} \<and> \<not> sat' \<sigma> V v k \<psi>" by blast
      then have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        using assms j_props interval_leq[of I 0 \<sigma> j i k]
        by auto
      then have "\<exists>x \<in> {i..<k}. mem I (\<tau> \<sigma> x - \<tau> \<sigma> i) \<and> sat' \<sigma> V v x (Formula.And \<phi> \<psi>)"
        using assms release k_props sat'_release_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> k]
        by auto
      then obtain x where x_props: "x \<in> {i..<k}" "mem I (\<tau> \<sigma> x - \<tau> \<sigma> i)" "sat' \<sigma> V v x (Formula.And \<phi> \<psi>)"
        by blast
      then have "x \<ge> Min A"
        using A_def A_props k_props j_props
        by auto
      then have "False"
        using j_def k_props x_props
        by auto
    }
    then have "\<forall>k \<in> {i..<j}. sat' \<sigma> V v k \<psi>" by blast
    then have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))"
      using j_props
      by auto
    }
    moreover {
      define B where "B = {j. j\<in>{i..j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat' \<sigma> V v j \<phi>}"
      define k where "k = Min B"
      assume "sat' \<sigma> V v j' \<phi>"
      then have B_props: "B \<noteq> {}" "finite B" using B_def j'_props by auto
      then have "k \<in> B" using k_def by auto
      then have k_props: "k\<in>{i..j'}" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" "sat' \<sigma> V v k \<phi>" using B_def by auto
      have "\<forall>l<k. l \<notin> B"
        using Min_le[OF B_props(2)]
        by (fastforce simp: k_def)
      {
        fix l
        assume l_props: "l \<in> {i..<k}"
        then have l_mem: "mem I (\<tau> \<sigma> l - \<tau> \<sigma> i)"
          using assms k_props interval_leq[of I 0 \<sigma> k i l]
          by auto
        {
          assume "sat' \<sigma> V v l \<phi>"
          then have "l \<in> B" using B_def l_props l_mem k_props by auto
          then have "l\<ge>k" "l<k"
            using k_def l_props B_props(2) Min_le[of B l]
            by auto
        }
        then have "\<not>sat' \<sigma> V v l \<phi>" by auto
      }
      then have not_phi: "\<forall>l\<in>{i..<k}. \<not>sat' \<sigma> V v l \<phi>" using assms B_def by auto
      
      then have k_sat_psi: "sat' \<sigma> V v k \<psi>" using k_props release B_def by auto
      {
        fix l
        assume l_props: "l\<in>{i..<k}"
        then have "mem I (\<tau> \<sigma> l - \<tau> \<sigma> i)"
          using k_props assms interval_leq[of I 0 \<sigma> k i l]
          by auto
        then have "sat' \<sigma> V v l \<psi>"
          using l_props release not_phi
          by auto
      }
      then have "\<forall>l\<in>{i..<k}. sat' \<sigma> V v l \<psi>"
        using not_phi assms release
        by auto
      then have "sat' \<sigma> V v i (Formula.Until \<psi> I (Formula.And \<phi> \<psi>))"
        using k_props k_sat_psi
        by auto
    }
    ultimately have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))" by auto
  }
  ultimately have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))" by blast
  then have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always_safe_0 I \<psi>))"
    using assms sat'_always_rewrite_0[of I \<sigma> V v i "\<psi>"]
    by auto
  then show "sat' \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
    using assms release_safe_0_def[of \<phi> I \<psi>]
    by auto
next
  assume "sat' \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
  then have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always_safe_0 I \<psi>))"
    using assms release_safe_0_def[of \<phi> I \<psi>]
    by auto
  then have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))"
    using assms sat'_always_rewrite_0[of I \<sigma> V v i "\<psi>"]
    by auto
  moreover {
    assume "sat' \<sigma> V v i (always I \<psi>)"
    then have "sat' \<sigma> V v i (Formula.Release \<phi> I \<psi>)" by auto
  }
  moreover {
    fix j
    assume until_and_j_props: "sat' \<sigma> V v i (Formula.Until \<psi> I (Formula.And \<phi> \<psi>))" "j \<ge> i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    then obtain "j'" where j'_props: "j'\<ge>i" "mem I (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "sat' \<sigma> V v j' (Formula.And \<phi> \<psi>)" "(\<forall>k \<in> {i ..< j'}. sat' \<sigma> V v k \<psi>)"
      by fastforce
    moreover {
      assume ge: "j' > j"
      then have "\<forall>k \<in> {i ..< j'}. sat' \<sigma> V v k \<psi>" using j'_props by auto
      then have "sat' \<sigma> V v j \<psi>" using until_and_j_props ge by auto
      then have "sat' \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat' \<sigma> V v k \<phi>)" by auto
    }
    moreover {
      assume leq: "\<not> j' > j"
      moreover {
        assume "j = j'"
        then have "sat' \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat' \<sigma> V v k \<phi>)"
          using j'_props
          by auto
      }
      moreover {
        assume neq: "j \<noteq> j'"
        then have "sat' \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat' \<sigma> V v k \<phi>)"
          using leq j'_props
          by auto
      }
      ultimately have "sat' \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat' \<sigma> V v k \<phi>)" by blast
    }
    ultimately have "sat' \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat' \<sigma> V v k \<phi>)" by blast
  }
  ultimately show "sat' \<sigma> V v i (Formula.Release \<phi> I \<psi>)" by auto
qed


subsubsection \<open> Soundness proof \<close>

lemma soundness: (*Theorem 3.12 helper*)
  assumes
    "safe_formula \<phi>" 
    "S,E \<turnstile> \<phi>"
    "\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y"
    "wty_envs S \<sigma> V"
  shows "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> sat' \<sigma> V v i \<phi>" 
  using assms 
proof (induction arbitrary: v V i S E rule: safe_formula_induct)
  case (Pred e tms)
  from Pred(2) obtain p tys where obt: "S p = Some tys \<and> list_all2 (\<lambda>tm ty. E \<turnstile> tm :: ty) tms tys" by cases auto
  from this Pred have tms_wty: "x \<in> set tms \<Longrightarrow> \<exists>t \<in> set tys. E \<turnstile> x :: t " for x 
    by (metis in_set_conv_nth list_all2_conv_all_nth) 
  have eval_tms_eq: "map (Formula.eval_trm v) tms = map (eval_trm' v) tms" using tms_wty Pred(3) by (auto dest!: eval_trm_sound)
  show ?case by (simp only: Formula.sat.simps sat'.simps eval_tms_eq)
next 
  case (Let p \<phi> \<psi>) 
  obtain E' where 
    psi_wty: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>" and
    phi_wty: "S, E' \<turnstile> \<phi>" using Let.prems(1) by cases auto
  have wtyenv: "x \<in> \<Gamma> \<sigma> i \<Longrightarrow> (case x of (p, xs) \<Rightarrow> (p, length xs) \<notin> dom V \<longrightarrow> (case S (p, length xs) of None \<Rightarrow> False | Some ts \<Rightarrow> wty_tuple ts xs))" for x i
    using Let.prems(3) by (auto simp add: wty_envs_def wty_event_def wty_tuple_def) 
  have list_all_tab:"length xs = Formula.nfv \<phi> \<Longrightarrow>
    Formula.sat \<sigma> V xs i \<phi> \<or> sat' \<sigma> V xs i \<phi> \<Longrightarrow> list_all2 (\<lambda>t x. ty_of x = t) (tabulate E' 0 (Formula.nfv \<phi>)) xs " for xs i 
  proof -
    assume a1: "Formula.sat \<sigma> V xs i \<phi> \<or> sat' \<sigma> V xs i \<phi>"
    assume a2: "length xs = Formula.nfv \<phi>"
    have "ty_of (xs ! x) = E' x" if "x < Formula.nfv \<phi>" for x
    proof -
      have "x \<in> fv \<phi>"
        by (rule subsetD[OF Let.hyps(1)]) (simp add: that)
      with a1 show ?thesis
        using ty_of_sat_safe[OF Let.hyps(2) phi_wty Let.prems(3)]
          ty_of_sat'_safe[OF Let.hyps(2) phi_wty Let.prems(3)]
        by blast
    qed
    with a2 show ?thesis
      by (simp add: list_all2_conv_all_nth)
  qed
  have phi_case: "sat' \<sigma> V v5 i5 \<phi> = Formula.sat \<sigma> V v5 i5 \<phi> " for v5 i5
  proof
    assume sat': "sat' \<sigma> V v5 i5 \<phi>"
    have "\<forall>y\<in>fv \<phi>. ty_of (v5 ! y) = E' y"
      using ty_of_sat'_safe[OF Let.hyps(2) phi_wty Let.prems(3) sat'] by blast
    with sat' show "Formula.sat \<sigma> V v5 i5 \<phi>"
      using Let.IH(1)[OF phi_wty _ Let.prems(3)] by blast
  next
    assume sat: "Formula.sat \<sigma> V v5 i5 \<phi>"
    have "\<forall>y\<in>fv \<phi>. ty_of (v5 ! y) = E' y"
      using ty_of_sat_safe[OF Let.hyps(2) phi_wty Let.prems(3) sat] by blast
    with sat show "sat' \<sigma> V v5 i5 \<phi>"
      using Let.IH(1)[OF phi_wty _ Let.prems(3)] by blast
  qed
  have V_eq: "V((p, Formula.nfv \<phi>) \<mapsto> (\<lambda>v i. Formula.sat \<sigma> V v i \<phi>)) = V((p, Formula.nfv \<phi>) \<mapsto> (\<lambda>v i. sat' \<sigma> V v i \<phi>))"
    using phi_case by auto
  let ?S' = "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>))"
  let ?V' = "V((p, Formula.nfv \<phi>) \<mapsto> (\<lambda>v i. sat' \<sigma> V v i \<phi>))"
  have wty_envs': "wty_envs ?S' \<sigma> ?V'"
  proof -
    {
      fix q xs j
      assume in_\<Gamma>: "(q, xs) \<in> \<Gamma> \<sigma> j" and not_V': "(q, length xs) \<notin> dom ?V'"
      then have "(q, length xs) \<noteq> (p, Formula.nfv \<phi>)" and "(q, length xs) \<notin> dom V"
        by auto
      moreover from in_\<Gamma> this(2) Let.prems(3) have "wty_event S q xs"
        unfolding wty_envs_def by blast
      ultimately have "wty_event ?S' q xs"
        by (auto simp: wty_event_def)
    } moreover {
      fix q xs j
      assume in_V': "(q, length xs) \<in> dom ?V'" and valid: "the (?V' (q, length xs)) xs j"
      have "wty_event ?S' q xs"
      proof (cases "(q, length xs) = (p, Formula.nfv \<phi>)")
        case True
        with valid have "sat' \<sigma> V xs j \<phi>" and "length xs = Formula.nfv \<phi>"
          by auto
        then have "list_all2 (\<lambda>t x. ty_of x = t) (tabulate E' 0 (Formula.nfv \<phi>)) xs"
          using list_all_tab by blast
        with True show ?thesis
          by (auto simp: wty_event_def wty_tuple_def)
      next
        case False
        with in_V' valid have "(q, length xs) \<in> dom V" and "the (V (q, length xs)) xs j"
          by auto
        with Let.prems(3) have "wty_event S q xs"
          unfolding wty_envs_def by blast
        with False show ?thesis
          by (auto simp: wty_event_def)
      qed
    } ultimately show ?thesis
      unfolding wty_envs_def by blast
  qed
  have "\<forall>y\<in>fv \<psi>. ty_of (v ! y) = E y"
    using Let.prems(2) by simp
  then have "Formula.sat \<sigma> ?V' v i \<psi> = sat' \<sigma> ?V' v i \<psi>"
    by (rule Let.IH(2)[OF psi_wty _ wty_envs'])
  then show ?case
    unfolding Formula.sat.simps sat'.simps V_eq .
next 
  case (Frz p \<phi> \<psi>) 
  obtain E' where 
    psi_wty: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>" and
    phi_wty: "S, E' \<turnstile> \<phi>" using Frz.prems(1) by cases auto
  have wtyenv: "x \<in> \<Gamma> \<sigma> i \<Longrightarrow> (case x of (p, xs) \<Rightarrow> (p, length xs) \<notin> dom V \<longrightarrow> (case S (p, length xs) of None \<Rightarrow> False | Some ts \<Rightarrow> wty_tuple ts xs))" for x i
    using Frz.prems(3) by (auto simp add: wty_envs_def wty_event_def wty_tuple_def) 
  have list_all_tab:"length xs = Formula.nfv \<phi> \<Longrightarrow>
    Formula.sat \<sigma> V xs i \<phi> \<or> sat' \<sigma> V xs i \<phi> \<Longrightarrow> list_all2 (\<lambda>t x. ty_of x = t) (tabulate E' 0 (Formula.nfv \<phi>)) xs " for xs i 
  proof -
    assume a1: "Formula.sat \<sigma> V xs i \<phi> \<or> sat' \<sigma> V xs i \<phi>"
    assume a2: "length xs = Formula.nfv \<phi>"
    have "ty_of (xs ! x) = E' x" if "x < Formula.nfv \<phi>" for x
    proof -
      have "x \<in> fv \<phi>"
        by (rule subsetD[OF Frz.hyps(1)]) (simp add: that)
      with a1 show ?thesis
        using ty_of_sat_safe[OF Frz.hyps(2) phi_wty Frz.prems(3)]
          ty_of_sat'_safe[OF Frz.hyps(2) phi_wty Frz.prems(3)]
        by blast
    qed
    with a2 show ?thesis
      by (simp add: list_all2_conv_all_nth)
  qed
  have phi_case: "sat' \<sigma> V v5 i5 \<phi> = Formula.sat \<sigma> V v5 i5 \<phi> " for v5 i5
  proof
    assume sat': "sat' \<sigma> V v5 i5 \<phi>"
    have "\<forall>y\<in>fv \<phi>. ty_of (v5 ! y) = E' y"
      using ty_of_sat'_safe[OF Frz.hyps(2) phi_wty Frz.prems(3) sat'] by blast
    with sat' show "Formula.sat \<sigma> V v5 i5 \<phi>"
      using Frz.IH(1)[OF phi_wty _ Frz.prems(3)] by blast
  next
    assume sat: "Formula.sat \<sigma> V v5 i5 \<phi>"
    have "\<forall>y\<in>fv \<phi>. ty_of (v5 ! y) = E' y"
      using ty_of_sat_safe[OF Frz.hyps(2) phi_wty Frz.prems(3) sat] by blast
    with sat show "sat' \<sigma> V v5 i5 \<phi>"
      using Frz.IH(1)[OF phi_wty _ Frz.prems(3)] by blast
  qed
  have V_eq: "V((p, Formula.nfv \<phi>) \<mapsto> (\<lambda>v j. Formula.sat \<sigma> V v i \<phi>)) = V((p, Formula.nfv \<phi>) \<mapsto> (\<lambda>v j. sat' \<sigma> V v i \<phi>))"
    using phi_case by auto
  let ?S' = "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>))"
  let ?V' = "V((p, Formula.nfv \<phi>) \<mapsto> (\<lambda>v j. sat' \<sigma> V v i \<phi>))"
  have wty_envs': "wty_envs ?S' \<sigma> ?V'"
  proof -
    {
      fix q xs j
      assume in_\<Gamma>: "(q, xs) \<in> \<Gamma> \<sigma> j" and not_V': "(q, length xs) \<notin> dom ?V'"
      then have "(q, length xs) \<noteq> (p, Formula.nfv \<phi>)" and "(q, length xs) \<notin> dom V"
        by auto
      moreover from in_\<Gamma> this(2) Frz.prems(3) have "wty_event S q xs"
        unfolding wty_envs_def by blast
      ultimately have "wty_event ?S' q xs"
        by (auto simp: wty_event_def)
    } moreover {
      fix q xs j
      assume in_V': "(q, length xs) \<in> dom ?V'" and valid: "the (?V' (q, length xs)) xs j"
      have "wty_event ?S' q xs"
      proof (cases "(q, length xs) = (p, Formula.nfv \<phi>)")
        case True
        with valid have "sat' \<sigma> V xs i \<phi>" and "length xs = Formula.nfv \<phi>"
          by auto
        then have "list_all2 (\<lambda>t x. ty_of x = t) (tabulate E' 0 (Formula.nfv \<phi>)) xs"
          using list_all_tab by blast
        with True show ?thesis
          by (auto simp: wty_event_def wty_tuple_def)
      next
        case False
        with in_V' valid have "(q, length xs) \<in> dom V" and "the (V (q, length xs)) xs j"
          by auto
        with Frz.prems(3) have "wty_event S q xs"
          unfolding wty_envs_def by blast
        with False show ?thesis
          by (auto simp: wty_event_def)
      qed
    } ultimately show ?thesis
      unfolding wty_envs_def by blast
  qed
  have "\<forall>y\<in>fv \<psi>. ty_of (v ! y) = E y"
    using Frz.prems(2) by simp
  then have "Formula.sat \<sigma> ?V' v i \<psi> = sat' \<sigma> ?V' v i \<psi>"
    by (rule Frz.IH(2)[OF psi_wty _ wty_envs'])
  then show ?case
    unfolding Formula.sat.simps sat'.simps V_eq .
next
  case (And_assign \<phi> \<psi>)
  obtain t1 t2 where eq: "\<psi> = formula.Eq t1 t2" using And_assign(2) by (auto simp add: safe_assignment_def split: formula.splits)
  obtain t where t_def: "E \<turnstile> t1 :: t \<and> E \<turnstile> t2 :: t" using  And_assign(4) by (auto simp add: eq  elim: wty_formula.cases)
  have " Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" using  t_def And_assign(4,5) by (auto simp add: eq dest: poly_value_of )
  then show ?case using And_assign by (auto elim: wty_formula.cases)
next
  case (And_constraint \<phi> \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" using And_constraint by (auto elim: wty_formula.cases)
  have psi_wty: "S, E \<turnstile> \<psi>" using And_constraint(7) by (auto elim: wty_formula.cases)
  show ?case using phi_eq And_constraint(5,8) psi_wty
    by (cases \<psi> rule: is_constraint.cases) 
      (auto simp add: undef_less_eq_sound undef_less_def less_event_data_def 
        dest: poly_value_of  elim!: wty_formula.cases)
next
  case (And_Not \<phi> \<psi>)
  have "S, E \<turnstile> \<psi>" using And_Not.prems(1) by (auto elim: wty_formula.cases)
  then show ?case using And_Not by (auto elim: wty_formula.cases)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  have "S, E \<turnstile> \<psi>'" 
    using And_Trigger.prems(1)
    by (auto elim: wty_formula.cases)
  then show ?case
    using And_Trigger wty_formula_AndD(2)[of S E \<phi>] 
      wty_formula_TriggerD(1)[of S E \<phi>' I \<psi>']
    by (auto elim: wty_formula.cases)
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  have "S, E \<turnstile> and_release_safe_bounded \<phi> \<phi>' I \<psi>'"
    using \<open>S, E \<turnstile> formula.And \<phi> (formula.Release \<phi>' I \<psi>')\<close> 
      wty_formulaD(16,17)[of _ _ \<phi>' I  \<psi>']
      wty_formulaD(4,5)[of S E \<phi>]
    by (auto simp: and_release_safe_bounded_def always_safe_bounded_def
      release_safe_bounded_def Formula.eventually_def once_def 
      intro!: wty_formula.intros)
  thus ?case
    using And_Release.IH
    unfolding sat_and_release_rewrite[OF \<open>bounded I\<close> \<open> \<not> mem I 0 \<close> ]
    unfolding sat'_and_release_rewrite[OF \<open>bounded I\<close> \<open> \<not> mem I 0 \<close> ]
    using \<open>\<forall>y\<in>fv (formula.And \<phi> (formula.Release \<phi>' I \<psi>')). ty_of (v ! y) = E y\<close>
    by (auto intro!: And_Release.IH[OF _ _ \<open>wty_envs S \<sigma> V\<close>])
next
  case (Ands l pos neg)
  have pos_IH: "\<phi> \<in> set pos \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> (\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y)  \<Longrightarrow>  wty_envs S \<sigma> V
\<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for \<phi> using Ands.IH(1)[unfolded list_all_iff] by blast
  have pos_case: "\<phi> \<in> set pos \<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi> " for \<phi> using Ands pos_IH by (auto elim: wty_formula.cases)
  have neg_IH: "\<phi> \<in> set (map remove_neg neg) \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> (\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y) \<Longrightarrow>  wty_envs S \<sigma> V
\<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for \<phi> using Ands.IH(2)[unfolded list_all_iff]
    by blast
  have neg_wty: "\<phi> \<in> set ( neg) \<Longrightarrow> S, E \<turnstile> \<phi> \<and> (\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y)" for \<phi> using Ands by (auto elim: wty_formula.cases)
  have "S, E \<turnstile> \<phi> \<and> (\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y)" if "\<phi> \<in> set (map remove_neg neg)" for \<phi>
  proof -
    from that obtain \<psi> where \<psi>: "\<psi> \<in> set neg" and \<phi>_def: "\<phi> = remove_neg \<psi>"
      by auto
    have "S, E \<turnstile> remove_neg \<psi>"
    proof (cases \<psi>)
      case (Neg \<alpha>)
      with neg_wty[OF \<psi>] show ?thesis
        by (auto dest: wty_formula_NegD)
    qed (use neg_wty[OF \<psi>] in simp_all)
    with neg_wty[OF \<psi>] show ?thesis
      unfolding \<phi>_def by simp
  qed
  then have remove_neg_case: "\<phi> \<in> set (map remove_neg neg) \<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi> " for \<phi> using Ands.prems(3) neg_IH by auto
  have remove_neg_sat: " (Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi> )= ( Formula.sat \<sigma> V v i (remove_neg \<phi>) = sat' \<sigma> V v i (remove_neg \<phi>))  " 
    for \<phi>  by (cases \<phi>)  auto
   have neg_case: "\<phi> \<in> set neg\<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for \<phi> 
    using  remove_neg_case[of "remove_neg \<phi>"]  by ( auto simp add:  remove_neg_sat[of \<phi>] )    
  then show ?case using pos_case neg_case Ands(1) by auto
next
  case (Exists t \<phi>)
  {
    fix za
    assume assm: "Formula.sat \<sigma> V (za # v) i \<phi>" 
    from Exists.prems(1) have wty: "S, case_nat t E \<turnstile> \<phi>" by cases
    have "0 \<in> fv \<phi> \<Longrightarrow> ty_of za = t" 
      using ty_of_sat_safe[where ?E="case_nat t E" and ?S=S and ?\<phi>=\<phi> and ?v="za#v" and ?V=V and ?i=i and ?\<sigma>=\<sigma> and ?x=0]  
      Exists(1,6) assm wty by auto 
    then have "\<forall>y\<in>fv \<phi>. ty_of ((za # v) ! y) = (case y of 0 \<Rightarrow> t | Suc x \<Rightarrow> E x)" using  Exists.prems(2)   by (auto simp add:  fvi_Suc split: nat.splits )
    from this  have "local.sat' \<sigma> V (za # v) i \<phi>" using Exists.IH[of S "case_nat t E" "za#v" V i] Exists(6) wty assm by auto
  } moreover {
    fix za
    assume assm: "sat' \<sigma> V (za # v) i \<phi>" 
    from Exists.prems(1) have wty: "S, case_nat t E \<turnstile> \<phi>" by cases
    have "0 \<in> fv \<phi> \<Longrightarrow> ty_of za = t" 
      using ty_of_sat'_safe[where ?E="case_nat t E" and ?S=S and ?\<phi>=\<phi> and ?v="za#v" and ?V=V and ?i=i and ?\<sigma>=\<sigma> and ?x=0]  
      Exists(1,6) assm wty by auto 
    then have "\<forall>y\<in>fv \<phi>. ty_of ((za # v) ! y) = (case y of 0 \<Rightarrow> t | Suc x \<Rightarrow> E x)" using  Exists.prems(2)   by (auto simp add:  fvi_Suc split: nat.splits )
    from this  have "Formula.sat \<sigma> V (za # v) i \<phi>" using Exists.IH[of S "case_nat t E" "za#v" V i] Exists(6) wty assm by auto
  }
  ultimately show ?case by auto 
next
  case (Agg y \<omega> tys f \<phi>) 
  have phi_wty: "S, agg_env E tys \<turnstile> \<phi>" using Agg.prems(1) by (auto elim: wty_formula.cases)
  have phi_case: "length zs = length tys \<Longrightarrow> Formula.sat \<sigma> V (zs @ v) i \<phi> =  sat' \<sigma> V (zs @ v) i \<phi>" for zs 
  proof -
    assume len_zs:"length zs = length tys"
    {
      assume sat: " Formula.sat \<sigma> V (zs @ v) i \<phi>"
      have fv_wty: "y \<in> fv \<phi> \<Longrightarrow> ty_of ((zs @ v) ! y) = agg_env E tys y" for y
        using ty_of_sat_safe Agg(4,8) sat len_zs phi_wty  by  (auto simp add: Formula.nfv_def)
      have " Formula.sat \<sigma> V (zs @ v) i \<phi> = sat' \<sigma> V (zs @ v) i \<phi> " 
        using phi_wty Agg(4,5,8) len_zs fv_wty by auto 
    } moreover{
      assume sat':"sat' \<sigma> V (zs @ v) i \<phi>"
      have fv_wty: "y \<in> fv \<phi> \<Longrightarrow> ty_of ((zs @ v) ! y) = agg_env E tys y" for y 
        using ty_of_sat'_safe Agg(4,8) sat' len_zs phi_wty by  (auto simp add: Formula.nfv_def)
      have " Formula.sat \<sigma> V (zs @ v) i \<phi> = sat' \<sigma> V (zs @ v) i \<phi> " 
        using phi_wty Agg(4,5,8) len_zs fv_wty by auto 
    }
    ultimately show ?thesis by auto
  qed
  have eval_eq: "Formula.eval_trm (zs @ v) f = eval_trm' (zs @ v) f"  if a1:"Formula.sat \<sigma> V (zs @ v) i \<phi>" and a2:"length zs = length tys" for zs
  proof -
    have fv_wty: "y\<in>fv_trm f \<Longrightarrow> ty_of ((zs @ v) ! y) = agg_env E tys y" for y 
      using ty_of_sat_safe  Agg(3,4,8) a1 a2 phi_wty by auto 
    show ?thesis using Agg.prems(1) fv_wty by (auto dest: eval_trm_sound elim: wty_formula.cases) 
  qed
  have 
 "{(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> Formula.sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
= {(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi> \<and> eval_trm' (zs @ v) f = x} \<and> Zs \<noteq> {}}"
  proof -
    have "{zs. length zs = length tys \<and> Formula.sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x}
      = {zs. length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi> \<and> eval_trm' (zs @ v) f = x}" for x
      by (rule Collect_cong) (metis phi_case eval_eq)
    then show ?thesis
      by simp
  qed
  moreover obtain agg_op d where omega_def:"\<omega> = (agg_op,d)" using Agg.prems(1) by cases auto
  moreover have eval_agg_op_case: "M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> Formula.sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
 \<Longrightarrow> eval_agg_op (agg_op,d) M = eval_agg_op' (agg_op,d) M" for M
    by (rule eval_agg_op_sound[OF _ Agg.prems(1)[unfolded omega_def] Agg.prems(3) Agg.hyps(3,4)]) 
  ultimately show ?case by auto
next
  case (Since \<phi> I \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i using Since by (auto elim: wty_formula.cases)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  using Since by (auto elim: wty_formula.cases)
  show ?case by (auto simp add: phi_eq psi_eq) 
next
  case (Not_Since \<phi> I \<psi>)
  have phi_wty: "S, E \<turnstile> \<phi>"
    by (rule wty_formula_NegD[OF wty_formula_SinceD(1)[OF Not_Since.prems(1)]])
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i
    by (rule Not_Since.IH(1)[OF phi_wty _ Not_Since.prems(3)]) (use Not_Since.prems(2) in simp)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  using Not_Since by (auto elim: wty_formula.cases)
  show ?case by (auto simp add: phi_eq psi_eq)
next
  case (Until \<phi> I \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i using Until by (auto elim: wty_formula.cases)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  using Until by (auto elim: wty_formula.cases)
  show ?case by (auto simp add: phi_eq psi_eq)
next
  case (Not_Until \<phi> I \<psi>)
  have phi_wty: "S, E \<turnstile> \<phi>"
    by (rule wty_formula_NegD[OF wty_formula_UntilD(1)[OF Not_Until.prems(1)]])
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i
    by (rule Not_Until.IH(1)[OF phi_wty _ Not_Until.prems(3)]) (use Not_Until.prems(2) in simp)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  using Not_Until by (auto elim: wty_formula.cases)
  show ?case by (auto simp add: phi_eq psi_eq) 
next
  case (Trigger_0 \<phi> I \<psi>)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  
    using Trigger_0 by (auto elim: wty_formula.cases)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i 
  proof -
    have wty_phi: "S, E \<turnstile> \<phi>"
      using Trigger_0.prems(1) by (rule wty_formula_TriggerD(1))
    have fv_phi: "\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y"
      using Trigger_0.prems(2) by simp
    from Trigger_0.IH(1) show ?thesis
    proof (elim disjE conjE case_NegE)
      assume "\<forall>v V i S E. S, E \<turnstile> \<phi> \<longrightarrow> (\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y) \<longrightarrow>
        wty_envs S \<sigma> V \<longrightarrow> Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>"
      then show ?thesis
        using wty_phi fv_phi Trigger_0.prems(3) by blast
    next
      fix \<phi>'
      assume \<phi>_def: "\<phi> = Formula.Neg \<phi>'"
        and IH': "\<forall>v V i S E. S, E \<turnstile> \<phi>' \<longrightarrow> (\<forall>y\<in>fv \<phi>'. ty_of (v ! y) = E y) \<longrightarrow>
        wty_envs S \<sigma> V \<longrightarrow> Formula.sat \<sigma> V v i \<phi>' = sat' \<sigma> V v i \<phi>'"
      have "S, E \<turnstile> \<phi>'"
        using wty_phi unfolding \<phi>_def by (rule wty_formula_NegD)
      moreover have "\<forall>y\<in>fv \<phi>'. ty_of (v ! y) = E y"
        using fv_phi unfolding \<phi>_def by simp
      ultimately have "Formula.sat \<sigma> V v i \<phi>' = sat' \<sigma> V v i \<phi>'"
        using IH' Trigger_0.prems(3) by blast
      then show ?thesis
        unfolding \<phi>_def by simp
    qed
  qed
  show ?case
    by (auto simp: phi_eq psi_eq)
next
  case (Trigger \<phi> I \<psi>)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  
    using Trigger by (auto elim: wty_formula.cases)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i 
    using Trigger
    by (clarsimp simp: case_Neg_iff)
  show ?case
    by (auto simp: phi_eq psi_eq)
next
  case (Release_0 \<phi> I \<psi>)
  have "S, E \<turnstile> release_safe_0 \<phi> I \<psi>"
    unfolding release_safe_0_def always_safe_0_def
    using \<open>S, E \<turnstile> formula.Release \<phi> I \<psi>\<close> 
      wty_formulaD(16,17)[of _ _ \<phi> I  \<psi>]
    by (auto intro!: wty_formula.intros)
  thus ?case
    unfolding sat_release_rewrite_0[OF \<open> mem I 0 \<close> \<open>bounded I\<close>]
    unfolding sat'_release_rewrite_0[OF \<open> mem I 0 \<close> \<open>bounded I\<close>]
    using \<open>\<forall>y\<in>fv (formula.Release \<phi> I \<psi>). ty_of (v ! y) = E y\<close>
    by (auto intro!: Release_0.IH[OF _ _ \<open>wty_envs S \<sigma> V\<close>])
next
  case (Release \<phi> I \<psi>)
  then show ?case 
    by clarsimp
next
  case (MatchP I r)
  from  MatchP(1) have "Regex.safe_regex fv rgx_safe_pred Past Strict r \<or> Regex.safe_regex fv rgx_safe_pred Past Lax r " by auto
  from this have atms_safe: " \<phi> \<in> regex.atms r \<Longrightarrow> safe_formula \<phi> \<or> (\<exists> \<psi>. \<phi> = Formula.Neg \<psi> \<and> safe_formula \<psi>)" for \<phi>
    using case_NegE  by (induction r) auto
  have atms_regex_atms: " \<phi> \<in> safe_atms r \<or> ( \<exists> \<psi>. \<phi> = Formula.Neg \<psi> \<and>  \<psi>\<in> safe_atms r)" if assm: " \<phi> \<in> regex.atms r" for \<phi> 
  proof (cases "safe_formula \<phi>")
    case True
    with assm show ?thesis
      unfolding safe_atms_def by auto
  next
    case False
    with atms_safe[OF assm] obtain \<psi> where \<phi>_def: "\<phi> = Formula.Neg \<psi>"
      by blast
    have "\<psi> \<in> safe_atms r"
      unfolding safe_atms_def
    proof (rule UN_I[OF assm])
      show "\<psi> \<in> (if safe_formula \<phi> then {\<phi>} else case \<phi> of Formula.Neg \<psi>' \<Rightarrow> {\<psi>'} | _ \<Rightarrow> {})"
        using False \<phi>_def by simp
    qed
    with \<phi>_def show ?thesis
      by blast
  qed
  have  " (\<phi> \<in> safe_atms r \<Longrightarrow>\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y)" for \<phi> 
  proof -
    assume "\<phi> \<in> safe_atms r"
    then obtain \<psi> where \<psi>: "\<psi> \<in> regex.atms r" and
      \<phi>_in: "\<phi> \<in> (if safe_formula \<psi> then {\<psi>} else case \<psi> of Formula.Neg \<psi>' \<Rightarrow> {\<psi>'} | _ \<Rightarrow> {})"
      unfolding safe_atms_def by blast
    have "fv \<phi> \<subseteq> fv \<psi>"
    proof (cases "safe_formula \<psi>")
      case True
      with \<phi>_in show ?thesis by simp
    next
      case False
      with atms_safe[OF \<psi>] obtain \<alpha> where \<psi>_def: "\<psi> = Formula.Neg \<alpha>"
        by blast
      from \<phi>_in have "\<phi> \<in> (case \<psi> of Formula.Neg \<psi>' \<Rightarrow> {\<psi>'} | _ \<Rightarrow> {})"
        by (simp only: if_not_P[OF False])
      with \<psi>_def show ?thesis by simp
    qed
    with \<psi> have "fv \<phi> \<subseteq> fv (Formula.MatchP I r)"
      by (auto simp: fv_regex_alt)
    with MatchP(4) show ?thesis
      by blast
  qed
  from this  MatchP have IH: "\<phi> \<in> safe_atms r \<Longrightarrow>Formula.sat \<sigma> V v i5 \<phi> = sat' \<sigma> V v i5 \<phi>" for \<phi> i5
    using match_safe_wty_nfv[of \<phi> r I S E] by auto
  have other_IH: "\<phi> \<in> regex.atms r \<Longrightarrow> Formula.sat \<sigma> V v i5 \<phi> = sat' \<sigma> V v i5 \<phi>" for \<phi> i5 
    using atms_regex_atms[of \<phi>] IH by auto 
  then show ?case  using match_cong[OF refl other_IH, where ?r=r] by auto 
next
  case (MatchF I r)
  from  MatchF(1) have "Regex.safe_regex fv rgx_safe_pred Futu Strict r 
  \<or> Regex.safe_regex fv rgx_safe_pred Futu Lax r " by auto
  from this have atms_safe: " \<phi> \<in> regex.atms r \<Longrightarrow> safe_formula \<phi> \<or> (\<exists> \<psi>. \<phi> = Formula.Neg \<psi> \<and> safe_formula \<psi>)" for \<phi>
    using case_NegE  by (induction r) auto
  have atms_regex_atms: " \<phi> \<in> safe_atms r \<or> ( \<exists> \<psi>. \<phi> = Formula.Neg \<psi> \<and>  \<psi>\<in> safe_atms r)" 
    if assm: " \<phi> \<in> regex.atms r" for \<phi> 
  proof (cases "safe_formula \<phi>")
    case True
    with assm show ?thesis
      unfolding safe_atms_def by auto
  next
    case False
    with atms_safe[OF assm] obtain \<psi> where \<phi>_def: "\<phi> = Formula.Neg \<psi>"
      by blast
    have "\<psi> \<in> safe_atms r"
      unfolding safe_atms_def
    proof (rule UN_I[OF assm])
      show "\<psi> \<in> (if safe_formula \<phi> then {\<phi>} else case \<phi> of Formula.Neg \<psi>' \<Rightarrow> {\<psi>'} | _ \<Rightarrow> {})"
        using False \<phi>_def by simp
    qed
    with \<phi>_def show ?thesis
      by blast
  qed
  have  " (\<phi> \<in> safe_atms r \<Longrightarrow>\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y)" for \<phi> 
  proof -
    assume "\<phi> \<in> safe_atms r"
    then obtain \<psi> where \<psi>: "\<psi> \<in> regex.atms r" and
      \<phi>_in: "\<phi> \<in> (if safe_formula \<psi> then {\<psi>} else case \<psi> of Formula.Neg \<psi>' \<Rightarrow> {\<psi>'} | _ \<Rightarrow> {})"
      unfolding safe_atms_def by blast
    have "fv \<phi> \<subseteq> fv \<psi>"
    proof (cases "safe_formula \<psi>")
      case True
      with \<phi>_in show ?thesis by simp
    next
      case False
      with atms_safe[OF \<psi>] obtain \<alpha> where \<psi>_def: "\<psi> = Formula.Neg \<alpha>"
        by blast
      from \<phi>_in have "\<phi> \<in> (case \<psi> of Formula.Neg \<psi>' \<Rightarrow> {\<psi>'} | _ \<Rightarrow> {})"
        by (simp only: if_not_P[OF False])
      with \<psi>_def show ?thesis by simp
    qed
    with \<psi> have "fv \<phi> \<subseteq> fv (Formula.MatchF I r)"
      by (auto simp: fv_regex_alt)
    with MatchF(4) show ?thesis
      by blast
  qed
  from this  MatchF have IH: "\<phi> \<in> safe_atms r \<Longrightarrow> Formula.sat \<sigma> V v i5 \<phi> = sat' \<sigma> V v i5 \<phi>" for \<phi> i5
    using match_safe_wty_nfv[of \<phi> r I S E] by auto
  have other_IH: "\<phi> \<in> regex.atms r \<Longrightarrow> Formula.sat \<sigma> V v i5 \<phi> = sat' \<sigma> V v i5 \<phi>" for \<phi> i5 
    using atms_regex_atms[of \<phi>] IH by auto 
  then show ?case using match_cong[OF refl other_IH, where ?r=r] by auto 
next
  case (LetPast p \<phi> \<psi>)
  obtain E' where 
    psi_wty: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>" and
    phi_wty: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E' \<turnstile> \<phi>" using LetPast.prems(1) by cases auto
  have wtyenv: "x \<in> \<Gamma> \<sigma> i \<Longrightarrow> (case x of (p, xs) \<Rightarrow> (p, length xs) \<notin> dom V \<longrightarrow> (case S (p, length xs) of None \<Rightarrow> False | Some ts \<Rightarrow> wty_tuple ts xs))" for x i
    using LetPast.prems(3) by (auto simp add: wty_envs_def wty_event_def wty_tuple_def) 
  let ?V' = "(V((p, Formula.nfv \<phi>) \<mapsto> letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)))"
  let ?V'' = "(V((p, Formula.nfv \<phi>) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)))"
  have wty_envs: "wty_envs (S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>))) \<sigma> ?V'"
    using wty_envs_update[OF LetPast(3) LetPast(9) phi_wty LetPast(2)] ty_of_sat'_safe[OF LetPast(3)] by blast
  then have wty_envs': "wty_envs (S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>))) \<sigma>
 (V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. j < i \<and> letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) w j))" for i
    unfolding wty_envs_def by(auto simp:domI) 
  have "(letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)) v i =
        (letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)) v i" for v i
  proof(induction i arbitrary: v rule:less_induct)
    case (less x)
    then show ?case
    proof -
      assume "(\<And>y v. y < x \<Longrightarrow>
          letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) v y =
          letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) v y)"
      then have eq: "(\<lambda>w j. j < x \<and> letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) w j) =
             (\<lambda>w j. j < x \<and> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) w j)"
        by auto
      {
        assume sat: "(letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)) v x"
        have *: "Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. j < x \<and> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) w j)) v x \<phi>"
          using iffD1[OF letpast_sat.simps sat] LetPast(5)[OF phi_wty _ wty_envs', of v x x]
          ty_of_sat'_safe[OF LetPast(3) phi_wty wty_envs' iffD1[OF letpast_sat.simps sat]] unfolding eq by blast
        have "letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) v x" 
          using iffD1[OF letpast_sat.simps[of "(\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)", symmetric], OF *] by auto
      } moreover {
        assume sat: "letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) v x"
        have *: "sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. j < x \<and> letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) w j)) v x \<phi>"
          using ty_of_sat_safe[OF LetPast(3) phi_wty wty_envs', of x, unfolded eq, OF iffD1[OF letpast_sat.simps sat]]
            iffD1[OF letpast_sat.simps sat] LetPast(5)[OF phi_wty _ wty_envs', of v x x]  unfolding eq by blast
        have "(letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)) v x" 
          using iffD1[OF letpast_sat.simps[of "(\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)", symmetric], OF *] by auto
      } ultimately show ?thesis by fastforce
    qed
  qed
  then have V_eq: "?V' = ?V''" by force
  have "Formula.sat \<sigma> ?V' v i \<psi> = sat' \<sigma> ?V' v i \<psi>" unfolding V_eq[symmetric] 
  proof -
    {
      assume sat: " Formula.sat \<sigma> ?V' v i \<psi>"
      have "Formula.sat \<sigma> ?V' v i \<psi> = sat' \<sigma> ?V' v i \<psi>" 
        using ty_of_sat_safe[OF LetPast(4) psi_wty wty_envs sat] LetPast(6)[OF psi_wty _ wty_envs] by blast
    } moreover {
      assume sat': "sat' \<sigma> ?V' v i \<psi>"
      have " Formula.sat \<sigma> ?V' v i \<psi> = sat' \<sigma> ?V' v i \<psi>"   
        using ty_of_sat'_safe[OF LetPast(4) psi_wty wty_envs sat'] LetPast(6)[OF psi_wty _ wty_envs] by blast
    } ultimately show ?thesis by auto
  qed
  then have "Formula.sat \<sigma> ?V'' v i \<psi> = sat' \<sigma> ?V' v i \<psi>" unfolding V_eq[symmetric] by auto
  then show ?case by(auto simp:Let_def)
next
  case (TP t)
  then show ?case by(auto simp:trm.is_Var_def trm.is_Const_def) 
next
  case (TS t)
  then show ?case by(auto simp:trm.is_Var_def trm.is_Const_def)
qed (auto elim: wty_formula.cases split: nat.splits)

lemma soundness2: (*Theorem 3.12*)
  assumes 
    "safe_formula \<phi>"
    "S,E \<turnstile> \<phi>"
    "wty_envs S \<sigma> V"
  shows "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> sat' \<sigma> V v i \<phi>" 
  using  soundness[OF assms(1-2) _ assms(3)]
    ty_of_sat_safe[OF assms(1-3), of v i]
    ty_of_sat'_safe[OF assms(1-3), of v i] 
  by auto

end
end
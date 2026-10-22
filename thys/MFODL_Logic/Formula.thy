(*<*)
theory Formula
  imports
    "MFOTL_Monitor_Devel.Event_Data"
    "MFOTL_Monitor_Devel.Preliminaries"
    Regex
    "MFOTL_Monitor_Devel.Table"
    Containers.Set_Impl
begin
(*>*)

section \<open>Metric first-order dynamic logic\<close>

subsection \<open>Container instances for enat\<close>

derive (eq) ceq enat

instantiation enat :: ccompare begin
definition ccompare_enat :: "enat comparator option" where
  "ccompare_enat = Some (\<lambda>x y. if x = y then order.Eq else if x < y then order.Lt else order.Gt)"

instance by intro_classes
    (auto simp: ccompare_enat_def split: if_splits intro!: comparator.intro)
end

instantiation enat :: card_UNIV begin
definition "finite_UNIV = Phantom(enat) False"
definition "card_UNIV = Phantom(enat) 0"
instance by intro_classes (simp_all add: finite_UNIV_enat_def card_UNIV_enat_def infinite_UNIV_char_0)
end

lemma ccomp_eq:
  assumes "ID ccompare = Some (c :: (event_data \<times> enat) comparator)"
  and "ID ccompare = Some (c' :: event_data comparator)"
  and "e1 \<noteq> e2"
  shows "c (e1, t1) (e2, t2) = c' e1 e2"
  using assms
proof -
  obtain c'' where "ID ccompare = Some (c'' :: enat comparator)"
    by (simp add: ccompare_enat_def ID_def)
  then have "c = comparator_prod c' c''"
    using assms(1-2) by(auto simp: ccompare_prod_def) (simp add: ID_def)
  moreover have "c' e1 e2 \<noteq> Eq" using ID_ccompare'[OF assms(2)] assms(3) by (auto simp:comparator.weak_eq)
  ultimately show ?thesis by (cases "c' e1 e2") auto
qed


subsection \<open>Traces and terms\<close>

context begin

qualified type_synonym name = string8
qualified type_synonym event = "(name \<times> event_data list)"
qualified type_synonym database = "event set"
qualified type_synonym prefix = "database prefix"
qualified type_synonym trace = "database trace"

qualified type_synonym env = "event_data list"

qualified datatype trm = is_Var: Var nat | is_Const: Const event_data
  | Plus trm trm | Minus trm trm | UMinus trm | Mult trm trm | Div trm trm | Mod trm trm
  | F2i trm | I2f trm

text \<open>Variables are de Bruijn indices: @{text "fvi_trm b"} returns the free variables below
  @{term b} binders, shifted down by @{term b}.\<close>

qualified primrec fvi_trm :: "nat \<Rightarrow> trm \<Rightarrow> nat set" where
  "fvi_trm b (Var x) = (if b \<le> x then {x - b} else {})"
| "fvi_trm b (Const _) = {}"
| "fvi_trm b (Plus x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Minus x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (UMinus x) = fvi_trm b x"
| "fvi_trm b (Mult x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Div x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Mod x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (F2i x) = fvi_trm b x"
| "fvi_trm b (I2f x) = fvi_trm b x"

abbreviation "fv_trm \<equiv> fvi_trm 0"

qualified primrec eval_trm :: "env \<Rightarrow> trm \<Rightarrow> event_data" where
  "eval_trm v (Var x) = v ! x"
| "eval_trm v (Const x) = x"
| "eval_trm v (Plus x y) = eval_trm v x + eval_trm v y"
| "eval_trm v (Minus x y) = eval_trm v x - eval_trm v y"
| "eval_trm v (UMinus x) = - eval_trm v x"
| "eval_trm v (Mult x y) = eval_trm v x * eval_trm v y"
| "eval_trm v (Div x y) = eval_trm v x div eval_trm v y"
| "eval_trm v (Mod x y) = eval_trm v x mod eval_trm v y"
| "eval_trm v (F2i x) = EInt (integer_of_event_data (eval_trm v x))"
| "eval_trm v (I2f x) = EFloat (double_of_event_data (eval_trm v x))"

lemma eval_trm_fv_cong: "\<forall>x\<in>fv_trm t. v ! x = v' ! x \<Longrightarrow> eval_trm v t = eval_trm v' t"
  by (induction t) simp_all


subsection \<open>Aggregation operators\<close>

datatype ty = TInt | TFloat | TString

qualified datatype agg_type = Agg_Cnt | Agg_Min | Agg_Max | Agg_Sum | Agg_Avg | Agg_Med
qualified type_synonym 't agg_op = "agg_type \<times> 't"

definition flatten_multiset :: "(event_data \<times> enat) set \<Rightarrow> event_data list" where
  "flatten_multiset M = concat (map (\<lambda>(x, c). replicate (the_enat c) x) (csorted_list_of_set M))"

lemma set_of_flatten_multiset:
  assumes "M = {(x, ecard Zs) | x Zs. Zs = f x \<and> Zs \<noteq> {}}" "finite {x. f x \<noteq> {}}"
  shows "set (flatten_multiset M) \<subseteq> fst ` M"
proof -
  have fin_M: "finite M"
    using assms(2)
    by (auto simp: assms(1))
  obtain c :: "(event_data \<times> enat) comparator" where c: "ID ccompare = Some c"
    by (auto simp: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def)
  show ?thesis
    using fin_M image_iff
    by (fastforce simp: flatten_multiset_def csorted_list_of_set_def c
        linorder.set_sorted_list_of_set[OF ID_ccompare[OF c]])
qed

lemma flatten_multiset_range:
  assumes "\<And> t m. (t, m) \<in> M \<Longrightarrow> t \<in> range f"
  and "finite M"
  shows "set (flatten_multiset M) \<subseteq> range f"
proof
  obtain c where c_def: "ID ccompare = Some (c :: (event_data \<times> enat) comparator)"
    by (simp add: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def split:if_splits option.splits)
  note c = ID_ccompare'[OF c_def]
  note c_class = comparator.linorder[OF c]
  fix x
  assume "x \<in> set (flatten_multiset M)"
  then obtain b where [simp]: "(x, b) \<in> set (csorted_list_of_set M)" by (auto simp:flatten_multiset_def)
  then have "(x, b) \<in> M" using assms(2) linorder.set_sorted_list_of_set[OF c_class] by(auto simp:csorted_list_of_set_def c_def)
  then show "x \<in> range f" using assms by auto
qed

lemma meval_in_set_aux:
  assumes "(m, enat n) \<in> s"
  and "finite s"
  and "n > 0"
  shows "m \<in> set (flatten_multiset s)"
  using assms(2)
proof -
  obtain c where c_def: "ID ccompare = Some (c :: (event_data \<times> enat) comparator)"
    by (simp add: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def split:if_splits option.splits)
  interpret linorder "le_of_comp c" "lt_of_comp c"
    using ID_ccompare[OF c_def] by auto
  show ?thesis using assms(2) assms(1) assms(3)
    by(induction s) (auto simp: set_insort_key flatten_multiset_def csorted_list_of_set_def c_def)
qed

lemma fold_flatten_multiset:
  assumes finite_m: "finite M"
  assumes commute_f: "comp_fun_commute f"
  shows "fold f (flatten_multiset M) y0  = Finite_Set.fold (\<lambda> (t, m) y. ((f t) ^^ (the_enat m)) y) y0 M"
proof -
  interpret comp_fun_commute "\<lambda> (t, m) y. ((f t) ^^ (the_enat m)) y"
    using cmp_comm[of f] commute_f
    by unfold_locales auto
  obtain c where c_def: "ID ccompare = Some (c :: (event_data \<times> enat) comparator)"
    by (simp add: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def split:if_splits option.splits)
  note c = ID_ccompare'[OF c_def]
  note c_class = comparator.linorder[OF c]
  show ?thesis
    using finite_m
  proof(induction M)
    case empty
    then show ?case
      using linorder.sorted_list_of_set_empty[OF c_class]
      by (auto simp add:flatten_multiset_def csorted_list_of_set_def c_def)
  next
    case (insert x F)
    obtain t m where x_def: "x = (t, m)"
      by (cases x) auto
    define xs where "xs = (linorder.sorted_list_of_set (le_of_comp c) F)"
    have "fold f (concat (map (\<lambda>(x, c). replicate (the_enat c) x) (linorder.insort_key (le_of_comp c) (\<lambda>x. x) (t, m) xs))) y0
       = (f t ^^ the_enat m) (fold f (concat (map (\<lambda>(x, c). replicate (the_enat c) x) xs)) y0)"
    proof(induction xs arbitrary: y0)
      case Nil
      then show ?case using linorder.insort_key.simps[OF c_class, of "(\<lambda>x. x)"] by (auto simp:xs_def)
    next
      case (Cons a as)
      then show ?case
        using linorder.insort_key.simps[OF c_class, of "(\<lambda>x. x)"] cmp_comm[of f "the_enat m"]
        by (auto simp:xs_def commute_f comp_fun_commute.comp_fun_commute fn_comm_power' fold_commute_apply)
    qed
    then show ?case
      using x_def insert linorder.sorted_list_of_set_insert[OF c_class]
      by (simp add:flatten_multiset_def csorted_list_of_set_def c_def xs_def)
  qed
qed

lemma foldl_flatten_multiset:
  assumes finite_m: "finite M"
  assumes commute_f: "comp_fun_commute f"
  and comm_f: "\<And>x y. f x y = f y x"
  shows "foldl f y0 (flatten_multiset M)  = Finite_Set.fold (\<lambda> (t, m) y. ((f t) ^^ (the_enat m)) y) y0 M"
  using assms fold_flatten_multiset fold_eq by (simp add: fold_eq fold_flatten_multiset)

lemma length_flatten_multiset:
  assumes "finite M"
  shows "length (flatten_multiset M) = Finite_Set.fold (\<lambda> (t, m) y. y + (the_enat m)) 0 M"
  using length_fold[of "flatten_multiset M"] fold_flatten_multiset[of M "(\<lambda>_ n. n + 1)" 0]
  by (simp add: fold_flatten_multiset assms comp_fun_commute.intro) (meson add.commute)

definition valid_finite_mset where
  "valid_finite_mset X = (finite X \<and> (\<forall>k x y. x \<noteq> y \<and> (k, x) \<in> X \<longrightarrow> (k, y) \<notin> X) \<and>
                              (\<forall>k x. (k, x) \<in> X \<longrightarrow> x \<noteq> \<infinity> \<and> x \<noteq> 0))"

lemma mset_prop_unfold:
  assumes "ID ccompare = Some (c :: (event_data \<times> enat) comparator)"
  and "\<forall>t m. (t, m) \<in> F \<longrightarrow> (\<exists>k. f t = Some k)"
  and "valid_finite_mset F"
  shows "\<forall>t. t \<in> set (flatten_multiset F) \<longrightarrow> (\<exists>k. f t = Some k)"
proof (rule allI, rule impI)
  interpret linorder "le_of_comp c" "lt_of_comp c"
    using ID_ccompare[OF assms(1)] by simp
  fix t
  assume "t \<in> set (flatten_multiset F)"
  moreover have "finite F" using assms(3) by(simp add:valid_finite_mset_def)
  ultimately obtain t' m where "(t', m) \<in> F" "t = t'"
    by(simp add:flatten_multiset_def csorted_list_of_set_def assms(1)) blast
  then show "\<exists>k. f t = Some k" using assms(2) by auto
qed

lemma mset_multi_prop_unfold:
  assumes "ID ccompare = Some (c :: (event_data \<times> enat) comparator)"
  and "ID ccompare = Some (c' :: event_data comparator)"
  and "\<forall>t1 m1 t2 m2. (t1, m1) \<in> F \<and> (t2, m2) \<in> F \<longrightarrow> c' t1 t2 = comp_of_ords (\<le>) (<) (the (f t1)) (the (f t2))"
  and "valid_finite_mset F"
  shows "\<forall>e1 e2. e1 \<in> set (flatten_multiset F) \<and> e2 \<in> set (flatten_multiset F) \<longrightarrow> c' e1 e2 = comp_of_ords (\<le>) (<) (the (f e1)) (the (f e2))"
proof (rule allI, rule allI, rule impI)
  interpret linorder "le_of_comp c" "lt_of_comp c"
    using ID_ccompare[OF assms(1)] by simp
  fix e1 e2
  assume "e1 \<in> set (flatten_multiset F) \<and> e2 \<in> set (flatten_multiset F)"
  moreover have "finite F" using assms(4) by(simp add:valid_finite_mset_def)
  ultimately obtain t1 m1 t2 m2 where "(t1, m1) \<in> F" "(t2, m2) \<in> F" "t1 = e1" "t2 = e2"
    by(simp add:flatten_multiset_def csorted_list_of_set_def assms(1)) blast
  then show "c' e1 e2 = comp_of_ords (\<le>) (<) (the (f e1)) (the (f e2))" using assms(3) by blast
qed

lemma set_insert_flatten_mset:
  assumes "ID ccompare = Some (c :: (event_data \<times> enat) comparator)"
  and "valid_finite_mset (Set.insert (t, m) F)"
  and "(t, m) \<notin> F"
  shows "set (flatten_multiset (Set.insert (t, m) F)) = Set.insert t (set (flatten_multiset (F)))"
proof -
  have "finite F" "m > 0" "m \<noteq> \<infinity>" using assms(2)
    unfolding valid_finite_mset_def by (meson finite_insert gr_zeroI insertI1)+
  moreover have "the_enat m > 0" using calculation(2-3) gr0I zero_enat_def by force
  ultimately show ?thesis using assms(1) assms(3) linorder.sorted_list_of_set_insert[OF ID_ccompare[OF assms(1)]]
  linorder.set_insort_key[OF ID_ccompare[OF assms(1)], of "\<lambda>x. x"] by(simp add:flatten_multiset_def csorted_list_of_set_def)
qed

definition finite_multiset :: "(event_data \<times> enat) set \<Rightarrow> bool" where
"finite_multiset M = (finite M \<and> \<not>(\<exists>s. (s,\<infinity>) \<in> M ))"

definition aggreg_default_value :: "agg_type \<Rightarrow> ty \<Rightarrow> event_data" where
  "aggreg_default_value op t = (case (op, t) of
    (Agg_Min, TFloat) \<Rightarrow> EFloat Code_Double.infinity |
    (Agg_Max, TFloat) \<Rightarrow> EFloat (-Code_Double.infinity) |
    (_, TFloat) \<Rightarrow> EFloat 0 |
    (_, TInt) \<Rightarrow> EInt 0 |
    (_, TString) \<Rightarrow> EString empty_string)"

fun eval_agg_op :: "ty agg_op \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> event_data" where
  "eval_agg_op (Agg_Cnt, ty) M = (let y0 = aggreg_default_value Agg_Cnt ty in
    case (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (xs,_) \<Rightarrow> EInt (integer_of_int (length xs)))"
| "eval_agg_op (Agg_Min, ty) M = (let y0 = aggreg_default_value Agg_Min ty in
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl min x xs)"
| "eval_agg_op (Agg_Max, ty) M = (let y0 = aggreg_default_value Agg_Max ty in 
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl max x xs)"
| "eval_agg_op (agg_type.Agg_Sum, ty) M = (let y0 = aggreg_default_value Agg_Sum ty in
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl (+) x xs)"
| "eval_agg_op (Agg_Avg, ty) M =(let y0 = aggreg_default_value Agg_Avg ty in 
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x#xs,_) \<Rightarrow> EFloat ( double_of_event_data_agg (foldl plus x xs) / double_of_int (length (x#xs))))"
| "eval_agg_op (Agg_Med, ty) M =(let y0 = aggreg_default_value Agg_Med ty in
    case (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (xs,_) \<Rightarrow> EFloat (let u = length xs;  u' = u div 2 in
          if even u then
            (double_of_event_data_agg (xs ! (u'-1)) + double_of_event_data_agg (xs ! u')) / double_of_int 2
          else double_of_event_data_agg (xs ! u')))"

subsection \<open>Formulas\<close>

text \<open>In @{text "Agg y \<omega> tys t \<phi>"}, the variables bound by @{text tys} range over the
  satisfying valuations of @{text \<phi>}; @{text y} holds the aggregate @{text \<omega>} of @{text t}.\<close>

qualified datatype (discs_sels) 't formula = Pred name "trm list"
  | Let name "'t formula" "'t formula"
  | Frz name "'t formula" "'t formula"
  | LetPast name "'t formula" "'t formula"
  | Eq trm trm | Less trm trm | LessEq trm trm
  | Neg "'t formula" | Or "'t formula" "'t formula" | And "'t formula" "'t formula" 
  | Ands "'t formula list" | Exists 't "'t formula"
  | Agg nat "'t agg_op" "'t list" trm "'t formula"
  | Prev \<I> "'t formula" | Next \<I> "'t formula"
  | Since "'t formula" \<I> "'t formula" | Until "'t formula" \<I> "'t formula"
  | Trigger "'t formula" \<I> "'t formula" | Release "'t formula" \<I> "'t formula"
  | MatchF \<I> "'t formula Regex.regex" | MatchP \<I> "'t formula Regex.regex"
  | TP trm | TS trm


qualified abbreviation "frwd_diam r I \<equiv> MatchF I r"
qualified abbreviation "bwrd_diam r I \<equiv> MatchP I r"

lemma case_Neg_iff: "(case \<gamma> of Neg x \<Rightarrow> P x | _ \<Rightarrow> False) 
    \<longleftrightarrow> (\<exists>\<gamma>'. \<gamma> = Neg \<gamma>' \<and> P \<gamma>')" 
  by (cases \<gamma>) auto

lemma case_NegE: "(case \<phi> of Neg \<phi>' \<Rightarrow> P \<phi>' | _ \<Rightarrow> False) 
  \<Longrightarrow> (\<And>\<phi>'. \<phi> = Neg \<phi>' \<Longrightarrow> P \<phi>' \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (simp add: case_Neg_iff)
    blast

lemma not_Neg_cases:
  "(\<forall>\<psi>. \<phi> \<noteq> Formula.Neg \<psi>) \<Longrightarrow> (case \<phi> of formula.Neg \<psi> \<Rightarrow> f \<psi> | _ \<Rightarrow> x) = x"
  by (cases \<phi>) auto

lemma case_release_iff: 
  "(case \<phi> of Release \<phi>' I \<psi>' \<Rightarrow> True | _ \<Rightarrow> False) \<longleftrightarrow> (\<exists>\<phi>' I \<psi>'. \<phi> = Release \<phi>' I \<psi>')"
  by (auto split: formula.splits)

lemma case_trigger_iff: 
  "(case \<phi> of Trigger \<phi>' I \<psi>' \<Rightarrow> True | _ \<Rightarrow> False) \<longleftrightarrow> (\<exists>\<phi>' I \<psi>'. \<phi> = Trigger \<phi>' I \<psi>')"
  by (auto split: formula.splits)

lemma case_Neg_in_iff: "x \<in> (case y of formula.Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {}) \<longleftrightarrow> y = formula.Neg x"
  by (cases y) auto

qualified definition "FF = Eq (Const (EInt 0)) (Const (EInt 1))"
qualified definition "TT \<equiv> Eq (Const (EInt 0)) (Const (EInt 0))"

subsection \<open>Free variables\<close>

qualified fun fvi :: "nat \<Rightarrow> 't formula \<Rightarrow> nat set" where
  "fvi b (Pred r ts) = (\<Union>t\<in>set ts. fvi_trm b t)"
| "fvi b (Let p \<phi> \<psi>) = fvi b \<psi>"
| "fvi b (Frz p \<phi> \<psi>) = fvi b \<psi>"
| "fvi b (LetPast p \<phi> \<psi>) = fvi b \<psi>"
| "fvi b (Eq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Less t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (LessEq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Neg \<phi>) = fvi b \<phi>"
| "fvi b (Or \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (And \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Ands \<phi>s) = (let xs = map (fvi b) \<phi>s in \<Union>x\<in>set xs. x)"
| "fvi b (Exists t \<phi>) = fvi (Suc b) \<phi>"
| "fvi b (Agg y \<omega> tys f \<phi>) = fvi (b + length tys) \<phi> \<union> fvi_trm (b + length tys) f \<union> (if b \<le> y then {y - b} else {})"
| "fvi b (Prev I \<phi>) = fvi b \<phi>"
| "fvi b (Next I \<phi>) = fvi b \<phi>"
| "fvi b (Since \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Until \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Trigger \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Release \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (MatchF I r) = Regex.fv_regex (fvi b) r"
| "fvi b (MatchP I r) = Regex.fv_regex (fvi b) r"
| "fvi b (TP t) = fvi_trm b t"
| "fvi b (TS t) = fvi_trm b t"

abbreviation "fv \<equiv> fvi 0"
abbreviation "fv_regex \<equiv> Regex.fv_regex fv"

lemma fv_abbrevs[simp]: "fv TT = {}" "fv FF = {}"
  unfolding TT_def FF_def by auto

lemma fvi_abbrevs[simp]: "\<forall>b. fvi b TT = {}" "\<forall>b. fvi b FF = {}"
  unfolding TT_def FF_def by auto

lemma fv_subset_Ands: "\<phi> \<in> set \<phi>s \<Longrightarrow> fv \<phi> \<subseteq> fv (Ands \<phi>s)"
  by auto

lemma finite_fvi_trm[simp]: "finite (fvi_trm b t)"
  by (induction t) simp_all

lemma finite_fvi[simp]: "finite (fvi b \<phi>)"
  by (induction \<phi> arbitrary: b) simp_all

lemma fvi_trm_plus: "x \<in> fvi_trm (b + c) t \<longleftrightarrow> x + c \<in> fvi_trm b t"
  by (induction t) auto

lemma fvi_trm_minus: "x \<in> fvi_trm b t \<and> x \<ge> c \<longrightarrow> x-c \<in> fvi_trm (b+c) t"
  by (induction t) auto

lemma fvi_trm_iff_fv_trm: "x \<in> fvi_trm b t \<longleftrightarrow> x + b \<in> fv_trm t"
  using fvi_trm_plus[where b=0 and c=b] by simp_all

lemma fvi_plus: "x \<in> fvi (b + c) \<phi> \<longleftrightarrow> x + c \<in> fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: formula.induct)
  case (Exists \<phi>)
  then show ?case by force
next
  case (Agg y \<omega> tys f \<phi>)
  let ?b' = "length tys"
  have *: "b + c + ?b' = b + ?b' + c" by simp
  from Agg show ?case by (force simp: * fvi_trm_plus)
qed (auto simp add: fvi_trm_plus fv_regex_commute[where g = "\<lambda>x. x + c"])

lemma fvi_minus: "x \<in> fvi b \<phi> \<and> x \<ge> c \<longrightarrow> x - c \<in> fvi (b+c) \<phi>"
  by (simp add: fvi_plus)

lemma fvi_Suc: "x \<in> fvi (Suc b) \<phi> \<longleftrightarrow> Suc x \<in> fvi b \<phi>"
  using fvi_plus[where c=1] by simp

lemma fvi_plus_bound:
  assumes "\<forall>i\<in>fvi (b + c) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < c + n"
proof
  fix i
  assume "i \<in> fvi b \<phi>"
  show "i < c + n"
  proof (cases "i < c")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain i' where "i = i' + c"
      using nat_le_iff_add by (auto simp: not_less)
    with assms \<open>i \<in> fvi b \<phi>\<close> show ?thesis by (simp add: fvi_plus)
  qed
qed

lemma fvi_Suc_bound:
  assumes "\<forall>i\<in>fvi (Suc b) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < Suc n"
  using assms fvi_plus_bound[where c=1] by simp

lemma fvi_iff_fv: "x \<in> fvi b \<phi> \<longleftrightarrow> x + b \<in> fv \<phi>"
  using fvi_plus[where b=0 and c=b] by simp_all

subsection \<open>Free variables as column lists\<close>

text \<open>The order is MonPoly's: by first occurrence, except that Since, Until, Trigger and
  Release list their right operand first and an aggregation lists its result variable first.\<close>

qualified primrec fvi_trm_list :: "nat \<Rightarrow> trm \<Rightarrow> nat list" where
  "fvi_trm_list b (Var x) = (if b \<le> x then [x - b] else [])"
| "fvi_trm_list b (Const _) = []"
| "fvi_trm_list b (Plus x y) = cols_union (fvi_trm_list b x) (fvi_trm_list b y)"
| "fvi_trm_list b (Minus x y) = cols_union (fvi_trm_list b x) (fvi_trm_list b y)"
| "fvi_trm_list b (UMinus x) = fvi_trm_list b x"
| "fvi_trm_list b (Mult x y) = cols_union (fvi_trm_list b x) (fvi_trm_list b y)"
| "fvi_trm_list b (Div x y) = cols_union (fvi_trm_list b x) (fvi_trm_list b y)"
| "fvi_trm_list b (Mod x y) = cols_union (fvi_trm_list b x) (fvi_trm_list b y)"
| "fvi_trm_list b (F2i x) = fvi_trm_list b x"
| "fvi_trm_list b (I2f x) = fvi_trm_list b x"

abbreviation "fv_trm_list \<equiv> fvi_trm_list 0"

qualified primrec fv_regex_list :: "('a \<Rightarrow> nat list) \<Rightarrow> 'a Regex.regex \<Rightarrow> nat list" where
  "fv_regex_list f (Regex.Skip n) = []"
| "fv_regex_list f (Regex.Test \<phi>) = f \<phi>"
| "fv_regex_list f (Regex.Plus r s) = cols_union (fv_regex_list f r) (fv_regex_list f s)"
| "fv_regex_list f (Regex.Times r s) = cols_union (fv_regex_list f r) (fv_regex_list f s)"
| "fv_regex_list f (Regex.Star r) = fv_regex_list f r"

lemma fv_regex_list_cong[fundef_cong]:
  "r = r' \<Longrightarrow> (\<And>z. z \<in> Regex.atms r \<Longrightarrow> f z = f' z) \<Longrightarrow> fv_regex_list f r = fv_regex_list f' r'"
  by (induct r arbitrary: r') auto

qualified fun fvi_list :: "nat \<Rightarrow> 't formula \<Rightarrow> nat list" where
  "fvi_list b (Pred r ts) = fold (\<lambda>t cs. cols_union cs (fvi_trm_list b t)) ts []"
| "fvi_list b (Let p \<phi> \<psi>) = fvi_list b \<psi>"
| "fvi_list b (Frz p \<phi> \<psi>) = fvi_list b \<psi>"
| "fvi_list b (LetPast p \<phi> \<psi>) = fvi_list b \<psi>"
| "fvi_list b (Eq t1 t2) = cols_union (fvi_trm_list b t1) (fvi_trm_list b t2)"
| "fvi_list b (Less t1 t2) = cols_union (fvi_trm_list b t1) (fvi_trm_list b t2)"
| "fvi_list b (LessEq t1 t2) = cols_union (fvi_trm_list b t1) (fvi_trm_list b t2)"
| "fvi_list b (Neg \<phi>) = fvi_list b \<phi>"
| "fvi_list b (Or \<phi> \<psi>) = cols_union (fvi_list b \<phi>) (fvi_list b \<psi>)"
| "fvi_list b (And \<phi> \<psi>) = cols_union (fvi_list b \<phi>) (fvi_list b \<psi>)"
| "fvi_list b (Ands \<phi>s) = fold (\<lambda>\<phi> cs. cols_union cs (fvi_list b \<phi>)) \<phi>s []"
| "fvi_list b (Exists t \<phi>) = fvi_list (Suc b) \<phi>"
| "fvi_list b (Agg y \<omega> tys f \<phi>) = cols_union (if b \<le> y then [y - b] else [])
    (cols_union (fvi_list (b + length tys) \<phi>) (fvi_trm_list (b + length tys) f))"
| "fvi_list b (Prev I \<phi>) = fvi_list b \<phi>"
| "fvi_list b (Next I \<phi>) = fvi_list b \<phi>"
| "fvi_list b (Since \<phi> I \<psi>) = cols_union (fvi_list b \<psi>) (fvi_list b \<phi>)"
| "fvi_list b (Until \<phi> I \<psi>) = cols_union (fvi_list b \<psi>) (fvi_list b \<phi>)"
| "fvi_list b (Trigger \<phi> I \<psi>) = cols_union (fvi_list b \<psi>) (fvi_list b \<phi>)"
| "fvi_list b (Release \<phi> I \<psi>) = cols_union (fvi_list b \<psi>) (fvi_list b \<phi>)"
| "fvi_list b (MatchF I r) = fv_regex_list (fvi_list b) r"
| "fvi_list b (MatchP I r) = fv_regex_list (fvi_list b) r"
| "fvi_list b (TP t) = fvi_trm_list b t"
| "fvi_list b (TS t) = fvi_trm_list b t"

abbreviation "fv_list \<equiv> fvi_list 0"

lemma set_fvi_trm_list[simp]: "set (fvi_trm_list b t) = fvi_trm b t"
  by (induction t) simp_all

lemma distinct_fvi_trm_list[simp]: "distinct (fvi_trm_list b t)"
  by (induction t) simp_all

lemma set_fv_regex_list[simp]: "set (fv_regex_list f r) = Regex.fv_regex (\<lambda>\<phi>. set (f \<phi>)) r"
  by (induction r) simp_all

lemma distinct_fv_regex_list:
  "(\<And>z. z \<in> Regex.atms r \<Longrightarrow> distinct (f z)) \<Longrightarrow> distinct (fv_regex_list f r)"
  by (induction r) simp_all

lemma set_fvi_list[simp]: "set (fvi_list b \<phi>) = fvi b \<phi>"
  by (induction b \<phi> rule: fvi_list.induct)
    (auto simp: set_fold_cols_union fv_regex_alt)

lemma distinct_fvi_list[simp]: "distinct (fvi_list b \<phi>)"
  by (induction b \<phi> rule: fvi_list.induct)
    (simp_all add: distinct_fold_cols_union distinct_fv_regex_list)

abbreviation regex_cols where
  "regex_cols r \<equiv> Formula.fv_regex_list Formula.fv_list r"

lemma set_regex_cols[simp]: "set (regex_cols r) = Formula.fv_regex r"
  by simp

lemma distinct_regex_cols[simp]: "distinct (regex_cols r)"
  by (simp add: distinct_fv_regex_list)

lemma fvi_trm_list_Suc: "fvi_trm_list (Suc b) t = ex_cols (fvi_trm_list b t)"
  by (induction t) (auto simp: ex_cols_Cons ex_cols_cols_union)

lemma ex_cols_fv_regex_list:
  "(\<And>z. z \<in> Regex.atms r \<Longrightarrow> ex_cols (f z) = g z) \<Longrightarrow> ex_cols (fv_regex_list f r) = fv_regex_list g r"
  by (induction r) (simp_all add: ex_cols_cols_union)

lemma fvi_list_Suc: "fvi_list (Suc b) \<phi> = ex_cols (fvi_list b \<phi>)"
  by (induction b \<phi> rule: fvi_list.induct)
    (auto simp: ex_cols_Cons ex_cols_cols_union ex_cols_fold_cols_union fvi_trm_list_Suc
      ex_cols_fv_regex_list cong: fold_cong fv_regex_list_cong)

lemma fvi_list_plus: "fvi_list (b + k) \<phi> = shift_cols k (fvi_list b \<phi>)"
  by (induction k) (simp_all add: fvi_list_Suc shift_cols_Suc)

subsection \<open>Number of free variables\<close>

qualified definition nfv :: "'t formula \<Rightarrow> nat" where
  "nfv \<phi> = Max (insert 0 (Suc ` fv \<phi>))"

qualified abbreviation nfv_regex where
  "nfv_regex \<equiv> Regex.nfv_regex fv"

qualified definition envs :: "'t formula \<Rightarrow> env set" where
  "envs \<phi> = {v. length v = nfv \<phi>}"

lemma nfv_simps[simp]:
  "nfv (Let p \<phi> \<psi>) = nfv \<psi>"
  "nfv (Frz p \<phi> \<psi>) = nfv \<psi>"
  "nfv (LetPast p \<phi> \<psi>) = nfv \<psi>"
  "nfv (Neg \<phi>) = nfv \<phi>"
  "nfv (Or \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (And \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Prev I \<phi>) = nfv \<phi>"
  "nfv (Next I \<phi>) = nfv \<phi>"
  "nfv (Since \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Until \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (MatchP I r) = Regex.nfv_regex fv r"
  "nfv (MatchF I r) = Regex.nfv_regex fv r"
  "nfv_regex (Regex.Skip n) = 0"
  "nfv_regex (Regex.Test \<phi>) = Max (insert 0 (Suc ` fv \<phi>))"
  "nfv_regex (Regex.Plus r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Regex.Times r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Regex.Star r) = nfv_regex r"
  unfolding nfv_def Regex.nfv_regex_def by (simp_all add: image_Un Max_Un[symmetric])

lemma nfv_Ands[simp]: "nfv (Ands l) = Max (insert 0 (nfv ` set l))"
proof (induction l)
  case Nil
  then show ?case unfolding nfv_def by simp
next
  case (Cons a l)
  have "fv (Ands (a # l)) = fv a \<union> fv (Ands l)" by simp
  then have "nfv (Ands (a # l)) = max (nfv a) (nfv (Ands l))"
    unfolding nfv_def
    by (auto simp: image_Un Max.union[symmetric])
  with Cons.IH show ?case
    by (cases l) auto
qed

lemma fvi_less_nfv: "\<forall>i\<in>fv \<phi>. i < nfv \<phi>"
  unfolding nfv_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

lemma set_fv_list_nfv:
  assumes "{0..<m} \<subseteq> fv \<phi>" "m = Formula.nfv \<phi>"
  shows "set (Formula.fv_list \<phi>) = set [0..<m]"
  using assms fvi_less_nfv[of \<phi>] by auto

lemma fvi_less_nfv_regex: "\<forall>i\<in>fv_regex \<phi>. i < nfv_regex \<phi>"
  unfolding Regex.nfv_regex_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

subsection \<open>Predicate occurrence\<close>

fun contains_pred :: "name \<times> nat \<Rightarrow> 't formula \<Rightarrow> bool" where
   "contains_pred p (Eq t1 t2) = False"
|  "contains_pred p (Less t1 t2) = False"
|  "contains_pred p (LessEq t1 t2) = False"
|  "contains_pred p (Pred e ts) = (p = (e, length ts))"
|  "contains_pred p (Let e \<phi> \<psi>) = ((contains_pred p \<phi> \<and> contains_pred (e, nfv \<phi>) \<psi>) \<or> (p \<noteq> (e, nfv \<phi>) \<and> contains_pred p \<psi>))"
|  "contains_pred p (Frz e \<phi> \<psi>) = ((contains_pred p \<phi> \<and> contains_pred (e, nfv \<phi>) \<psi>) \<or> (p \<noteq> (e, nfv \<phi>) \<and> contains_pred p \<psi>))"
|  "contains_pred p (LetPast e \<phi> \<psi>) =  (p \<noteq> (e, nfv \<phi>) \<and> ((contains_pred p \<phi> \<and> contains_pred (e, nfv \<phi>) \<psi>) \<or> contains_pred p \<psi>))"
|  "contains_pred p (Neg \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Or \<phi> \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (And \<phi> \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (Ands l) = (\<exists>\<phi>\<in>set l. contains_pred p \<phi>)"
|  "contains_pred p (Exists t \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Agg y \<omega> tys f \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Prev I \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Next I \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Since \<phi> I \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (Until \<phi> I \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (Trigger \<phi> I \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (Release \<phi> I \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (MatchP I r) = (\<exists>\<phi>\<in>Regex.atms r. contains_pred p \<phi>)"
|  "contains_pred p (MatchF I r) =  (\<exists>\<phi>\<in>Regex.atms r. contains_pred p \<phi>)"
|  "contains_pred p (TP t) = False"
|  "contains_pred p (TS t) = False"

lemma TT_no_pred [simp]: 
  "\<not> contains_pred p Formula.TT"
  by (simp add: Formula.TT_def)


subsection \<open>Semantics\<close>

declare conj_cong[fundef_cong]
fun letpast_sat where
  "letpast_sat sat v (i::nat) = sat (\<lambda>w j. j < i \<and> letpast_sat sat w j) v i"
declare letpast_sat.simps[simp del]

lemma V_subst_letpast_sat:
  "(\<And>X v j. j \<le> i \<Longrightarrow> f X v j = g X v j) \<Longrightarrow>
  Formula.letpast_sat f v i = Formula.letpast_sat g v i"
  by (induct f v i rule: letpast_sat.induct) (subst (1 2) letpast_sat.simps, auto cong: conj_cong)

qualified fun sat :: "trace \<Rightarrow> (name \<times> nat \<rightharpoonup> env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> ty formula \<Rightarrow> bool" where
  "sat \<sigma> V v i (Pred r ts) = (case V (r, length ts) of
       None \<Rightarrow> (r, map (eval_trm v) ts) \<in> \<Gamma> \<sigma> i
     | Some X \<Rightarrow> X (map (eval_trm v) ts) i)"
| "sat \<sigma> V v i (Let p \<phi> \<psi>) = sat \<sigma> (V((p, nfv \<phi>) \<mapsto> \<lambda>w j. sat \<sigma> V w j \<phi>)) v i \<psi>"
| "sat \<sigma> V v i (Frz p \<phi> \<psi>) = sat \<sigma> (V((p, nfv \<phi>) \<mapsto> \<lambda>w j. sat \<sigma> V w i \<phi>)) v i \<psi>"
| "sat \<sigma> V v i (LetPast p \<phi> \<psi>) =
    (let pn = (p, nfv \<phi>) in
    sat \<sigma> (V(pn \<mapsto> letpast_sat (\<lambda>X u k. sat \<sigma> (V(pn \<mapsto> X)) u k \<phi>))) v i \<psi>)"
| "sat \<sigma> V v i (Eq t1 t2) = (eval_trm v t1 = eval_trm v t2)"
| "sat \<sigma> V v i (Less t1 t2) = (eval_trm v t1 < eval_trm v t2)"
| "sat \<sigma> V v i (LessEq t1 t2) = (eval_trm v t1 \<le> eval_trm v t2)"
| "sat \<sigma> V v i (Neg \<phi>) = (\<not> sat \<sigma> V v i \<phi>)"
| "sat \<sigma> V v i (Or \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<or> sat \<sigma> V v i \<psi>)"
| "sat \<sigma> V v i (And \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v i \<psi>)"
| "sat \<sigma> V v i (Ands l) = (\<forall>\<phi> \<in> set l. sat \<sigma> V v i \<phi>)"
| "sat \<sigma> V v i (Exists t \<phi>) = (\<exists>z. sat \<sigma> V (z # v) i \<phi>)"
| "sat \<sigma> V v i (Agg y \<omega> tys f \<phi>) =
    (let M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> sat \<sigma> V (zs @ v) i \<phi> \<and> eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
    in (M = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<length tys}) \<and> v ! y = eval_agg_op \<omega> M)"
| "sat \<sigma> V v i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>)"
| "sat \<sigma> V v i (Next I \<phi>) = (mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) \<and> sat \<sigma> V v (Suc i) \<phi>)"
| "sat \<sigma> V v i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (Trigger \<phi> I \<psi>) = (\<forall>j\<le>i. (mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>)))"
| "sat \<sigma> V v i (Release \<phi> I \<psi>) = (\<forall>j\<ge>i. (mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)))"
| "sat \<sigma> V v i (MatchP I r) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Regex.match (sat \<sigma> V v) r j i)"
| "sat \<sigma> V v i (MatchF I r) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Regex.match (sat \<sigma> V v) r i j)"
| "sat \<sigma> V v i (TP t) = (eval_trm v t = EInt (integer_of_nat i))"
| "sat \<sigma> V v i (TS t) = (eval_trm v t = EInt (integer_of_nat (\<tau> \<sigma> i)))"

lemma sat_abbrevs[simp]:
  "sat \<sigma> V v i TT" "\<not> sat \<sigma> V v i FF"
  unfolding TT_def FF_def by auto

lemma sat_MatchP_rec: "sat \<sigma> V v i (MatchP I r) \<longleftrightarrow> memL I 0 \<and> Regex.eps (sat \<sigma> V v) i r \<or>
  i > 0 \<and> memR I (\<Delta> \<sigma> i) \<and> (\<exists>s \<in> Regex.rpd (sat \<sigma> V v) i r. sat \<sigma> V v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" and "Regex.match (sat \<sigma> V v) r j i" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "j < i")
    case True
    with \<open>Regex.match (sat \<sigma> V v) r j i\<close> rpd_match[of j i "sat \<sigma> V v" r]
    obtain s where "s \<in> Regex.rpd (sat \<sigma> V v) i r" "Regex.match (sat \<sigma> V v) s j (i - 1)" by auto
    with True j have ?R2
      by (auto simp: diff_le_mono2 intro!: exI[of _ j])
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "memR I (\<Delta> \<sigma> i)"
  moreover
  fix s
  assume [simp]: "s \<in> Regex.rpd (sat \<sigma> V v) i r" and "sat \<sigma> V v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s)" "i > 0"
  then obtain j where "j < i" "Regex.match (sat \<sigma> V v) s j (i - 1)"
    "mem (subtract (\<Delta> \<sigma> i) I) (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j)" by (auto simp: gr0_conv_Suc less_Suc_eq_le)
  ultimately show ?L
    by (auto simp: rpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_MatchP_point: "sat \<sigma> V v i (MatchP I r) \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<Longrightarrow> sat \<sigma> V v i (MatchP (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) r) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_MatchP_pointD: "sat \<sigma> V v i (MatchP (point t) r) \<Longrightarrow> mem I t \<Longrightarrow> sat \<sigma> V v i (MatchP I r)"
  by auto

lemma sat_fv_cong: "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>"
proof (induct \<phi> arbitrary: V v v' i rule: formula.induct)
  case (Pred n ts)
  show ?case by (simp cong: map_cong eval_trm_fv_cong[OF Pred[simplified, THEN bspec]] split: option.splits)
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by auto
next
  case (Eq x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (Less x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (LessEq x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (Ands l)
  have "\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>"
  proof -
    fix \<phi> assume "\<phi> \<in> set l"
    then have "fv \<phi> \<subseteq> fv (Ands l)" using fv_subset_Ands by blast
    then have "\<forall>x\<in>fv \<phi>. v!x = v'!x" using Ands.prems by blast
    then show "sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>" using Ands.hyps \<open>\<phi> \<in> set l\<close> by blast
  qed
  then show ?case using sat.simps(11) by blast
next
  case (Exists t \<phi>)
  then show ?case unfolding sat.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> tys f \<phi>)
  let ?b = "length tys"
  have "v ! y = v' ! y"
    using Agg.prems by simp
  moreover have "sat \<sigma> V (zs @ v) i \<phi> = sat \<sigma> V (zs @ v') i \<phi>" if "length zs = ?b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b= ?b])
  moreover have "eval_trm (zs @ v) f = eval_trm (zs @ v') f" if "length zs = ?b" for zs
    using that Agg.prems by (auto intro!: eval_trm_fv_cong[where v="zs @ v" and v'="zs @ v'"]
        simp: nth_append fvi_iff_fv(1)[where b= ?b] fvi_trm_iff_fv_trm[where b= ?b])
  ultimately show ?case
    by (simp cong: conj_cong)
next
  case (MatchF I r)
  then have "Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
    by (intro match_fv_cong) (auto simp: fv_regex_alt)
  then show ?case
    by auto
next
  case (MatchP I r)
  then have "Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
    by (intro match_fv_cong) (auto simp: fv_regex_alt)
  then show ?case
    by auto
next
  case (Trigger \<phi> I \<psi>)
  show ?case
    using Trigger(1, 2)[of v v'] Trigger(3)
    by auto
next
  case (Release \<phi> I \<psi>)
  show ?case
    using Release(1, 2)[of v v'] Release(3)
    by auto
next
  case (TP t)
  then show ?case unfolding fvi.simps sat.simps by (metis eval_trm_fv_cong)
next
  case (TS t)
  then show ?case unfolding fvi.simps sat.simps by (metis eval_trm_fv_cong)
qed (auto 10 0 simp: Let_def split: nat.splits intro!: iff_exI)

lemma sat_restrict: "fv \<phi> \<subseteq> set ds \<Longrightarrow>
  Formula.sat \<sigma> V (val n ds (restrict ds cs v)) i \<phi> = Formula.sat \<sigma> V (val n cs v) i \<phi>"
  by (rule sat_fv_cong) (auto simp: val_restrict_nth)

text \<open>A table over the columns @{term cs} whose tuples, as valuations of the first @{term n}
  variables, are the valuations in @{term R} satisfying @{term \<phi>} at @{term i}.\<close>

abbreviation sat_table :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow>
  ty Formula.formula \<Rightarrow> event_data table \<Rightarrow> bool" where
  "sat_table \<sigma> V n R cs i \<phi> \<equiv> qtable cs (mem_restr R cs) (\<lambda>v. Formula.sat \<sigma> V (val n cs v) i \<phi>)"

lemma qtable_project_fv:
  assumes "distinct cs" "set cs = fv \<phi>" "\<forall>x\<in>fv \<phi>. x < Suc n"
    and "qtable cs (mem_restr (lift_envs R) cs) (\<lambda>v. Formula.sat \<sigma> V (val (Suc n) cs v) i \<phi>) X"
  shows "qtable (ex_cols cs) (mem_restr R (ex_cols cs))
    (\<lambda>v. Formula.sat \<sigma> V (val n (ex_cols cs) v) i (Formula.Exists t \<phi>)) (ex_proj cs ` X)"
proof (rule qtable_cong[OF qtable_project[OF assms(1,4)] refl])
  fix v
  assume "mem_restr R (ex_cols cs) v"
  then have wf: "wf_tuple (ex_cols cs) v"
    by (rule mem_restr_wf_tuple)
  have agree: "Formula.sat \<sigma> V (val (Suc n) cs x) i \<phi> \<longleftrightarrow> Formula.sat \<sigma> V (z # val n (ex_cols cs) v) i \<phi>"
    if "0 \<in> set cs \<Longrightarrow> tup_get cs x 0 = z" "\<And>c. c \<in> set cs \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> tup_get cs x c = tup_get (ex_cols cs) v (c - 1)"
    for x z
  proof (rule sat_fv_cong, intro ballI)
    fix c
    assume "c \<in> fv \<phi>"
    then show "val (Suc n) cs x ! c = (z # val n (ex_cols cs) v) ! c"
      using assms(2,3) that by (cases c) auto
  qed
  show "(\<exists>x. wf_tuple cs x \<and> ex_proj cs x = v \<and> Formula.sat \<sigma> V (val (Suc n) cs x) i \<phi>) \<longleftrightarrow>
    Formula.sat \<sigma> V (val n (ex_cols cs) v) i (Formula.Exists t \<phi>)"
  proof
    assume "\<exists>x. wf_tuple cs x \<and> ex_proj cs x = v \<and> Formula.sat \<sigma> V (val (Suc n) cs x) i \<phi>"
    then obtain x where x: "ex_proj cs x = v" "Formula.sat \<sigma> V (val (Suc n) cs x) i \<phi>"
      by blast
    have "Formula.sat \<sigma> V (tup_get cs x 0 # val n (ex_cols cs) v) i \<phi>"
      using x(2) tup_get_ex_proj[of _ cs x] by (subst agree[symmetric]) (auto simp: x(1)[symmetric])
    then show "Formula.sat \<sigma> V (val n (ex_cols cs) v) i (Formula.Exists t \<phi>)"
      by auto
  next
    assume "Formula.sat \<sigma> V (val n (ex_cols cs) v) i (Formula.Exists t \<phi>)"
    then obtain z where z: "Formula.sat \<sigma> V (z # val n (ex_cols cs) v) i \<phi>"
      by auto
    define x where "x = map (\<lambda>c. if c = 0 then z else tup_get (ex_cols cs) v (c - 1)) cs"
    have get: "tup_get cs x c = (if c = 0 then z else tup_get (ex_cols cs) v (c - 1))" if "c \<in> set cs" for c
      using that by (simp add: x_def tup_get_map_self)
    have "ex_proj cs x = map (tup_get (ex_cols cs) v) (ex_cols cs)"
      by (auto simp: ex_proj_def ex_cols_def restrict_def get)
    also have "\<dots> = v"
      using restrict_idle[OF distinct_ex_cols[OF assms(1)] wf] by (simp add: restrict_def)
    finally have "ex_proj cs x = v" .
    moreover have "Formula.sat \<sigma> V (val (Suc n) cs x) i \<phi>"
      using z by (subst agree) (simp_all add: get)
    ultimately show "\<exists>x. wf_tuple cs x \<and> ex_proj cs x = v \<and> Formula.sat \<sigma> V (val (Suc n) cs x) i \<phi>"
      by (intro exI[of _ x]) (simp add: wf_tuple_def x_def)
  qed
qed

lemma sat_the_update: "y \<notin> fv \<phi> \<Longrightarrow> Formula.sat \<sigma> V (map the (x[y:=z])) i \<phi> = Formula.sat \<sigma> V (map the x) i \<phi>"
  by (rule sat_fv_cong) (metis map_update nth_list_update_neq)

lemma match_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
  by (rule match_fv_cong, rule sat_fv_cong) (auto simp: fv_regex_alt)

lemma eps_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.eps (sat \<sigma> V v) i r = Regex.eps (sat \<sigma> V v') i r"
  unfolding eps_match by (erule match_fv_cong[THEN fun_cong, THEN fun_cong])


subsection \<open>Derived temporal operators\<close>

qualified definition "first = Neg (Prev all TT)"

lemma first_fv[simp]: "fv first = {}"
  by (simp add: first_def)

lemma first_sat[simp] : "sat \<sigma> V v i first = (i=0)"
  using interval_all by (auto simp: first_def split: nat.split)

lemma first_fvi[simp]: "fvi b first = {}"
  by (auto simp: first_def TT_def FF_def split: nat.split)

lemma "sat \<sigma> V v i (Trigger \<phi> I \<psi>) = sat \<sigma> V v i (Neg (Since (Neg \<phi>) I (Neg \<psi>)))"
  by auto

lemma "sat \<sigma> V v i (Release \<phi> I \<psi>) = sat \<sigma> V v i (Neg (Until (Neg \<phi>) I (Neg \<psi>)))"
  by auto

definition release :: "'t formula \<Rightarrow> \<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "release \<phi> I \<psi> = Neg (Until (Neg \<phi>) I (Neg \<psi>))"

lemma sat_release[simp]:
  "sat \<sigma> V v i (release \<phi> I \<psi>) = (\<forall>j\<ge>i. (mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)))"
  unfolding release_def
  by auto

lemma sat_release_eq[simp]: "sat \<sigma> V v i (Release \<phi> I \<psi>) = sat \<sigma> V v i (release \<phi> I \<psi>)"
  by auto

definition once :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "once I \<phi> = Since TT I \<phi>"

lemma syntax_once_simps [simp]:
  "once I \<psi> \<noteq> (Formula.Eq t1 t2)"
  "once I \<psi> \<noteq> (Formula.Less t1 t2)"
  "once I \<psi> \<noteq> (Formula.LessEq t1 t2)"
  "once I \<psi> \<noteq> (Formula.Neg \<phi>)"
  unfolding once_def
  by auto

lemma once_fv[simp]: "fv (once I \<phi>) = fv \<phi>"
  by (simp add: once_def)

lemma sat_once[simp] : "sat \<sigma> V v i (once I \<phi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>)"
  by (auto simp: once_def)

lemma once_fvi[simp] : "fvi b (once I \<phi>) = fvi b \<phi>"
  by (auto simp: once_def)

definition historically :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "historically I \<phi> = (Neg (once I (Neg \<phi>)))"

lemma fv_historically[simp]: "fv (historically I \<phi>) = fv \<phi>"
  by (simp add: historically_def)

lemma sat_historically[simp]: "sat \<sigma> V v i (historically I \<phi>) = (\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> sat \<sigma> V v j \<phi>)"
  unfolding historically_def
  by auto

definition eventually :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "eventually I \<phi> = Until TT I \<phi>"

lemma syntax_eventually_simps [simp]:
  "Formula.eventually I \<psi> \<noteq> (Formula.Eq t1 t2)"
  "Formula.eventually I \<psi> \<noteq> (Formula.Less t1 t2)"
  "Formula.eventually I \<psi> \<noteq> (Formula.LessEq t1 t2)"
  "Formula.eventually I \<psi> \<noteq> (Formula.Neg \<phi>)"
  unfolding Formula.eventually_def
  by auto

lemma eventually_fv[simp]: "fv (eventually I \<phi>) = fv \<phi>"
  by (simp add: eventually_def)

lemma eventually_fvi[simp]: "fvi b (eventually I \<phi>) = fvi b \<phi>"
  by (auto simp: eventually_def)

lemma sat_eventually[simp]: "sat \<sigma> V v i (eventually I \<phi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<phi>)"
  by (auto simp: eventually_def)

lemma contains_pred_eventually [simp]: 
  "contains_pred p (Formula.eventually I \<psi>') \<longleftrightarrow> contains_pred p \<psi>'"
  unfolding Formula.eventually_def
  by simp

lemma contains_pred_once [simp]: 
  "contains_pred p (once I \<psi>') \<longleftrightarrow> contains_pred p \<psi>'"
  unfolding once_def
  by simp

definition always :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "always I \<phi> = (Neg (eventually I (Neg \<phi>)))"

lemma fv_always[simp]: "fv (always I \<phi>) = fv \<phi>"
  by (simp add: always_def)

lemma sat_always[simp]: "sat \<sigma> V v i (always I \<phi>) = (\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v j \<phi>)"
  unfolding always_def
  by auto

definition always_safe_0 :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "always_safe_0 I \<phi> = (Or (Until \<phi> (flip_int_double_upper I) (Prev all \<phi>)) (Until \<phi> I (And \<phi> (Next (flip_int I) TT))))"

definition always_safe_bounded :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "always_safe_bounded I \<phi> = (And (eventually I \<phi>) (Neg (eventually I (And (Or (once (int_remove_lower_bound I) \<phi>) (eventually (int_remove_lower_bound I) \<phi>)) (Neg \<phi>)))))"

lemma always_safe_0_safe_fv[simp]: "fv (always_safe_0 I \<phi>) = fv \<phi>"
  by (auto simp add: always_safe_0_def)

lemma always_safe_bounded_fv[simp]: "fv (always_safe_bounded I \<phi>) = fv \<phi>"
  by (auto simp add: always_safe_bounded_def)

definition release_safe_0 :: "'t formula \<Rightarrow> \<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "release_safe_0 \<phi> I \<psi> = Or (Until \<psi> I (And \<psi> \<phi>)) (always_safe_0 I \<psi>)"

lemma fvi_release_safe_0[simp]:
  "Formula.fvi b (release_safe_0 \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: release_safe_0_def always_safe_0_def)

definition release_safe_bounded :: "'t formula \<Rightarrow> \<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "release_safe_bounded \<phi> I \<psi> = And (eventually I TT) (Or (Or (always_safe_bounded I \<psi>) (eventually (flip_int_less_lower I) \<phi>)) (eventually (flip_int_less_lower I) (Next all (Until \<psi> (int_remove_lower_bound I) (And \<psi> \<phi>)))))"

lemma fvi_release_safe_bounded[simp]:
  "Formula.fvi b (release_safe_bounded \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: release_safe_bounded_def always_safe_bounded_def)

lemma map_formula_release_safe_bounded[simp]: "Formula.formula.map_formula f (release_safe_bounded \<phi> I \<psi>) =
  release_safe_bounded (Formula.formula.map_formula f \<phi>) I (Formula.formula.map_formula f \<psi>)"
  by (auto simp: release_safe_bounded_def eventually_def Formula.TT_def always_safe_bounded_def once_def)

lemma formula_release_safe_bounded_induct[case_names Pred Let Frz LetPast
    Eq Less LessEq Neg Or And Ands Exists Agg
    Prev Next Since Until Trigger Release MatchP MatchF TP TS]:
  assumes Pred: "\<And>e ts. Q (formula.Pred e ts)"
    and Let: "\<And>p \<phi> \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.Let p \<phi> \<psi>)"
    and Frz: "\<And>p \<phi> \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.Frz p \<phi> \<psi>)"
    and LetPast: "\<And>p \<phi> \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.LetPast p \<phi> \<psi>)"
    and Eq: "\<And>t1 t2. Q (Formula.Eq t1 t2)"
    and Less: "\<And>t1 t2. Q (Formula.Less t1 t2)"
    and LessEq: "\<And>t1 t2. Q (Formula.LessEq t1 t2)"
    and Neg: "\<And>\<phi>. Q \<phi> \<Longrightarrow> Q (formula.Neg \<phi>)"
    and Or: "\<And>\<phi> \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.Or \<phi> \<psi>)"
    and And: "\<And>\<phi> \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.And \<phi> \<psi>)"
    and Ands: "\<And>\<phi>s. (\<And>\<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> Q \<phi>) \<Longrightarrow> Q (formula.Ands \<phi>s)"
    and Exists: "\<And>t \<phi>. Q \<phi> \<Longrightarrow> Q (formula.Exists t \<phi>)"
    and Agg: "\<And>y \<omega> tys f \<phi>. Q \<phi> \<Longrightarrow> Q (Formula.Agg y \<omega> tys f \<phi>)"
    and Prev: "\<And>I \<phi>. Q \<phi> \<Longrightarrow> Q (formula.Prev I \<phi>)"
    and Next: "\<And>I \<phi>. Q \<phi> \<Longrightarrow> Q (formula.Next I \<phi>)"
    and Since: "\<And>\<phi> I \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.Since \<phi> I \<psi>)"
    and Until: "\<And>\<phi> I \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.Until \<phi> I \<psi>)"
    and Trigger: "\<And>\<phi> I \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.Trigger \<phi> I \<psi>)"
    and Release: "\<And>\<phi> I \<psi>. (mem I 0 \<or> \<not> bounded I \<Longrightarrow> Q \<phi>) \<Longrightarrow> (mem I 0 \<or> \<not> bounded I \<Longrightarrow> Q \<psi>)
    \<Longrightarrow> (\<not> (mem I 0 \<or> \<not> bounded I) \<Longrightarrow> Q (release_safe_bounded \<phi> I \<psi>))
    \<Longrightarrow> Q (formula.Release \<phi> I \<psi>)"
    and MatchP: "(\<And>I r. (\<And>z. z \<in> regex.atms r \<Longrightarrow> Q z) \<Longrightarrow> Q (formula.MatchP I r))"
    and MatchF: "(\<And>I r. (\<And>z. z \<in> regex.atms r \<Longrightarrow> Q z) \<Longrightarrow> Q (formula.MatchF I r))"
    and TP: "\<And>t. Q (Formula.TP t)"
    and TS: "\<And>t. Q (Formula.TS t)"
  shows "Q \<phi>"
  by (induct \<phi>)
    (auto simp: release_safe_bounded_def Formula.eventually_def
      Formula.TT_def always_safe_bounded_def once_def intro!: assms)

definition and_release_safe_bounded :: "'t formula \<Rightarrow> 't formula \<Rightarrow> \<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "and_release_safe_bounded \<phi> \<phi>' I \<psi>' = (Or (And \<phi> (Neg (eventually I TT))) (And \<phi> (release_safe_bounded \<phi>' I \<psi>')))"

lemma fvi_and_release_safe_bounded[simp]: 
  "Formula.fvi b (and_release_safe_bounded \<phi> \<phi>'' I \<psi>') = Formula.fvi b \<phi> \<union> (Formula.fvi b \<phi>'' \<union> Formula.fvi b \<psi>')"
  by (auto simp: and_release_safe_bounded_def release_safe_bounded_def always_safe_bounded_def)


subsection \<open>Predicate occurrence and satisfaction\<close>

lemma contains_pred_always_safe_bounded [simp]:
  "contains_pred p (always_safe_bounded I \<psi>') \<longleftrightarrow> contains_pred p \<psi>'"
  unfolding always_safe_bounded_def
  by simp

lemma contains_pred_release_safe_bounded [simp]: "contains_pred p (release_safe_bounded \<phi>' I \<psi>') 
  \<longleftrightarrow> contains_pred p \<phi>' \<or> contains_pred p \<psi>'"
  unfolding release_safe_bounded_def
  by auto

lemma not_contains_pred_sat[simp]: 
  "\<not> contains_pred p \<phi> \<Longrightarrow> Formula.sat \<sigma> (V(p \<mapsto> x)) v i \<phi> = Formula.sat \<sigma> V v i \<phi>"
  supply fun_upd_apply[simp del]
proof (induction p \<phi> arbitrary: V v x i rule: contains_pred.induct)
  case (5 p e \<phi> \<psi> V v x i)
  let ?q = "(e, Formula.nfv \<phi>)"
  let ?F = "\<lambda>V w j. Formula.sat \<sigma> V w j \<phi>"
  have "Formula.sat \<sigma> (V(p \<mapsto> x, ?q \<mapsto> ?F (V(p \<mapsto> x)))) v i \<psi> =
    Formula.sat \<sigma> (V(?q \<mapsto> ?F V)) v i \<psi>"
  proof (cases "contains_pred p \<phi>")
    case True
    with "5.prems" have q: "\<not> contains_pred ?q \<psi>" and p: "p \<noteq> ?q \<Longrightarrow> \<not> contains_pred p \<psi>"
      by auto
    from q have "Formula.sat \<sigma> (V(p \<mapsto> x, ?q \<mapsto> ?F (V(p \<mapsto> x)))) v i \<psi> =
      Formula.sat \<sigma> (V(p \<mapsto> x)) v i \<psi>"
      by (rule "5.IH"(2))
    also have "\<dots> = Formula.sat \<sigma> V v i \<psi>"
      using q p by (cases "p = ?q") (simp_all add: "5.IH"(2,3))
    also have "\<dots> = Formula.sat \<sigma> (V(?q \<mapsto> ?F V)) v i \<psi>"
      using q by (rule "5.IH"(2)[symmetric])
    finally show ?thesis .
  next
    case False
    then have "\<And>w j. Formula.sat \<sigma> (V(p \<mapsto> x)) w j \<phi> = Formula.sat \<sigma> V w j \<phi>"
      by (rule "5.IH"(1))
    moreover have "Formula.sat \<sigma> (V(p \<mapsto> x, ?q \<mapsto> ?F V)) v i \<psi> = Formula.sat \<sigma> (V(?q \<mapsto> ?F V)) v i \<psi>"
    proof (cases "p = ?q")
      case False
      with "5.prems" have "\<not> contains_pred p \<psi>"
        by simp
      with False show ?thesis
        by (simp add: fun_upd_twist[OF False] "5.IH"(3))
    qed simp
    ultimately show ?thesis
      by simp
  qed
  then show ?case
    by simp
next
  case (6 p e \<phi> \<psi> V v x i)
  let ?q = "(e, Formula.nfv \<phi>)"
  let ?F = "\<lambda>V w j. Formula.sat \<sigma> V w i \<phi>"
  have "Formula.sat \<sigma> (V(p \<mapsto> x, ?q \<mapsto> ?F (V(p \<mapsto> x)))) v i \<psi> =
    Formula.sat \<sigma> (V(?q \<mapsto> ?F V)) v i \<psi>"
  proof (cases "contains_pred p \<phi>")
    case True
    with "6.prems" have q: "\<not> contains_pred ?q \<psi>" and p: "p \<noteq> ?q \<Longrightarrow> \<not> contains_pred p \<psi>"
      by auto
    from q have "Formula.sat \<sigma> (V(p \<mapsto> x, ?q \<mapsto> ?F (V(p \<mapsto> x)))) v i \<psi> =
      Formula.sat \<sigma> (V(p \<mapsto> x)) v i \<psi>"
      by (rule "6.IH"(2))
    also have "\<dots> = Formula.sat \<sigma> V v i \<psi>"
      using q p by (cases "p = ?q") (simp_all add: "6.IH"(2,3))
    also have "\<dots> = Formula.sat \<sigma> (V(?q \<mapsto> ?F V)) v i \<psi>"
      using q by (rule "6.IH"(2)[symmetric])
    finally show ?thesis .
  next
    case False
    then have "\<And>w. Formula.sat \<sigma> (V(p \<mapsto> x)) w i \<phi> = Formula.sat \<sigma> V w i \<phi>"
      by (rule "6.IH"(1))
    moreover have "Formula.sat \<sigma> (V(p \<mapsto> x, ?q \<mapsto> ?F V)) v i \<psi> = Formula.sat \<sigma> (V(?q \<mapsto> ?F V)) v i \<psi>"
    proof (cases "p = ?q")
      case False
      with "6.prems" have "\<not> contains_pred p \<psi>"
        by simp
      with False show ?thesis
        by (simp add: fun_upd_twist[OF False] "6.IH"(3))
    qed simp
    ultimately show ?thesis
      by simp
  qed
  then show ?case
    by simp
next
  case (7 p e \<phi> \<psi> V v x i)
  let ?q = "(e, Formula.nfv \<phi>)"
  let ?L = "\<lambda>V. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?q \<mapsto> X)) u k \<phi>)"
  have "Formula.sat \<sigma> (V(p \<mapsto> x, ?q \<mapsto> ?L (V(p \<mapsto> x)))) v i \<psi> =
    Formula.sat \<sigma> (V(?q \<mapsto> ?L V)) v i \<psi>"
  proof (cases "p = ?q")
    case False
    with "7.prems" have p: "\<not> contains_pred p \<psi>"
      by simp
    from False "7.prems" have "\<not> contains_pred p \<phi> \<or> \<not> contains_pred ?q \<psi>"
      by simp
    then show ?thesis
    proof
      assume "\<not> contains_pred p \<phi>"
      then have "?L (V(p \<mapsto> x)) = ?L V"
        by (simp add: fun_upd_twist[OF False] "7.IH"(1))
      with p show ?thesis
        by (simp add: fun_upd_twist[OF False] "7.IH"(3))
    next
      assume "\<not> contains_pred ?q \<psi>"
      with p show ?thesis
        by (simp add: "7.IH"(2,3))
    qed
  qed simp
  then show ?case
    by (simp add: Let_def)
qed (simp_all add: fun_upd_apply split: nat.splits cong: match_cong)


subsection \<open>Well-formed formulas\<close>

fun wf_formula :: "'t formula \<Rightarrow> bool" 
  where "wf_formula (Let p \<phi> \<psi>) = ({0..<nfv \<phi>} \<subseteq> fv \<phi> \<and> wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (Frz p \<phi> \<psi>) = ({0..<nfv \<phi>} \<subseteq> fv \<phi> \<and> wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (LetPast p \<phi> \<psi>) = ({0..<nfv \<phi>} \<subseteq> fv \<phi> \<and> wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (Neg \<phi>) =  wf_formula \<phi>"
| "wf_formula (Or \<phi> \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (And \<phi> \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi> )"
| "wf_formula (Ands l) = (list_all wf_formula l)"
| "wf_formula (Exists x \<phi>) = (wf_formula \<phi> \<and> 0 \<in> fv \<phi>)"
| "wf_formula (Agg y \<omega> tys f \<phi>) = (wf_formula \<phi> \<and> y + length tys \<notin> fv \<phi> \<and> {0..< length tys} \<subseteq> fv \<phi> )"
| "wf_formula (Prev I \<phi>) = (wf_formula \<phi>)"
| "wf_formula (Next I \<phi>) = (wf_formula \<phi>)"
| "wf_formula (Since \<phi> I \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (Until \<phi> I \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (Trigger \<phi> I \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (Release \<phi> I \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (MatchP I r) = Regex.pred_regex wf_formula r"
| "wf_formula (MatchF I r) = Regex.pred_regex wf_formula r"
| "wf_formula _ = True"

subsection \<open>Mapping type annotations\<close>

lemma map_regex_fv:  assumes "\<And>x . x \<in> regex.atms x2 \<Longrightarrow>  g (formula.map_formula f x) = g' x"
  shows "Regex.fv_regex g (regex.map_regex (formula.map_formula f) x2) = Regex.fv_regex g' x2" using assms by (induction x2) auto

lemma map_regex_pred:  assumes "\<And>x . x \<in> regex.atms x2 \<Longrightarrow>  g (formula.map_formula f x) = g' x"
  shows "regex.pred_regex g (regex.map_regex (formula.map_formula f) x2) = regex.pred_regex g' x2" using assms by (induction x2) auto

lemma fvi_map_formula[simp]:  shows "Formula.fvi b (formula.map_formula f \<psi>) = Formula.fvi b \<psi>"
proof (induction \<psi> arbitrary: b)
  case (MatchF x1 x2)
  show ?case using map_regex_fv[where ?g="Formula.fvi b" and ?f=f] MatchF by auto
  case (MatchP x1 x2)
  show ?case using map_regex_fv[where ?g="Formula.fvi b" and ?f=f] MatchP by auto
qed auto

lemma nfv_map[simp]: "Formula.nfv (formula.map_formula f \<psi>) = Formula.nfv \<psi>"
  unfolding Formula.nfv_def by auto

lemma wf_formula_map_iff[simp]: "wf_formula (formula.map_formula f \<psi>) = wf_formula \<psi>"
  by (induction \<psi>) (auto simp add: list_all_def map_regex_pred)

lemma wf_formula_map: "wf_formula \<phi> \<Longrightarrow> wf_formula (formula.map_formula f \<phi>)"
  by simp

lemma fv_map:
  "fv \<phi> = fv (formula.map_formula f \<phi>)" by auto

lemma map_regex_size: assumes "\<And>x . x \<in> regex.atms r \<Longrightarrow>   size (f x) = size x" shows "regex.size_regex size r = regex.size_regex size (regex.map_regex f r) "
  using assms by (induction r arbitrary: ) auto

lemma map_regex_map_formula_size[simp]: " size (regex.map_regex (formula.map_formula f) r) = size r"
  by (induction r)  auto

lemma map_formula_size[simp]:"size (formula.map_formula f \<psi>) = size \<psi>"
proof (induction \<psi> arbitrary: f)
  case (Ands \<phi>s)
  from Ands.IH show ?case
    by (simp add: dual_order.eq_iff size_list_pointwise)
next
  case (Agg y \<omega> tys t \<phi>)
  then show ?case by (cases \<omega>) simp
next
  case (MatchF I r)
  have "regex.size_regex size r = regex.size_regex size (regex.map_regex (formula.map_formula f) r)"
    by (rule map_regex_size) (rule MatchF.IH)
  then show ?case by simp
next
  case (MatchP I r)
  have "regex.size_regex size r = regex.size_regex size (regex.map_regex (formula.map_formula f) r)"
    by (rule map_regex_size) (rule MatchP.IH)
  then show ?case by simp
qed simp_all

lemma[simp]: "regex.size_regex size (regex.map_regex (formula.map_formula x2) s) = regex.size_regex size s"
  by (induction s)  auto

end

subsection \<open>Finite prefixes\<close>

lift_definition pfinite :: "Formula.prefix \<Rightarrow> bool" is "\<lambda>p. \<forall>x \<in> set p. finite (fst x)" .

lemma pfinite_psnoc: "pfinite \<pi> \<Longrightarrow> finite (fst x) \<Longrightarrow> last_ts \<pi> \<le> snd x \<Longrightarrow> pfinite (psnoc \<pi> x)"
  by (transfer fixing: x) simp

lemma pfinite_psnocD: "pfinite (psnoc \<pi> x) \<Longrightarrow> last_ts \<pi> \<le> snd x \<Longrightarrow> pfinite \<pi> \<and> finite (fst x)"
  by (transfer fixing: x) simp

lemma pfinite_mono: "pfinite \<pi>' \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> pfinite \<pi>"
  by transfer auto


subsection \<open>Notation\<close>

context
begin

abbreviation "eval_trm_option v t \<equiv> Formula.eval_trm (map the v) t"

abbreviation "sat_the \<sigma> V v i \<equiv> Formula.sat \<sigma> V (map the v) i"

end

bundle MFODL_no_notation
begin

no_notation trm.Var ("\<^bold>v")
     and trm.Const ("\<^bold>c")

no_notation formula.Pred ("_ \<dagger> _" [85, 85] 85)
     and formula.Eq (infixl "=\<^sub>F" 75)
     and formula.LessEq ("(_/ \<le>\<^sub>F _)" [76,76] 75)
     and formula.Less ("(_/ <\<^sub>F _)" [76,76] 75)
     and formula.Neg ("\<not>\<^sub>F _" [82] 82)
     and formula.And (infixr "\<and>\<^sub>F" 80)
     and formula.Or (infixr "\<or>\<^sub>F" 80)
     and formula.Exists ("\<exists>\<^sub>F:_. _" [70,70] 70)
     and formula.Ands ("\<And>\<^sub>F _" [70] 70)
     and formula.Prev ("\<^bold>Y _ _" [55, 65] 65)
     and formula.Next ("\<^bold>X _ _" [55, 65] 65)
     and formula.Since ("_ \<^bold>S _ _" [60,55,60] 60)
     and formula.Until ("_ \<^bold>U _ _" [60,55,60] 60)
     and formula.Trigger ("_ \<^bold>T _ _" [60,55,60] 60)
     and formula.Release ("_ \<^bold>R _ _" [60,55,60] 60)

no_notation Regex.Skip ("SKIP _" [56] 56)
    and Regex.Test ("\<questiondown>_?")
    and Regex.Times (infixl ";\<^sub>r" 55)
    and Regex.Plus (infixl "+\<^sub>r" 54)
    and Regex.Star ("_\<^sup>\<star>" [57] 57)
    and Formula.frwd_diam ("\<bar>_\<rangle>_" [51, 81] 81)
    and Formula.bwrd_diam ("\<langle>_\<bar>_" [51, 81] 81)

no_notation Formula.fv_trm ("FV\<^sub>t")
     and Formula.fv ("FV")
     and eval_trm_option ("_\<lbrakk>_\<rbrakk>\<^sub>M" [51,89] 89)
     and sat_the ("\<langle>_, _, _, _\<rangle> \<Turnstile>\<^sub>M _" [56, 56, 56, 56, 56] 55)
     and Formula.sat ("\<langle>_, _, _, _\<rangle> \<Turnstile> _" [56, 56, 56, 56, 56] 55)

end

bundle MFODL_notation
begin

notation trm.Var ("\<^bold>v")
     and trm.Const ("\<^bold>c")

notation formula.Pred ("_ \<dagger> _" [85, 85] 85)
     and formula.Eq (infixl "=\<^sub>F" 75)
     and formula.LessEq ("(_/ \<le>\<^sub>F _)" [76,76] 75)
     and formula.Less ("(_/ <\<^sub>F _)" [76,76] 75)
     and formula.Neg ("\<not>\<^sub>F _" [82] 82)
     and formula.And (infixr "\<and>\<^sub>F" 80)
     and formula.Or (infixr "\<or>\<^sub>F" 80)
     and formula.Exists ("\<exists>\<^sub>F:_. _" [70,70] 70)
     and formula.Ands ("\<And>\<^sub>F _" [70] 70)
     and formula.Prev ("\<^bold>Y _ _" [55, 65] 65)
     and formula.Next ("\<^bold>X _ _" [55, 65] 65)
     and formula.Since ("_ \<^bold>S _ _" [60,55,60] 60)
     and formula.Until ("_ \<^bold>U _ _" [60,55,60] 60)
     and formula.Trigger ("_ \<^bold>T _ _" [60,55,60] 60)
     and formula.Release ("_ \<^bold>R _ _" [60,55,60] 60)

notation Regex.Skip ("SKIP _" [56] 56)
    and Regex.Test ("\<questiondown>_?")
    and Regex.Times (infixl ";\<^sub>r" 55)
    and Regex.Plus (infixl "+\<^sub>r" 54)
    and Regex.Star ("_\<^sup>\<star>" [57] 57)
    and Formula.frwd_diam ("\<bar>_\<rangle>_" [51, 81] 81)
    and Formula.bwrd_diam ("\<langle>_\<bar>_" [51, 81] 81)

notation Formula.fv_trm ("FV\<^sub>t")
     and Formula.fv ("FV")
     and eval_trm_option ("_\<lbrakk>_\<rbrakk>\<^sub>M" [51,89] 89)
     and sat_the ("\<langle>_, _, _, _\<rangle> \<Turnstile>\<^sub>M _" [56, 56, 56, 56, 56] 55)
     and Formula.sat ("\<langle>_, _, _, _\<rangle> \<Turnstile> _" [56, 56, 56, 56, 56] 55)

end

unbundle MFODL_notation
unbundle ivl_notation

term "v\<lbrakk>\<^bold>c t\<rbrakk>\<^sub>M"
term "\<And>\<^sub>F [
      \<^bold>c (EInt 0) =\<^sub>F \<^bold>c (EInt 0),
      \<exists>\<^sub>F:t. (trm =\<^sub>F \<^bold>v x) \<and>\<^sub>F (a \<le>\<^sub>F \<^bold>c z), 
      \<phi> \<^bold>U I \<psi>, 
      \<exists>\<^sub>F:t. \<bar>(skip 2)\<^sup>\<star> ;\<^sub>r \<questiondown>trm =\<^sub>F \<^bold>v x? +\<^sub>r skip 3\<rangle>\<^bold>[2,3\<^bold>] 
        \<and>\<^sub>F (a \<le>\<^sub>F \<^bold>c z)
    ]"
term "\<langle>\<sigma>, V, v, i + length v\<rangle> \<Turnstile>\<^sub>M \<^bold>Y I (\<not>\<^sub>F (P \<dagger> [\<^bold>c a, \<^bold>v 0]) 
        \<and>\<^sub>F (Q \<dagger> [\<^bold>v y])) \<^bold>S (point n) ((\<^bold>X \<^bold>[2,3\<^bold>] (P \<dagger> [\<^bold>c b, \<^bold>v 0])) \<or>\<^sub>F Q \<dagger> [\<^bold>v y])"

abbreviation point_Since :: "'a Formula.formula \<Rightarrow> nat \<Rightarrow> 'a Formula.formula 
  \<Rightarrow> 'a Formula.formula" ("_ \<^bold>S{_} _" [60,55,60] 60)
  where "\<alpha> \<^bold>S{r} \<beta> \<equiv> \<alpha> \<^bold>S (point r) \<beta>"

abbreviation point_Until :: "'a Formula.formula \<Rightarrow> nat \<Rightarrow> 'a Formula.formula 
  \<Rightarrow> 'a Formula.formula" ("_ \<^bold>U{_} _" [60,55,60] 60)
  where "\<alpha> \<^bold>U{r} \<beta> \<equiv> \<alpha> \<^bold>U (point r) \<beta>"

unbundle MFODL_no_notation
unbundle ivl_no_notation


(*<*)
end
(*>*)

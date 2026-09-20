(*<*)
theory Dense_Utuple
  imports "MFODL_Monitor_Devel.Code_Opt"
begin
(*>*)

section \<open>Tuples without the option: the operations that read a field\<close>

text \<open>
  A dense tuple has no holes, so the @{typ "'a option"} around every field of the kernel's
  tuples pays for a possibility that cannot arise.  The executable dense monitor runs on tuples
  without it (@{typ "event_data list"}); the verified dense evaluator is stated on the kernel's
  tuples, where its theorems can be related to the kernel's.  The two representations are
  connected by \<open>deopt\<close>, which strips the option, and \<open>reopt\<close>, which puts it back; on hole-free
  tuples they are inverse.

  Most dense operations move fields without looking at them, and generalise over the element
  type.  The ones below read a field -- the term evaluation, the match, the constraint, the
  assignment and the aggregation -- and cannot.  They are defined here over the short tuples
  once, and the verified evaluator's versions over the kernel's tuples are \<^emph>\<open>defined\<close> as these
  read through @{text deopt}: on the hole-free tuples the simulation guarantees that is the
  kernel's reading, and on every tuple it is what the unboxed evaluator computes, so the
  refinement to short tuples holds without any invariant.
\<close>

type_synonym utable = "event_data list set"

subsection \<open>The sorted list of a table\<close>

text \<open>
  The operations that walk a table walk @{const csorted_list_of_set} of it, which is unspecified
  on an infinite set -- and unspecified differently at every type, so that an operation stated
  over the kernel's tuples and its twin over short tuples cannot be related on infinite tables at
  all.  The walks below go through this wrapper instead, which is the sorted list on a finite
  table and empty otherwise, and which the generated code computes with one finiteness test
  (constant time on a tree).  Every table the monitor handles is finite, so nothing changes at
  run time; what changes is that the refinement to short tuples needs no finiteness invariant.
\<close>

definition csl :: "'a :: ccompare set \<Rightarrow> 'a list" where
  "csl X = (if finite X then csorted_list_of_set X else [])"

lemma csl_finite: "finite X \<Longrightarrow> csl X = csorted_list_of_set X"
  by (simp add: csl_def)

lemma csl_infinite: "\<not> finite X \<Longrightarrow> csl X = []"
  by (simp add: csl_def)

subsection \<open>Stripping and restoring the option\<close>

definition deopt :: "'a tuple \<Rightarrow> 'a list" where
  "deopt = map the"

definition reopt :: "'a list \<Rightarrow> 'a tuple" where
  "reopt = map Some"

definition deopt_table :: "'a table \<Rightarrow> 'a list set" where
  "deopt_table X = deopt ` X"

definition reopt_table :: "'a list set \<Rightarrow> 'a table" where
  "reopt_table X = reopt ` X"

text \<open>The sanitiser: the identity on hole-free tables.  The verified evaluator applies it where
  a table enters from a kernel structure whose result it does not otherwise inspect.\<close>

definition dsan :: "'a table \<Rightarrow> 'a table" where
  "dsan X = reopt_table (deopt_table X)"

lemma deopt_simps[simp]:
  "deopt [] = []" "deopt (a # x) = the a # deopt x"
  "deopt (xs @ ys) = deopt xs @ deopt ys"
  "deopt (take p x) = take p (deopt x)" "deopt (drop p x) = drop p (deopt x)"
  "deopt (tl x) = tl (deopt x)"
  by (simp_all add: deopt_def drop_map take_map map_tl)

lemma reopt_simps[simp]:
  "reopt [] = []" "reopt (a # x) = Some a # reopt x"
  "reopt (xs @ ys) = reopt xs @ reopt ys"
  "reopt (take p x) = take p (reopt x)" "reopt (drop p x) = drop p (reopt x)"
  "reopt (tl x) = tl (reopt x)"
  by (simp_all add: reopt_def drop_map take_map map_tl)

lemma deopt_reopt[simp]: "deopt (reopt xs) = xs"
  by (simp add: deopt_def reopt_def comp_def)

lemma reopt_inj[simp]: "reopt x = reopt y \<longleftrightarrow> x = y"
  by (auto simp: reopt_def)

lemma inj_reopt: "inj reopt"
  by (simp add: inj_def)

lemma reopt_deopt_iff: "reopt (deopt x) = x \<longleftrightarrow> (\<forall>a \<in> set x. a \<noteq> None)"
proof (induct x)
  case (Cons a x)
  then show ?case by (cases a) (auto simp: reopt_def deopt_def)
qed (simp add: reopt_def deopt_def)

lemma deopt_table_reopt_table[simp]: "deopt_table (reopt_table X) = X"
  by (force simp: deopt_table_def reopt_table_def)

lemma dsan_reopt_table[simp]: "dsan (reopt_table X) = reopt_table X"
  by (simp add: dsan_def)

lemma dsan_eq:
  assumes "\<And>x. x \<in> X \<Longrightarrow> \<forall>a \<in> set x. a \<noteq> None"
  shows "dsan X = X"
proof -
  have "reopt (deopt x) = x" if "x \<in> X" for x
    using assms[OF that] by (simp add: reopt_deopt_iff)
  then show ?thesis by (auto simp: dsan_def reopt_table_def deopt_table_def image_image)
qed

lemma length_deopt[simp]: "length (deopt x) = length x"
  by (simp add: deopt_def)

lemma length_reopt[simp]: "length (reopt xs) = length xs"
  by (simp add: reopt_def)

lemma nth_deopt: "i < length x \<Longrightarrow> deopt x ! i = the (x ! i)"
  by (simp add: deopt_def)

lemma nth_reopt: "i < length x \<Longrightarrow> reopt x ! i = Some (x ! i)"
  by (simp add: reopt_def)

lemma reopt_table_simps[simp]:
  "reopt_table {} = {}"
  "reopt_table (Set.insert x X) = Set.insert (reopt x) (reopt_table X)"
  "reopt_table (X \<union> Y) = reopt_table X \<union> reopt_table Y"
  "reopt_table (X \<inter> Y) = reopt_table X \<inter> reopt_table Y"
  "reopt_table (X - Y) = reopt_table X - reopt_table Y"
  "reopt_table (Set.remove x X) = Set.remove (reopt x) (reopt_table X)"
  "reopt_table (Set.filter P X) = Set.filter (\<lambda>y. P (deopt y)) (reopt_table X)"
  "reopt x \<in> reopt_table X \<longleftrightarrow> x \<in> X"
  "reopt_table X = {} \<longleftrightarrow> X = {}"
  "reopt_table X = reopt_table Y \<longleftrightarrow> X = Y"
  "Set.is_empty (reopt_table X) \<longleftrightarrow> Set.is_empty X"
  "finite (reopt_table X) \<longleftrightarrow> finite X"
  "card (reopt_table X) = card X"
  "reopt_table (f ` X) = (reopt \<circ> f) ` X"
  unfolding reopt_table_def
  by (auto simp: image_Int image_set_diff inj_reopt Set.remove_eq Set.is_empty_iff
      card_image inj_on_def finite_image_iff image_iff inj_image_eq_iff[OF inj_reopt]
      intro!: inj_on_image_set_diff)

lemma reopt_table_singleton[simp]: "reopt_table {x} = {reopt x}"
  by (simp add: reopt_table_def)



lemma deopt_table_simps[simp]:
  "deopt_table {} = {}"
  "deopt_table (X \<union> Y) = deopt_table X \<union> deopt_table Y"
  by (auto simp: deopt_table_def)

subsection \<open>Term evaluation\<close>

fun umeval_trm :: "Formula.trm \<Rightarrow> event_data list \<Rightarrow> event_data" where
  "umeval_trm (Formula.Var x) v = v ! x"
| "umeval_trm (Formula.Const x) v = x"
| "umeval_trm (Formula.Plus x y) v = umeval_trm x v + umeval_trm y v"
| "umeval_trm (Formula.Minus x y) v = umeval_trm x v - umeval_trm y v"
| "umeval_trm (Formula.UMinus x) v = - umeval_trm x v"
| "umeval_trm (Formula.Mult x y) v = umeval_trm x v * umeval_trm y v"
| "umeval_trm (Formula.Div x y) v = umeval_trm x v div umeval_trm y v"
| "umeval_trm (Formula.Mod x y) v = umeval_trm x v mod umeval_trm y v"
| "umeval_trm (Formula.F2i x) v = EInt (integer_of_event_data (umeval_trm x v))"
| "umeval_trm (Formula.I2f x) v = EFloat (double_of_event_data (umeval_trm x v))"

lemma umeval_trm_deopt:
  "Formula.fv_trm t \<subseteq> {i. i < length x} \<Longrightarrow> umeval_trm t (deopt x) = meval_trm t x"
  by (induct t) (simp_all add: nth_deopt)

subsection \<open>The assignment\<close>

definition uassign1 :: "nat \<Rightarrow> Formula.trm \<Rightarrow> event_data list \<Rightarrow> event_data list" where
  "uassign1 p t d = take p d @ umeval_trm t d # drop p d"

definition uassign :: "nat \<Rightarrow> Formula.trm \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "uassign p t D = uassign1 p t ` D"

subsection \<open>The time point and time stamp terms\<close>

fun umtrm :: "mtrm \<Rightarrow> event_data \<Rightarrow> event_data list set" where
  "umtrm (MVar v) x = {[x]}"
| "umtrm (MConst c) x = (if c = x then {[]} else {})"

subsection \<open>The match\<close>

fun umatch :: "Formula.trm list \<Rightarrow> event_data list \<Rightarrow> (nat \<rightharpoonup> event_data) option" where
  "umatch [] [] = Some Map.empty"
| "umatch (Formula.Const x # ts) (y # ys) = (if x = y then umatch ts ys else None)"
| "umatch (Formula.Var x # ts) (y # ys) = (case umatch ts ys of
      None \<Rightarrow> None
    | Some f \<Rightarrow> (case f x of
        None \<Rightarrow> Some (f(x \<mapsto> y))
      | Some z \<Rightarrow> if y = z then Some f else None))"
| "umatch _ _ = None"

lemma umatch_reopt: "umatch tms xs = match tms (reopt xs)"
  by (induct tms xs rule: umatch.induct) auto

lemma these_map_option_image: "Option.these (map_option g ` S) = g ` Option.these S"
  by (force simp: Option.these_def image_iff)

definition umatch_table :: "Formula.trm list \<Rightarrow> nat list \<Rightarrow> event_data list set \<Rightarrow>
    event_data list set" where
  "umatch_table tms cs X =
     Option.these ((\<lambda>x. map_option (\<lambda>f. map (\<lambda>c. the (f c)) cs) (umatch tms x)) ` X)"

subsection \<open>The constraint\<close>

definition ueval_constraint :: "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow>
    event_data list \<Rightarrow> bool" where
  "ueval_constraint conf x = (case conf of (t1, p, c, t2) \<Rightarrow>
     eval_constraint0 c (umeval_trm t1 x) (umeval_trm t2 x) = p)"

lemma ueval_constraint_deopt:
  "Formula.fv_trm (fst conf) \<subseteq> {i. i < length x} \<Longrightarrow>
   Formula.fv_trm (snd (snd (snd conf))) \<subseteq> {i. i < length x} \<Longrightarrow>
   ueval_constraint conf (deopt x) = eval_constraint conf x"
  by (cases conf) (simp add: ueval_constraint_def umeval_trm_deopt)

subsection \<open>The aggregation\<close>

definition uagg_values :: "Formula.trm \<Rightarrow> event_data list set \<Rightarrow> (event_data \<times> enat) set" where
  "uagg_values f G = (let vals = cluster (Some \<circ> umeval_trm f) G in
     (\<lambda>v. case Mapping.lookup vals v of Some S \<Rightarrow> (v, ecard S)) ` Mapping.keys vals)"

definition uagg :: "bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> Formula.trm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    event_data list set \<Rightarrow> event_data list set" where
  "uagg g0 \<omega> f k pos rel =
     (if g0 \<and> Set.is_empty rel then {[eval_agg_op \<omega> {}]}
      else (let groups = cluster (Some \<circ> drop k) rel in
        (\<lambda>g. case Mapping.lookup groups g of
                None \<Rightarrow> g
              | Some G \<Rightarrow> take pos g @ eval_agg_op \<omega> (uagg_values f G) # drop pos g)
          ` Mapping.keys groups))"

lemma uagg_values:
  "uagg_values f G = (\<lambda>v. (v, ecard (Set.filter (\<lambda>x. umeval_trm f x = v) G))) ` umeval_trm f ` G"
  unfolding uagg_values_def Let_def keys_cluster
  by (intro image_cong[OF refl]) (simp add: lookup_cluster_Some)

text \<open>On hole-free tuples whose width covers the term's variables, the short aggregation reads
  what the kernel's reads.\<close>

lemma uagg_values_deopt:
  assumes fv: "\<And>x. x \<in> G \<Longrightarrow> Formula.fv_trm f \<subseteq> {i. i < length x}"
    and hf: "\<And>x. x \<in> G \<Longrightarrow> \<forall>a \<in> set x. a \<noteq> None"
  shows "uagg_values f (deopt_table G) = agg_values f G"
proof -
  have inj: "inj_on deopt G"
    by (rule inj_onI) (metis hf reopt_deopt_iff)
  have ev: "\<And>x. x \<in> G \<Longrightarrow> umeval_trm f (deopt x) = meval_trm f x"
    by (simp add: umeval_trm_deopt fv)
  have "Set.filter (\<lambda>x. umeval_trm f x = v) (deopt_table G)
      = deopt ` Set.filter (\<lambda>x. meval_trm f x = v) G" for v
    by (auto simp: deopt_table_def ev)
  then have "ecard (Set.filter (\<lambda>x. umeval_trm f x = v) (deopt_table G))
      = ecard (Set.filter (\<lambda>x. meval_trm f x = v) G)" for v
    by (simp add: ecard_def card_image inj_on_subset[OF inj] finite_image_iff
        inj_on_subset[OF inj])
  moreover have "umeval_trm f ` deopt_table G = meval_trm f ` G"
    unfolding deopt_table_def image_image by (intro image_cong[OF refl] ev)
  ultimately show ?thesis unfolding uagg_values agg_values by simp
qed

text \<open>Whole tables, read through @{const deopt} and written back through @{const reopt}: the
  shape the verified evaluator's operations take.\<close>

lemma drop_deopt_eq_iff:
  "reopt (deopt x) = x \<Longrightarrow> reopt (deopt y) = y \<Longrightarrow>
     drop k (deopt x) = drop k (deopt y) \<longleftrightarrow> drop k x = drop k y"
  by (metis deopt_simps(5) reopt_simps(5))

lemma reopt_deopt_sub: "reopt (deopt x) = x \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> reopt (deopt y) = y"
  by (auto simp: reopt_deopt_iff)

lemma reopt_deopt_take_drop[simp]:
  "reopt (deopt x) = x \<Longrightarrow> reopt (deopt (take p x)) = take p x"
  "reopt (deopt x) = x \<Longrightarrow> reopt (deopt (drop p x)) = drop p x"
  "reopt (deopt x) = x \<Longrightarrow> reopt (deopt (take p (drop k x))) = take p (drop k x)"
  by (auto intro!: reopt_deopt_sub dest: in_set_takeD in_set_dropD)

lemma uagg_deopt:
  assumes hf: "\<And>x. x \<in> rel \<Longrightarrow> \<forall>a \<in> set x. a \<noteq> None"
    and fv: "\<And>x. x \<in> rel \<Longrightarrow> Formula.fv_trm f \<subseteq> {i. i < length x}"
  shows "reopt_table (uagg g0 \<omega> f k pos (deopt_table rel)) =
     (if g0 \<and> Set.is_empty rel then {[Some (eval_agg_op \<omega> {})]}
      else (let groups = cluster (Some \<circ> drop k) rel in
        (\<lambda>g. case Mapping.lookup groups g of
                None \<Rightarrow> g
              | Some G \<Rightarrow> take pos g @ Some (eval_agg_op \<omega> (agg_values f G)) # drop pos g)
          ` Mapping.keys groups))"
proof (cases "g0 \<and> Set.is_empty rel")
  case True
  then show ?thesis by (simp add: uagg_def deopt_table_def Set.is_empty_iff)
next
  case False
  have rd: "\<And>x. x \<in> rel \<Longrightarrow> reopt (deopt x) = x" using hf by (simp add: reopt_deopt_iff)
  have ne: "\<not> (g0 \<and> Set.is_empty (deopt_table rel))"
    using False by (simp add: deopt_table_def Set.is_empty_iff)
  let ?gr = "\<lambda>x. {z \<in> rel. drop k z = drop k x}"
  have grp: "\<And>x. x \<in> rel \<Longrightarrow> {z \<in> deopt ` rel. drop k z = drop k (deopt x)} = deopt ` ?gr x"
    by (auto simp: drop_deopt_eq_iff[OF rd rd])
  have av: "\<And>x. x \<in> rel \<Longrightarrow> uagg_values f (deopt ` ?gr x) = agg_values f (?gr x)"
    unfolding deopt_table_def[symmetric]
    by (rule uagg_values_deopt) (use fv hf in blast)+
  have "reopt_table (uagg g0 \<omega> f k pos (deopt_table rel))
      = reopt ` (\<lambda>g. case Mapping.lookup (cluster (Some \<circ> drop k) (deopt ` rel)) g of
          None \<Rightarrow> g
        | Some G \<Rightarrow> take pos g @ eval_agg_op \<omega> (uagg_values f G) # drop pos g)
        ` (drop k ` deopt ` rel)"
    using ne unfolding uagg_def Let_def keys_cluster reopt_table_def deopt_table_def by simp
  also have "\<dots> = (\<lambda>x. reopt (take pos (drop k (deopt x)) @
      eval_agg_op \<omega> (uagg_values f {z \<in> deopt ` rel. drop k z = drop k (deopt x)}) #
      drop pos (drop k (deopt x)))) ` rel"
    unfolding image_image by (intro image_cong[OF refl]) (simp add: lookup_cluster_Some)
  also have "\<dots> = (\<lambda>x. reopt (take pos (drop k (deopt x)) @
      eval_agg_op \<omega> (agg_values f (?gr x)) # drop pos (drop k (deopt x)))) ` rel"
    by (intro image_cong[OF refl]) (simp only: grp av)
  also have "\<dots> = (\<lambda>x. take pos (drop k x) @ Some (eval_agg_op \<omega> (agg_values f (?gr x))) #
      drop pos (drop k x)) ` rel"
    by (intro image_cong[OF refl]) (simp flip: deopt_simps add: rd)
  also have "\<dots> = (if g0 \<and> Set.is_empty rel then {[Some (eval_agg_op \<omega> {})]}
      else (let groups = cluster (Some \<circ> drop k) rel in
        (\<lambda>g. case Mapping.lookup groups g of
                None \<Rightarrow> g
              | Some G \<Rightarrow> take pos g @ Some (eval_agg_op \<omega> (agg_values f G)) # drop pos g)
          ` Mapping.keys groups))"
    using False unfolding Let_def keys_cluster image_image
    by (auto simp: lookup_cluster_Some intro!: image_cong[OF refl])
  finally show ?thesis .
qed

lemma uassign1_deopt:
  assumes hf: "\<forall>a \<in> set d. a \<noteq> None" and fv: "Formula.fv_trm t \<subseteq> {i. i < length d}"
  shows "reopt (uassign1 p t (deopt d)) = take p d @ Some (meval_trm t d) # drop p d"
proof -
  have rd: "reopt (deopt d) = d" using hf by (simp add: reopt_deopt_iff)
  show ?thesis by (simp add: uassign1_def umeval_trm_deopt[OF fv] rd flip: deopt_simps)
qed

lemma umatch_table_deopt:
  assumes hf: "\<And>x. x \<in> X \<Longrightarrow> \<forall>a \<in> set x. a \<noteq> None"
    and tot: "\<And>f. f \<in> Option.these (match tms ` X) \<Longrightarrow> \<forall>c \<in> set cs. f c \<noteq> None"
  shows "reopt_table (umatch_table tms cs (deopt_table X)) = (\<lambda>f. map f cs) ` Option.these (match tms ` X)"
proof -
  have rd: "\<And>x. x \<in> X \<Longrightarrow> reopt (deopt x) = x" using hf by (simp add: reopt_deopt_iff)
  have m: "(\<lambda>x. umatch tms x) ` deopt_table X = match tms ` X"
    unfolding deopt_table_def image_image umatch_reopt by (intro image_cong[OF refl]) (simp add: rd)
  have "reopt_table (umatch_table tms cs (deopt_table X))
      = (\<lambda>f. reopt (map (\<lambda>c. the (f c)) cs)) ` Option.these (match tms ` X)"
    unfolding umatch_table_def reopt_table_def image_image[symmetric] these_map_option_image m
    by (simp add: image_image)
  also have "\<dots> = (\<lambda>f. map f cs) ` Option.these (match tms ` X)"
    using tot by (intro image_cong[OF refl]) (simp add: reopt_def comp_def)
  finally show ?thesis .
qed

definition deval_constraint :: "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow>
    event_data tuple \<Rightarrow> bool" where
  "deval_constraint conf x = ueval_constraint conf (deopt x)"

lemma deval_constraint_eq:
  "Formula.fv_trm (fst conf) \<subseteq> {i. i < length x} \<Longrightarrow>
   Formula.fv_trm (snd (snd (snd conf))) \<subseteq> {i. i < length x} \<Longrightarrow>
   deval_constraint conf x = eval_constraint conf x"
  by (simp add: deval_constraint_def ueval_constraint_deopt)

lemma deval_constraint_reopt[simp]: "deval_constraint conf (reopt x) = ueval_constraint conf x"
  by (simp add: deval_constraint_def)

(*<*)
end
(*>*)

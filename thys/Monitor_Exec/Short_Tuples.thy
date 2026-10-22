(*<*)
theory Short_Tuples
  imports "Monitor_Impl.Efficient_Instance" "Monitor_Impl.Monitor_Instance"
begin
(*>*)

section \<open>Field-reading operations on short tuples\<close>

text \<open>
  The executable operations that read a field, over tuples holding a formula's columns in
  ascending order (the kernel orders them by @{const Formula.fv_list}).
\<close>

type_synonym utable = "event_data list set"

subsection \<open>Sorted list of a table\<close>

text \<open>
  Unlike @{const csorted_list_of_set}, the wrapper is specified on infinite sets, so statements
  about a walk need no finiteness assumption.
\<close>

definition csl :: "'a :: ccompare set \<Rightarrow> 'a list" where
  "csl X = (if finite X then csorted_list_of_set X else [])"

lemma csl_finite: "finite X \<Longrightarrow> csl X = csorted_list_of_set X"
  by (simp add: csl_def)

lemma csl_infinite: "\<not> finite X \<Longrightarrow> csl X = []"
  by (simp add: csl_def)

lemma set_csl_ed: "finite (X :: event_data list set) \<Longrightarrow> set (csl X) = X"
  using ID_ccompare_etuple_dq by (simp add: csl_finite) (subst csorted_list_of_set_split, auto)

subsection \<open>Terms and assignment\<close>

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

definition uassign1 :: "nat \<Rightarrow> Formula.trm \<Rightarrow> event_data list \<Rightarrow> event_data list" where
  "uassign1 p t d = take p d @ umeval_trm t d # drop p d"

definition uassign :: "nat \<Rightarrow> Formula.trm \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "uassign p t D = uassign1 p t ` D"

fun umtrm :: "mtrm \<Rightarrow> event_data \<Rightarrow> event_data list set" where
  "umtrm (MVar v) x = {[x]}"
| "umtrm (MConst c) x = (if c = x then {[]} else {})"

subsection \<open>Match and constraint\<close>

fun umatch :: "Formula.trm list \<Rightarrow> event_data list \<Rightarrow> (nat \<rightharpoonup> event_data) option" where
  "umatch [] [] = Some Map.empty"
| "umatch (Formula.Const x # ts) (y # ys) = (if x = y then umatch ts ys else None)"
| "umatch (Formula.Var x # ts) (y # ys) = (case umatch ts ys of
      None \<Rightarrow> None
    | Some f \<Rightarrow> (case f x of
        None \<Rightarrow> Some (f(x \<mapsto> y))
      | Some z \<Rightarrow> if y = z then Some f else None))"
| "umatch _ _ = None"

definition umatch_table :: "Formula.trm list \<Rightarrow> nat list \<Rightarrow> event_data list set \<Rightarrow>
    event_data list set" where
  "umatch_table tms cs X =
     Option.these ((\<lambda>x. map_option (\<lambda>f. map (\<lambda>c. the (f c)) cs) (umatch tms x)) ` X)"

definition ueval_constraint :: "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow>
    event_data list \<Rightarrow> bool" where
  "ueval_constraint conf x = (case conf of (t1, p, c, t2) \<Rightarrow>
     eval_constraint0 c (umeval_trm t1 x) (umeval_trm t2 x) = p)"

subsection \<open>Aggregation\<close>

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

(*<*)
end
(*>*)

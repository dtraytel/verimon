(*<*)
theory Tuple_Fields
  imports "Monitor_Impl.Code_Opt"
begin
(*>*)

section \<open>The operations of the executable monitor that read a field\<close>

text \<open>
  The executable monitor keeps every table over the columns of its formula in ascending order, the
  kernel over the columns in the order of @{const Formula.fv_list}.  Most executable operations move
  fields without looking at them and are generic in the element type.  The ones below read a
  field -- the term evaluation, the match, the constraint, the assignment and the aggregation --
  and are stated here, over the short tuples, once.  Their agreement with the kernel's
  operations is proved in @{text Frame}, through the reordering that relates the two column
  orders.
\<close>

type_synonym utable = "event_data list set"

subsection \<open>The sorted list of a table\<close>

text \<open>
  The operations that walk a table walk @{const csorted_list_of_set} of it, which is unspecified
  on an infinite set.  The walks below go through this wrapper instead, which is the sorted list
  on a finite table and empty otherwise, and which the generated code computes with one
  finiteness test (constant time on a tree).  Every table the monitor handles is finite, so
  nothing changes at run time; what changes is that no statement about a walk needs a
  finiteness assumption to be well defined.
\<close>

definition csl :: "'a :: ccompare set \<Rightarrow> 'a list" where
  "csl X = (if finite X then csorted_list_of_set X else [])"

lemma csl_finite: "finite X \<Longrightarrow> csl X = csorted_list_of_set X"
  by (simp add: csl_def)

lemma csl_infinite: "\<not> finite X \<Longrightarrow> csl X = []"
  by (simp add: csl_def)

lemma ID_ccompare_ed: "ID CCOMPARE(event_data list) \<noteq> None"
  by (simp add: ccompare_list_def ccompare_event_data_def ID_def split: option.splits)

lemma set_csl_ed: "finite (X :: event_data list set) \<Longrightarrow> set (csl X) = X"
  using ID_ccompare_ed by (simp add: csl_finite) (subst csorted_list_of_set_split, auto)

subsection \<open>Term evaluation\<close>

text \<open>A term of the executable monitor is re-indexed to the positions of its tuple's fields.\<close>

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

lemma umatch_match: "umatch tms xs = match tms xs"
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

(*<*)
end
(*>*)

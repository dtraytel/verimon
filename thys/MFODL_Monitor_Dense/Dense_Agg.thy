(*<*)
theory Dense_Agg
  imports Dense_Let
begin
(*>*)

section \<open>The aggregated temporal nodes\<close>

text \<open>
  The kernel fuses an aggregation into the Since and Until nodes: for
  \<open>Agg y \<omega> tys f (Since \<phi> I \<psi>)\<close> it builds a single @{const MSince} whose @{term args} carry
  @{term "Some aggargs"}, and the node then evaluates its operands at the inner frame
  @{term "length tys + n"} while emitting tables over the aggregation's output columns.
  @{thm [source] produces_MSince} and @{thm [source] produces_MUntil} are stated for an
  arbitrary output column list, given that the node's output step @{const eval_args_agg} takes
  finite tables over the right operand's columns to finite tables over it; this section
  supplies that step for both shapes of @{term args}, the aggregated one from
  @{thm [source] ftable_eval_agg}, which the @{const MAgg} node already needed.
\<close>

lemma ftable_eval_args_agg_None:
  "args_agg args = None \<Longrightarrow> ftable kR X \<Longrightarrow> ftable kR (eval_args_agg args X)"
  by (simp add: eval_args_agg_def)

lemma ftable_eval_args_agg_Some:
  assumes agg: "args_agg args = Some aggargs"
    and g0: "aggargs_g0 aggargs \<Longrightarrow>
      shift_cols (length (aggargs_tys aggargs)) (aggargs_cols aggargs) = []"
    and f: "ftable kR X"
  shows "ftable (aggargs_y aggargs # shift_cols (length (aggargs_tys aggargs)) (aggargs_cols aggargs))
      (eval_args_agg args X)"
  using ftable_eval_agg[of X "aggargs_g0 aggargs" "aggargs_tys aggargs" "aggargs_cols aggargs"
      "aggargs_y aggargs" "aggargs_\<omega> aggargs" "aggargs_f aggargs"] f g0
  by (simp add: eval_args_agg_def agg eval_aggargs_def)

lemma produces_MSince_plain:
  fixes args :: args
  assumes p1: "produces n kL tw \<phi>" and p2: "produces n kR tw \<psi>"
    and r: "saux_inv args kL kR tw buf aux" and agg: "args_agg args = None"
    and an: "args_n args = n" and aL: "args_L args = kL" and aR: "args_R args = kR"
    and sub: "set kL \<subseteq> set kR"
  shows "produces n kR tw (MSince args \<phi> \<psi> buf aux)"
  by (rule produces_MSince[OF p1 p2 r _ an aL aR sub]) (rule ftable_eval_args_agg_None[OF agg])

lemma produces_MUntil_plain:
  fixes args :: args
  assumes p1: "produces n kL tw \<phi>" and p2: "produces n kR tw \<psi>"
    and r: "until_inv args kL kR tw t aux buf nts" and agg: "args_agg args = None"
    and an: "args_n args = n" and aL: "args_L args = kL" and aR: "args_R args = kR"
    and sub: "set kL \<subseteq> set kR"
  shows "produces n kR tw (MUntil args \<phi> \<psi> buf nts t aux)"
  by (rule produces_MUntil[OF p1 p2 r _ an aL aR sub]) (rule ftable_eval_args_agg_None[OF agg])

lemma produces_MSince_agg:
  fixes args :: args
  assumes p1: "produces m kL tw \<phi>" and p2: "produces m kR tw \<psi>"
    and r: "saux_inv args kL kR tw buf aux" and agg: "args_agg args = Some aggargs"
    and an: "args_n args = m" and aL: "args_L args = kL" and aR: "args_R args = kR"
    and sub: "set kL \<subseteq> set kR"
    and g0: "aggargs_g0 aggargs \<Longrightarrow>
      shift_cols (length (aggargs_tys aggargs)) (aggargs_cols aggargs) = []"
  shows "produces n (aggargs_y aggargs # shift_cols (length (aggargs_tys aggargs)) (aggargs_cols aggargs))
      tw (MSince args \<phi> \<psi> buf aux)"
  by (rule produces_MSince[OF p1 p2 r _ an aL aR sub]) (rule ftable_eval_args_agg_Some[OF agg g0])

lemma produces_MUntil_agg:
  fixes args :: args
  assumes p1: "produces m kL tw \<phi>" and p2: "produces m kR tw \<psi>"
    and r: "until_inv args kL kR tw t aux buf nts" and agg: "args_agg args = Some aggargs"
    and an: "args_n args = m" and aL: "args_L args = kL" and aR: "args_R args = kR"
    and sub: "set kL \<subseteq> set kR"
    and g0: "aggargs_g0 aggargs \<Longrightarrow>
      shift_cols (length (aggargs_tys aggargs)) (aggargs_cols aggargs) = []"
  shows "produces n (aggargs_y aggargs # shift_cols (length (aggargs_tys aggargs)) (aggargs_cols aggargs))
      tw (MUntil args \<phi> \<psi> buf nts t aux)"
  by (rule produces_MUntil[OF p1 p2 r _ an aL aR sub]) (rule ftable_eval_args_agg_Some[OF agg g0])

(*<*)
end
(*>*)

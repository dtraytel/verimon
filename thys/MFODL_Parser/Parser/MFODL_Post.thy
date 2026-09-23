theory MFODL_Post
  imports MFODL_Grammar.MFODL_Syntax
begin

section \<open>Post-processing\<close>

text \<open>
  MonPoly's semantic actions do more than build the syntax tree: they name
  anonymous predicate arguments, quantify them, and reject some formulas. The
  grammar's actions are pure, so these steps are a separate pass over the
  parsed formula.

  \<^descr>[Anonymous arguments] \<open>_\<close> in a predicate argument becomes a fresh
  variable \<open>_1\<close>, \<open>_2\<close>, \<dots>, numbered in textual order (MonPoly's counter
  \<^verbatim>\<open>var_cnt\<close> is incremented whenever the rule \<^verbatim>\<open>termarg: LD\<close> is reduced,
  which happens left to right). The grammar leaves the placeholder
  \<^term>\<open>TVar ''_''\<close>, which the lexer never produces for a named variable.

  \<^descr>[Existential closure] (\<^verbatim>\<open>add_ex\<close>) a predicate with arguments that are
  variables starting with \<open>_\<close> is wrapped in an existential quantifier over them.

  \<^descr>[Checks] the formula is rejected if a quantifier has no variables, if the
  predicate defined by \<open>LET\<close>, \<open>LETPAST\<close> or \<open>FRZ\<close> would be quantified by
  \<^verbatim>\<open>add_ex\<close>, or if the aggregated variable or a group-by variable of an
  aggregation is not free in the aggregated formula (\<^verbatim>\<open>MFOTL.free_vars\<close>).
\<close>

subsection \<open>Numbering anonymous arguments\<close>

fun digits_of_nat :: \<open>nat \<Rightarrow> string\<close> where
  \<open>digits_of_nat n = (if n < 10 then [char_of (48 + n)] else digits_of_nat (n div 10) @ [char_of (48 + n mod 10)])\<close>

declare digits_of_nat.simps [simp del]

definition anon_name :: \<open>nat \<Rightarrow> string\<close> where
  \<open>anon_name k = CHR ''_'' # digits_of_nat k\<close>

fun number_args :: \<open>trm list \<Rightarrow> nat \<Rightarrow> trm list \<times> nat\<close> where
  \<open>number_args [] k = ([], k)\<close>
| \<open>number_args (t # ts) k = (if t = TVar ''_''
     then (let (ts', k') = number_args ts (Suc k) in (TVar (anon_name (Suc k)) # ts', k'))
     else (let (ts', k') = number_args ts k in (t # ts', k')))\<close>

definition number_pred :: \<open>predicate \<Rightarrow> nat \<Rightarrow> predicate \<times> nat\<close> where
  \<open>number_pred p k = (let (ts, k') = number_args (snd p) k in ((fst p, ts), k'))\<close>

fun number_f :: \<open>formula \<Rightarrow> nat \<Rightarrow> formula \<times> nat\<close>
and number_r :: \<open>regex \<Rightarrow> nat \<Rightarrow> regex \<times> nat\<close> where
  \<open>number_f (FPred p) k = (let (p', k') = number_pred p k in (FPred p', k'))\<close>
| \<open>number_f (FLet p f g) k = (let (p', k1) = number_pred p k; (f', k2) = number_f f k1;
     (g', k3) = number_f g k2 in (FLet p' f' g', k3))\<close>
| \<open>number_f (FLetPast p f g) k = (let (p', k1) = number_pred p k; (f', k2) = number_f f k1;
     (g', k3) = number_f g k2 in (FLetPast p' f' g', k3))\<close>
| \<open>number_f (FFrz p f g) k = (let (p', k1) = number_pred p k; (f', k2) = number_f f k1;
     (g', k3) = number_f g k2 in (FFrz p' f' g', k3))\<close>
| \<open>number_f (FNeg f) k = (let (f', k') = number_f f k in (FNeg f', k'))\<close>
| \<open>number_f (FAnd f g) k = (let (f', k1) = number_f f k; (g', k2) = number_f g k1 in (FAnd f' g', k2))\<close>
| \<open>number_f (FOr f g) k = (let (f', k1) = number_f f k; (g', k2) = number_f g k1 in (FOr f' g', k2))\<close>
| \<open>number_f (FImplies f g) k = (let (f', k1) = number_f f k; (g', k2) = number_f g k1 in (FImplies f' g', k2))\<close>
| \<open>number_f (FEquiv f g) k = (let (f', k1) = number_f f k; (g', k2) = number_f g k1 in (FEquiv f' g', k2))\<close>
| \<open>number_f (FExists vs f) k = (let (f', k') = number_f f k in (FExists vs f', k'))\<close>
| \<open>number_f (FForAll vs f) k = (let (f', k') = number_f f k in (FForAll vs f', k'))\<close>
| \<open>number_f (FAggreg y op x g f) k = (let (f', k') = number_f f k in (FAggreg y op x g f', k'))\<close>
| \<open>number_f (FPrev i f) k = (let (f', k') = number_f f k in (FPrev i f', k'))\<close>
| \<open>number_f (FNext i f) k = (let (f', k') = number_f f k in (FNext i f', k'))\<close>
| \<open>number_f (FEventually i f) k = (let (f', k') = number_f f k in (FEventually i f', k'))\<close>
| \<open>number_f (FOnce i f) k = (let (f', k') = number_f f k in (FOnce i f', k'))\<close>
| \<open>number_f (FAlways i f) k = (let (f', k') = number_f f k in (FAlways i f', k'))\<close>
| \<open>number_f (FPastAlways i f) k = (let (f', k') = number_f f k in (FPastAlways i f', k'))\<close>
| \<open>number_f (FSince i f g) k = (let (f', k1) = number_f f k; (g', k2) = number_f g k1 in (FSince i f' g', k2))\<close>
| \<open>number_f (FTrigger i f g) k = (let (f', k1) = number_f f k; (g', k2) = number_f g k1 in (FTrigger i f' g', k2))\<close>
| \<open>number_f (FUntil i f g) k = (let (f', k1) = number_f f k; (g', k2) = number_f g k1 in (FUntil i f' g', k2))\<close>
| \<open>number_f (FRelease i f g) k = (let (f', k1) = number_f f k; (g', k2) = number_f g k1 in (FRelease i f' g', k2))\<close>
| \<open>number_f (FFrex i r) k = (let (r', k') = number_r r k in (FFrex i r', k'))\<close>
| \<open>number_f (FPrex i r) k = (let (r', k') = number_r r k in (FPrex i r', k'))\<close>
| \<open>number_f f k = (f, k)\<close>
| \<open>number_r (RTest f) k = (let (f', k') = number_f f k in (RTest f', k'))\<close>
| \<open>number_r (RConcat r s) k = (let (r', k1) = number_r r k; (s', k2) = number_r s k1 in (RConcat r' s', k2))\<close>
| \<open>number_r (RPlus r s) k = (let (r', k1) = number_r r k; (s', k2) = number_r s k1 in (RPlus r' s', k2))\<close>
| \<open>number_r (RStar r) k = (let (r', k') = number_r r k in (RStar r', k'))\<close>
| \<open>number_r r k = (r, k)\<close>

subsection \<open>Existential closure of predicates\<close>

definition is_anon :: \<open>string \<Rightarrow> bool\<close> where
  \<open>is_anon v = (case v of c # _ \<Rightarrow> c = CHR ''_'' | [] \<Rightarrow> False)\<close>

text \<open>The variables starting with \<open>_\<close> among the arguments, with repetitions.\<close>

definition anon_vars :: \<open>predicate \<Rightarrow> string list\<close> where
  \<open>anon_vars p = concat (map (\<lambda>t. case t of TVar v \<Rightarrow> if is_anon v then [v] else [] | _ \<Rightarrow> []) (snd p))\<close>

fun add_ex_f :: \<open>formula \<Rightarrow> formula\<close>
and add_ex_r :: \<open>regex \<Rightarrow> regex\<close> where
  \<open>add_ex_f (FPred p) = (if anon_vars p = [] then FPred p else FExists (anon_vars p) (FPred p))\<close>
| \<open>add_ex_f (FLet p f g) = FLet p (add_ex_f f) (add_ex_f g)\<close>
| \<open>add_ex_f (FLetPast p f g) = FLetPast p (add_ex_f f) (add_ex_f g)\<close>
| \<open>add_ex_f (FFrz p f g) = FFrz p (add_ex_f f) (add_ex_f g)\<close>
| \<open>add_ex_f (FNeg f) = FNeg (add_ex_f f)\<close>
| \<open>add_ex_f (FAnd f g) = FAnd (add_ex_f f) (add_ex_f g)\<close>
| \<open>add_ex_f (FOr f g) = FOr (add_ex_f f) (add_ex_f g)\<close>
| \<open>add_ex_f (FImplies f g) = FImplies (add_ex_f f) (add_ex_f g)\<close>
| \<open>add_ex_f (FEquiv f g) = FEquiv (add_ex_f f) (add_ex_f g)\<close>
| \<open>add_ex_f (FExists vs f) = FExists vs (add_ex_f f)\<close>
| \<open>add_ex_f (FForAll vs f) = FForAll vs (add_ex_f f)\<close>
| \<open>add_ex_f (FAggreg y op x g f) = FAggreg y op x g (add_ex_f f)\<close>
| \<open>add_ex_f (FPrev i f) = FPrev i (add_ex_f f)\<close>
| \<open>add_ex_f (FNext i f) = FNext i (add_ex_f f)\<close>
| \<open>add_ex_f (FEventually i f) = FEventually i (add_ex_f f)\<close>
| \<open>add_ex_f (FOnce i f) = FOnce i (add_ex_f f)\<close>
| \<open>add_ex_f (FAlways i f) = FAlways i (add_ex_f f)\<close>
| \<open>add_ex_f (FPastAlways i f) = FPastAlways i (add_ex_f f)\<close>
| \<open>add_ex_f (FSince i f g) = FSince i (add_ex_f f) (add_ex_f g)\<close>
| \<open>add_ex_f (FTrigger i f g) = FTrigger i (add_ex_f f) (add_ex_f g)\<close>
| \<open>add_ex_f (FUntil i f g) = FUntil i (add_ex_f f) (add_ex_f g)\<close>
| \<open>add_ex_f (FRelease i f g) = FRelease i (add_ex_f f) (add_ex_f g)\<close>
| \<open>add_ex_f (FFrex i r) = FFrex i (add_ex_r r)\<close>
| \<open>add_ex_f (FPrex i r) = FPrex i (add_ex_r r)\<close>
| \<open>add_ex_f f = f\<close>
| \<open>add_ex_r (RTest f) = RTest (add_ex_f f)\<close>
| \<open>add_ex_r (RConcat r s) = RConcat (add_ex_r r) (add_ex_r s)\<close>
| \<open>add_ex_r (RPlus r s) = RPlus (add_ex_r r) (add_ex_r s)\<close>
| \<open>add_ex_r (RStar r) = RStar (add_ex_r r)\<close>
| \<open>add_ex_r r = r\<close>

subsection \<open>Checks\<close>

text \<open>Variables of terms (\<^verbatim>\<open>Predicate.tvars\<close>) and free variables of formulas
  (\<^verbatim>\<open>MFOTL.free_vars\<close>), as lists; only membership is tested. A predicate
  contributes only its arguments that are variables (\<^verbatim>\<open>Predicate.pvars\<close>).\<close>

fun tvars :: \<open>trm \<Rightarrow> string list\<close> where
  \<open>tvars (TVar v) = [v]\<close>
| \<open>tvars (TCst _) = []\<close>
| \<open>tvars (TF2i t) = tvars t\<close> | \<open>tvars (TI2f t) = tvars t\<close> | \<open>tvars (TI2s t) = tvars t\<close>
| \<open>tvars (TS2i t) = tvars t\<close> | \<open>tvars (TF2s t) = tvars t\<close> | \<open>tvars (TS2f t) = tvars t\<close>
| \<open>tvars (TDayOfMonth t) = tvars t\<close> | \<open>tvars (TMonth t) = tvars t\<close> | \<open>tvars (TYear t) = tvars t\<close>
| \<open>tvars (TFormatDate t) = tvars t\<close> | \<open>tvars (TR2s t) = tvars t\<close> | \<open>tvars (TS2r t) = tvars t\<close>
| \<open>tvars (TUMinus t) = tvars t\<close>
| \<open>tvars (TPlus t u) = tvars t @ tvars u\<close> | \<open>tvars (TMinus t u) = tvars t @ tvars u\<close>
| \<open>tvars (TMult t u) = tvars t @ tvars u\<close> | \<open>tvars (TDiv t u) = tvars t @ tvars u\<close>
| \<open>tvars (TMod t u) = tvars t @ tvars u\<close>

definition pvars :: \<open>predicate \<Rightarrow> string list\<close> where
  \<open>pvars p = concat (map (\<lambda>t. case t of TVar v \<Rightarrow> [v] | _ \<Rightarrow> []) (snd p))\<close>

fun fv_f :: \<open>formula \<Rightarrow> string list\<close>
and fv_r :: \<open>regex \<Rightarrow> string list\<close> where
  \<open>fv_f (FEqual t u) = tvars t @ tvars u\<close>
| \<open>fv_f (FLess t u) = tvars t @ tvars u\<close>
| \<open>fv_f (FLessEq t u) = tvars t @ tvars u\<close>
| \<open>fv_f (FSubstring t u) = tvars t @ tvars u\<close>
| \<open>fv_f (FMatches t u ts) = tvars t @ tvars u @ concat (map tvars (List.map_filter id ts))\<close>
| \<open>fv_f (FPred p) = pvars p\<close>
| \<open>fv_f (FLet _ _ g) = fv_f g\<close>
| \<open>fv_f (FLetPast _ _ g) = fv_f g\<close>
| \<open>fv_f (FFrz _ _ g) = fv_f g\<close>
| \<open>fv_f (FNeg f) = fv_f f\<close>
| \<open>fv_f (FAnd f g) = fv_f f @ fv_f g\<close>
| \<open>fv_f (FOr f g) = fv_f f @ fv_f g\<close>
| \<open>fv_f (FImplies f g) = fv_f f @ fv_f g\<close>
| \<open>fv_f (FEquiv f g) = fv_f f @ fv_f g\<close>
| \<open>fv_f (FExists vs f) = filter (\<lambda>v. v \<notin> set vs) (fv_f f)\<close>
| \<open>fv_f (FForAll vs f) = filter (\<lambda>v. v \<notin> set vs) (fv_f f)\<close>
| \<open>fv_f (FAggreg y _ _ g _) = y # g\<close>
| \<open>fv_f (FPrev _ f) = fv_f f\<close>
| \<open>fv_f (FNext _ f) = fv_f f\<close>
| \<open>fv_f (FEventually _ f) = fv_f f\<close>
| \<open>fv_f (FOnce _ f) = fv_f f\<close>
| \<open>fv_f (FAlways _ f) = fv_f f\<close>
| \<open>fv_f (FPastAlways _ f) = fv_f f\<close>
| \<open>fv_f (FSince _ f g) = fv_f f @ fv_f g\<close>
| \<open>fv_f (FTrigger _ f g) = fv_f f @ fv_f g\<close>
| \<open>fv_f (FUntil _ f g) = fv_f f @ fv_f g\<close>
| \<open>fv_f (FRelease _ f g) = fv_f f @ fv_f g\<close>
| \<open>fv_f (FFrex _ r) = fv_r r\<close>
| \<open>fv_f (FPrex _ r) = fv_r r\<close>
| \<open>fv_r (RSkip _) = []\<close>
| \<open>fv_r (RTest f) = fv_f f\<close>
| \<open>fv_r (RConcat r s) = fv_r r @ fv_r s\<close>
| \<open>fv_r (RPlus r s) = fv_r r @ fv_r s\<close>
| \<open>fv_r (RStar r) = fv_r r\<close>

definition def_ok :: \<open>predicate \<Rightarrow> bool\<close> where
  \<open>def_ok p = (anon_vars p = [])\<close>

fun ok_f :: \<open>formula \<Rightarrow> bool\<close>
and ok_r :: \<open>regex \<Rightarrow> bool\<close> where
  \<open>ok_f (FLet p f g) = (def_ok p \<and> ok_f f \<and> ok_f g)\<close>
| \<open>ok_f (FLetPast p f g) = (def_ok p \<and> ok_f f \<and> ok_f g)\<close>
| \<open>ok_f (FFrz p f g) = (def_ok p \<and> ok_f f \<and> ok_f g)\<close>
| \<open>ok_f (FNeg f) = ok_f f\<close>
| \<open>ok_f (FAnd f g) = (ok_f f \<and> ok_f g)\<close>
| \<open>ok_f (FOr f g) = (ok_f f \<and> ok_f g)\<close>
| \<open>ok_f (FImplies f g) = (ok_f f \<and> ok_f g)\<close>
| \<open>ok_f (FEquiv f g) = (ok_f f \<and> ok_f g)\<close>
| \<open>ok_f (FExists vs f) = (vs \<noteq> [] \<and> ok_f f)\<close>
| \<open>ok_f (FForAll vs f) = (vs \<noteq> [] \<and> ok_f f)\<close>
| \<open>ok_f (FAggreg y op x g f) = (x \<in> set (fv_f f) \<and> set g \<subseteq> set (fv_f f) \<and> ok_f f)\<close>
| \<open>ok_f (FPrev _ f) = ok_f f\<close>
| \<open>ok_f (FNext _ f) = ok_f f\<close>
| \<open>ok_f (FEventually _ f) = ok_f f\<close>
| \<open>ok_f (FOnce _ f) = ok_f f\<close>
| \<open>ok_f (FAlways _ f) = ok_f f\<close>
| \<open>ok_f (FPastAlways _ f) = ok_f f\<close>
| \<open>ok_f (FSince _ f g) = (ok_f f \<and> ok_f g)\<close>
| \<open>ok_f (FTrigger _ f g) = (ok_f f \<and> ok_f g)\<close>
| \<open>ok_f (FUntil _ f g) = (ok_f f \<and> ok_f g)\<close>
| \<open>ok_f (FRelease _ f g) = (ok_f f \<and> ok_f g)\<close>
| \<open>ok_f (FFrex _ r) = ok_r r\<close>
| \<open>ok_f (FPrex _ r) = ok_r r\<close>
| \<open>ok_f _ = True\<close>
| \<open>ok_r (RTest f) = ok_f f\<close>
| \<open>ok_r (RConcat r s) = (ok_r r \<and> ok_r s)\<close>
| \<open>ok_r (RPlus r s) = (ok_r r \<and> ok_r s)\<close>
| \<open>ok_r (RStar r) = ok_r r\<close>
| \<open>ok_r _ = True\<close>

definition postprocess :: \<open>formula \<Rightarrow> formula option\<close> where
  \<open>postprocess f = (let g = add_ex_f (fst (number_f f 0)) in if ok_f g then Some g else None)\<close>

end

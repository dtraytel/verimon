(*<*)
theory Surface_Conversion
  imports "MFODL_Logic.Typing" "MFODL_Syntax.String_Escape" "MFODL_Syntax.Byte_String" "MFODL_Syntax.Surface_Postprocessing"
begin
(*>*)

section \<open>Strings\<close>

text \<open>The monitor's strings are @{typ string8}; @{text str8_of_string} converts the
  characters of the formula and of the signature into one. The code implements it by OCaml's
  strings of bytes (theory @{text CLI_Export}).\<close>

definition str8_of_string :: "string \<Rightarrow> string8" where
  "str8_of_string = Abs_string8"

lemma Rep_str8_of_string[simp]: "Rep_string8 (str8_of_string s) = s"
  by (simp add: str8_of_string_def Abs_string8_inverse)

lemma str8_of_string_inject[simp]: "str8_of_string s = str8_of_string t \<longleftrightarrow> s = t"
  by (metis Rep_str8_of_string)

section \<open>From the parsed formula to the monitor's formula\<close>

text \<open>
  The parser (session @{text MFODL_Parser}) produces MonPoly's syntax tree, with named variables
  and MonPoly's derived operators. The monitor reads formulas over de Bruijn indices
  (@{typ "tysym Formula.formula"}). This theory converts the one into the other as MonPoly's
  front end does for @{text "-verified"} (\<^verbatim>\<open>Verified_adapter.convert_formula\<close>):

  \<^item> The free variables are numbered in the order of MonPoly's @{text MFOTL.free_vars}
    (@{text mp_fv}), which is also the order of the columns MonPoly prints. A bound variable is
    numbered by its distance to its quantifier, the free ones after all bound ones.
  \<^item> @{text tp}, @{text ts} and @{text tpts} become the operators @{const Formula.TP} and
    @{const Formula.TS}, unless a @{text LET} binds the predicate.
  \<^item> The derived operators are expanded: implication, equivalence, universal quantification,
    the unary temporal operators, and the variables of a quantifier one at a time.
  \<^item> An aggregation binds the variables of the aggregated formula that are not grouped.
  \<^item> An interval of the input is converted into the monitor's (@{text conv_intv}).

  With rewriting (the default, @{text "-no_rw"} disables it), MonPoly's front end first eliminates
  the syntactic sugar (@{text Rewriting.normalize_syntax}), which also replaces @{text ALWAYS}
  and @{text PAST_ALWAYS} by @{text RELEASE} and @{text TRIGGER} with a false left operand and
  drops unused quantified variables; @{text elim_sugar} does the same. Its folding of ground
  terms is done on the converted formula by the monitor's own evaluation of terms
  (@{text fold_ground}), and so preserves its semantics (@{text sat_fold_ground}).

  The conversion differs from MonPoly's in one respect: without rewriting, MonPoly converts the
  equivalence of @{text \<phi>} and @{text \<psi>} into
  @{text "(\<phi> IMPLIES \<psi>) AND (\<psi> IMPLIES \<psi>)"}; here it is the equivalence.
\<close>

subsection \<open>Free variables in MonPoly's order\<close>

text \<open>@{text Misc.union}: the first list, then the elements of the second that are not in it.\<close>

definition mp_union :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "mp_union xs ys = xs @ filter (\<lambda>y. y \<notin> set xs) ys"

lemma set_mp_union[simp]: "set (mp_union xs ys) = set xs \<union> set ys"
  by (auto simp: mp_union_def)

text \<open>The first occurrence of each element, in order.\<close>

definition dedup :: "'a list \<Rightarrow> 'a list" where
  "dedup xs = rev (remdups (rev xs))"

lemma set_dedup[simp]: "set (dedup xs) = set xs"
  by (simp add: dedup_def)

lemma distinct_dedup[simp]: "distinct (dedup xs)"
  by (simp add: dedup_def)

text \<open>@{text Predicate.pvars}: the variables among the arguments, each once.\<close>

definition mp_pvars :: "predicate \<Rightarrow> string list" where
  "mp_pvars p = dedup (pvars p)"

fun mp_fv :: "formula \<Rightarrow> string list"
and mp_fv_r :: "regex \<Rightarrow> string list" where
  "mp_fv (FEqual t u) = mp_union (tvars t) (tvars u)"
| "mp_fv (FLess t u) = mp_union (tvars t) (tvars u)"
| "mp_fv (FLessEq t u) = mp_union (tvars t) (tvars u)"
| "mp_fv (FSubstring t u) = mp_union (tvars t) (tvars u)"
| "mp_fv (FMatches t u ts) = fold (\<lambda>t s. case t of None \<Rightarrow> s | Some t \<Rightarrow> mp_union s (tvars t)) ts
     (mp_union (tvars t) (tvars u))"
| "mp_fv (FPred p) = mp_pvars p"
| "mp_fv (FLet _ _ g) = mp_fv g"
| "mp_fv (FLetPast _ _ g) = mp_fv g"
| "mp_fv (FFrz _ _ g) = mp_fv g"
| "mp_fv (FNeg f) = mp_fv f"
| "mp_fv (FAnd f g) = mp_union (mp_fv f) (mp_fv g)"
| "mp_fv (FOr f g) = mp_union (mp_fv f) (mp_fv g)"
| "mp_fv (FImplies f g) = mp_union (mp_fv f) (mp_fv g)"
| "mp_fv (FEquiv f g) = mp_union (mp_fv f) (mp_fv g)"
| "mp_fv (FExists vs f) = filter (\<lambda>v. v \<notin> set vs) (mp_fv f)"
| "mp_fv (FForAll vs f) = filter (\<lambda>v. v \<notin> set vs) (mp_fv f)"
| "mp_fv (FAggreg y _ _ g _) = y # g"
| "mp_fv (FPrev _ f) = mp_fv f"
| "mp_fv (FNext _ f) = mp_fv f"
| "mp_fv (FEventually _ f) = mp_fv f"
| "mp_fv (FOnce _ f) = mp_fv f"
| "mp_fv (FAlways _ f) = mp_fv f"
| "mp_fv (FPastAlways _ f) = mp_fv f"
| "mp_fv (FSince _ f g) = mp_union (mp_fv g) (mp_fv f)"
| "mp_fv (FTrigger _ f g) = mp_union (mp_fv g) (mp_fv f)"
| "mp_fv (FUntil _ f g) = mp_union (mp_fv g) (mp_fv f)"
| "mp_fv (FRelease _ f g) = mp_union (mp_fv g) (mp_fv f)"
| "mp_fv (FFrex _ r) = mp_fv_r r"
| "mp_fv (FPrex _ r) = mp_fv_r r"
| "mp_fv_r (RSkip _) = []"
| "mp_fv_r (RTest f) = mp_fv f"
| "mp_fv_r (RConcat r s) = mp_union (mp_fv_r r) (mp_fv_r s)"
| "mp_fv_r (RPlus r s) = mp_union (mp_fv_r r) (mp_fv_r s)"
| "mp_fv_r (RStar r) = mp_fv_r r"

text \<open>The free variables in the order of the output: those of MonPoly's list, each once (MonPoly's
  list may repeat a variable that occurs twice in a term).\<close>

definition out_vars :: "formula \<Rightarrow> string list" where
  "out_vars f = dedup (mp_fv f)"

subsection \<open>Eliminating the syntactic sugar\<close>

text \<open>@{text Rewriting.elim_syntactic_sugar}, as MonPoly's front end applies it for the verified
  monitor.\<close>

definition ffalse :: formula where
  "ffalse = FNeg (FEqual (TCst (CStr ''x'')) (TCst (CStr ''x'')))"

definition ex_used :: "string list \<Rightarrow> formula \<Rightarrow> formula" where
  "ex_used vs f = (let vs' = filter (\<lambda>v. v \<in> set (mp_fv f)) vs in if vs' = [] then f else FExists vs' f)"

fun elim_sugar :: "formula \<Rightarrow> formula"
and elim_sugar_r :: "regex \<Rightarrow> regex" where
  "elim_sugar (FLet p f g) = FLet p (elim_sugar f) (elim_sugar g)"
| "elim_sugar (FLetPast p f g) = FLetPast p (elim_sugar f) (elim_sugar g)"
| "elim_sugar (FFrz p f g) = FFrz p (elim_sugar f) (elim_sugar g)"
| "elim_sugar (FNeg f) = FNeg (elim_sugar f)"
| "elim_sugar (FAnd f g) = FAnd (elim_sugar f) (elim_sugar g)"
| "elim_sugar (FOr f g) = FOr (elim_sugar f) (elim_sugar g)"
| "elim_sugar (FExists vs f) = ex_used vs (elim_sugar f)"
| "elim_sugar (FImplies f g) = FOr (FNeg (elim_sugar f)) (elim_sugar g)"
| "elim_sugar (FEquiv f g) = FAnd (FOr (FNeg (elim_sugar f)) (elim_sugar g)) (FOr (elim_sugar f) (FNeg (elim_sugar g)))"
| "elim_sugar (FForAll vs f) = FNeg (ex_used vs (FNeg (elim_sugar f)))"
| "elim_sugar (FAggreg y op x g f) = FAggreg y op x g (elim_sugar f)"
| "elim_sugar (FPrev i f) = FPrev i (elim_sugar f)"
| "elim_sugar (FNext i f) = FNext i (elim_sugar f)"
| "elim_sugar (FEventually i f) = FEventually i (elim_sugar f)"
| "elim_sugar (FOnce i f) = FOnce i (elim_sugar f)"
| "elim_sugar (FAlways i f) = FRelease i ffalse (elim_sugar f)"
| "elim_sugar (FPastAlways i f) = FTrigger i ffalse (elim_sugar f)"
| "elim_sugar (FSince i f g) = FSince i (elim_sugar f) (elim_sugar g)"
| "elim_sugar (FUntil i f g) = FUntil i (elim_sugar f) (elim_sugar g)"
| "elim_sugar (FTrigger i f g) = FTrigger i (elim_sugar f) (elim_sugar g)"
| "elim_sugar (FRelease i f g) = FRelease i (elim_sugar f) (elim_sugar g)"
| "elim_sugar (FFrex i r) = FFrex i (elim_sugar_r r)"
| "elim_sugar (FPrex i r) = FPrex i (elim_sugar_r r)"
| "elim_sugar f = f"
| "elim_sugar_r (RTest f) = RTest (elim_sugar f)"
| "elim_sugar_r (RConcat r s) = RConcat (elim_sugar_r r) (elim_sugar_r s)"
| "elim_sugar_r (RPlus r s) = RPlus (elim_sugar_r r) (elim_sugar_r s)"
| "elim_sugar_r (RStar r) = RStar (elim_sugar_r r)"
| "elim_sugar_r r = r"

subsection \<open>Messages\<close>

text \<open>The parts of the formula that the verified monitor does not support are reported as
  MonPoly's front end reports them: by the exception @{text UnsupportedFragment} of its
  conversion, which ends the program.\<close>

definition unsupported :: "string \<Rightarrow> string" where
  "unsupported msg = ''Fatal error: exception Libmonpoly.Verified_adapter.UnsupportedFragment('' @
     CHR 0x22 # escaped msg @ CHR 0x22 # '')''"

definition string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i = (if i < 0 then CHR ''-'' # digits_of_nat (nat (- i)) else digits_of_nat (nat i))"

fun string_of_cst :: "cst \<Rightarrow> string" where
  "string_of_cst (CInt i) = string_of_int i"
| "string_of_cst (CStr s) = CHR 0x22 # s @ [CHR 0x22]"
| "string_of_cst (CFloat s) = s"
| "string_of_cst (CRegexp s) = CHR ''r'' # CHR 0x22 # s @ [CHR 0x22]"

text \<open>@{text Predicate.string_of_term}: parentheses around the operands that are not variables or
  constants.\<close>

definition paren :: "bool \<Rightarrow> string \<Rightarrow> string" where
  "paren b s = (if b then s else ''('' @ s @ '')'')"

primrec t2s :: "trm \<Rightarrow> bool \<Rightarrow> string" where
  "t2s (TVar v) b = v"
| "t2s (TCst c) b = string_of_cst c"
| "t2s (TF2i u) b = paren b (''f2i('' @ t2s u True @ '')'')"
| "t2s (TI2f u) b = paren b (''i2f('' @ t2s u True @ '')'')"
| "t2s (TI2s u) b = paren b (''i2s('' @ t2s u True @ '')'')"
| "t2s (TS2i u) b = paren b (''s2i('' @ t2s u True @ '')'')"
| "t2s (TF2s u) b = paren b (''f2s('' @ t2s u True @ '')'')"
| "t2s (TS2f u) b = paren b (''s2f('' @ t2s u True @ '')'')"
| "t2s (TDayOfMonth u) b = paren b (''DAY_OF_MONTH('' @ t2s u True @ '')'')"
| "t2s (TMonth u) b = paren b (''MONTH('' @ t2s u True @ '')'')"
| "t2s (TYear u) b = paren b (''YEAR('' @ t2s u True @ '')'')"
| "t2s (TFormatDate u) b = paren b (''FORMAT_DATE('' @ t2s u True @ '')'')"
| "t2s (TR2s u) b = paren b (''r2s('' @ t2s u True @ '')'')"
| "t2s (TS2r u) b = paren b (''s2r('' @ t2s u True @ '')'')"
| "t2s (TPlus u v) b = paren b (t2s u False @ '' + '' @ t2s v False)"
| "t2s (TMinus u v) b = paren b (t2s u False @ '' - '' @ t2s v False)"
| "t2s (TUMinus u) b = paren b (''-'' @ t2s u False)"
| "t2s (TMult u v) b = paren b (t2s u False @ '' * '' @ t2s v False)"
| "t2s (TDiv u v) b = paren b (t2s u False @ '' / '' @ t2s v False)"
| "t2s (TMod u v) b = paren b (t2s u False @ '' mod '' @ t2s v False)"
definition string_of_term :: "trm \<Rightarrow> string" where
  "string_of_term t = t2s t True"

text \<open>@{text MFOTL.string_of_opt_term}, and @{text Misc.string_of_list_ext}'s separators.\<close>

definition string_of_opt_term :: "trm option \<Rightarrow> string" where
  "string_of_opt_term t = (case t of None \<Rightarrow> ''_'' | Some u \<Rightarrow> string_of_term u)"

fun between_list :: "string \<Rightarrow> string list \<Rightarrow> string list" where
  "between_list s [] = []"
| "between_list s [x] = [x]"
| "between_list s (x # y # zs) = x # s # between_list s (y # zs)"

fun string_of_bound_l :: "bound \<Rightarrow> string" where
  "string_of_bound_l (OBnd a) = ''('' @ string_of_int a @ '',''"
| "string_of_bound_l (CBnd a) = ''['' @ string_of_int a @ '',''"
| "string_of_bound_l BInf = ''(*,''"

fun string_of_bound_r :: "bound \<Rightarrow> string" where
  "string_of_bound_r (OBnd a) = string_of_int a @ '')''"
| "string_of_bound_r (CBnd a) = string_of_int a @ '']''"
| "string_of_bound_r BInf = ''*)''"

definition string_of_interval :: "interval \<Rightarrow> string" where
  "string_of_interval i = string_of_bound_l (fst i) @ string_of_bound_r (snd i)"

subsection \<open>Terms and intervals\<close>

text \<open>The index of a variable: its position among the bound variables, innermost first, or the
  number of bound variables plus its position among the free variables
  (@{text Verified_adapter.convert_var}).\<close>

definition pos_of :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "pos_of xs a = length (takeWhile (\<lambda>x. x \<noteq> a) xs)"

definition var_idx :: "string list \<Rightarrow> string list \<Rightarrow> string \<Rightarrow> nat" where
  "var_idx fvl bvl a = (if a \<in> set bvl then pos_of bvl a else length bvl + pos_of fvl a)"

text \<open>The reader of floating point numbers is a parameter, as for the log: the front end passes
  OCaml's @{text float_of_string_opt}, which MonPoly's lexer also uses.\<close>

definition bytes_of_string :: "string \<Rightarrow> bytes" where
  "bytes_of_string = Abs_bytes"

fun conv_cst :: "(bytes \<Rightarrow> double option) \<Rightarrow> cst \<Rightarrow> string + event_data" where
  "conv_cst pf (CInt i) = Inr (EInt (integer_of_int i))"
| "conv_cst pf (CStr s) = Inr (EString (str8_of_string s))"
| "conv_cst pf (CFloat s) = (case pf (bytes_of_string s) of
     Some d \<Rightarrow> Inr (EFloat d)
   | None \<Rightarrow> Inl (unsupported (''Unsupported float constant '' @ s)))"
| "conv_cst pf (CRegexp s) = Inl (unsupported ''Regular expression constant are not supported'')"

fun conv_trm :: "(bytes \<Rightarrow> double option) \<Rightarrow> string list \<Rightarrow> string list \<Rightarrow> trm \<Rightarrow> string + Formula.trm" where
  "conv_trm pf fvl bvl (TVar a) = Inr (Formula.Var (var_idx fvl bvl a))"
| "conv_trm pf fvl bvl (TCst c) = map_sum id Formula.Const (conv_cst pf c)"
| "conv_trm pf fvl bvl (TF2i t) = map_sum id Formula.F2i (conv_trm pf fvl bvl t)"
| "conv_trm pf fvl bvl (TI2f t) = map_sum id Formula.I2f (conv_trm pf fvl bvl t)"
| "conv_trm pf fvl bvl (TUMinus t) = map_sum id Formula.UMinus (conv_trm pf fvl bvl t)"
| "conv_trm pf fvl bvl (TPlus t u) = (case conv_trm pf fvl bvl t of Inl e \<Rightarrow> Inl e
     | Inr a \<Rightarrow> map_sum id (Formula.Plus a) (conv_trm pf fvl bvl u))"
| "conv_trm pf fvl bvl (TMinus t u) = (case conv_trm pf fvl bvl t of Inl e \<Rightarrow> Inl e
     | Inr a \<Rightarrow> map_sum id (Formula.Minus a) (conv_trm pf fvl bvl u))"
| "conv_trm pf fvl bvl (TMult t u) = (case conv_trm pf fvl bvl t of Inl e \<Rightarrow> Inl e
     | Inr a \<Rightarrow> map_sum id (Formula.Mult a) (conv_trm pf fvl bvl u))"
| "conv_trm pf fvl bvl (TDiv t u) = (case conv_trm pf fvl bvl t of Inl e \<Rightarrow> Inl e
     | Inr a \<Rightarrow> map_sum id (Formula.Div a) (conv_trm pf fvl bvl u))"
| "conv_trm pf fvl bvl (TMod t u) = (case conv_trm pf fvl bvl t of Inl e \<Rightarrow> Inl e
     | Inr a \<Rightarrow> map_sum id (Formula.Mod a) (conv_trm pf fvl bvl u))"
| "conv_trm pf fvl bvl t = Inl (unsupported (''Unsupported term '' @ string_of_term t))"

fun conv_trms :: "(bytes \<Rightarrow> double option) \<Rightarrow> string list \<Rightarrow> string list \<Rightarrow> trm list \<Rightarrow> string + Formula.trm list" where
  "conv_trms pf fvl bvl [] = Inr []"
| "conv_trms pf fvl bvl (t # ts) = (case conv_trm pf fvl bvl t of Inl e \<Rightarrow> Inl e
     | Inr a \<Rightarrow> map_sum id (Cons a) (conv_trms pf fvl bvl ts))"

text \<open>An interval of the input, with integer bounds, closed or open or unbounded, as the
  monitor's interval of natural numbers (@{text Verified_adapter.convert_interval}). A
  negative bound counts as zero.\<close>

definition conv_intv :: "interval \<Rightarrow> string + \<I>" where
  "conv_intv i = (let err = Inl (unsupported (''Unsupported interval '' @ string_of_interval i)) in
     case fst i of BInf \<Rightarrow> err | _ \<Rightarrow>
     let l = (case fst i of OBnd a \<Rightarrow> a + 1 | CBnd a \<Rightarrow> a | BInf \<Rightarrow> 0) in
     (case snd i of
       BInf \<Rightarrow> Inr (interval (nat l) \<infinity>)
     | b \<Rightarrow> let r = (case b of OBnd a \<Rightarrow> a - 1 | CBnd a \<Rightarrow> a | BInf \<Rightarrow> 0) in
         if l \<le> r then Inr (interval (nat l) (enat (nat r))) else err))"

fun conv_agg_op :: "agg_op \<Rightarrow> Formula.agg_type" where
  "conv_agg_op ACnt = Formula.Agg_Cnt"
| "conv_agg_op AMin = Formula.Agg_Min"
| "conv_agg_op AMax = Formula.Agg_Max"
| "conv_agg_op ASum = Formula.Agg_Sum"
| "conv_agg_op AAvg = Formula.Agg_Avg"
| "conv_agg_op AMed = Formula.Agg_Med"

subsection \<open>Formulas\<close>

text \<open>The conversion threads a counter for the type variables of the quantified variables and of
  the aggregations; the first ones are those of the free variables
  (@{text Verified_adapter.convert_formula}).\<close>

type_synonym 'a conv = "nat \<Rightarrow> string + 'a \<times> nat"

definition cbind :: "'a conv \<Rightarrow> ('a \<Rightarrow> 'b conv) \<Rightarrow> 'b conv" where
  "cbind m f k = (case m k of Inl e \<Rightarrow> Inl e | Inr (a, k') \<Rightarrow> f a k')"

definition cret :: "'a \<Rightarrow> 'a conv" where
  "cret a k = Inr (a, k)"

definition clift :: "string + 'a \<Rightarrow> 'a conv" where
  "clift x k = map_sum id (\<lambda>a. (a, k)) x"

lemma cbind_cong[fundef_cong]:
  "m k = m' k \<Longrightarrow> (\<And>a k'. m k = Inr (a, k') \<Longrightarrow> f a k' = f' a k') \<Longrightarrow> cbind m f k = cbind m' f' k"
  by (auto simp: cbind_def split: sum.splits)

adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> cbind

text \<open>Fresh type variables.\<close>

definition fresh_ty :: "tysym conv" where
  "fresh_ty k = Inr (TAny k, Suc k)"

fun ex_wrap :: "nat \<Rightarrow> tysym Formula.formula \<Rightarrow> tysym Formula.formula conv" where
  "ex_wrap 0 f = cret f"
| "ex_wrap (Suc n) f = do { t \<leftarrow> fresh_ty; ex_wrap n (Formula.Exists t f) }"

fun fresh_tys :: "nat \<Rightarrow> tysym list conv" where
  "fresh_tys 0 = cret []"
| "fresh_tys (Suc n) = do { t \<leftarrow> fresh_ty; ts \<leftarrow> fresh_tys n; cret (t # ts) }"

definition truth :: "tysym Formula.formula" where
  "truth = Formula.Eq (Formula.Const (EInt 0)) (Formula.Const (EInt 0))"

definition special_preds :: "string list" where
  "special_preds = [''tp'', ''ts'', ''tpts'']"

text \<open>@{text lets}: the predicates that a @{text LET}, @{text LETPAST} or @{text FRZ} binds
  where the subformula occurs, with their arities.\<close>

fun conv_pred :: "(bytes \<Rightarrow> double option) \<Rightarrow> string list \<Rightarrow> string list \<Rightarrow> (string \<times> nat) list \<Rightarrow>
    predicate \<Rightarrow> string + tysym Formula.formula" where
  "conv_pred pf fvl bvl lets (n, ts) = (case conv_trms pf fvl bvl ts of
     Inl e \<Rightarrow> Inl e
   | Inr us \<Rightarrow> Inr (if n \<in> set special_preds \<and> (n, length ts) \<notin> set lets then
       (case (n, us) of
         (''tp'', [u]) \<Rightarrow> Formula.TP u
       | (''ts'', [u]) \<Rightarrow> Formula.TS u
       | (''tpts'', [u, v]) \<Rightarrow> Formula.And (Formula.TP u) (Formula.TS v)
       | _ \<Rightarrow> Formula.Pred (str8_of_string n) us)
     else Formula.Pred (str8_of_string n) us))"

text \<open>The variables of the arguments of a predicate that @{text LET} defines, in order: the free
  variables of its definition.\<close>

definition def_vars :: "predicate \<Rightarrow> string list" where
  "def_vars p = concat (map tvars (snd p))"

fun conv_f :: "(bytes \<Rightarrow> double option) \<Rightarrow> string list \<Rightarrow> string list \<Rightarrow> (string \<times> nat) list \<Rightarrow>
    formula \<Rightarrow> tysym Formula.formula conv"
and conv_r :: "(bytes \<Rightarrow> double option) \<Rightarrow> string list \<Rightarrow> string list \<Rightarrow> (string \<times> nat) list \<Rightarrow>
    regex \<Rightarrow> tysym Formula.formula Regex.regex conv" where
  "conv_f pf fvl bvl lets (FEqual t u) = clift (case conv_trm pf fvl bvl t of Inl e \<Rightarrow> Inl e
     | Inr a \<Rightarrow> map_sum id (Formula.Eq a) (conv_trm pf fvl bvl u))"
| "conv_f pf fvl bvl lets (FLess t u) = clift (case conv_trm pf fvl bvl t of Inl e \<Rightarrow> Inl e
     | Inr a \<Rightarrow> map_sum id (Formula.Less a) (conv_trm pf fvl bvl u))"
| "conv_f pf fvl bvl lets (FLessEq t u) = clift (case conv_trm pf fvl bvl t of Inl e \<Rightarrow> Inl e
     | Inr a \<Rightarrow> map_sum id (Formula.LessEq a) (conv_trm pf fvl bvl u))"
| "conv_f pf fvl bvl lets (FSubstring t u) = clift (Inl (unsupported
     (''Unsupported formula '' @ string_of_term t @ '' SUBSTRING '' @ string_of_term u)))"
| "conv_f pf fvl bvl lets (FMatches t u ts) = clift (Inl (unsupported
     (''Unsupported formula '' @ string_of_term t @ '' MATCHES '' @ string_of_term u @
      (if ts = [] then [] else '' ('' @ concat (between_list '', '' (map string_of_opt_term ts)) @ '')''))))"
| "conv_f pf fvl bvl lets (FPred p) = clift (conv_pred pf fvl bvl lets p)"
| "conv_f pf fvl bvl lets (FLet p f g) = do {
     a \<leftarrow> conv_f pf (def_vars p) [] lets f;
     b \<leftarrow> conv_f pf fvl bvl ((fst p, length (snd p)) # lets) g;
     cret (Formula.Let (str8_of_string (fst p)) a b) }"
| "conv_f pf fvl bvl lets (FLetPast p f g) = do {
     a \<leftarrow> conv_f pf (def_vars p) [] ((fst p, length (snd p)) # lets) f;
     b \<leftarrow> conv_f pf fvl bvl ((fst p, length (snd p)) # lets) g;
     cret (Formula.LetPast (str8_of_string (fst p)) a b) }"
| "conv_f pf fvl bvl lets (FFrz p f g) = do {
     a \<leftarrow> conv_f pf (def_vars p) [] lets f;
     b \<leftarrow> conv_f pf fvl bvl ((fst p, length (snd p)) # lets) g;
     cret (Formula.Frz (str8_of_string (fst p)) a b) }"
| "conv_f pf fvl bvl lets (FNeg f) = do { a \<leftarrow> conv_f pf fvl bvl lets f; cret (Formula.Neg a) }"
| "conv_f pf fvl bvl lets (FAnd f g) = do {
     a \<leftarrow> conv_f pf fvl bvl lets f; b \<leftarrow> conv_f pf fvl bvl lets g; cret (Formula.And a b) }"
| "conv_f pf fvl bvl lets (FOr f g) = do {
     a \<leftarrow> conv_f pf fvl bvl lets f; b \<leftarrow> conv_f pf fvl bvl lets g; cret (Formula.Or a b) }"
| "conv_f pf fvl bvl lets (FImplies f g) = do {
     a \<leftarrow> conv_f pf fvl bvl lets f; b \<leftarrow> conv_f pf fvl bvl lets g; cret (Formula.Or (Formula.Neg a) b) }"
| "conv_f pf fvl bvl lets (FEquiv f g) = do {
     a \<leftarrow> conv_f pf fvl bvl lets f; b \<leftarrow> conv_f pf fvl bvl lets g;
     cret (Formula.And (Formula.Or (Formula.Neg a) b) (Formula.Or (Formula.Neg b) a)) }"
| "conv_f pf fvl bvl lets (FExists vs f) = do {
     a \<leftarrow> conv_f pf fvl (vs @ bvl) lets f; ex_wrap (length vs) a }"
| "conv_f pf fvl bvl lets (FForAll vs f) = do {
     a \<leftarrow> conv_f pf fvl (vs @ bvl) lets f; b \<leftarrow> ex_wrap (length vs) (Formula.Neg a); cret (Formula.Neg b) }"
| "conv_f pf fvl bvl lets (FAggreg y op x g f) = (let bound = filter (\<lambda>v. v \<notin> set g) (dedup (mp_fv f)) in do {
     t \<leftarrow> fresh_ty;
     ts \<leftarrow> fresh_tys (length bound);
     u \<leftarrow> clift (conv_trm pf fvl (bound @ bvl) (TVar x));
     a \<leftarrow> conv_f pf fvl (bound @ bvl) lets f;
     cret (Formula.Agg (var_idx fvl bvl y) (conv_agg_op op, t) ts u a) })"
| "conv_f pf fvl bvl lets (FPrev i f) = do {
     I \<leftarrow> clift (conv_intv i); a \<leftarrow> conv_f pf fvl bvl lets f; cret (Formula.Prev I a) }"
| "conv_f pf fvl bvl lets (FNext i f) = do {
     I \<leftarrow> clift (conv_intv i); a \<leftarrow> conv_f pf fvl bvl lets f; cret (Formula.Next I a) }"
| "conv_f pf fvl bvl lets (FEventually i f) = do {
     I \<leftarrow> clift (conv_intv i); a \<leftarrow> conv_f pf fvl bvl lets f; cret (Formula.Until truth I a) }"
| "conv_f pf fvl bvl lets (FOnce i f) = do {
     I \<leftarrow> clift (conv_intv i); a \<leftarrow> conv_f pf fvl bvl lets f; cret (Formula.Since truth I a) }"
| "conv_f pf fvl bvl lets (FAlways i f) = do {
     I \<leftarrow> clift (conv_intv i); a \<leftarrow> conv_f pf fvl bvl lets f;
     cret (Formula.Neg (Formula.Until truth I (Formula.Neg a))) }"
| "conv_f pf fvl bvl lets (FPastAlways i f) = do {
     I \<leftarrow> clift (conv_intv i); a \<leftarrow> conv_f pf fvl bvl lets f;
     cret (Formula.Neg (Formula.Since truth I (Formula.Neg a))) }"
| "conv_f pf fvl bvl lets (FSince i f g) = do {
     I \<leftarrow> clift (conv_intv i); a \<leftarrow> conv_f pf fvl bvl lets f; b \<leftarrow> conv_f pf fvl bvl lets g;
     cret (Formula.Since a I b) }"
| "conv_f pf fvl bvl lets (FTrigger i f g) = do {
     I \<leftarrow> clift (conv_intv i); a \<leftarrow> conv_f pf fvl bvl lets f; b \<leftarrow> conv_f pf fvl bvl lets g;
     cret (Formula.Trigger a I b) }"
| "conv_f pf fvl bvl lets (FUntil i f g) = do {
     I \<leftarrow> clift (conv_intv i); a \<leftarrow> conv_f pf fvl bvl lets f; b \<leftarrow> conv_f pf fvl bvl lets g;
     cret (Formula.Until a I b) }"
| "conv_f pf fvl bvl lets (FRelease i f g) = do {
     I \<leftarrow> clift (conv_intv i); a \<leftarrow> conv_f pf fvl bvl lets f; b \<leftarrow> conv_f pf fvl bvl lets g;
     cret (Formula.Release a I b) }"
| "conv_f pf fvl bvl lets (FFrex i r) = do {
     I \<leftarrow> clift (conv_intv i); a \<leftarrow> conv_r pf fvl bvl lets r; cret (Formula.MatchF I a) }"
| "conv_f pf fvl bvl lets (FPrex i r) = do {
     I \<leftarrow> clift (conv_intv i); a \<leftarrow> conv_r pf fvl bvl lets r; cret (Formula.MatchP I a) }"
| "conv_r pf fvl bvl lets (RSkip n) = cret (Regex.Skip n)"
| "conv_r pf fvl bvl lets (RTest f) = do { a \<leftarrow> conv_f pf fvl bvl lets f; cret (Regex.Test a) }"
| "conv_r pf fvl bvl lets (RConcat r s) = do {
     a \<leftarrow> conv_r pf fvl bvl lets r; b \<leftarrow> conv_r pf fvl bvl lets s; cret (Regex.Times a b) }"
| "conv_r pf fvl bvl lets (RPlus r s) = do {
     a \<leftarrow> conv_r pf fvl bvl lets r; b \<leftarrow> conv_r pf fvl bvl lets s; cret (Regex.Plus a b) }"
| "conv_r pf fvl bvl lets (RStar r) = do { a \<leftarrow> conv_r pf fvl bvl lets r; cret (Regex.Star a) }"

subsection \<open>Folding ground terms\<close>

text \<open>A term without variables is replaced by its value, in the atoms where MonPoly's front end
  folds them.  This is @{text Rewriting.simplify_terms}, which preserves the semantics
  (@{text Rewriting.simplify_terms_sat}); the front end keeps its own copy because theory
  @{text Rewriting} declares a formula datatype and a function @{text tvars} whose names clash
  with those of the parse tree.\<close>

fun ground :: "Formula.trm \<Rightarrow> bool" where
  "ground (Formula.Var x) = False"
| "ground (Formula.Const c) = True"
| "ground (Formula.Plus t u) = (ground t \<and> ground u)"
| "ground (Formula.Minus t u) = (ground t \<and> ground u)"
| "ground (Formula.UMinus t) = ground t"
| "ground (Formula.Mult t u) = (ground t \<and> ground u)"
| "ground (Formula.Div t u) = (ground t \<and> ground u)"
| "ground (Formula.Mod t u) = (ground t \<and> ground u)"
| "ground (Formula.F2i t) = ground t"
| "ground (Formula.I2f t) = ground t"

definition fold_trm :: "Formula.trm \<Rightarrow> Formula.trm" where
  "fold_trm t = (if ground t then Formula.Const (Formula.eval_trm [] t) else t)"

fun fold_ground :: "'t Formula.formula \<Rightarrow> 't Formula.formula" where
  "fold_ground (Formula.Pred p ts) = Formula.Pred p (map fold_trm ts)"
| "fold_ground (Formula.Let p f g) = Formula.Let p (fold_ground f) (fold_ground g)"
| "fold_ground (Formula.Frz p f g) = Formula.Frz p (fold_ground f) (fold_ground g)"
| "fold_ground (Formula.LetPast p f g) = Formula.LetPast p (fold_ground f) (fold_ground g)"
| "fold_ground (Formula.Eq t u) = Formula.Eq (fold_trm t) (fold_trm u)"
| "fold_ground (Formula.Less t u) = Formula.Less (fold_trm t) (fold_trm u)"
| "fold_ground (Formula.LessEq t u) = Formula.LessEq (fold_trm t) (fold_trm u)"
| "fold_ground (Formula.Neg f) = Formula.Neg (fold_ground f)"
| "fold_ground (Formula.Or f g) = Formula.Or (fold_ground f) (fold_ground g)"
| "fold_ground (Formula.And f g) = Formula.And (fold_ground f) (fold_ground g)"
| "fold_ground (Formula.Ands fs) = Formula.Ands (map fold_ground fs)"
| "fold_ground (Formula.Exists t f) = Formula.Exists t (fold_ground f)"
| "fold_ground (Formula.Agg y \<omega> b u f) = Formula.Agg y \<omega> b u (fold_ground f)"
| "fold_ground (Formula.Prev I f) = Formula.Prev I (fold_ground f)"
| "fold_ground (Formula.Next I f) = Formula.Next I (fold_ground f)"
| "fold_ground (Formula.Since f I g) = Formula.Since (fold_ground f) I (fold_ground g)"
| "fold_ground (Formula.Until f I g) = Formula.Until (fold_ground f) I (fold_ground g)"
| "fold_ground (Formula.Trigger f I g) = Formula.Trigger (fold_ground f) I (fold_ground g)"
| "fold_ground (Formula.Release f I g) = Formula.Release (fold_ground f) I (fold_ground g)"
| "fold_ground (Formula.MatchF I r) = Formula.MatchF I (Regex.regex.map_regex fold_ground r)"
| "fold_ground (Formula.MatchP I r) = Formula.MatchP I (Regex.regex.map_regex fold_ground r)"
| "fold_ground (Formula.TP t) = Formula.TP (fold_trm t)"
| "fold_ground (Formula.TS t) = Formula.TS (fold_trm t)"

subsection \<open>The formula of the input\<close>

text \<open>The monitor's formula for the parsed formula: with rewriting (@{text rw}), after the
  syntactic sugar is eliminated; its free variables are numbered in the order of
  @{const out_vars} of the input.\<close>

definition conv_formula :: "(bytes \<Rightarrow> double option) \<Rightarrow> bool \<Rightarrow> formula \<Rightarrow> string + tysym Formula.formula" where
  "conv_formula pf rw f = (let fvl = out_vars f in
     map_sum id (\<lambda>(\<phi>, _). if rw then fold_ground \<phi> else \<phi>)
       (conv_f pf fvl [] [] (if rw then elim_sugar f else f) (length fvl)))"

(*<*)
end
(*>*)

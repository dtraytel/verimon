(*<*)
theory Match_Window
  imports Frame_Aux Until_Gen
begin
(*>*)



section \<open>The match windows over the operands' own columns\<close>

text \<open>
  @{theory Monitor_Exec.Frame_Aux} relates the kernel's match windows at the kernel's
  columns to the kernel's windows run at the ascending columns, on the reordered operands.  The
  windows below are what the executable evaluator runs:
  an operand is probed by the semi-join against its mask instead of the kernel's join, and they
  are polymorphic in the field type.  This theory shows that at the ascending columns they are
  the kernel's windows, so the relations @{const emrd_rel} and @{const emld_rel} of
  @{theory Monitor_Exec.Frame_Aux} hold of them unchanged.

  Two things differ from the kernel's derivatives.  The join against an atom is a semi-join,
  which @{thm [source] join_sub_eq} relates to the kernel's join; and the join of two lax
  epsilons is an intersection, which it is because both are tables over the node's columns.  The
  unit table is the empty tuple, which is the kernel's, and a strict epsilon's atom needs no
  reordering, because its columns are the node's.
\<close>

subsection \<open>The match structures over short tuples\<close>

text \<open>
  The two match structures are lists of tables indexed by a time stamp and, for the past one, by
  a marked regular expression, so they carry over on their own.  The derivative operations that
  fill them do not, in two places.

  The first is the join against an atom.  The kernel's lax epsilon joins the guard -- a table over
  the node's columns -- with an atom's table, whose columns are a subset of them; over the
  ascending columns that is the semi-join against the atom's mask, and the masks are computed
  once, at compile time, one per atom.  Where both sides are results of the lax epsilon they are
  both over the node's columns, so the join is an intersection.

  The second is the unit table that the two strict epsilons return at a
  @{term "Regex.Skip 0"} and at a star.  That table is a table over the node's columns only
  because the safety condition forces those columns to be empty where it arises -- a star or an
  empty skip that could match the empty word while the node still binds a variable would make
  the formula unsafe.  With no columns the unit table is the one empty tuple, which is what the
  operations below return.

  An atom's table is read with @{text gnth}, the empty table past the end of the list.  A
  well-formed node never reads past it; reading it totally makes the operations total.
\<close>

definition gnth :: "'b list set list \<Rightarrow> nat \<Rightarrow> 'b list set" where
  "gnth xs i = (if i < length xs then xs ! i else {})"

lemma gnth_nth[simp]: "i < length xs \<Longrightarrow> gnth xs i = xs ! i"
  by (simp add: gnth_def)

definition glookup :: "(mregex, 'b list set) mapping \<Rightarrow> mregex \<Rightarrow> 'b list set" where
  "glookup = Mapping.lookup_default {}"

lift_definition gmrtabulate :: "mregex list \<Rightarrow> (mregex \<Rightarrow> 'b list set) \<Rightarrow>
    (mregex, 'b list set) mapping"
  is "\<lambda>ks f. map_of (List.map_filter (\<lambda>k. let fk = f k in if fk = {} then None else Some (k, fk)) ks)" .

text \<open>The lifted definition on its own would build the function-backed mapping, which the
  mapping operations cannot look a key up in; it needs the same tree code equation the kernel's
  tabulation has.\<close>

lemma gmrtabulate_rbt_code[code]: "gmrtabulate (xs :: mregex list) f =
  (case ID CCOMPARE(mregex) of
     None \<Rightarrow> Code.abort (STR ''gmrtabulate RBT_Mapping: ccompare = None'') (\<lambda>_. gmrtabulate xs f)
   | _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.bulkload
       (List.map_filter (\<lambda>k. let fk = f k in if fk = {} then None else Some (k, fk)) xs)))"
  unfolding gmrtabulate.abs_eq RBT_Mapping_def
  by (auto split: option.splits)

fun geps_lax :: "bool list list \<Rightarrow> 'b list set \<Rightarrow> 'b list set list \<Rightarrow> mregex \<Rightarrow> 'b list set" where
  "geps_lax msks guard \<phi>s (MSkip n) = (if n = 0 then guard else {})"
| "geps_lax msks guard \<phi>s (MTestPos i) = esemi (msks ! i) True guard (gnth \<phi>s i)"
| "geps_lax msks guard \<phi>s (MTestNeg i) = esemi (msks ! i) False guard (gnth \<phi>s i)"
| "geps_lax msks guard \<phi>s (MPlus r s) = geps_lax msks guard \<phi>s r \<union> geps_lax msks guard \<phi>s s"
| "geps_lax msks guard \<phi>s (MTimes r s) = geps_lax msks guard \<phi>s r \<inter> geps_lax msks guard \<phi>s s"
| "geps_lax msks guard \<phi>s (MStar r) = guard"

fun greps_strict :: "bool list list \<Rightarrow> 'b list set list \<Rightarrow> mregex \<Rightarrow> 'b list set" where
  "greps_strict msks \<phi>s (MSkip m) = (if m = 0 then {[]} else {})"
| "greps_strict msks \<phi>s (MTestPos i) = gnth \<phi>s i"
| "greps_strict msks \<phi>s (MTestNeg i) = (if gnth \<phi>s i = {} then {[]} else {})"
| "greps_strict msks \<phi>s (MPlus r s) = greps_strict msks \<phi>s r \<union> greps_strict msks \<phi>s s"
| "greps_strict msks \<phi>s (MTimes r s) = geps_lax msks (greps_strict msks \<phi>s r) \<phi>s s"
| "greps_strict msks \<phi>s (MStar r) = {[]}"

fun gleps_strict :: "bool list list \<Rightarrow> 'b list set list \<Rightarrow> mregex \<Rightarrow> 'b list set" where
  "gleps_strict msks \<phi>s (MSkip m) = (if m = 0 then {[]} else {})"
| "gleps_strict msks \<phi>s (MTestPos i) = gnth \<phi>s i"
| "gleps_strict msks \<phi>s (MTestNeg i) = (if gnth \<phi>s i = {} then {[]} else {})"
| "gleps_strict msks \<phi>s (MPlus r s) = gleps_strict msks \<phi>s r \<union> gleps_strict msks \<phi>s s"
| "gleps_strict msks \<phi>s (MTimes r s) = geps_lax msks (gleps_strict msks \<phi>s s) \<phi>s r"
| "gleps_strict msks \<phi>s (MStar r) = {[]}"

fun grdelta :: "bool list list \<Rightarrow> (mregex \<Rightarrow> mregex) \<Rightarrow> (mregex, 'b list set) mapping \<Rightarrow>
    'b list set list \<Rightarrow> mregex \<Rightarrow> 'b list set" where
  "grdelta msks \<kappa> X \<phi>s (MSkip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> glookup X (\<kappa> (MSkip m)))"
| "grdelta msks \<kappa> X \<phi>s (MTestPos i) = {}"
| "grdelta msks \<kappa> X \<phi>s (MTestNeg i) = {}"
| "grdelta msks \<kappa> X \<phi>s (MPlus r s) = grdelta msks \<kappa> X \<phi>s r \<union> grdelta msks \<kappa> X \<phi>s s"
| "grdelta msks \<kappa> X \<phi>s (MTimes r s) =
     grdelta msks (\<lambda>t. \<kappa> (MTimes r t)) X \<phi>s s \<union> geps_lax msks (grdelta msks \<kappa> X \<phi>s r) \<phi>s s"
| "grdelta msks \<kappa> X \<phi>s (MStar r) = grdelta msks (\<lambda>t. \<kappa> (MTimes (MStar r) t)) X \<phi>s r"

fun gldelta :: "bool list list \<Rightarrow> (mregex \<Rightarrow> mregex) \<Rightarrow> (mregex, 'b list set) mapping \<Rightarrow>
    'b list set list \<Rightarrow> mregex \<Rightarrow> 'b list set" where
  "gldelta msks \<kappa> X \<phi>s (MSkip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> glookup X (\<kappa> (MSkip m)))"
| "gldelta msks \<kappa> X \<phi>s (MTestPos i) = {}"
| "gldelta msks \<kappa> X \<phi>s (MTestNeg i) = {}"
| "gldelta msks \<kappa> X \<phi>s (MPlus r s) = gldelta msks \<kappa> X \<phi>s r \<union> gldelta msks \<kappa> X \<phi>s s"
| "gldelta msks \<kappa> X \<phi>s (MTimes r s) =
     gldelta msks (\<lambda>t. \<kappa> (MTimes t s)) X \<phi>s r \<union> geps_lax msks (gldelta msks \<kappa> X \<phi>s s) \<phi>s r"
| "gldelta msks \<kappa> X \<phi>s (MStar r) = gldelta msks (\<lambda>t. \<kappa> (MTimes t (MStar r))) X \<phi>s r"

type_synonym 'b gmrdaux = "(ts \<times> (mregex, 'b list set) mapping) list"
type_synonym 'b gmldaux = "(ts \<times> 'b list set list \<times> 'b list set) list"

definition gupdate_matchP :: "bool list list \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> 'b list set list \<Rightarrow>
    ts \<Rightarrow> 'b gmrdaux \<Rightarrow> 'b list set \<times> 'b gmrdaux" where
  "gupdate_matchP msks I mr mrs rels nt aux =
    (let aux = (case [(t, gmrtabulate mrs (\<lambda>mr.
        grdelta msks id rel rels mr \<union> (if t = nt then greps_strict msks rels mr else {}))).
      (t, rel) \<leftarrow> aux, memR I (nt - t)]
      of [] \<Rightarrow> [(nt, gmrtabulate mrs (greps_strict msks rels))]
      | x # aux' \<Rightarrow> (if fst x = nt then x # aux'
                    else (nt, gmrtabulate mrs (greps_strict msks rels)) # x # aux'))
    in (foldr (\<union>) [glookup rel mr. (t, rel) \<leftarrow> aux, memL I (nt - t)] {}, aux))"

definition gupdate_matchF_base :: "bool list list \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow>
    'b list set list \<Rightarrow> ts \<Rightarrow> 'b gmldaux \<times> (mregex, 'b list set) mapping" where
  "gupdate_matchF_base msks I mr mrs rels nt =
     (let X = gmrtabulate mrs (gleps_strict msks rels)
      in ([(nt, rels, if memL I 0 then glookup X mr else {})], X))"

definition gupdate_matchF_step :: "bool list list \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> ts \<Rightarrow>
    ts \<times> 'b list set list \<times> 'b list set \<Rightarrow> 'b gmldaux \<times> (mregex, 'b list set) mapping \<Rightarrow>
    'b gmldaux \<times> (mregex, 'b list set) mapping" where
  "gupdate_matchF_step msks I mr mrs nt = (\<lambda>(t, rels', rel) (aux', X).
     (let Y = gmrtabulate mrs (gldelta msks id X rels')
      in ((t, rels', if mem I (nt - t) then rel \<union> glookup Y mr else rel) # aux', Y)))"

definition gupdate_matchF :: "bool list list \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> 'b list set list \<Rightarrow>
    ts \<Rightarrow> 'b gmldaux \<Rightarrow> 'b gmldaux" where
  "gupdate_matchF msks I mr mrs rels nt aux =
     fst (foldr (gupdate_matchF_step msks I mr mrs nt) aux
       (gupdate_matchF_base msks I mr mrs rels nt))"

fun geval_matchF :: "\<I> \<Rightarrow> mregex \<Rightarrow> ts \<Rightarrow> 'b gmldaux \<Rightarrow> 'b list set list \<times> 'b gmldaux" where
  "geval_matchF I mr nt [] = ([], [])"
| "geval_matchF I mr nt ((t, rels, rel) # aux) = (if \<not> memR I (nt - t)
    then (let (xs, aux) = geval_matchF I mr nt aux in (rel # xs, aux))
    else ([], (t, rels, rel) # aux))"

subsection \<open>The windows at the ascending columns\<close>

definition emb_msk :: "nat option list \<Rightarrow> bool list" where
  "emb_msk p = map (\<lambda>q. q \<noteq> None) p"

lemma mrg_left_key_map:
  "sorted_wrt (<) cs1 \<Longrightarrow> sorted_wrt (<) cs2 \<Longrightarrow> set cs2 \<subseteq> set cs1 \<Longrightarrow>
     mrg_left_key (mrg_plan cs1 cs2) = map (\<lambda>c. c \<in> set cs2) cs1"
proof (induct cs1 cs2 rule: mrg_plan.induct)
  case (1 ds)
  then show ?case by (simp add: mrg_left_key_MRgt)
next
  case (2 c cs)
  then show ?case by simp
next
  case (3 c cs d ds)
  note cc = mrg_plan_Cons_cases[OF 3(4,5,6)]
  show ?case
  proof (cases "c < d")
    case True
    have "c \<notin> set (d # ds)" using True 3(5) by auto
    moreover have "c \<noteq> d" using True by simp
    ultimately show ?thesis using 3(1)[OF True] 3(4,5) cc(2)[OF True] by simp
  next
    case False
    then have e: "c = d" using cc(1) by simp
    have "map (\<lambda>x. x \<in> set (c # ds)) cs = map (\<lambda>x. x \<in> set ds) cs" using 3(4) by auto
    then show ?thesis using 3(3)[OF False cc(1)] 3(4,5) cc(3)[OF e] False e by simp
  qed
qed

lemma emb_msk_emb_plan:
  assumes s1: "sorted_wrt (<) cs" and s2: "sorted_wrt (<) c" and sub: "set c \<subseteq> set cs"
  shows "emb_msk (emb_plan cs c) = emsk cs c"
  by (simp add: emb_msk_def emb_plan_def emsk_def mrg_left_key_map[OF s1 s2 sub] comp_def)

lemma eproj_dmsk:
  assumes s1: "sorted_wrt (<) cs" and s2: "sorted_wrt (<) ds" and sub: "set ds \<subseteq> set cs"
    and l: "length a = length cs"
  shows "eproj (emsk cs ds) a = restrict ds cs a"
  using emsk_args_dproj[OF emsk_args_dargs[OF s1 s2 sub, of undefined], of a] l
  by (simp add: emsk_def)

lemma glookup_lookup: "glookup = lookup"
  by (simp add: glookup_def Monitor.lookup_def empty_table_def)

lemma gmrtabulate_mrtabulate: "gmrtabulate xs f = mrtabulate xs f"
  by transfer (simp add: empty_table_def)

lemma mrtabulate_cong:
  assumes "\<And>k. k \<in> set ks \<Longrightarrow> f k = g k"
  shows "mrtabulate ks f = mrtabulate ks g"
proof -
  have "List.map_filter (\<lambda>k. let fk = f k in if fk = empty_table then None else Some (k, fk)) ks
      = List.map_filter (\<lambda>k. let fk = g k in if fk = empty_table then None else Some (k, fk)) ks"
    using assms
  proof (induct ks)
    case (Cons a ks)
    then have "f a = g a" by simp
    with Cons show ?case by (simp add: Let_def)
  qed simp
  then show ?thesis unfolding mrtabulate.abs_eq by simp
qed

lemma join_same:
  assumes d: "distinct cs" and tA: "table cs A" and tB: "table cs B"
  shows "join cs A True cs B = A \<inter> B"
  using join_sub_eq[OF d d tA tB subset_refl, of True] tA
  by (auto simp: table_def restrict_idle[OF d])

lemma geps_lax_eq:
  assumes s: "sorted_wrt (<) cs" and wf: "wf_atoms cs css css \<phi>s"
  shows "ok (length \<phi>s) mr \<Longrightarrow> table cs guard \<Longrightarrow>
     geps_lax (map (emsk cs) css) guard \<phi>s mr = \<epsilon>_lax cs css guard \<phi>s mr"
proof (induct mr arbitrary: guard)
  case (MSkip m)
  then show ?case by (simp add: empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length \<phi>s" by simp
  have lc: "length css = length \<phi>s" using wf by (simp add: wf_atoms_def)
  have fi: "eframe (css ! i) (css ! i)" and si: "set (css ! i) \<subseteq> set cs"
    and ti: "table (css ! i) (\<phi>s ! i)" using wf_atomsD[OF wf i] by simp_all
  have dc: "distinct cs" using s by (simp add: strict_sorted_iff)
  have p: "\<And>a. a \<in> guard \<Longrightarrow> eproj (emsk cs (css ! i)) a = restrict (css ! i) cs a"
    using MTestPos(2) eproj_dmsk[OF s eframeD(2)[OF fi] si] by (auto simp: table_def wf_tuple_def)
  show ?case using i lc join_sub_eq[OF dc eframeD(1)[OF fi] MTestPos(2) ti si, of True] p
    by (auto simp: esemi_def)
next
  case (MTestNeg i)
  then have i: "i < length \<phi>s" by simp
  have lc: "length css = length \<phi>s" using wf by (simp add: wf_atoms_def)
  have fi: "eframe (css ! i) (css ! i)" and si: "set (css ! i) \<subseteq> set cs"
    and ti: "table (css ! i) (\<phi>s ! i)" using wf_atomsD[OF wf i] by simp_all
  have dc: "distinct cs" using s by (simp add: strict_sorted_iff)
  have p: "\<And>a. a \<in> guard \<Longrightarrow> eproj (emsk cs (css ! i)) a = restrict (css ! i) cs a"
    using MTestNeg(2) eproj_dmsk[OF s eframeD(2)[OF fi] si] by (auto simp: table_def wf_tuple_def)
  show ?case using i lc join_sub_eq[OF dc eframeD(1)[OF fi] MTestNeg(2) ti si, of False] p
    by (auto simp: esemi_def)
next
  case (MPlus r t)
  then show ?case by simp
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have dc: "distinct cs" using s by (simp add: strict_sorted_iff)
  have t1: "table cs (\<epsilon>_lax cs css guard \<phi>s r)" by (rule table_eps_lax[OF wf o1 MTimes(4)])
  have t2: "table cs (\<epsilon>_lax cs css guard \<phi>s t)" by (rule table_eps_lax[OF wf o2 MTimes(4)])
  show ?case using MTimes(1)[OF o1 MTimes(4)] MTimes(2)[OF o2 MTimes(4)]
    by (simp add: join_same[OF dc t1 t2])
qed simp

lemma grdelta_eq:
  assumes s: "sorted_wrt (<) cs" and wf: "wf_atoms cs css css \<phi>s"
    and X: "\<And>ms. table cs (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> grdelta (map (emsk cs) css) \<kappa> X \<phi>s mr = r\<delta> cs css \<kappa> X \<phi>s mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case by (cases m) (simp_all add: glookup_lookup empty_table_def)
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have tg: "table cs (r\<delta> cs css \<kappa> X \<phi>s r)" by (rule table_rdelta[OF wf X o1])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2] by (simp add: geps_lax_eq[OF s wf o2 tg])
qed (simp_all add: empty_table_def)

lemma gldelta_eq:
  assumes s: "sorted_wrt (<) cs" and wf: "wf_atoms cs css css \<phi>s"
    and X: "\<And>ms. table cs (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> gldelta (map (emsk cs) css) \<kappa> X \<phi>s mr = l\<delta> cs css \<kappa> X \<phi>s mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case by (cases m) (simp_all add: glookup_lookup empty_table_def)
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have tg: "table cs (l\<delta> cs css \<kappa> X \<phi>s t)" by (rule table_ldelta[OF wf X o2])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2] by (simp add: geps_lax_eq[OF s wf o1 tg])
qed (simp_all add: empty_table_def)

subsection \<open>The strict epsilons\<close>

context eregex_frame
begin

abbreviation (input) "gmsks \<equiv> map (emsk cs) css"

lemma ewf_atoms: "wfrels rels \<Longrightarrow> wf_atoms cs css css (erels rels)"
  using lc fa sub eframeD(3)[OF fK]
  by (auto simp: wf_atoms_def list_all2_conv_all_nth eframe_def table_etabc strict_sorted_iff)

lemma css_eq:
  assumes i: "i < length \<psi>s" and e: "Formula.fv (\<psi>s ! i) = set ks"
  shows "css ! i = cs"
  using eframeD(2,3)[OF fK] eframeD(2,3)[OF fa[OF i]] e by (intro strict_sorted_equal) auto

lemma greps_strict_eq:
  assumes ops: "wfrels rels"
  shows "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     greps_strict gmsks (erels rels) mr = r\<epsilon>_strict cs css (erels rels) mr"
proof (induct mr)
  case (MSkip m)
  then show ?case by (simp add: unit_table_def empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length \<psi>s" by simp
  have "css ! i = cs" using css_eq[OF i] MTestPos(3) by simp
  then show ?case using i lr[OF ops] by (simp add: reorder_def)
next
  case (MTestNeg i)
  then show ?case using lr[OF ops] by (simp add: unit_table_def empty_table_def)
next
  case (MPlus r t)
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4) by simp
next
  case (MTimes r t)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr1: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex r \<psi>s)"
    using MTimes(3) by simp
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)" using MTimes(3,5) by auto
  have tg: "table cs (r\<epsilon>_strict cs css (erels rels) r)"
    using table_etabc etabc_reps_strict[OF ops sr1 o1 fvr] by metis
  show ?case using MTimes(1)[OF sr1 o1 fvr] o2 lr[OF ops]
    by (simp add: geps_lax_eq[OF eframeD(2)[OF fK] ewf_atoms[OF ops] _ tg])
next
  case (MStar r)
  then show ?case by (simp add: unit_table_def)
qed

lemma gleps_strict_eq:
  assumes ops: "wfrels rels"
  shows "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     gleps_strict gmsks (erels rels) mr = l\<epsilon>_strict cs css (erels rels) mr"
proof (induct mr)
  case (MSkip m)
  then show ?case by (simp add: unit_table_def empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length \<psi>s" by simp
  have "css ! i = cs" using css_eq[OF i] MTestPos(3) by simp
  then show ?case using i lr[OF ops] by (simp add: reorder_def)
next
  case (MTestNeg i)
  then show ?case using lr[OF ops] by (simp add: unit_table_def empty_table_def)
next
  case (MPlus r t)
  have fvr: "set ks = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4) by simp
next
  case (MTimes r t)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr2: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex t \<psi>s)"
    using MTimes(3) by simp
  have fvt: "set ks = fv_regex (from_mregex t \<psi>s)" using MTimes(3,5) by auto
  have tg: "table cs (l\<epsilon>_strict cs css (erels rels) t)"
    using table_etabc etabc_leps_strict[OF ops sr2 o2 fvt] by metis
  show ?case using MTimes(2)[OF sr2 o2 fvt] o1 lr[OF ops]
    by (simp add: geps_lax_eq[OF eframeD(2)[OF fK] ewf_atoms[OF ops] _ tg])
next
  case (MStar r)
  then show ?case by (simp add: unit_table_def)
qed

end

lemma emrd_rel_table:
  "emrd_rel ks cs aux daux \<Longrightarrow> (t, X) \<in> set daux \<Longrightarrow> table cs (lookup X ms)"
  by (induct rule: emrd_rel_induct) (auto simp: table_etabc)

context ematchP_frame
begin

lemma ldrels: "length (erels rels) = length \<psi>s"
  using lr[OF ops] by simp

lemma gtab_head:
  "mrtabulate mrs (greps_strict gmsks (erels rels)) = mrtabulate mrs (r\<epsilon>_strict cs css (erels rels))"
  using mrsok by (intro mrtabulate_cong greps_strict_eq[OF ops]) auto

lemma gtab_step:
  assumes X: "\<And>ms. table cs (lookup X ms)"
  shows "mrtabulate mrs (\<lambda>ms. grdelta gmsks id X (erels rels) ms
       \<union> (if t = nt then greps_strict gmsks (erels rels) ms else {}))
     = mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X (erels rels) ms
       \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {}))"
proof (rule mrtabulate_cong)
  fix ms
  assume ms: "ms \<in> set mrs"
  have o: "ok (length (erels rels)) ms" using mrsok[OF ms] ldrels by simp
  show "grdelta gmsks id X (erels rels) ms \<union> (if t = nt then greps_strict gmsks (erels rels) ms else {})
      = r\<delta> cs css id X (erels rels) ms \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {})"
    using mrsok[OF ms]
    by (simp add: grdelta_eq[OF eframeD(2)[OF fK] ewf_atoms[OF ops] X o] greps_strict_eq[OF ops])
qed

lemma gtab_window:
  "(\<And>t X ms. (t, X) \<in> set D \<Longrightarrow> table cs (lookup X ms)) \<Longrightarrow>
   [(t, mrtabulate mrs (\<lambda>ms. grdelta gmsks id X (erels rels) ms
       \<union> (if t = nt then greps_strict gmsks (erels rels) ms else {}))). (t, X) \<leftarrow> D, memR I (nt - t)]
   = [(t, mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X (erels rels) ms
       \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {}))). (t, X) \<leftarrow> D, memR I (nt - t)]"
proof (induct D)
  case (Cons x D)
  obtain t X where x: "x = (t, X)" by (cases x)
  have "\<And>ms. table cs (lookup X ms)" using Cons(2)[of t X] x by simp
  moreover have "\<And>t X ms. (t, X) \<in> set D \<Longrightarrow> table cs (lookup X ms)"
    using Cons(2) by (metis list.set_intros(2))
  ultimately show ?case using Cons(1) x by (simp add: gtab_step)
qed simp

lemma gupdate_matchP_eq:
  assumes rel: "emrd_rel ks cs aux daux"
  shows "gupdate_matchP gmsks I mr mrs (erels rels) nt daux
     = update_matchP cs css I mr mrs (erels rels) nt daux"
proof -
  have w: "[(t, mrtabulate mrs (\<lambda>ms. grdelta gmsks id X (erels rels) ms
       \<union> (if t = nt then greps_strict gmsks (erels rels) ms else {}))). (t, X) \<leftarrow> daux, memR I (nt - t)]
   = [(t, mrtabulate mrs (\<lambda>ms. r\<delta> cs css id X (erels rels) ms
       \<union> (if t = nt then r\<epsilon>_strict cs css (erels rels) ms else {}))). (t, X) \<leftarrow> daux, memR I (nt - t)]"
    by (rule gtab_window[OF emrd_rel_table[OF rel]])
  show ?thesis
    unfolding gupdate_matchP_def update_matchP_def glookup_lookup gmrtabulate_mrtabulate gtab_head w ..
qed

lemma etabc_gupdate_matchP:
  assumes rel: "emrd_rel ks cs aux daux"
  shows "etabc ks cs (fst (update_matchP ks kss I mr mrs rels nt aux))
       = fst (gupdate_matchP gmsks I mr mrs (erels rels) nt daux) \<and>
     emrd_rel ks cs (snd (update_matchP ks kss I mr mrs rels nt aux))
       (snd (gupdate_matchP gmsks I mr mrs (erels rels) nt daux))"
  unfolding gupdate_matchP_eq[OF rel] by (rule etabc_update_matchP[OF rel])

end

lemma geval_matchF_eval_matchF: "geval_matchF I mr nt aux = eval_matchF I mr nt aux"
  by (induct aux rule: eval_matchF.induct) simp_all

context ematchF_frame
begin

lemma table_lookup_dbase:
  assumes rels: "wfrels rels"
  shows "table cs (lookup (mrtabulate mrs (l\<epsilon>_strict cs css (erels rels))) ms)"
  using etabL[OF rels] by (simp add: lookup_tabulate[OF d] table_etabc flip: etabL[OF rels])

lemma gupdate_matchF_base_eq:
  assumes rels: "wfrels rels"
  shows "gupdate_matchF_base gmsks I mr mrs (erels rels) nt
     = update_matchF_base cs css I mr mrs (erels rels) nt"
proof -
  have "mrtabulate mrs (gleps_strict gmsks (erels rels)) = mrtabulate mrs (l\<epsilon>_strict cs css (erels rels))"
    using mrsok by (intro mrtabulate_cong gleps_strict_eq[OF rels]) auto
  then show ?thesis
    by (simp add: gupdate_matchF_base_def update_matchF_base_def glookup_lookup gmrtabulate_mrtabulate
        Let_def empty_table_def)
qed

lemma gupdate_matchF_step_eq:
  assumes rls: "wfrels rls" and X: "\<And>ms. table cs (lookup X ms)"
  shows "gupdate_matchF_step gmsks I mr mrs nt (t, erels rls, drel) (A, X)
       = update_matchF_step cs css I mr mrs nt (t, erels rls, drel) (A, X)"
    and "table cs (lookup (mrtabulate mrs (l\<delta> cs css id X (erels rls))) ms)"
proof -
  have o: "\<And>ms. ms \<in> set mrs \<Longrightarrow> ok (length (erels rls)) ms" using okms[OF _ rls] by simp
  have "mrtabulate mrs (gldelta gmsks id X (erels rls)) = mrtabulate mrs (l\<delta> cs css id X (erels rls))"
    by (intro mrtabulate_cong gldelta_eq[OF eframeD(2)[OF fK] ewf_atoms[OF rls] X o])
  then show "gupdate_matchF_step gmsks I mr mrs nt (t, erels rls, drel) (A, X)
       = update_matchF_step cs css I mr mrs nt (t, erels rls, drel) (A, X)"
    by (simp add: gupdate_matchF_step_def update_matchF_step_def glookup_lookup gmrtabulate_mrtabulate
        Let_def)
  show "table cs (lookup (mrtabulate mrs (l\<delta> cs css id X (erels rls))) ms)"
    using table_ldelta[OF ewf_atoms[OF rls] X o]
    by (simp add: lookup_tabulate[OF d])
qed

lemma gmatchF_foldr_eq:
  assumes rels: "wfrels rels" and rel: "emld_rel ks cs \<psi>s css aux daux"
  shows "foldr (gupdate_matchF_step gmsks I mr mrs nt) daux (gupdate_matchF_base gmsks I mr mrs (erels rels) nt)
       = foldr (update_matchF_step cs css I mr mrs nt) daux (update_matchF_base cs css I mr mrs (erels rels) nt)
     \<and> (\<forall>ms. table cs (lookup (snd (foldr (update_matchF_step cs css I mr mrs nt) daux
          (update_matchF_base cs css I mr mrs (erels rels) nt))) ms))"
  using rel
proof (induct rule: emld_rel_induct)
  case Nil
  show ?case using table_lookup_dbase[OF rels]
    by (simp add: gupdate_matchF_base_eq[OF rels] update_matchF_base_def Let_def)
next
  case (Cons t rls rel aux daux)
  obtain A X where W: "foldr (update_matchF_step cs css I mr mrs nt) daux
      (update_matchF_base cs css I mr mrs (erels rels) nt) = (A, X)"
    by (cases "foldr (update_matchF_step cs css I mr mrs nt) daux
      (update_matchF_base cs css I mr mrs (erels rels) nt)")
  have IH: "foldr (gupdate_matchF_step gmsks I mr mrs nt) daux
      (gupdate_matchF_base gmsks I mr mrs (erels rels) nt) = (A, X)"
    and tX: "\<And>ms. table cs (lookup X ms)" using Cons(3) unfolding W by simp_all
  have E: "foldr (update_matchF_step cs css I mr mrs nt) ((t, erels rls, etabc ks cs rel) # daux)
      (update_matchF_base cs css I mr mrs (erels rels) nt)
      = update_matchF_step cs css I mr mrs nt (t, erels rls, etabc ks cs rel) (A, X)"
    unfolding W[symmetric] by simp
  have GE: "foldr (gupdate_matchF_step gmsks I mr mrs nt) ((t, erels rls, etabc ks cs rel) # daux)
      (gupdate_matchF_base gmsks I mr mrs (erels rels) nt)
      = gupdate_matchF_step gmsks I mr mrs nt (t, erels rls, etabc ks cs rel) (A, X)"
    unfolding IH[symmetric] by simp
  show ?case unfolding E GE gupdate_matchF_step_eq(1)[OF Cons(1) tX]
    using gupdate_matchF_step_eq(2)[OF Cons(1) tX]
    by (simp add: update_matchF_step_def Let_def)
qed

lemma gupdate_matchF_eq:
  assumes rels: "wfrels rels" and rel: "emld_rel ks cs \<psi>s css aux daux"
  shows "gupdate_matchF gmsks I mr mrs (erels rels) nt daux
     = update_matchF cs css I mr mrs (erels rels) nt daux"
  using gmatchF_foldr_eq[OF rels rel] by (simp add: gupdate_matchF_def update_matchF_def)

lemma etabc_gupdate_matchF:
  assumes rels: "wfrels rels" and rel: "emld_rel ks cs \<psi>s css aux daux"
  shows "emld_rel ks cs \<psi>s css (update_matchF ks kss I mr mrs rels nt aux)
     (gupdate_matchF gmsks I mr mrs (erels rels) nt daux)"
  unfolding gupdate_matchF_eq[OF rels rel] by (rule etabc_update_matchF[OF rels rel])

lemma etabc_geval_matchF:
  assumes "emld_rel ks cs \<psi>s css aux daux"
  shows "fst (geval_matchF I mr nt daux) = map (etabc ks cs) (fst (eval_matchF I mr nt aux)) \<and>
     emld_rel ks cs \<psi>s css (snd (eval_matchF I mr nt aux)) (snd (geval_matchF I mr nt daux))"
  unfolding geval_matchF_eval_matchF by (rule etabc_eval_matchF[OF assms])

end

(*<*)
end
(*>*)

(*<*)
theory Match_Window
  imports Exec_Since Exec_Until
begin
(*>*)

section \<open>Match windows over ascending columns\<close>

subsection \<open>Atoms and their frames\<close>

definition etabcs :: "cols list \<Rightarrow> cols list \<Rightarrow> 'b list set list \<Rightarrow> 'b list set list" where
  "etabcs kss css rels = map (\<lambda>i. etabc (kss ! i) (css ! i) (rels ! i)) [0..<length rels]"

lemma length_etabcs[simp]: "length (etabcs kss css rels) = length rels"
  by (simp add: etabcs_def)

lemma nth_etabcs[simp]: "i < length rels \<Longrightarrow> etabcs kss css rels ! i = etabc (kss ! i) (css ! i) (rels ! i)"
  by (simp add: etabcs_def)

definition wf_atoms :: "cols \<Rightarrow> cols list \<Rightarrow> cols list \<Rightarrow> 'b list set list \<Rightarrow> bool" where
  "wf_atoms ks kss css rels \<longleftrightarrow> length kss = length rels \<and> length css = length rels \<and>
     (\<forall>i < length rels. eframe (kss ! i) (css ! i) \<and> set (kss ! i) \<subseteq> set ks \<and> table (kss ! i) (rels ! i))"

locale eregex_frame =
  fixes ks cs :: cols and \<psi>s :: "ty Formula.formula list" and css :: "cols list"
  assumes fK: "eframe ks cs" and lc: "length css = length \<psi>s"
    and fa: "\<And>i. i < length \<psi>s \<Longrightarrow> eframe (Formula.fv_list (\<psi>s ! i)) (css ! i)"
    and sub: "\<And>i. i < length \<psi>s \<Longrightarrow> Formula.fv (\<psi>s ! i) \<subseteq> set ks"
begin

abbreviation (input) wfrels :: "event_data table list \<Rightarrow> bool" where
  "wfrels rels \<equiv> list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel \<and> finite rel) \<psi>s rels"

abbreviation (input) erels :: "event_data table list \<Rightarrow> event_data table list" where
  "erels rels \<equiv> etabcs (map Formula.fv_list \<psi>s) css rels"

lemma lr: "wfrels rels \<Longrightarrow> length \<psi>s = length rels"
  by (simp add: list_all2_lengthD)

end

subsection \<open>Past-match structure\<close>

text \<open>A tabulation is only read through @{const lookup}, so the relation compares lookups.\<close>

definition emrd_rel :: "cols \<Rightarrow> cols \<Rightarrow> event_data mr\<delta>aux \<Rightarrow> event_data mr\<delta>aux \<Rightarrow> bool" where
  "emrd_rel ks cs = list_all2 (\<lambda>(t, X) (t', X'). t = t' \<and>
     (\<forall>ms. table ks (lookup X ms)) \<and> (\<forall>ms. lookup X' ms = etabc ks cs (lookup X ms)))"

lemma emrd_rel_Nil[simp]: "emrd_rel ks cs [] []"
  by (simp add: emrd_rel_def)

lemma emrd_rel_Cons[simp]:
  "emrd_rel ks cs ((t, X) # aux) ((t', X') # daux) \<longleftrightarrow> t = t' \<and>
     (\<forall>ms. table ks (lookup X ms)) \<and> (\<forall>ms. lookup X' ms = etabc ks cs (lookup X ms)) \<and>
     emrd_rel ks cs aux daux"
  by (simp add: emrd_rel_def)

locale ematchP_frame = eregex_frame ks cs \<psi>s css
  for ks cs :: cols and \<psi>s :: "ty Formula.formula list" and css :: "cols list" +
  fixes rels :: "event_data table list" and mrs :: "mregex list"
  assumes ops: "list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel \<and> finite rel) \<psi>s rels"
    and d: "distinct mrs"
    and mrsok: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
       Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex ms \<psi>s) \<and> ok (length \<psi>s) ms \<and>
       set ks = fv_regex (from_mregex ms \<psi>s)"
begin

abbreviation (input) "kss \<equiv> map Formula.fv_list \<psi>s"

end

subsection \<open>Future-match structure\<close>

definition emld_rel :: "cols \<Rightarrow> cols \<Rightarrow> ty Formula.formula list \<Rightarrow> cols list \<Rightarrow>
    event_data ml\<delta>aux \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> bool" where
  "emld_rel ks cs \<psi>s css = list_all2 (\<lambda>(t, rls, rel) (t', drls, drel). t = t' \<and>
     list_all2 (\<lambda>\<psi> r. table (Formula.fv_list \<psi>) r \<and> finite r) \<psi>s rls \<and>
     drls = etabcs (map Formula.fv_list \<psi>s) css rls \<and> drel = etabc ks cs rel)"

lemma emld_rel_Nil[simp]: "emld_rel ks cs \<psi>s css [] []"
  by (simp add: emld_rel_def)

lemma emld_rel_Cons[simp]:
  "emld_rel ks cs \<psi>s css ((t, rls, rel) # aux) ((t', drls, drel) # daux) \<longleftrightarrow> t = t' \<and>
     list_all2 (\<lambda>\<psi> r. table (Formula.fv_list \<psi>) r \<and> finite r) \<psi>s rls \<and>
     drls = etabcs (map Formula.fv_list \<psi>s) css rls \<and> drel = etabc ks cs rel \<and>
     emld_rel ks cs \<psi>s css aux daux"
  by (simp add: emld_rel_def)

locale ematchF_frame = eregex_frame ks cs \<psi>s css
  for ks cs :: cols and \<psi>s :: "ty Formula.formula list" and css :: "cols list" +
  fixes mrs :: "mregex list"
  assumes d: "distinct mrs"
    and mrsok: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
       Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex ms \<psi>s) \<and> ok (length \<psi>s) ms \<and>
       set ks = fv_regex (from_mregex ms \<psi>s)"
begin

abbreviation (input) "kss \<equiv> map Formula.fv_list \<psi>s"

end




subsection \<open>Derivatives over short tuples\<close>

text \<open>
  An atom is joined by a semi-join on its mask, computed at compile time; the strict epsilons'
  unit table is the empty tuple, as safety forces the node's columns to be empty there.
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

text \<open>Without this code equation the mapping is function-backed, where keys cannot be looked up.\<close>

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

subsection \<open>Masks of the atoms\<close>

definition emb_msk :: "nat option list \<Rightarrow> bool list" where
  "emb_msk p = map (\<lambda>q. q \<noteq> None) p"

context eregex_frame
begin

abbreviation (input) "gmsks \<equiv> map (emsk cs) css"

end

context ematchP_frame
begin

end

context ematchF_frame
begin

end

(*<*)
end
(*>*)

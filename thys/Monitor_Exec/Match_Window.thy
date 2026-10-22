(*<*)
theory Match_Window
  imports Frame_Aux Until_Gen
begin
(*>*)



section \<open>The match windows over the operands' own columns\<close>

text \<open>
  @{theory MFODL_Monitor_Exec.Frame_Aux} relates the kernel's match windows at the kernel's
  columns to the kernel's windows run at the ascending columns, on the reordered operands.  The
  windows below are what the executable evaluator runs:
  an operand is probed by the semi-join against its mask instead of the kernel's join, and they
  are polymorphic in the field type.  This theory shows that at the ascending columns they are
  the kernel's windows, so the relations @{const emrd_rel} and @{const emld_rel} of
  @{theory MFODL_Monitor_Exec.Frame_Aux} hold of them unchanged.

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

text \<open>The window's lookup and tabulation are the kernel's.\<close>

lemma glookup_lookup: "glookup = lookup"
  by (simp add: glookup_def Monitor.lookup_def empty_table_def)

subsection \<open>The lax epsilon\<close>

subsection \<open>The strict epsilons\<close>

context eregex_frame
begin

abbreviation (input) "gmsks \<equiv> map (emsk cs) css"

end

subsection \<open>The past-match window\<close>

context ematchP_frame
begin

end

subsection \<open>The future-match window\<close>

context ematchF_frame
begin

end

(*<*)
end
(*>*)

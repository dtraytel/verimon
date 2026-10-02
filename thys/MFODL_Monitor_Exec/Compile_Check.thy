(*<*)
theory Compile_Check
  imports Correct Produces_Agg
begin
(*>*)

section \<open>One criterion for the whole formula\<close>

text \<open>
  The node lemmas of the four preceding theories each say: if the operands produce finite tables
  over their columns, so does this node -- one per kernel constructor, plus the two modes of
  @{const MPred} that read the database and the aggregated forms of @{const MSince} and
  @{const MUntil}.  They compose by structural induction, and the predicate \<open>mok\<close> below is what
  they compose into -- one rule per node, carrying exactly that node's lemma's hypotheses, with
  the operands' @{const produces} replaced by \<open>mok\<close> itself.  So \<open>mok\<close> is a structural criterion
  on the kernel's formula, and the theorem \<open>mok_produces\<close> that follows it discharges the
  simulation's remaining input hypothesis in one step.

  Two rules cannot be read off the kernel's formula alone: the match nodes carry a marked regular
  expression whose safety is a property of the source regex, so their rules quantify over the
  atom list the expression was compiled from.  That is why \<open>mok\<close> is inductive rather than a
  recursive function.
\<close>

inductive mok :: "nat \<Rightarrow> cols \<Rightarrow> ts \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool" where
  MokRel: "ftable ks rel \<Longrightarrow> mok n ks tw (MRel rel)"
| MokNeg: "ks = [] \<Longrightarrow> mok n ks tw (MNeg \<phi>)"
| MokAndRel: "mok n ks tw \<phi> \<Longrightarrow> mok n ks tw (MAndRel cs \<phi> conf)"
| MokAndAssign: "mok n k tw \<phi> \<Longrightarrow> ks = k @ [fst conf] \<Longrightarrow> mok n ks tw (MAndAssign cs \<phi> conf)"
| MokExists: "mok (Suc n) kks tw \<phi> \<Longrightarrow> ks = ex_cols cs \<Longrightarrow> mok n ks tw (MExists cs \<phi>)"
| MokPredDb: "mode \<noteq> Match \<Longrightarrow> length ks = length tms \<Longrightarrow> mok n ks tw (MPred e tms mode)"
| MokPredM: "ks = pred_cols tms \<Longrightarrow> mok n ks tw (MPred e tms Match)"
| MokTP: "ks = mtrm_ecols mt \<Longrightarrow> mok n ks tw (MTP mt i)"
| MokTS: "ks = mtrm_ecols mt \<Longrightarrow> mok n ks tw (MTS mt)"
| MokOr: "mok n ks tw \<phi> \<Longrightarrow> mok n k2 tw \<psi> \<Longrightarrow>
    list_all (ftable ks) (fst buf) \<Longrightarrow> list_all (ftable k2) (snd buf) \<Longrightarrow>
    mok n ks tw (MOr ks \<phi> k2 \<psi> buf)"
| MokAnd: "mok n k1 tw \<phi> \<Longrightarrow> mok n k2 tw \<psi> \<Longrightarrow>
    list_all (ftable k1) (fst buf) \<Longrightarrow> list_all (ftable k2) (snd buf) \<Longrightarrow>
    distinct k1 \<Longrightarrow> distinct k2 \<Longrightarrow> (\<not> pos \<Longrightarrow> set k2 \<subseteq> set k1) \<Longrightarrow> ks = cols_union k1 k2 \<Longrightarrow>
    mok n ks tw (MAnd k1 \<phi> pos k2 \<psi> buf)"
| MokPrev: "mok n ks tw \<phi> \<Longrightarrow> list_all (ftable ks) buf \<Longrightarrow> mok n ks tw (MPrev I \<phi> first buf nts)"
| MokNext: "mok n ks tw \<phi> \<Longrightarrow> mok n ks tw (MNext I \<phi> first nts)"
| MokAgg: "mok (length (aggargs_tys args) + n) k0 tw \<phi> \<Longrightarrow>
    (aggargs_g0 args \<Longrightarrow> shift_cols (length (aggargs_tys args)) (aggargs_cols args) = []) \<Longrightarrow>
    ks = aggargs_y args # shift_cols (length (aggargs_tys args)) (aggargs_cols args) \<Longrightarrow>
    mok n ks tw (MAgg args \<phi>)"
| MokAnds: "length L = length ((k0 # kss) @ nkss) \<Longrightarrow> length buf = length ((k0 # kss) @ nkss) \<Longrightarrow>
    (\<forall>i < length ((k0 # kss) @ nkss). mok n (((k0 # kss) @ nkss) ! i) tw (L ! i)) \<Longrightarrow>
    (\<forall>i < length ((k0 # kss) @ nkss). list_all (ftable (((k0 # kss) @ nkss) ! i)) (buf ! i)) \<Longrightarrow>
    (\<forall>k \<in> set ((k0 # kss) @ nkss). distinct k) \<Longrightarrow>
    (\<forall>k \<in> set nkss. set k \<subseteq> set (kands_cols k0 kss)) \<Longrightarrow>
    distinct ks \<Longrightarrow> set ks = set (kands_cols k0 kss) \<Longrightarrow>
    mok n ks tw (MAnds ks (k0 # kss) nkss L buf)"
| MokSince: "mok n kL tw \<phi> \<Longrightarrow> mok n kR tw \<psi> \<Longrightarrow>
    saux_inv args kL kR tw buf aux \<Longrightarrow> args_agg args = None \<Longrightarrow> args_n args = n \<Longrightarrow>
    args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow> set kL \<subseteq> set kR \<Longrightarrow>
    mok n kR tw (MSince args \<phi> \<psi> buf aux)"
| MokUntil: "mok n kL tw \<phi> \<Longrightarrow> mok n kR tw \<psi> \<Longrightarrow>
    until_inv args kL kR tw t aux buf nts \<Longrightarrow> args_agg args = None \<Longrightarrow> args_n args = n \<Longrightarrow>
    args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow> set kL \<subseteq> set kR \<Longrightarrow>
    mok n kR tw (MUntil args \<phi> \<psi> buf nts t aux)"
| MokSinceAgg: "mok m kL tw \<phi> \<Longrightarrow> mok m kR tw \<psi> \<Longrightarrow>
    saux_inv args kL kR tw buf aux \<Longrightarrow> args_agg args = Some aggargs \<Longrightarrow> args_n args = m \<Longrightarrow>
    args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow> set kL \<subseteq> set kR \<Longrightarrow>
    (aggargs_g0 aggargs \<Longrightarrow> shift_cols (length (aggargs_tys aggargs)) (aggargs_cols aggargs) = []) \<Longrightarrow>
    ks = aggargs_y aggargs # shift_cols (length (aggargs_tys aggargs)) (aggargs_cols aggargs) \<Longrightarrow>
    mok n ks tw (MSince args \<phi> \<psi> buf aux)"
| MokUntilAgg: "mok m kL tw \<phi> \<Longrightarrow> mok m kR tw \<psi> \<Longrightarrow>
    until_inv args kL kR tw t aux buf nts \<Longrightarrow> args_agg args = Some aggargs \<Longrightarrow> args_n args = m \<Longrightarrow>
    args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow> set kL \<subseteq> set kR \<Longrightarrow>
    (aggargs_g0 aggargs \<Longrightarrow> shift_cols (length (aggargs_tys aggargs)) (aggargs_cols aggargs) = []) \<Longrightarrow>
    ks = aggargs_y aggargs # shift_cols (length (aggargs_tys aggargs)) (aggargs_cols aggargs) \<Longrightarrow>
    mok n ks tw (MUntil args \<phi> \<psi> buf nts t aux)"
| MokTrigger: "mok n kL tw \<phi> \<Longrightarrow> mok n kR tw \<psi> \<Longrightarrow>
    trigger_inv args kL kR tw aux buf nts \<Longrightarrow>
    args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow> mem (args_ivl args) 0 \<Longrightarrow>
    mok n kR tw (MTrigger args \<phi> \<psi> buf nts aux)"
| MokAndTrigger: "mok n ks tw \<alpha> \<Longrightarrow> mok n kL tw \<phi> \<Longrightarrow> mok n kR tw \<psi> \<Longrightarrow>
    trigger_inv args kL kR tw aux buf2 nts \<Longrightarrow>
    list_all (ftable ks) (fst buf1) \<Longrightarrow> list_all (tpair kR) (snd buf1) \<Longrightarrow>
    args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow> distinct ks \<Longrightarrow> distinct kR \<Longrightarrow>
    (mem (args_ivl args) 0 \<or> (args_pos args \<and> set kL = set kR)) \<Longrightarrow> set kR \<subseteq> set ks \<Longrightarrow>
    mok n ks tw (MAndTrigger ks \<alpha> buf1 args \<phi> \<psi> buf2 nts aux)"
| MokLet: "mok m kks tw \<phi> \<Longrightarrow> mok n ks tw \<psi> \<Longrightarrow> mok n ks tw (MLet p m kks \<phi> \<psi>)"
| MokLetPast: "mok m kks tw \<phi> \<Longrightarrow> mok n ks tw \<psi> \<Longrightarrow>
    (\<forall>y. buf = Some y \<longrightarrow> ftable [0..<m] y) \<Longrightarrow>
    mok n ks tw (MLetPast p m kks \<phi> \<psi> i buf)"
| MokFrz: "mok m kks tw \<phi> \<Longrightarrow> mok n ks tw \<psi> \<Longrightarrow>
    list_all (ftable [0..<m]) \<alpha>s \<Longrightarrow> mok n ks tw \<rho> \<Longrightarrow> list_all (ftable ks) rb \<Longrightarrow>
    (lv \<noteq> None \<longrightarrow> mok n ks tw \<rho>L) \<Longrightarrow>
    mok n ks tw (MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L)"
| MokMatchP: "Regex.safe_regex fv rgx_safe_pred Past Strict
      (from_mregex mr (\<psi>s :: ty Formula.formula list)) \<Longrightarrow>
    ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow> distinct ks \<Longrightarrow>
    distinct mrs \<Longrightarrow> set mrs = RPDs mr \<Longrightarrow>
    (\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> set ks) \<Longrightarrow> dss = map Formula.fv_list \<psi>s \<Longrightarrow>
    length L = length \<psi>s \<Longrightarrow> (\<forall>i < length \<psi>s. mok n (dss ! i) tw (L ! i)) \<Longrightarrow>
    length buf = length \<psi>s \<Longrightarrow> (\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (buf ! i)) \<Longrightarrow>
    maux_inv ks aux \<Longrightarrow>
    mok n ks tw (MMatchP I ks dss mr mrs L buf nts aux)"
| MokMatchF: "Regex.safe_regex fv rgx_safe_pred Futu Strict
      (from_mregex mr (\<psi>s :: ty Formula.formula list)) \<Longrightarrow>
    ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow> distinct ks \<Longrightarrow>
    distinct mrs \<Longrightarrow> set mrs = LPDs mr \<Longrightarrow>
    (\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> set ks) \<Longrightarrow> dss = map Formula.fv_list \<psi>s \<Longrightarrow>
    length L = length \<psi>s \<Longrightarrow> (\<forall>i < length \<psi>s. mok n (dss ! i) tw (L ! i)) \<Longrightarrow>
    length buf = length \<psi>s \<Longrightarrow> (\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (buf ! i)) \<Longrightarrow>
    mfaux_inv ks \<psi>s aux \<Longrightarrow>
    mok n ks tw (MMatchF I ks dss mr mrs L buf nts t aux)"

text \<open>
  Every rule is discharged by the node lemma it was read off, applied to the induction
  hypotheses of its operands.
\<close>

theorem mok_produces: "mok n ks tw \<phi> \<Longrightarrow> produces n ks tw \<phi>"
proof (induct rule: mok.induct)
  case MokRel then show ?case by (rule produces_MRel)
next
  case MokNeg then show ?case by (simp add: produces_MNeg)
next
  case MokAndRel then show ?case by (simp add: produces_MAndRel)
next
  case MokAndAssign then show ?case by (simp add: produces_MAndAssign)
next
  case MokExists then show ?case by (simp add: produces_MExists)
next
  case MokPredDb then show ?case by (simp add: produces_MPred_db)
next
  case MokPredM then show ?case by (simp add: produces_MPred_Match)
next
  case MokTP then show ?case by (simp add: produces_MTP)
next
  case MokTS then show ?case by (simp add: produces_MTS)
next
  case MokOr then show ?case by (simp add: produces_MOr)
next
  case (MokAnd n k1 tw \<phi> k2 \<psi> buf pos ks)
  show ?case unfolding MokAnd(10)
    by (rule produces_MAnd[OF MokAnd(2) MokAnd(4) MokAnd(5) MokAnd(6) MokAnd(7) MokAnd(8)
        MokAnd(9)])
next
  case MokPrev then show ?case by (simp add: produces_MPrev)
next
  case MokNext then show ?case by (simp add: produces_MNext)
next
  case (MokAgg args n k0 tw \<phi> ks)
  show ?case unfolding MokAgg(4) by (rule produces_MAgg[OF MokAgg(2) MokAgg(3)])
next
  case (MokAnds L k0 kss nkss buf n tw ks)
  have pL: "\<forall>i < length ((k0 # kss) @ nkss). produces n (((k0 # kss) @ nkss) ! i) tw (L ! i)"
    using MokAnds(3) by blast
  show ?case
    by (rule produces_MAnds[OF MokAnds(1) MokAnds(2) pL MokAnds(4) MokAnds(5) MokAnds(6)
        MokAnds(7) MokAnds(8)])
next
  case MokSince
  show ?case
    by (rule produces_MSince_plain[OF MokSince(2) MokSince(4) MokSince(5) MokSince(6)
        MokSince(7) MokSince(8) MokSince(9) MokSince(10)])
next
  case MokUntil
  show ?case
    by (rule produces_MUntil_plain[OF MokUntil(2) MokUntil(4) MokUntil(5) MokUntil(6)
        MokUntil(7) MokUntil(8) MokUntil(9) MokUntil(10)])
next
  case MokSinceAgg
  show ?case unfolding MokSinceAgg(12)
    by (rule produces_MSince_agg[OF MokSinceAgg(2) MokSinceAgg(4) MokSinceAgg(5)
        MokSinceAgg(6) MokSinceAgg(7) MokSinceAgg(8) MokSinceAgg(9) MokSinceAgg(10)
        MokSinceAgg(11)])
next
  case MokUntilAgg
  show ?case unfolding MokUntilAgg(12)
    by (rule produces_MUntil_agg[OF MokUntilAgg(2) MokUntilAgg(4) MokUntilAgg(5)
        MokUntilAgg(6) MokUntilAgg(7) MokUntilAgg(8) MokUntilAgg(9) MokUntilAgg(10)
        MokUntilAgg(11)])
next
  case MokTrigger
  show ?case
    by (rule produces_MTrigger[OF MokTrigger(2) MokTrigger(4) MokTrigger(5)
        MokTrigger(6) MokTrigger(7) MokTrigger(8)])
next
  case MokAndTrigger
  show ?case
    by (rule produces_MAndTrigger[OF MokAndTrigger(2) MokAndTrigger(4) MokAndTrigger(6)
        MokAndTrigger(7) MokAndTrigger(8) MokAndTrigger(9) MokAndTrigger(10)
        MokAndTrigger(11) MokAndTrigger(12) MokAndTrigger(13) MokAndTrigger(14)
        MokAndTrigger(15)])
next
  case MokLet
  show ?case by (rule produces_MLet[OF MokLet(2) MokLet(4)])
next
  case MokLetPast
  show ?case by (rule produces_MLetPast[OF MokLetPast(2) MokLetPast(4) MokLetPast(5)])
next
  case MokFrz
  show ?case
    by (rule produces_MFrz[OF MokFrz(2) MokFrz(4) MokFrz(5) MokFrz(7) MokFrz(8)])
      (use MokFrz(9) in blast)
next
  case (MokMatchP mr \<psi>s ks mrs dss L n tw buf aux I nts)
  have pL: "\<forall>i < length \<psi>s. produces n (dss ! i) tw (L ! i)"
    using MokMatchP(10) by blast
  show ?case unfolding MokMatchP(8)
    by (rule produces_MMatchP[OF MokMatchP(1) MokMatchP(2) MokMatchP(3) MokMatchP(4)
        MokMatchP(5) MokMatchP(6) MokMatchP(7) MokMatchP(9) pL[unfolded MokMatchP(8)]
        MokMatchP(11) MokMatchP(12)[unfolded MokMatchP(8)] MokMatchP(13)])
next
  case (MokMatchF mr \<psi>s ks mrs dss L n tw buf aux I nts t)
  have pL: "\<forall>i < length \<psi>s. produces n (dss ! i) tw (L ! i)"
    using MokMatchF(10) by blast
  show ?case unfolding MokMatchF(8)
    by (rule produces_MMatchF[OF MokMatchF(1) MokMatchF(2) MokMatchF(3) MokMatchF(4)
        MokMatchF(5) MokMatchF(6) MokMatchF(7) MokMatchF(9) pL[unfolded MokMatchF(8)]
        MokMatchF(11) MokMatchF(12)[unfolded MokMatchF(8)] MokMatchF(13)])
qed

section \<open>Closing the chain\<close>

text \<open>
  The transferred correctness theorems of @{theory MFODL_Monitor_Exec.Correct} all ask the
  caller for a related initial state, @{term "emsim_state n ks cs 0 (minit_safe \<phi>) dst"}, and
  until one is produced they say nothing about any concrete monitor.  Everything the criterion of
  the previous section buys is the hypothesis @{const produces}, which @{thm [source]
  mok_produces} now supplies from a structural check; the state itself is built by the descending
  compiler of the theory after next.
\<close>

(*<*)
end
(*>*)

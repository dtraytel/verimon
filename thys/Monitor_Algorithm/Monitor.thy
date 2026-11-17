(*<*)
theory Monitor
  imports
    "MFODL_Logic.Typing"
    "MFODL_Logic.Freeze_Locality"
    "MFODL_Logic.Monitorable"
    "MFODL_Logic.Table_Join"
    "HOL-Library.While_Combinator"
    "HOL-Library.Mapping"
begin
(*>*)

section \<open>Generic monitoring algorithm\<close>

text \<open>The algorithm is parametrized by the auxiliary data structures of the temporal operators.\<close>

subsection \<open>Regular expressions\<close>

subsubsection \<open>Indexed regular expressions\<close>

datatype mregex =
  MSkip nat
  | MTestPos nat
  | MTestNeg nat
  | MPlus mregex mregex
  | MTimes mregex mregex
  | MStar mregex

primrec ok where
  "ok _ (MSkip n) = True"
| "ok m (MTestPos n) = (n < m)"
| "ok m (MTestNeg n) = (n < m)"
| "ok m (MPlus r s) = (ok m r \<and> ok m s)"
| "ok m (MTimes r s) = (ok m r \<and> ok m s)"
| "ok m (MStar r) = ok m r"

primrec from_mregex where
  "from_mregex (MSkip n) _ = Regex.Skip n"
| "from_mregex (MTestPos n) \<phi>s = Regex.Test (\<phi>s ! n)"
| "from_mregex (MTestNeg n) \<phi>s = (if safe_formula (Formula.Neg (\<phi>s ! n))
    then Regex.Test (Formula.Neg (Formula.Neg (Formula.Neg (\<phi>s ! n))))
    else Regex.Test (Formula.Neg (\<phi>s ! n)))"
| "from_mregex (MPlus r s) \<phi>s = Regex.Plus (from_mregex r \<phi>s) (from_mregex s \<phi>s)"
| "from_mregex (MTimes r s) \<phi>s = Regex.Times (from_mregex r \<phi>s) (from_mregex s \<phi>s)"
| "from_mregex (MStar r) \<phi>s = Regex.Star (from_mregex r \<phi>s)"

primrec to_mregex_exec where
  "to_mregex_exec (Regex.Skip n) xs = (MSkip n, xs)"
| "to_mregex_exec (Regex.Test \<phi>) xs = (if safe_formula \<phi> then (MTestPos (length xs), xs @ [\<phi>])
     else case \<phi> of Formula.Neg \<phi>' \<Rightarrow> (MTestNeg (length xs), xs @ [\<phi>']) | _ \<Rightarrow> (MSkip 0, xs))"
| "to_mregex_exec (Regex.Plus r s) xs =
     (let (mr, ys) = to_mregex_exec r xs; (ms, zs) = to_mregex_exec s ys
     in (MPlus mr ms, zs))"
| "to_mregex_exec (Regex.Times r s) xs =
     (let (mr, ys) = to_mregex_exec r xs; (ms, zs) = to_mregex_exec s ys
     in (MTimes mr ms, zs))"
| "to_mregex_exec (Regex.Star r) xs =
     (let (mr, ys) = to_mregex_exec r xs in (MStar mr, ys))"

primrec shift where
  "shift (MSkip n) k = MSkip n"
| "shift (MTestPos i) k = MTestPos (i + k)"
| "shift (MTestNeg i) k = MTestNeg (i + k)"
| "shift (MPlus r s) k = MPlus (shift r k) (shift s k)"
| "shift (MTimes r s) k = MTimes (shift r k) (shift s k)"
| "shift (MStar r) k = MStar (shift r k)"

primrec to_mregex where
  "to_mregex (Regex.Skip n) = (MSkip n, [])"
| "to_mregex (Regex.Test \<phi>) = (if safe_formula \<phi> then (MTestPos 0, [\<phi>])
     else case \<phi> of Formula.Neg \<phi>' \<Rightarrow> (MTestNeg 0, [\<phi>']) | _ \<Rightarrow> (MSkip 0, []))"
| "to_mregex (Regex.Plus r s) =
     (let (mr, ys) = to_mregex r; (ms, zs) = to_mregex s
     in (MPlus mr (shift ms (length ys)), ys @ zs))"
| "to_mregex (Regex.Times r s) =
     (let (mr, ys) = to_mregex r; (ms, zs) = to_mregex s
     in (MTimes mr (shift ms (length ys)), ys @ zs))"
| "to_mregex (Regex.Star r) =
     (let (mr, ys) = to_mregex r in (MStar mr, ys))"

lemma shift_0: "shift r 0 = r"
  by (induct r) auto

lemma shift_shift: "shift (shift r k) j = shift r (k + j)"
  by (induct r) auto

lemma to_mregex_to_mregex_exec:
  "case to_mregex r of (mr, \<phi>s) \<Rightarrow> to_mregex_exec r xs = (shift mr (length xs), xs @ \<phi>s)"
  by (induct r arbitrary: xs)
    (auto simp: shift_shift ac_simps split: formula.splits prod.splits)

lemma to_mregex_to_mregex_exec_Nil[code]: "to_mregex r = to_mregex_exec r []"
  using to_mregex_to_mregex_exec[where xs="[]" and r = r] by (auto simp: shift_0)

lemma ok_mono: "ok m mr \<Longrightarrow> m \<le> n \<Longrightarrow> ok n mr"
  by (induct mr) auto

lemma ok_shift: "ok (i + m) (Monitor.shift r i) \<longleftrightarrow> ok m r"
  by (induct r) auto

lemma to_mregex_ok: "to_mregex r = (mr, ys) \<Longrightarrow> set ys = safe_atms r \<and> ok (length ys) mr"
proof (induct r arbitrary: mr ys)
  case (Skip x)
  then show ?case by (auto simp: safe_atms_def elim: ok_mono split: if_splits prod.splits)
next
  case (Test x)
  show ?case proof (cases "\<exists>x'. x = Formula.Neg x'")
    case True
    with Test show ?thesis 
      by (auto split: if_splits prod.splits simp: safe_atms_def elim: ok_mono)
  next
    case False
    with Test show ?thesis 
      by (auto split: if_splits prod.splits simp: safe_atms_def not_Neg_cases elim: ok_mono)
  qed
next
  case (Plus r1 r2)
  then show ?case by (fastforce simp: ok_shift safe_atms_def elim: ok_mono split: if_splits prod.splits)
next
  case (Times r1 r2)
  then show ?case by (fastforce simp: ok_shift safe_atms_def elim: ok_mono split: if_splits prod.splits)
next
  case (Star r)
  then show ?case by (auto simp: safe_atms_def elim: ok_mono split: if_splits prod.splits)
qed


derive linorder mregex

subsubsection \<open>Left partial derivatives\<close>

definition saturate where
  "saturate f = while (\<lambda>S. f S \<noteq> S) f"

lemma saturate_code[code]:
  "saturate f S = (let S' = f S in if S' = S then S else saturate f S')"
  unfolding saturate_def Let_def
  by (subst while_unfold) auto

lemma saturate_commute:
  assumes "\<And>s. r \<in> g s" "\<And>s. g (Set.insert r s) = g s" "\<And>s. r \<in> s \<Longrightarrow> h s = g s"
  and terminates: "mono g" "\<And>X. X \<subseteq> C \<Longrightarrow> g X \<subseteq> C" "finite C"
shows "saturate g {} = saturate h {r}"
proof (cases "g {} = {r}")
  case True
  with assms have "g {r} = {r}" "h {r} = {r}" by auto
  with True show ?thesis
    by (subst (1 2) saturate_code; subst saturate_code) (simp add: Let_def)
next
  case False
  then show ?thesis
    unfolding saturate_def while_def
    using while_option_finite_subset_Some[OF terminates] assms(1-3)
    by (subst while_option_commute_invariant[of "\<lambda>S. S = {} \<or> r \<in> S" "\<lambda>S. g S \<noteq> S" g "\<lambda>S. h S \<noteq> S" "Set.insert r" h "{}", symmetric])
      (auto 4 4 dest: while_option_stop[of "\<lambda>S. g S \<noteq> S" g "{}"])
qed

definition "MTimesL r S = MTimes r ` S"
definition "MTimesR R s = (\<lambda>r. MTimes r s) ` R"

primrec LPD where
  "LPD (MSkip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> {MSkip m})"
| "LPD (MTestPos \<phi>) = {}"
| "LPD (MTestNeg \<phi>) = {}"
| "LPD (MPlus r s) = (LPD r \<union> LPD s)"
| "LPD (MTimes r s) = MTimesR (LPD r) s \<union> LPD s"
| "LPD (MStar r) = MTimesR (LPD r) (MStar r)"

primrec LPDi where
  "LPDi 0 r = {r}"
| "LPDi (Suc i) r = (\<Union>s \<in> LPD r. LPDi i s)"

lemma LPDi_Suc_alt: "LPDi (Suc i) r = (\<Union>s \<in> LPDi i r. LPD s)"
  by (induct i arbitrary: r) fastforce+

definition "LPDs r = (\<Union>i. LPDi i r)"

lemma LPDs_refl: "r \<in> LPDs r"
  by (auto simp: LPDs_def intro: exI[of _ 0])
lemma LPDs_trans: "r \<in> LPD s \<Longrightarrow> s \<in> LPDs t \<Longrightarrow> r \<in> LPDs t"
  by (force simp: LPDs_def LPDi_Suc_alt simp del: LPDi.simps intro: exI[of _ "Suc _"])

lemma LPDi_Test:
  "LPDi i (MSkip 0) \<subseteq> {MSkip 0}"
  "LPDi i (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "LPDi i (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  by (induct i) auto

lemma LPDs_Test:
  "LPDs (MSkip 0) \<subseteq> {MSkip 0}"
  "LPDs (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "LPDs (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  unfolding LPDs_def using LPDi_Test by blast+

lemma LPDi_MSkip: "LPDi i (MSkip n) \<subseteq> MSkip ` {i. i \<le> n}"
  by (induct i arbitrary: n) (auto dest: set_mp[OF LPDi_Test(1)] simp: le_Suc_eq split: nat.splits)

lemma LPDs_MSkip: "LPDs (MSkip n) \<subseteq> MSkip ` {i. i \<le> n}"
  unfolding LPDs_def using LPDi_MSkip by auto

lemma LPDi_Plus: "LPDi i (MPlus r s) \<subseteq> {MPlus r s} \<union> LPDi i r \<union> LPDi i s"
  by (induct i arbitrary: r s) auto

lemma LPDs_Plus: "LPDs (MPlus r s) \<subseteq> {MPlus r s} \<union> LPDs r \<union> LPDs s"
  unfolding LPDs_def using LPDi_Plus[of _ r s] by auto

lemma LPDi_Times:
  "LPDi i (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesR (\<Union>j \<le> i. LPDi j r) s \<union> (\<Union>j \<le> i. LPDi j s)"
proof (induct i arbitrary: r s)
  case (Suc i)
  show ?case
    by (fastforce simp: MTimesR_def dest: bspec[of _ _ "Suc _"] dest!: set_mp[OF Suc])
qed simp

lemma LPDs_Times: "LPDs (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesR (LPDs r) s \<union> LPDs s"
  unfolding LPDs_def using LPDi_Times[of _ r s] by (force simp: MTimesR_def)

lemma LPDi_Star: "j \<le> i \<Longrightarrow> LPDi j (MStar r) \<subseteq> {MStar r} \<union> MTimesR (\<Union>j \<le> i. LPDi j r) (MStar r)"
proof (induct i arbitrary: j r)
  case (Suc i)
  from Suc(2) show ?case
    by (auto 0 5 simp: MTimesR_def image_iff le_Suc_eq
        dest: bspec[of _ _ "Suc 0"] bspec[of _ _ "Suc _"] set_mp[OF Suc(1)] dest!: set_mp[OF LPDi_Times])
qed simp

lemma LPDs_Star: "LPDs (MStar r) \<subseteq> {MStar r} \<union> MTimesR (LPDs r) (MStar r)"
  unfolding LPDs_def using LPDi_Star[OF order_refl, of _ r] by (force simp: MTimesR_def)

lemma finite_LPDs: "finite (LPDs r)"
proof (induct r)
  case (MSkip n)
  then show ?case by (intro finite_subset[OF LPDs_MSkip]) simp
next
  case (MTestPos \<phi>)
  then show ?case by (intro finite_subset[OF LPDs_Test(2)]) simp
next
  case (MTestNeg \<phi>)
  then show ?case by (intro finite_subset[OF LPDs_Test(3)]) simp
next
  case (MPlus r s)
  then show ?case by (intro finite_subset[OF LPDs_Plus]) simp
next
  case (MTimes r s)
  then show ?case by (intro finite_subset[OF LPDs_Times]) (simp add: MTimesR_def)
next
  case (MStar r)
  then show ?case by (intro finite_subset[OF LPDs_Star]) (simp add: MTimesR_def)
qed

context begin

private abbreviation (input) "addLPD r \<equiv> \<lambda>S. insert r S \<union> Set.bind (insert r S) LPD"

private lemma mono_addLPD: "mono (addLPD r)"
  unfolding mono_def Set.bind_def by auto

private lemma LPDs_aux1: "lfp (addLPD r) \<subseteq> LPDs r"
  by (rule lfp_induct[OF mono_addLPD], auto intro: LPDs_refl LPDs_trans simp: Set.bind_def)

private lemma LPDs_aux2: "LPDi i r \<subseteq> lfp (addLPD r)"
proof (induct i)
  case 0
  then show ?case
    by (subst lfp_unfold[OF mono_addLPD]) auto
next
  case (Suc i)
  then show ?case
    by (subst lfp_unfold[OF mono_addLPD]) (auto simp: LPDi_Suc_alt simp del: LPDi.simps)
qed

lemma LPDs_alt: "LPDs r = lfp (addLPD r)"
  using LPDs_aux1 LPDs_aux2 by (force simp: LPDs_def)

lemma LPDs_code[code]:
  "LPDs r = saturate (addLPD r) {}"
  unfolding LPDs_alt saturate_def
  by (rule lfp_while[OF mono_addLPD _ finite_LPDs, of r]) (auto simp: LPDs_refl LPDs_trans Set.bind_def)

end

subsubsection \<open>Right partial derivatives\<close>

primrec RPD where
  "RPD (MSkip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> {MSkip m})"
| "RPD (MTestPos \<phi>) = {}"
| "RPD (MTestNeg \<phi>) = {}"
| "RPD (MPlus r s) = (RPD r \<union> RPD s)"
| "RPD (MTimes r s) = MTimesL r (RPD s) \<union> RPD r"
| "RPD (MStar r) = MTimesL (MStar r) (RPD r)"

primrec RPDi where
  "RPDi 0 r = {r}"
| "RPDi (Suc i) r = (\<Union>s \<in> RPD r. RPDi i s)"

lemma RPDi_Suc_alt: "RPDi (Suc i) r = (\<Union>s \<in> RPDi i r. RPD s)"
  by (induct i arbitrary: r) fastforce+

definition "RPDs r = (\<Union>i. RPDi i r)"

lemma RPDs_refl: "r \<in> RPDs r"
  by (auto simp: RPDs_def intro: exI[of _ 0])
lemma RPDs_trans: "r \<in> RPD s \<Longrightarrow> s \<in> RPDs t \<Longrightarrow> r \<in> RPDs t"
  by (force simp: RPDs_def RPDi_Suc_alt simp del: RPDi.simps intro: exI[of _ "Suc _"])

lemma RPDi_Test:
  "RPDi i (MSkip 0) \<subseteq> {MSkip 0}"
  "RPDi i (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "RPDi i (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  by (induct i) auto

lemma RPDs_Test:
  "RPDs (MSkip 0) \<subseteq> {MSkip 0}"
  "RPDs (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "RPDs (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  unfolding RPDs_def using RPDi_Test by blast+

lemma RPDi_MSkip: "RPDi i (MSkip n) \<subseteq> MSkip ` {i. i \<le> n}"
  by (induct i arbitrary: n) (auto dest: set_mp[OF RPDi_Test(1)] simp: le_Suc_eq split: nat.splits)

lemma RPDs_MSkip: "RPDs (MSkip n) \<subseteq> MSkip ` {i. i \<le> n}"
  unfolding RPDs_def using RPDi_MSkip by auto

lemma RPDi_Plus: "RPDi i (MPlus r s) \<subseteq> {MPlus r s} \<union> RPDi i r \<union> RPDi i s"
  by (induct i arbitrary: r s) auto

lemma RPDs_Plus: "RPDs (MPlus r s) \<subseteq> {MPlus r s} \<union> RPDs r \<union> RPDs s"
  unfolding RPDs_def using RPDi_Plus[of _ r s] by auto

lemma RPDi_Times:
  "RPDi i (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesL r (\<Union>j \<le> i. RPDi j s) \<union> (\<Union>j \<le> i. RPDi j r)"
proof (induct i arbitrary: r s)
  case (Suc i)
  show ?case
    by (fastforce simp: MTimesL_def dest: bspec[of _ _ "Suc _"] dest!: set_mp[OF Suc])
qed simp

lemma RPDs_Times: "RPDs (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesL r (RPDs s) \<union> RPDs r"
  unfolding RPDs_def using RPDi_Times[of _ r s] by (force simp: MTimesL_def)

lemma RPDi_Star: "j \<le> i \<Longrightarrow> RPDi j (MStar r) \<subseteq> {MStar r} \<union> MTimesL (MStar r) (\<Union>j \<le> i. RPDi j r)"
proof (induct i arbitrary: j r)
  case (Suc i)
  from Suc(2) show ?case
    by (auto 0 5 simp: MTimesL_def image_iff le_Suc_eq
        dest: bspec[of _ _ "Suc 0"] bspec[of _ _ "Suc _"] set_mp[OF Suc(1)] dest!: set_mp[OF RPDi_Times])
qed simp

lemma RPDs_Star: "RPDs (MStar r) \<subseteq> {MStar r} \<union> MTimesL (MStar r) (RPDs r)"
  unfolding RPDs_def using RPDi_Star[OF order_refl, of _ r] by (force simp: MTimesL_def)

lemma finite_RPDs: "finite (RPDs r)"
proof (induct r)
  case MSkip
  then show ?case by (intro finite_subset[OF RPDs_MSkip]) simp
next
  case (MTestPos \<phi>)
  then show ?case by (intro finite_subset[OF RPDs_Test(2)]) simp
next
  case (MTestNeg \<phi>)
  then show ?case by (intro finite_subset[OF RPDs_Test(3)]) simp
next
  case (MPlus r s)
  then show ?case by (intro finite_subset[OF RPDs_Plus]) simp
next
  case (MTimes r s)
  then show ?case by (intro finite_subset[OF RPDs_Times]) (simp add: MTimesL_def)
next
  case (MStar r)
  then show ?case by (intro finite_subset[OF RPDs_Star]) (simp add: MTimesL_def)
qed

context begin

private abbreviation (input) "addRPD r \<equiv> \<lambda>S. insert r S \<union> Set.bind (insert r S) RPD"

private lemma mono_addRPD: "mono (addRPD r)"
  unfolding mono_def Set.bind_def by auto

private lemma RPDs_aux1: "lfp (addRPD r) \<subseteq> RPDs r"
  by (rule lfp_induct[OF mono_addRPD], auto intro: RPDs_refl RPDs_trans simp: Set.bind_def)

private lemma RPDs_aux2: "RPDi i r \<subseteq> lfp (addRPD r)"
proof (induct i)
  case 0
  then show ?case
    by (subst lfp_unfold[OF mono_addRPD]) auto
next
  case (Suc i)
  then show ?case
    by (subst lfp_unfold[OF mono_addRPD]) (auto simp: RPDi_Suc_alt simp del: RPDi.simps)
qed

lemma RPDs_alt: "RPDs r = lfp (addRPD r)"
  using RPDs_aux1 RPDs_aux2 by (force simp: RPDs_def)

lemma RPDs_code[code]:
  "RPDs r = saturate (addRPD r) {}"
  unfolding RPDs_alt saturate_def
  by (rule lfp_while[OF mono_addRPD _ finite_RPDs, of r]) (auto simp: RPDs_refl RPDs_trans Set.bind_def)

end


subsection \<open>Datatypes of the monitor state\<close>

type_synonym ts = nat

type_synonym 'a mbuf2 = "'a table list \<times> 'a table list"
type_synonym 'a mbuft2 = "('a table) list \<times> (nat list \<times> 'a table) list"
type_synonym 'a mbufn = "'a table list list"
type_synonym 'a mbuf2S = "'a table list \<times> 'a table list \<times> ts list \<times> bool"

type_synonym 'a msaux = "(ts \<times> 'a table) list"
type_synonym 'a mtaux = "(ts \<times> 'a table \<times> 'a table) list"
type_synonym 'a muaux = "(ts \<times> 'a table \<times> 'a table) list"
type_synonym 'a mr\<delta>aux = "(ts \<times> (mregex, 'a table) mapping) list"
type_synonym 'a ml\<delta>aux = "(ts \<times> 'a table list \<times> 'a table) list"

datatype mconstraint = MEq | MLess | MLessEq

record aggargs =
  aggargs_cols :: "nat list"
  aggargs_n :: nat
  aggargs_g0 :: bool
  aggargs_y :: nat
  aggargs_\<omega> :: "ty Formula.agg_op"
  aggargs_tys :: "ty list"
  aggargs_f :: "Formula.trm"

record args =
  args_ivl :: \<I>
  args_n :: nat
  args_L :: "nat list"
  args_R :: "nat list"
  args_pos :: bool
  args_agg :: "aggargs option"

datatype pred_mode = Copy | Simple | Match

datatype mtrm = MVar nat | MConst event_data

text \<open>The mode of a freeze: not separable, replaying the body per frozen table, or running two
copies of the body, fed a table @{term L} of all pending frozen tables and the empty table.\<close>

datatype ('a, 't) frz_sep =
    FSOff
  | FSStock nat nat nat 'a nat nat nat "'a list"
  | FSSep 'a nat nat "('t \<times> 't) list" nat nat nat 'a

text \<open>The operations of the separable mode: combining the copies' verdicts, union, number of new
tuples, size, empty table and sample.\<close>

datatype ('a, 't) frz_ops = FrzOps (fo_cmb: "'t \<Rightarrow> 't \<Rightarrow> 'a \<Rightarrow> 't") (fo_un: "'a \<Rightarrow> 'a \<Rightarrow> 'a")
  (fo_fr: "'a \<Rightarrow> 'a \<Rightarrow> nat") (fo_cd: "'a \<Rightarrow> nat") (fo_emp: 'a) (fo_smp: "'a \<Rightarrow> 'a")

text \<open>Each node produces its tables over the columns @{const Formula.fv_list} of its formula and
records its operands' columns where it combines their tables.\<close>

datatype (dead 'msaux, dead 'muaux, dead 'mtaux) mformula =
  MRel "event_data table"
  | MPred Formula.name "Formula.trm list" pred_mode
  | MLet Formula.name nat "nat list" "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula"
  | MFrz Formula.name nat "nat list" "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula"
     nat nat nat "event_data table list"
     "('msaux, 'muaux, 'mtaux) mformula" nat nat "ts list" "event_data table list" enat bool bool
     "nat option" "('msaux, 'muaux, 'mtaux) mformula"
     "(event_data list set, event_data table) frz_sep" "nat list" "('msaux, 'muaux, 'mtaux) mformula"
     "('msaux, 'muaux, 'mtaux) mformula"
  | MLetPast Formula.name nat "nat list" "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" nat "event_data table option"
  | MAnd "nat list" "('msaux, 'muaux, 'mtaux) mformula" bool "nat list" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2"
  | MAndAssign "nat list" "('msaux, 'muaux, 'mtaux) mformula" "nat \<times> Formula.trm"
  | MAndRel "nat list" "('msaux, 'muaux, 'mtaux) mformula" "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | MAndTrigger "nat list" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuft2" args "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2" "ts list" "'mtaux"
  | MAnds "nat list" "nat list list" "nat list list" "('msaux, 'muaux, 'mtaux) mformula list" "event_data mbufn"
  | MOr "nat list" "('msaux, 'muaux, 'mtaux) mformula" "nat list" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2"
  | MNeg "('msaux, 'muaux, 'mtaux) mformula"
  | MExists "nat list" "('msaux, 'muaux, 'mtaux) mformula"
  | MAgg "aggargs" "('msaux, 'muaux, 'mtaux) mformula"
  | MPrev \<I> "('msaux, 'muaux, 'mtaux) mformula" bool "event_data table list" "ts list"
  | MNext \<I> "('msaux, 'muaux, 'mtaux) mformula" bool "ts list"
  | MSince args "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2S" "'msaux"
  | MUntil args "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2" "ts list" ts "'muaux"
  | MTrigger args "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2" "ts list" "'mtaux"
  | MRelease args "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2" "ts list" ts "event_data muaux"
  | MMatchP \<I> "nat list" "nat list list" "mregex" "mregex list" "('msaux, 'muaux, 'mtaux) mformula list" "event_data mbufn" "ts list" "event_data mr\<delta>aux"
  | MMatchF \<I> "nat list" "nat list list" "mregex" "mregex list" "('msaux, 'muaux, 'mtaux) mformula list" "event_data mbufn" "ts list" ts "event_data ml\<delta>aux"
  | MTP mtrm nat
  | MTS mtrm

record ('msaux, 'muaux, 'mtaux) mstate =
  mstate_i :: nat
  mstate_j :: nat
  mstate_m :: "('msaux, 'muaux, 'mtaux) mformula"
  mstate_n :: nat
  mstate_t :: "ts list"

subsection \<open>Arguments, terms and aggregations\<close>

definition init_args :: "\<I> \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> aggargs option \<Rightarrow> args" where
  "init_args I n L R pos agg = \<lparr>args_ivl = I, args_n = n, args_L = L, args_R = R,
    args_pos = pos, args_agg = agg\<rparr>"

definition init_aggargs :: "nat list \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> ty Formula.agg_op \<Rightarrow> ty list \<Rightarrow>
  Formula.trm \<Rightarrow> aggargs" where
  "init_aggargs cs n g0 y \<omega> tys f = \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0,
    aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"

fun eq_rel :: "Formula.trm \<Rightarrow> Formula.trm \<Rightarrow> event_data table" where
  "eq_rel (Formula.Const x) (Formula.Const y) = (if x = y then unit_table else empty_table)"
| "eq_rel (Formula.Var x) (Formula.Const y) = singleton_table y"
| "eq_rel (Formula.Const x) (Formula.Var y) = singleton_table x"
| "eq_rel _ _ = undefined"

fun meval_trm :: "nat list \<Rightarrow> Formula.trm \<Rightarrow> event_data tuple \<Rightarrow> event_data" where
  "meval_trm cs (Formula.Var x) v = tup_get cs v x"
| "meval_trm cs (Formula.Const x) v = x"
| "meval_trm cs (Formula.Plus x y) v = meval_trm cs x v + meval_trm cs y v"
| "meval_trm cs (Formula.Minus x y) v = meval_trm cs x v - meval_trm cs y v"
| "meval_trm cs (Formula.UMinus x) v = - meval_trm cs x v"
| "meval_trm cs (Formula.Mult x y) v = meval_trm cs x v * meval_trm cs y v"
| "meval_trm cs (Formula.Div x y) v = meval_trm cs x v div meval_trm cs y v"
| "meval_trm cs (Formula.Mod x y) v = meval_trm cs x v mod meval_trm cs y v"
| "meval_trm cs (Formula.F2i x) v = EInt (integer_of_event_data (meval_trm cs x v))"
| "meval_trm cs (Formula.I2f x) v = EFloat (double_of_event_data (meval_trm cs x v))"

lemma meval_trm_eval_trm: "fv_trm t \<subseteq> set cs \<Longrightarrow> \<forall>i\<in>set cs. i < n \<Longrightarrow>
    meval_trm cs t x = Formula.eval_trm (val n cs x) t"
  by (induction t) auto

definition packagg :: "args \<Rightarrow> ty Formula.formula \<Rightarrow> ty Formula.formula" where
  "packagg args f = (case args_agg args of None \<Rightarrow> f
    | Some aggargs \<Rightarrow> Formula.Agg (aggargs_y aggargs)
      (aggargs_\<omega> aggargs) (aggargs_tys aggargs) (aggargs_f aggargs) f)"

text \<open>The tuples are grouped by their columns not bound by the aggregation, the key; each group
yields the aggregate followed by the key.\<close>

definition agg_key :: "nat \<Rightarrow> nat list \<Rightarrow> event_data tuple \<Rightarrow> event_data tuple" where
  "agg_key k cs x = restrict (filter (\<lambda>x. k \<le> x) cs) cs x"

definition eval_agg :: "nat list \<Rightarrow> bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> ty list \<Rightarrow> Formula.trm \<Rightarrow>
  event_data table \<Rightarrow> event_data table" where
  "eval_agg cs g0 \<omega> tys f rel = (if g0 \<and> rel = empty_table
    then singleton_table (eval_agg_op \<omega> {})
    else (\<lambda>k.
      let group = Set.filter (\<lambda>x. agg_key (length tys) cs x = k) rel;
        M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
      in eval_agg_op \<omega> M # k) ` agg_key (length tys) cs ` rel)"

definition eval_aggargs :: "aggargs \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "eval_aggargs args = eval_agg (aggargs_cols args) (aggargs_g0 args)
    (aggargs_\<omega> args) (aggargs_tys args) (aggargs_f args)"

definition eval_args_agg :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "eval_args_agg args X = (case args_agg args of None \<Rightarrow> X | Some aggargs \<Rightarrow> eval_aggargs aggargs X)"

definition type_restr :: "aggargs \<Rightarrow> event_data table \<Rightarrow> bool" where
  "type_restr args X = (let Z = meval_trm (aggargs_cols args) (aggargs_f args) ` X;
    all_int = Z \<subseteq> range EInt;
    all_float = Z \<subseteq> range EFloat;
    all_string = Z \<subseteq> range EString in
    case aggargs_\<omega> args of (Formula.Agg_Cnt, _) \<Rightarrow> True
    | (Formula.Agg_Min, _) \<Rightarrow> all_int \<or> all_string
    | (Formula.Agg_Max, _) \<Rightarrow> all_int \<or> all_string
    | (Formula.Agg_Sum, _) \<Rightarrow> all_int
    | (Formula.Agg_Avg, _) \<Rightarrow> all_int
    | (Formula.Agg_Med, _) \<Rightarrow> all_int)"

definition safe_aggargs :: "aggargs \<Rightarrow> bool" where
  "safe_aggargs args = (aggargs_y args < aggargs_n args \<and> distinct (aggargs_cols args) \<and>
    (\<forall>i \<in> set (aggargs_cols args). i < length (aggargs_tys args) + aggargs_n args) \<and>
    aggargs_y args + length (aggargs_tys args) \<notin> set (aggargs_cols args) \<and>
    {0..<length (aggargs_tys args)} \<subseteq> set (aggargs_cols args) \<and>
    Formula.fv_trm (aggargs_f args) \<subseteq> set (aggargs_cols args) \<and>
    aggargs_g0 args = (set (aggargs_cols args) \<subseteq> {0..<length (aggargs_tys args)}))"

definition "valid_aggargs n R args = (case args of None \<Rightarrow> True | Some aggargs \<Rightarrow>
  n = length (aggargs_tys aggargs) + aggargs_n aggargs \<and> R = aggargs_cols aggargs \<and> safe_aggargs aggargs)"

definition args_cols :: "args \<Rightarrow> nat list" where
  "args_cols args = (case args_agg args of None \<Rightarrow> args_R args
    | Some aggargs \<Rightarrow> aggargs_y aggargs # shift_cols (length (aggargs_tys aggargs)) (args_R args))"

subsection \<open>Auxiliary structures\<close>

text \<open>Each structure has a locale of its operations and one of their specification; the algorithm
is defined over the operations alone.\<close>

subsubsection \<open>Since\<close>

locale msaux_ops =
  fixes init_msaux :: "args \<Rightarrow> 'msaux"
    and add_new_ts_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and join_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and add_new_table_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and result_msaux :: "args \<Rightarrow> 'msaux \<Rightarrow> event_data table"

locale msaux =
  fixes valid_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> event_data msaux \<Rightarrow> bool"
    and init_msaux :: "args \<Rightarrow> 'msaux"
    and add_new_ts_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and join_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and add_new_table_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and result_msaux :: "args \<Rightarrow> 'msaux \<Rightarrow> event_data table"
  assumes valid_init_msaux: "set L \<subseteq> set R \<Longrightarrow> distinct L \<Longrightarrow> distinct R \<Longrightarrow> valid_aggargs n R agg \<Longrightarrow>
    valid_msaux (init_args I n L R pos agg) 0 (init_msaux (init_args I n L R pos agg)) []"
  assumes valid_add_new_ts_msaux: "valid_msaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
    valid_msaux args nt (add_new_ts_msaux args nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  assumes valid_join_msaux: "valid_msaux args cur aux auxlist \<Longrightarrow>
    table (args_L args) rel1 \<Longrightarrow>
    valid_msaux args cur (join_msaux args rel1 aux)
    (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) rel1)) auxlist)"
  assumes valid_add_new_table_msaux: "valid_msaux args cur aux auxlist \<Longrightarrow>
    table (args_R args) rel2 \<Longrightarrow>
    valid_msaux args cur (add_new_table_msaux args rel2 aux)
    (case auxlist of
      [] => [(cur, rel2)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)"
  assumes valid_result_msaux: "valid_msaux args cur aux auxlist \<Longrightarrow> result_msaux args aux =
    eval_args_agg args (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"

subsubsection \<open>Trigger\<close>

fun trigger_results :: "args \<Rightarrow> ts \<Rightarrow> event_data mtaux \<Rightarrow> (nat list \<times> event_data table)" where
  "trigger_results args cur auxlist = (
    if (length (filter (\<lambda> (t, _, _). mem (args_ivl args) (cur - t)) auxlist) > 0) then (
      (args_R args), {
      tuple. wf_tuple (args_R args) tuple \<and>
        (\<forall>i \<in> {0..<(length auxlist)}.
          let (t, l, r) = auxlist!i in
          mem (args_ivl args) (cur - t) \<longrightarrow> 
          (
            tuple \<in> r \<or>
            (\<exists>j \<in> {i<..<(length auxlist)}.
              join_cond (args_pos args) ((fst o snd) (auxlist!j)) (restrict (args_L args) (args_R args) tuple)
            )
          )
        )
      }
    ) else
    ([], unit_table)
)"

sublocale msaux \<subseteq> msaux_ops init_msaux add_new_ts_msaux join_msaux add_new_table_msaux result_msaux .

locale mtaux_ops =
  fixes init_mtaux :: "args \<Rightarrow> 'mtaux"
    and update_mtaux :: "args \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux"
    and result_mtaux :: "args \<Rightarrow> 'mtaux \<Rightarrow> (nat list \<times> event_data table)"

locale mtaux =
  fixes valid_mtaux :: "args \<Rightarrow> ts \<Rightarrow> 'mtaux \<Rightarrow> event_data mtaux \<Rightarrow> bool"
    and init_mtaux :: "args \<Rightarrow> 'mtaux"
    and update_mtaux :: "args \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux"
    and result_mtaux :: "args \<Rightarrow> 'mtaux \<Rightarrow> (nat list \<times> event_data table)"

  assumes valid_init_mtaux: "(
    if (mem I 0)
      then
        set L \<subseteq> set R
      else 
        set L = set R
    ) \<Longrightarrow>
    distinct L \<Longrightarrow> distinct R \<Longrightarrow>
    \<not>mem I 0 \<longrightarrow> pos \<Longrightarrow>
    let args = init_args I n L R pos agg in
    valid_mtaux args 0 (init_mtaux args) []"

  assumes valid_update_mtaux: "
    nt \<ge> cur \<Longrightarrow>
    table (args_L args) l \<Longrightarrow>
    table (args_R args) r \<Longrightarrow>    valid_mtaux args cur aux auxlist \<Longrightarrow>
    valid_mtaux
      args
      nt
      (update_mtaux args nt l r aux)
      ((filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) @ [(nt, l, r)])
  "

  and valid_result_mtaux: "
    valid_mtaux args cur aux auxlist \<Longrightarrow>
    result_mtaux args aux = trigger_results args cur auxlist
  "

fun check_before :: "\<I> \<Rightarrow> ts \<Rightarrow> (ts \<times> 'a \<times> 'b) \<Rightarrow> bool" where
  "check_before I dt (t, a, b) \<longleftrightarrow> \<not> memR I (dt - t)"

fun proj_thd :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'c" where
  "proj_thd (t, a1, a2) = a2"

subsubsection \<open>Until and release\<close>

definition update_until :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> event_data muaux \<Rightarrow> event_data muaux" where
  "update_until args rel1 rel2 nt aux =
    (map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if (args_pos args) then a1 \<inter> rel1 else a1 \<union> rel1,
      if mem  (args_ivl args) (nt - t) then a2 \<union> join (args_R args) rel2 (args_pos args) (args_L args) a1 else a2)) aux) @
    [(nt, rel1, if memL (args_ivl args) 0 then rel2 else empty_table)]"

fun eval_until :: "\<I> \<Rightarrow> ts \<Rightarrow> event_data muaux \<Rightarrow> event_data table list \<times> event_data muaux" where
  "eval_until I nt [] = ([], [])"
| "eval_until I nt ((t, a1, a2) # aux) = (if \<not> memR I (nt - t) then
    (let (xs, aux) = eval_until I nt aux in (a2 # xs, aux)) else ([], (t, a1, a2) # aux))"

text \<open>A release with 0 in its interval is evaluated like an until: each pending time point keeps
the tuples waiting to be released and those still alive, its verdict once its window is left.\<close>

definition update_release :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> event_data muaux \<Rightarrow> event_data muaux" where
  "update_release args rel1 rel2 nt aux =
    map (\<lambda>(t, a1, a2). if memR (args_ivl args) (nt - t)
      then (t, join (args_R args) (a1 \<inter> rel2) (\<not> args_pos args) (args_L args) rel1, a2 - (a1 - rel2))
      else (t, a1, a2)) aux @
    [(nt, join (args_R args) rel2 (\<not> args_pos args) (args_L args) rel1, rel2)]"

sublocale mtaux \<subseteq> mtaux_ops init_mtaux update_mtaux result_mtaux .

locale muaux_ops =
  fixes init_muaux :: "args \<Rightarrow> 'muaux"
    and add_new_muaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> 'muaux"
    and length_muaux :: "args \<Rightarrow> 'muaux \<Rightarrow> nat"
    and eval_muaux :: "args \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> event_data table list \<times> 'muaux"

locale muaux =
  fixes valid_muaux :: "args \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> event_data muaux \<Rightarrow> bool"
    and init_muaux :: "args \<Rightarrow> 'muaux"
    and add_new_muaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> 'muaux"
    and length_muaux :: "args \<Rightarrow> 'muaux \<Rightarrow> nat"
    and eval_muaux :: "args \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> event_data table list \<times> 'muaux"
  assumes valid_init_muaux: "set L \<subseteq> set R \<Longrightarrow> distinct L \<Longrightarrow> distinct R \<Longrightarrow> valid_aggargs n R aggargs \<Longrightarrow>
    valid_muaux (init_args I n L R pos aggargs) 0 (init_muaux (init_args I n L R pos aggargs)) []"
  assumes valid_add_new_muaux: "valid_muaux args cur aux auxlist \<Longrightarrow>
    table (args_L args) rel1 \<Longrightarrow>
    table (args_R args) rel2 \<Longrightarrow>    nt \<ge> cur \<Longrightarrow>
    valid_muaux args nt (add_new_muaux args rel1 rel2 nt aux)
    (update_until args rel1 rel2 nt auxlist)"
  assumes valid_length_muaux: "valid_muaux args cur aux auxlist \<Longrightarrow> length_muaux args aux = length auxlist"
  assumes valid_eval_muaux: "valid_muaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
    eval_muaux args nt aux = (res, aux') \<Longrightarrow> eval_until (args_ivl args) nt auxlist = (res', auxlist') \<Longrightarrow>
    valid_muaux args cur aux' auxlist' \<and> res = map (eval_args_agg args) res'"

sublocale muaux \<subseteq> muaux_ops init_muaux add_new_muaux length_muaux eval_muaux .

subsection \<open>Locale of the algorithm\<close>

locale maux = msaux valid_msaux init_msaux add_new_ts_msaux join_msaux add_new_table_msaux result_msaux +
  muaux valid_muaux init_muaux add_new_muaux length_muaux eval_muaux + 
  mtaux valid_mtaux init_mtaux update_mtaux result_mtaux
  for valid_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> event_data msaux \<Rightarrow> bool"
    and init_msaux :: "args \<Rightarrow> 'msaux"
    and add_new_ts_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and join_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and add_new_table_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and result_msaux :: "args \<Rightarrow> 'msaux \<Rightarrow> event_data table"

    and valid_muaux :: "args \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> event_data muaux \<Rightarrow> bool"
    and init_muaux :: "args \<Rightarrow> 'muaux"
    and add_new_muaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> 'muaux"
    and length_muaux :: "args \<Rightarrow> 'muaux \<Rightarrow> nat"
    and eval_muaux :: "args \<Rightarrow> nat \<Rightarrow> 'muaux \<Rightarrow> event_data table list \<times> 'muaux"

    and valid_mtaux :: "args \<Rightarrow> ts \<Rightarrow> 'mtaux \<Rightarrow> event_data mtaux \<Rightarrow> bool"
    and init_mtaux :: "args \<Rightarrow> 'mtaux"
    and update_mtaux :: "args \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux"
    and result_mtaux :: "args \<Rightarrow> 'mtaux \<Rightarrow> (nat list \<times> event_data table)"
  + fixes bin_join :: "nat list \<Rightarrow> event_data table \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> event_data table \<Rightarrow> event_data table"
    and mmulti_join :: "nat list \<Rightarrow> nat list list \<Rightarrow> nat list list \<Rightarrow> event_data table list \<Rightarrow> event_data table"
  assumes bin_join_table: "distinct cs \<Longrightarrow> distinct ds \<Longrightarrow> table cs t \<Longrightarrow> table ds t' \<Longrightarrow>
    bin_join cs t pos ds t' = join cs t pos ds t'"
    and mmulti_join_correct: "A_pos \<noteq> [] \<Longrightarrow>
      list_all2 (\<lambda>A X. distinct A \<and> table A X) (A_pos @ A_neg) L \<Longrightarrow>
      (\<Union>A\<in>set A_neg. set A) \<subseteq> (\<Union>A\<in>set A_pos. set A) \<Longrightarrow>
      distinct cs \<Longrightarrow> set cs = (\<Union>A\<in>set A_pos. set A) \<Longrightarrow>
      z \<in> mmulti_join cs A_pos A_neg L \<longleftrightarrow> wf_tuple cs z \<and>
      list_all2 (\<lambda>A X. restrict A cs z \<in> X) A_pos (take (length A_pos) L) \<and>
      list_all2 (\<lambda>A X. restrict A cs z \<notin> X) A_neg (drop (length A_pos) L)"

locale maux_ops = msaux_ops init_msaux add_new_ts_msaux join_msaux add_new_table_msaux result_msaux +
  muaux_ops init_muaux add_new_muaux length_muaux eval_muaux +
  mtaux_ops init_mtaux update_mtaux result_mtaux
  for init_msaux :: "args \<Rightarrow> 'msaux"
    and add_new_ts_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and join_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and add_new_table_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and result_msaux :: "args \<Rightarrow> 'msaux \<Rightarrow> event_data table"
    and init_muaux :: "args \<Rightarrow> 'muaux"
    and add_new_muaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> 'muaux"
    and length_muaux :: "args \<Rightarrow> 'muaux \<Rightarrow> nat"
    and eval_muaux :: "args \<Rightarrow> nat \<Rightarrow> 'muaux \<Rightarrow> event_data table list \<times> 'muaux"
    and init_mtaux :: "args \<Rightarrow> 'mtaux"
    and update_mtaux :: "args \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux"
    and result_mtaux :: "args \<Rightarrow> 'mtaux \<Rightarrow> (nat list \<times> event_data table)"
  + fixes bin_join :: "nat list \<Rightarrow> event_data table \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> event_data table \<Rightarrow> event_data table"
    and mmulti_join :: "nat list \<Rightarrow> nat list list \<Rightarrow> nat list list \<Rightarrow> event_data table list \<Rightarrow> event_data table"

sublocale maux \<subseteq> maux_ops init_msaux add_new_ts_msaux join_msaux add_new_table_msaux result_msaux
  init_muaux add_new_muaux length_muaux eval_muaux init_mtaux update_mtaux result_mtaux
  bin_join mmulti_join .

subsection \<open>Initialization\<close>

subsubsection \<open>Conjuncts and predicates\<close>

fun split_assignment :: "nat set \<Rightarrow> 't Formula.formula \<Rightarrow> nat \<times> Formula.trm" where
  "split_assignment X (Formula.Eq t1 t2) = (case (t1, t2) of
      (Formula.Var x, Formula.Var y) \<Rightarrow> if x \<in> X then (y, t1) else (x, t2)
    | (Formula.Var x, _) \<Rightarrow> (x, t2)
    | (_, Formula.Var y) \<Rightarrow> (y, t1))"
| "split_assignment _ _ = undefined"

fun split_constraint :: "'t Formula.formula \<Rightarrow> Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm" where
  "split_constraint (Formula.Eq t1 t2) = (t1, True, MEq, t2)"
| "split_constraint (Formula.Less t1 t2) = (t1, True, MLess, t2)"
| "split_constraint (Formula.LessEq t1 t2) = (t1, True, MLessEq, t2)"
| "split_constraint (Formula.Neg (Formula.Eq t1 t2)) = (t1, False, MEq, t2)"
| "split_constraint (Formula.Neg (Formula.Less t1 t2)) = (t1, False, MLess, t2)"
| "split_constraint (Formula.Neg (Formula.LessEq t1 t2)) = (t1, False, MLessEq, t2)"
| "split_constraint _ = undefined"

definition is_copy_pattern :: "nat \<Rightarrow> Formula.trm list \<Rightarrow> bool" where
  "is_copy_pattern n ts = (ts = map Formula.Var [0..<n])"

fun is_simple_pattern :: "Formula.trm list \<Rightarrow> nat \<Rightarrow> bool" where
  "is_simple_pattern [] _ = True"
| "is_simple_pattern (Formula.Var y # ts) x = (x \<le> y \<and> is_simple_pattern ts (Suc y))"
| "is_simple_pattern _ _ = False"

definition pred_mode_of :: "nat \<Rightarrow> Formula.trm list \<Rightarrow> pred_mode" where
  "pred_mode_of n ts = (if is_copy_pattern n ts then Copy
    else if is_simple_pattern ts 0 then Simple else Match)"

subsubsection \<open>Temporal operators\<close>

abbreviation (input) "init_mbuf2S \<equiv> ([], [], [], False)"

definition (in msaux_ops) "init_since minit0 n agg \<phi> I \<psi> =
  (let args = (\<lambda>b. (init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) b agg)) in
   if safe_formula \<phi>
   then MSince (args True) (minit0 n \<phi>) (minit0 n \<psi>) init_mbuf2S (init_msaux (args True))
   else (case \<phi> of
     Formula.Neg \<phi>' \<Rightarrow> MSince (args False) (minit0 n \<phi>') (minit0 n \<psi>) init_mbuf2S (init_msaux (args False))
   | _ \<Rightarrow> MRel empty_table))"

lemma (in msaux_ops) init_since_cong[fundef_cong]:
  assumes "\<And>\<alpha> m. size' \<alpha> \<le> size' \<phi> + size' \<psi> \<Longrightarrow> minit0 m \<alpha> = minit0' m \<alpha>"
  shows "init_since minit0 n agg \<phi> I \<psi> = init_since minit0' n agg \<phi> I \<psi>"
  using assms
  by (auto simp: init_since_def split: formula.splits)

definition (in muaux_ops) "init_until minit0 n agg \<phi> I \<psi> =
  (let args = (\<lambda>b. (init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) b agg)) in
   if safe_formula \<phi>
   then MUntil (args True) (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux (args True))
   else (case \<phi> of
     Formula.Neg \<phi>' \<Rightarrow> MUntil (args False) (minit0 n \<phi>') (minit0 n \<psi>) ([], []) [] 0 (init_muaux (args False))
   | _ \<Rightarrow> MRel empty_table))"

lemma (in muaux_ops) init_until_cong[fundef_cong]:
  assumes "\<And>\<alpha> m. size' \<alpha> \<le> size' \<phi> + size' \<psi> \<Longrightarrow> minit0 m \<alpha> = minit0' m \<alpha>"
  shows "init_until minit0 n agg \<phi> I \<psi> = init_until minit0' n agg \<phi> I \<psi>"
  using assms
  by (auto simp: init_until_def split: formula.splits)

definition (in mtaux_ops) "init_and_trigger minit0 n agg \<phi> \<phi>' I \<psi>' =
  (let args = (\<lambda>b. (init_args I n (Formula.fv_list \<phi>') (Formula.fv_list \<psi>') b agg)) in
    if (safe_formula \<phi>') then
      MAndTrigger (Formula.fv_list \<phi>) (minit0 n \<phi>) ([], []) (args True) (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mtaux (args True))
    else (case \<phi>' of 
      Formula.Neg \<phi>' \<Rightarrow> MAndTrigger (Formula.fv_list \<phi>) (minit0 n \<phi>) ([], []) (args False) (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mtaux (args False))
      | _ \<Rightarrow> MRel empty_table))"

lemma (in mtaux_ops) init_and_trigger_cong[fundef_cong]:
  assumes "\<And>\<alpha> m. size' \<alpha> \<le> size' \<phi> + size' \<phi>' + size' \<psi>' \<Longrightarrow> minit0 m \<alpha> = minit0' m \<alpha>"
  shows "init_and_trigger minit0 n agg \<phi> \<phi>' I \<psi>' = init_and_trigger minit0' n agg \<phi> \<phi>' I \<psi>'"
  using assms
  by (clarsimp simp: init_and_trigger_def split: formula.splits)

definition (in mtaux_ops) "init_trigger minit0 n agg \<phi> I \<psi> =
  (let args = (\<lambda>b. (init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) b agg)) in
   if safe_formula \<phi>
    then MTrigger (args True) (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_mtaux (args True))
    else (case \<phi> of
      Formula.Neg \<phi> \<Rightarrow> MTrigger (args False) (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_mtaux (args False))
      | _ \<Rightarrow> MRel empty_table))"
lemma (in mtaux_ops) init_trigger_cong[fundef_cong]:
  assumes "\<And>\<alpha> m. size' \<alpha> \<le> size' \<phi> + size' \<psi> \<Longrightarrow> minit0 m \<alpha> = minit0' m \<alpha>"
  shows "init_trigger minit0 n agg \<phi> I \<psi> = init_trigger minit0' n agg \<phi> I \<psi>"
  using assms
  by (auto simp: init_trigger_def split: formula.splits)

text \<open>An unsafe left operand of a release is conjoined with the right one, which is equivalent with
0 in the interval (@{thm [source] sat_release_conj_0}).\<close>

definition release_left :: "'t Formula.formula \<Rightarrow> 't Formula.formula \<Rightarrow> 't Formula.formula \<times> bool" where
  "release_left \<phi> \<psi> = (if safe_formula \<phi> then (\<phi>, True) else (case \<phi> of
      Formula.Neg \<phi>' \<Rightarrow> if safe_formula \<phi>' then (\<phi>', False) else (Formula.And \<psi> \<phi>, True)
    | _ \<Rightarrow> (Formula.And \<psi> \<phi>, True)))"

lemma size'_release_left: "size' (fst (release_left \<phi> \<psi>)) < size' (Formula.Release \<phi> I \<psi>)"
  by (auto simp: release_left_def split: formula.splits)

subsubsection \<open>Initial state\<close>

fun mtrm_of_trm :: "Formula.trm \<Rightarrow> mtrm" where
  "mtrm_of_trm (Formula.Var x) = MVar x"
| "mtrm_of_trm (Formula.Const x) = MConst x"
| "mtrm_of_trm _ = undefined"

text \<open>Whether a predicate occurs under a negation, which decides the table with which a freeze's
replay base absorbs old time points (@{text frz_fill}).\<close>

fun neg_pred :: "Formula.name \<times> nat \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
  "neg_pred p (Formula.Neg \<phi>) = Formula.contains_pred p \<phi>"
| "neg_pred p (Formula.Let e \<phi> \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.Frz e \<phi> \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.LetPast e \<phi> \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.Or \<phi> \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.And \<phi> \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.Ands l) = (\<exists>\<phi>\<in>set l. neg_pred p \<phi>)"
| "neg_pred p (Formula.Exists t \<phi>) = neg_pred p \<phi>"
| "neg_pred p (Formula.Agg y \<omega> tys f \<phi>) = neg_pred p \<phi>"
| "neg_pred p (Formula.Prev I \<phi>) = neg_pred p \<phi>"
| "neg_pred p (Formula.Next I \<phi>) = neg_pred p \<phi>"
| "neg_pred p (Formula.Since \<phi> I \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.Until \<phi> I \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.Trigger \<phi> I \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.Release \<phi> I \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.MatchP I r) = (\<exists>\<phi>\<in>Regex.atms r. neg_pred p \<phi>)"
| "neg_pred p (Formula.MatchF I r) = (\<exists>\<phi>\<in>Regex.atms r. neg_pred p \<phi>)"
| "neg_pred p _ = False"

definition frz_sep_init :: "Formula.name \<times> nat \<Rightarrow> 't Formula.formula \<Rightarrow> ('a set, 'b) frz_sep" where
  "frz_sep_init pn \<psi> = (if key_sep pn \<psi> \<and> Formula.contains_pred pn \<psi> then FSStock 0 1 0 {} 0 0 0 [] else FSOff)"


function (in maux_ops) (sequential) minit0 :: "nat \<Rightarrow> ty Formula.formula \<Rightarrow> ('msaux, 'muaux, 'mtaux) mformula" where
  "minit0 n (Formula.Neg \<phi>) = (if fv \<phi> = {} then MNeg (minit0 n \<phi>) else MRel empty_table)"
| "minit0 n (Formula.Eq t1 t2) = MRel (eq_rel t1 t2)"
| "minit0 n (Formula.Pred e ts) = MPred e ts (pred_mode_of n ts)"
| "minit0 n (Formula.Let p \<phi> \<psi>) = MLet p (Formula.nfv \<phi>) (Formula.fv_list \<phi>) (minit0 (Formula.nfv \<phi>) \<phi>) (minit0 n \<psi>)"
| "minit0 n (Formula.Frz p \<phi> \<psi>) = MFrz p (Formula.nfv \<phi>) (Formula.fv_list \<phi>) (minit0 (Formula.nfv \<phi>) \<phi>) (minit0 n \<psi>) 0 0 0 []
    (minit0 n \<psi>) 0 0 [] [] (past_reach \<psi>) (safe_letpast (p, Formula.nfv \<phi>) \<psi> \<le> NonFutuRec)
    (neg_pred (p, Formula.nfv \<phi>) \<psi>) None (minit0 n \<psi>)
    (frz_sep_init (p, Formula.nfv \<phi>) \<psi>) (Formula.fv_list \<psi>) (minit0 n \<psi>) (minit0 n \<psi>)"
| "minit0 n (Formula.LetPast p \<phi> \<psi>) = MLetPast p (Formula.nfv \<phi>) (Formula.fv_list \<phi>) (minit0 (Formula.nfv \<phi>) \<phi>) (minit0 n \<psi>) 0 None"
| "minit0 n (Formula.Or \<phi> \<psi>) = MOr (Formula.fv_list \<phi>) (minit0 n \<phi>) (Formula.fv_list \<psi>) (minit0 n \<psi>) ([], [])"
| "minit0 n (Formula.And \<phi> \<psi>) = (if safe_assignment (fv \<phi>) \<psi> then
      MAndAssign (Formula.fv_list \<phi>) (minit0 n \<phi>) (split_assignment (fv \<phi>) \<psi>)
    else if safe_formula \<psi> then
      MAnd (Formula.fv_list \<phi>) (minit0 n \<phi>) True (Formula.fv_list \<psi>) (minit0 n \<psi>) ([], [])
    else if is_constraint \<psi> then
      MAndRel (Formula.fv_list \<phi>) (minit0 n \<phi>) (split_constraint \<psi>)
    else (case \<psi> of
        (Formula.Neg \<psi>) \<Rightarrow> MAnd (Formula.fv_list \<phi>) (minit0 n \<phi>) False (Formula.fv_list \<psi>) (minit0 n \<psi>) ([], [])
      | (Formula.Trigger \<phi>' I \<psi>') \<Rightarrow> init_and_trigger minit0 n None \<phi> \<phi>' I \<psi>'
      | (Formula.Release \<phi>' I \<psi>') \<Rightarrow> minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
      | _ \<Rightarrow> MRel empty_table))"
| "minit0 n (Formula.Ands l) = (let (pos, neg) = partition safe_formula l in
    let mpos = map (minit0 n) pos in
    let mneg = map (minit0 n) (map remove_neg neg) in
    let vpos = map Formula.fv_list pos in
    let vneg = map Formula.fv_list neg in
    MAnds (Formula.fv_list (Formula.Ands l)) vpos vneg (mpos @ mneg) (replicate (length l) []))"
| "minit0 n (Formula.Exists t \<phi>) = MExists (Formula.fv_list \<phi>) (minit0 (Suc n) \<phi>)"
| "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = 
    (let default = MAgg (init_aggargs (Formula.fv_list \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f) (minit0 (length tys + n) \<phi>) in
    (case \<phi> of Formula.Since \<phi>' I \<psi>' \<Rightarrow>
        let agg = Some (init_aggargs (Formula.fv_list \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f) in
        init_since minit0 (length tys + n) agg \<phi>' I \<psi>'
     | Formula.Until \<phi>' I \<psi>' \<Rightarrow>
        let agg = Some (init_aggargs (Formula.fv_list \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f) in
        init_until minit0 (length tys + n) agg \<phi>' I \<psi>'
     | _ \<Rightarrow> default))"
| "minit0 n (Formula.Prev I \<phi>) = MPrev I (minit0 n \<phi>) True [] []"
| "minit0 n (Formula.Next I \<phi>) = MNext I (minit0 n \<phi>) True []"
| "minit0 n (Formula.Since \<phi> I \<psi>) = init_since minit0 n None \<phi> I \<psi>"
| "minit0 n (Formula.Until \<phi> I \<psi>) = init_until minit0 n None \<phi> I \<psi>"
| "minit0 n (Formula.Trigger \<phi> I \<psi>) = init_trigger minit0 n None \<phi> I \<psi>"
| "minit0 n (Formula.Release \<phi> I \<psi>) = (
  if mem I 0
    then
      MRelease (init_args I n (Formula.fv_list (fst (release_left \<phi> \<psi>))) (Formula.fv_list \<psi>)
        (snd (release_left \<phi> \<psi>)) None) (minit0 n (fst (release_left \<phi> \<psi>))) (minit0 n \<psi>) ([], []) [] 0 []
    else
      minit0 n (release_safe_bounded \<phi> I \<psi>))"
| "minit0 n (Formula.MatchP I r) =
    (let (mr, \<phi>s) = to_mregex r
    in MMatchP I (Formula.fv_list (Formula.MatchP I r)) (map Formula.fv_list \<phi>s) mr
      (sorted_list_of_set (RPDs mr)) (map (minit0 n) \<phi>s) (replicate (length \<phi>s) []) [] [])"
| "minit0 n (Formula.MatchF I r) =
    (let (mr, \<phi>s) = to_mregex r
    in MMatchF I (Formula.fv_list (Formula.MatchF I r)) (map Formula.fv_list \<phi>s) mr
      (sorted_list_of_set (LPDs mr)) (map (minit0 n) \<phi>s) (replicate (length \<phi>s) []) [] 0 [])"| "minit0 n (Formula.TP t) = MTP (mtrm_of_trm t) 0"
| "minit0 n (Formula.TS t) = MTS (mtrm_of_trm t)"
| "minit0 n _ = MRel empty_table"
  by pat_completeness auto

termination (in maux_ops) minit0
proof ((relation "measure (\<lambda>(_, \<phi>). size' \<phi>)"; clarsimp), goal_cases)
  case (1 \<phi> \<psi>)
  then show ?case
    by (cases \<psi>; clarsimp)
next
  case (2 \<phi> \<psi>)
  then show ?case
    by (cases \<psi>; clarsimp)
next
  case (3 \<phi> \<psi>)
  then show ?case 
    by (cases \<psi>; clarsimp)
next
  case (4 \<phi> \<psi>)
  then show ?case 
    by (cases \<psi>; clarsimp)
next
  case (5 \<phi> \<phi>' I \<psi>')
  then show ?case
    using size'_and_release[of \<phi> \<phi>' I \<psi>']
    by simp
next
  case (6 \<phi>s \<phi>)
  then show ?case
    unfolding less_Suc_eq_le
    using size_list_estimation'[of \<phi> \<phi>s]
    by (simp add: sum_list_mem_leq)
next
  case (7 n \<phi>s \<phi>)
  then show ?case
    unfolding less_Suc_eq_le
    using sum_list_mem_leq[of \<phi> \<phi>s size']
      size'_remove_neg le_trans by metis
next
  case (8 \<phi> I \<psi>)
  then show ?case 
    using size'_release_left[of \<phi> \<psi> I]
    by simp
next
  case (9 \<phi> I \<psi>)
  then show ?case 
    using size'_release_aux(3)[of \<phi> I \<psi>]
    by simp
next
  case (10 r r' \<phi>s r'' \<phi>s' \<phi>)
  then show ?case 
    by (clarsimp  dest!: to_mregex_ok[OF sym] atms_size')
next
  case (11 r r' \<phi>s r'' \<phi>s' \<phi>)
  then show ?case 
    by (clarsimp  dest!: to_mregex_ok[OF sym] atms_size')
qed

definition (in maux_ops) minit :: "ty Formula.formula \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate" where
  "minit \<phi> = (let n = Formula.nfv \<phi>
              in \<lparr>mstate_i = 0, mstate_j = 0, mstate_m = minit0 n \<phi>, mstate_n = n, mstate_t = []\<rparr>)"

definition (in maux_ops) minit_safe where
  "minit_safe \<phi> = (if mmonitorable_exec \<phi> then minit \<phi> else undefined)"


subsection \<open>Step functions of the operators\<close>

subsubsection \<open>Buffers\<close>

fun mprev_next :: "\<I> \<Rightarrow> (event_data table) list \<Rightarrow> ts list \<Rightarrow> (event_data table) list \<times> (event_data table) list \<times> ts list" where
  "mprev_next I [] ts = ([], [], ts)"
| "mprev_next I xs [] = ([], xs, [])"
| "mprev_next I xs [t] = ([], xs, [t])"
| "mprev_next I (x # xs) (t # t' # ts) = (let (ys, zs) = mprev_next I xs (t' # ts)
    in ((if mem I ((t' - t)) then x else (empty_table)) # ys, zs))"

fun mbuf2_add where
  "mbuf2_add xs' ys' (xs, ys) = (xs @ xs', ys @ ys')"

fun mbuf2S_add :: "event_data table list \<Rightarrow> event_data table list \<Rightarrow> ts list \<Rightarrow> event_data mbuf2S \<Rightarrow> event_data mbuf2S" where
  "mbuf2S_add xs' ys' ts' (xs, ys, ts, skew) = (xs @ xs', ys @ ys', ts @ ts', skew)"

fun mbuf2_take where
  "mbuf2_take f (x # xs, y # ys) = (let (zs, buf) = mbuf2_take f (xs, ys) in (f x y # zs, buf))"
| "mbuf2_take f (xs, ys) = ([], (xs, ys))"

fun mbuf2T_take where
  "mbuf2T_take f z (x # xs, y # ys) (t # ts) = mbuf2T_take f (f x y t z) (xs, ys) ts"
| "mbuf2T_take f z (xs, ys) ts = (z, (xs, ys), ts)"

fun mbuf2t_take :: "(event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow>
    event_data mbuf2 \<Rightarrow> ts \<Rightarrow> ts list \<Rightarrow> 'b \<times> event_data mbuf2 \<times> ts \<times> ts list" where
  "mbuf2t_take f z (x # xs, y # ys) t0 (t # ts) = mbuf2t_take f (f x y t z) (xs, ys) t ts"
| "mbuf2t_take f z (xs, ys) t0 ts = (z, (xs, ys), (case ts of [] \<Rightarrow> t0 | t # _ \<Rightarrow> t), ts)"

subsubsection \<open>Since\<close>

context maux_ops begin
context fixes args :: args begin

fun eval_since :: "event_data table list \<Rightarrow> event_data mbuf2S \<Rightarrow> 'msaux \<Rightarrow>
    event_data table list \<times> event_data mbuf2S \<times> 'msaux" where
  "eval_since rs (x # xs, [], t # ts, skew) aux =
    (if skew \<or> memL (args_ivl args) 0
    then (rev rs, (x # xs, [], t # ts, skew), aux)
    else (let aux' = join_msaux args x (add_new_ts_msaux args t aux)
      in (rev (result_msaux args aux' # rs), (xs, [], ts, True), aux')))"
| "eval_since rs (xs, y # ys, ts, True) aux =
    eval_since rs (xs, ys, ts, False) (add_new_table_msaux args y aux)"
| "eval_since rs (x # xs, y # ys, t # ts, False) aux =
    (let aux' = add_new_table_msaux args y (join_msaux args x (add_new_ts_msaux args t aux))
    in eval_since (result_msaux args aux' # rs) (xs, ys, ts, False) aux')"
| "eval_since rs buf aux = (rev rs, buf, aux)"

end
end

subsubsection \<open>Multiway buffers\<close>

fun mbufn_add :: "(event_data table) list list \<Rightarrow> event_data mbufn \<Rightarrow> event_data mbufn" where
  "mbufn_add xs' xs = List.map2 (@) xs xs'"

function mbufn_take :: "((event_data table) list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> event_data mbufn \<Rightarrow> 'b \<times> event_data mbufn" where
  "mbufn_take f z buf = (if buf = [] \<or> [] \<in> set buf then (z, buf)
    else mbufn_take f (f (map hd buf) z) (map tl buf))"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(_, _, buf). size_list length buf)")
    (auto simp: comp_def Suc_le_eq size_list_length_diff1)

fun mbufnt_take' :: "((event_data table) list \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
    'b \<Rightarrow> event_data mbufn \<Rightarrow> ts list \<Rightarrow> 'b \<times> event_data mbufn \<times> ts list" where
  "mbufnt_take' f z buf ts =
    (if [] \<in> set buf \<or> ts = [] then (z, buf, ts)
    else mbufnt_take' f (f (map hd buf) (hd ts) z) (map tl buf) (tl ts))"

fun mbufnt_take :: "(event_data table list \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
    'b \<Rightarrow> event_data mbufn \<Rightarrow> ts \<Rightarrow> ts list \<Rightarrow> 'b \<times> event_data mbufn \<times> ts \<times> ts list" where
  "mbufnt_take f z buf t0 ts =
    (if [] \<in> set buf \<or> ts = [] then (z, buf, (case ts of [] \<Rightarrow> t0 | t # _ \<Rightarrow> t), ts)
    else mbufnt_take f (f (map hd buf) (hd ts) z) (map tl buf) (hd ts) (tl ts))"

subsubsection \<open>Predicates\<close>

fun match :: "Formula.trm list \<Rightarrow> event_data tuple \<Rightarrow> (nat \<rightharpoonup> event_data) option" where
  "match [] [] = Some Map.empty"
| "match (Formula.Const x # ts) (y # ys) = (if x = y then match ts ys else None)"
| "match (Formula.Var x # ts) (y # ys) = (case match ts ys of
      None \<Rightarrow> None
    | Some f \<Rightarrow> (case f x of
        None \<Rightarrow> Some (f(x \<mapsto> y))
      | Some z \<Rightarrow> if y = z then Some f else None))"
| "match _ _ = None"

text \<open>With a simple pattern, of distinct variables in increasing order, the event tuples are the
table's tuples; otherwise they are matched against the pattern.\<close>

definition tabulate_match :: "nat list \<Rightarrow> (nat \<rightharpoonup> event_data) \<Rightarrow> event_data tuple" where
  "tabulate_match cs f = map (\<lambda>x. the (f x)) cs"
definition "lookup = Mapping.lookup_default empty_table"

subsubsection \<open>Match operators\<close>

text \<open>The derivatives' tables are over the expression's columns @{term cs}, the atoms' tables over
their own columns @{term dss}.\<close>

fun \<epsilon>_lax where
  "\<epsilon>_lax cs dss guard \<phi>s (MSkip n) = (if n = 0 then guard else empty_table)"
| "\<epsilon>_lax cs dss guard \<phi>s (MTestPos i) = join cs guard True (dss ! i) (\<phi>s ! i)"
| "\<epsilon>_lax cs dss guard \<phi>s (MTestNeg i) = join cs guard False (dss ! i) (\<phi>s ! i)"
| "\<epsilon>_lax cs dss guard \<phi>s (MPlus r s) = \<epsilon>_lax cs dss guard \<phi>s r \<union> \<epsilon>_lax cs dss guard \<phi>s s"
| "\<epsilon>_lax cs dss guard \<phi>s (MTimes r s) = join cs (\<epsilon>_lax cs dss guard \<phi>s r) True cs (\<epsilon>_lax cs dss guard \<phi>s s)"
| "\<epsilon>_lax cs dss guard \<phi>s (MStar r) = guard"

fun r\<epsilon>_strict where
  "r\<epsilon>_strict cs dss \<phi>s (MSkip m) = (if m = 0 then unit_table else empty_table)"
| "r\<epsilon>_strict cs dss \<phi>s (MTestPos i) = reorder cs (dss ! i) (\<phi>s ! i)"
| "r\<epsilon>_strict cs dss \<phi>s (MTestNeg i) = (if \<phi>s ! i = empty_table then unit_table else empty_table)"
| "r\<epsilon>_strict cs dss \<phi>s (MPlus r s) = r\<epsilon>_strict cs dss \<phi>s r \<union> r\<epsilon>_strict cs dss \<phi>s s"
| "r\<epsilon>_strict cs dss \<phi>s (MTimes r s) = \<epsilon>_lax cs dss (r\<epsilon>_strict cs dss \<phi>s r) \<phi>s s"
| "r\<epsilon>_strict cs dss \<phi>s (MStar r) = unit_table"

fun l\<epsilon>_strict where
  "l\<epsilon>_strict cs dss \<phi>s (MSkip m) = (if m = 0 then unit_table else empty_table)"
| "l\<epsilon>_strict cs dss \<phi>s (MTestPos i) = reorder cs (dss ! i) (\<phi>s ! i)"
| "l\<epsilon>_strict cs dss \<phi>s (MTestNeg i) = (if \<phi>s ! i = empty_table then unit_table else empty_table)"
| "l\<epsilon>_strict cs dss \<phi>s (MPlus r s) = l\<epsilon>_strict cs dss \<phi>s r \<union> l\<epsilon>_strict cs dss \<phi>s s"
| "l\<epsilon>_strict cs dss \<phi>s (MTimes r s) = \<epsilon>_lax cs dss (l\<epsilon>_strict cs dss \<phi>s s) \<phi>s r"
| "l\<epsilon>_strict cs dss \<phi>s (MStar r) = unit_table"

fun r\<delta> :: "nat list \<Rightarrow> nat list list \<Rightarrow> (mregex \<Rightarrow> mregex) \<Rightarrow> (mregex, 'a table) mapping \<Rightarrow> 'a table list \<Rightarrow> mregex \<Rightarrow> 'a table"  where
  "r\<delta> cs dss \<kappa> X \<phi>s (MSkip n) = (case n of 0 \<Rightarrow> empty_table | Suc m \<Rightarrow> lookup X (\<kappa> (MSkip m)))"
| "r\<delta> cs dss \<kappa> X \<phi>s (MTestPos i) = empty_table"
| "r\<delta> cs dss \<kappa> X \<phi>s (MTestNeg i) = empty_table"
| "r\<delta> cs dss \<kappa> X \<phi>s (MPlus r s) = r\<delta> cs dss \<kappa> X \<phi>s r \<union> r\<delta> cs dss \<kappa> X \<phi>s s"
| "r\<delta> cs dss \<kappa> X \<phi>s (MTimes r s) = r\<delta> cs dss (\<lambda>t. \<kappa> (MTimes r t)) X \<phi>s s \<union> \<epsilon>_lax cs dss (r\<delta> cs dss \<kappa> X \<phi>s r) \<phi>s s"
| "r\<delta> cs dss \<kappa> X \<phi>s (MStar r) = r\<delta> cs dss (\<lambda>t. \<kappa> (MTimes (MStar r) t)) X \<phi>s r"

fun l\<delta> :: "nat list \<Rightarrow> nat list list \<Rightarrow> (mregex \<Rightarrow> mregex) \<Rightarrow> (mregex, 'a table) mapping \<Rightarrow> 'a table list \<Rightarrow> mregex \<Rightarrow> 'a table" where
  "l\<delta> cs dss \<kappa> X \<phi>s (MSkip n) = (case n of 0 \<Rightarrow> empty_table | Suc m \<Rightarrow> lookup X (\<kappa> (MSkip m)))"
| "l\<delta> cs dss \<kappa> X \<phi>s (MTestPos i) = empty_table"
| "l\<delta> cs dss \<kappa> X \<phi>s (MTestNeg i) = empty_table"
| "l\<delta> cs dss \<kappa> X \<phi>s (MPlus r s) = l\<delta> cs dss \<kappa> X \<phi>s r \<union> l\<delta> cs dss \<kappa> X \<phi>s s"
| "l\<delta> cs dss \<kappa> X \<phi>s (MTimes r s) = l\<delta> cs dss (\<lambda>t. \<kappa> (MTimes t s)) X \<phi>s r \<union> \<epsilon>_lax cs dss (l\<delta> cs dss \<kappa> X \<phi>s s) \<phi>s r"
| "l\<delta> cs dss \<kappa> X \<phi>s (MStar r) = l\<delta> cs dss (\<lambda>t. \<kappa> (MTimes t (MStar r))) X \<phi>s r"
lift_definition mrtabulate :: "mregex list \<Rightarrow> (mregex \<Rightarrow> 'b table) \<Rightarrow> (mregex, 'b table) mapping"
  is "\<lambda>ks f. (map_of (List.map_filter (\<lambda>k. let fk = f k in if fk = empty_table then None else Some (k, fk)) ks))" .

definition update_matchP :: "nat list \<Rightarrow> nat list list \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> event_data table list \<Rightarrow> ts \<Rightarrow>
  event_data mr\<delta>aux \<Rightarrow> event_data table \<times> event_data mr\<delta>aux" where
  "update_matchP cs dss I mr mrs rels nt aux =
    (let aux = (case [(t, mrtabulate mrs (\<lambda>mr.
        r\<delta> cs dss id rel rels mr \<union> (if t = nt then r\<epsilon>_strict cs dss rels mr else {}))).
      (t, rel) \<leftarrow> aux, memR I (nt - t)]
      of [] \<Rightarrow> [(nt, mrtabulate mrs (r\<epsilon>_strict cs dss rels))]
      | x # aux' \<Rightarrow> (if fst x = nt then x # aux'
                     else (nt, mrtabulate mrs (r\<epsilon>_strict cs dss rels)) # x # aux'))
    in (foldr (\<union>) [lookup rel mr. (t, rel) \<leftarrow> aux, memL I (nt - t)] {}, aux))"

definition update_matchF_base where
  "update_matchF_base cs dss I mr mrs rels nt =
     (let X = mrtabulate mrs (l\<epsilon>_strict cs dss rels)
     in ([(nt, rels, if memL I 0 then lookup X mr else empty_table)], X))"

definition update_matchF_step where
  "update_matchF_step cs dss I mr mrs nt = (\<lambda>(t, rels', rel) (aux', X).
     (let Y = mrtabulate mrs (l\<delta> cs dss id X rels')
     in ((t, rels', if mem I ((nt - t)) then rel \<union> lookup Y mr else rel) # aux', Y)))"

definition update_matchF :: "nat list \<Rightarrow> nat list list \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> event_data table list \<Rightarrow> ts \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> event_data ml\<delta>aux" where
  "update_matchF cs dss I mr mrs rels nt aux =
     fst (foldr (update_matchF_step cs dss I mr mrs nt) aux (update_matchF_base cs dss I mr mrs rels nt))"
fun eval_matchF :: "\<I> \<Rightarrow> mregex \<Rightarrow> ts \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> event_data table list \<times> event_data ml\<delta>aux" where
  "eval_matchF I mr nt [] = ([], [])"
| "eval_matchF I mr nt ((t, rels, rel) # aux) = (if \<not> memR I (nt - t) then
    (let (xs, aux) = eval_matchF I mr nt aux in (rel # xs, aux)) else ([], (t, rels, rel) # aux))"

primrec map_split where
  "map_split f [] = ([], [])"
| "map_split f (x # xs) =
    (let (y, z) = f x; (ys, zs) = map_split f xs
    in (y # ys, z # zs))"

lemma map_split_map: "map_split f (map g xs) = map_split (f o g) xs"
  by (induct xs) auto

lemma map_split_eq_Pair_iff: "map_split f xs = (ys, zs) \<longleftrightarrow> ys = map (fst o f) xs \<and> zs = map (snd o f) xs"
  by (induct xs arbitrary: ys zs) (auto split: prod.splits)

subsubsection \<open>Assignments and constraints\<close>

fun eval_assignment :: "nat list \<Rightarrow> nat \<times> Formula.trm \<Rightarrow> event_data tuple \<Rightarrow> event_data tuple" where
  "eval_assignment cs (x, t) y = y @ [meval_trm cs t y]"

fun eval_constraint0 :: "mconstraint \<Rightarrow> event_data \<Rightarrow> event_data \<Rightarrow> bool" where
  "eval_constraint0 MEq x y = (x = y)"
| "eval_constraint0 MLess x y = (x < y)"
| "eval_constraint0 MLessEq x y = (x \<le> y)"

fun eval_constraint :: "nat list \<Rightarrow> Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow> event_data tuple \<Rightarrow> bool" where
  "eval_constraint cs (t1, p, c, t2) x = (eval_constraint0 c (meval_trm cs t1 x) (meval_trm cs t2 x) = p)"

subsubsection \<open>Recursive let\<close>

function letpast_meval0 where
  "letpast_meval0 eval j i ys xs p ts db \<phi> =
     (let (ys', \<phi>') = eval ts (Mapping.update p xs db) \<phi>
     in if size \<phi>' \<noteq> size \<phi> then ([], 0, None, \<phi>)
     else (case ys' of
       [] \<Rightarrow> (ys @ ys', i + length xs, None, \<phi>')
     | y # _ \<Rightarrow> (if Suc (i + length xs) \<ge> j then (ys @ ys', i + length xs, Some y, \<phi>')
         else letpast_meval0 eval j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>')))"
  by auto
termination
  by (relation "measure (\<lambda>(_, j, i, _, xs, _). j - (i + length xs))")
    (auto simp: not_le min_def diff_less_mono2)

declare letpast_meval0.simps[simp del]

lemma letpast_meval0_cong[fundef_cong]:
  assumes "(\<And>ts db \<psi>. size \<psi> = size \<phi> \<Longrightarrow>  eval ts db \<psi> = eval' ts db \<psi>)"
  shows "letpast_meval0 eval j i ys xs p ts db \<phi> = letpast_meval0 eval' j i ys xs p ts db \<phi>"
  using assms
proof (induct eval j i ys xs p ts db \<phi> rule: letpast_meval0.induct)
  case (1 eval j i ys xs p ts db \<phi>)
  obtain ys' \<phi>' where eval: "eval ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    by fastforce
  have eval': "eval' ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    using 1(2)[of \<phi>] eval by simp
  show ?case
  proof (cases ys')
    case Nil
    then show ?thesis
      using eval eval' by (subst (1 2) letpast_meval0.simps) simp
  next
    case (Cons y ys'')
    have "letpast_meval0 eval j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>' =
      letpast_meval0 eval' j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>'"
      if "size \<phi>' = size \<phi>" "\<not> j \<le> Suc (i + length xs)"
      using 1(1)[OF eval[symmetric] refl _ Cons] 1(2) that by simp
    then show ?thesis
      using eval eval' Cons by (subst (1 2) letpast_meval0.simps) (simp add: Let_def)
  qed
qed

lemma size_letpast_meval: "(\<And>ts db \<psi>. size \<psi> = size \<phi> \<Longrightarrow> size (snd (eval ts db \<psi>)) = size \<psi>) \<Longrightarrow>
  size (snd (snd (snd (letpast_meval0 eval j i ys xs p ts db \<phi>)))) = size \<phi>"
proof (induct eval j i ys xs p ts db \<phi> rule: letpast_meval0.induct)
  case (1 eval j i ys xs p ts db \<phi>)
  obtain ys' \<phi>' where eval: "eval ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    by fastforce
  have size: "size \<phi>' = size \<phi>"
    using 1(2)[of \<phi> ts "Mapping.update p xs db"] eval by simp
  show ?case
  proof (cases ys')
    case Nil
    then show ?thesis
      using eval size by (subst letpast_meval0.simps) simp
  next
    case (Cons y ys'')
    have "size (snd (snd (snd (letpast_meval0 eval j (i + length xs) (ys @ ys') ys' p []
      (Mapping.map_values (\<lambda>_ _. []) db) \<phi>')))) = size \<phi>'" if "\<not> j \<le> Suc (i + length xs)"
      using 1(1)[OF eval[symmetric] refl _ Cons] 1(2) size that by simp
    then show ?thesis
      using eval size Cons by (subst letpast_meval0.simps) (simp add: Let_def)
  qed
qed

subsection \<open>Step function of the freeze\<close>

subsubsection \<open>Replay mode\<close>

text \<open>In the replay mode, each pending frozen table gets a copy of the replay base, replayed over the
window. The first copy without a verdict stays live, replacing its slot only at equal size.\<close>

definition frz_keep_lv :: "(nat \<times> 'a :: size) option \<Rightarrow> 'a \<Rightarrow> nat option" where
  "frz_keep_lv lv \<rho>L = (case lv of Some (g, st) \<Rightarrow> if size st = size \<rho>L then Some g else None | None \<Rightarrow> None)"

definition frz_keep_st :: "(nat \<times> 'a :: size) option \<Rightarrow> 'a \<Rightarrow> 'a" where
  "frz_keep_st lv \<rho>L = (case lv of Some (g, st) \<Rightarrow> if size st = size \<rho>L then st else \<rho>L | None \<Rightarrow> \<rho>L)"

lemma size_frz_keep_st[simp]: "size (frz_keep_st lv \<rho>L) = size \<rho>L"
  by (auto simp: frz_keep_st_def split: option.splits)

text \<open>The window drops the time points beyond the body's past reach @{term d} from every pending
verdict. With @{term po}, the copy at @{term i} gets the frozen predicate only up to @{term i}.\<close>

definition frz_adv :: "enat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ts list \<Rightarrow> nat" where
  "frz_adv d w jfrz j tq = (if d \<noteq> \<infinity> \<and> w \<le> jfrz \<and> w < j
     then length (takeWhile (\<lambda>t. enat t + d < enat (tq ! (min jfrz (j - 1) - w))) tq) else 0)"

definition frz_cut :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "frz_cut po w i j = (if po then min (j - w) (Suc i - w) else j - w)"

text \<open>Any frozen table can fill the time points that leave the window; the latest one under a
negation, the empty one otherwise, keeps the work that the copies discard small.\<close>

definition frz_fill :: "bool \<Rightarrow> 'a set list \<Rightarrow> 'a set" where
  "frz_fill ng \<alpha>s = (if ng then last ({} # \<alpha>s) else {})"

text \<open>Before each copy, the replay base's window moves as far as the copy's time point allows; a
moved base replaces the old one only at equal size.\<close>

definition frz_adv_st :: "('m \<Rightarrow> nat) \<Rightarrow> (ts list \<Rightarrow> ('k, 'a list) mapping \<Rightarrow> 'm \<Rightarrow> 't list \<times> 'm) \<Rightarrow>
    'k \<Rightarrow> ('k, 'a list) mapping \<Rightarrow> 'a \<Rightarrow> enat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'm \<times> nat \<times> nat \<times> ts list \<times> 't list \<Rightarrow>
    'm \<times> nat \<times> nat \<times> ts list \<times> 't list" where
  "frz_adv_st sz ev pm dbe fl d j i s = (case s of (\<rho>, w, pR, tq, rb) \<Rightarrow>
     let a = frz_adv d w i j tq in
     (case ev [] (Mapping.update pm (replicate a fl) dbe) \<rho> of (rs, \<rho>') \<Rightarrow>
       if sz \<rho>' = sz \<rho>
       then (\<rho>', w + a, pR + length rs, drop a tq, drop (min i (pR + length rs) - (pR - length rb)) (rb @ rs))
       else s))"

primrec frz_loop :: "('m \<Rightarrow> nat) \<Rightarrow> (ts list \<Rightarrow> ('k, 'a list) mapping \<Rightarrow> 'm \<Rightarrow> 't list \<times> 'm) \<Rightarrow>
    'k \<Rightarrow> ('k, 'a list) mapping \<Rightarrow> 'a \<Rightarrow> enat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'm \<times> nat \<times> nat \<times> ts list \<times> 't list \<Rightarrow>
    't list \<times> 'a list \<times> (nat \<times> 'm) option \<times> ('m \<times> nat \<times> nat \<times> ts list \<times> 't list)" where
  "frz_loop sz ev pm dbe fl d po j i [] s = ([], [], None, frz_adv_st sz ev pm dbe fl d j i s)"
| "frz_loop sz ev pm dbe fl d po j i (\<alpha> # \<alpha>s) s =
    (case frz_adv_st sz ev pm dbe fl d j i s of (\<rho>, w, pR, tq, rb) \<Rightarrow>
     (case ev [] (Mapping.update pm (replicate (frz_cut po w i j) \<alpha>) dbe) \<rho> of (us, \<sigma>) \<Rightarrow>
      (case drop (i - (pR - length rb)) (rb @ us) of
        [] \<Rightarrow> ([], \<alpha> # \<alpha>s, Some (i - (pR - length rb) - length (rb @ us), \<sigma>), (\<rho>, w, pR, tq, rb))
      | y # _ \<Rightarrow> (case frz_loop sz ev pm dbe fl d po j (Suc i) \<alpha>s (\<rho>, w, pR, tq, rb) of
          (zs, \<alpha>s', lv, s') \<Rightarrow> (y # zs, \<alpha>s', lv, s')))))"

definition frz_live_loop where
  "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (case lr of
     None \<Rightarrow> frz_loop sz ev pm dbe fl d po j i \<alpha>s s
   | Some (g, us, st) \<Rightarrow> (case drop g us of
       [] \<Rightarrow> ([], \<alpha>s, Some (g - length us, st), frz_adv_st sz ev pm dbe fl d j i s)
     | y # _ \<Rightarrow> (case frz_loop sz ev pm dbe fl d po j (Suc i) (tl \<alpha>s) s of
         (zs, \<alpha>s', lv, s') \<Rightarrow> (y # zs, \<alpha>s', lv, s'))))"

lemma size_frz_adv_st: "sz (fst (frz_adv_st sz ev pm dbe fl d j i s)) = sz (fst s)"
  by (auto simp: frz_adv_st_def Let_def split: prod.splits)

lemma frz_loop_size:
  "frz_loop sz ev pm dbe fl d po j i \<alpha>s s = (ys, \<alpha>s', lv, s') \<Longrightarrow> sz (fst s') = sz (fst s)"
proof (induction \<alpha>s arbitrary: i s ys \<alpha>s' lv s')
  case Nil
  then show ?case
    using size_frz_adv_st[of sz ev pm dbe fl d j i s] by auto
next
  case (Cons \<alpha> \<alpha>s)
  obtain \<rho> w pR tq rb where s1: "frz_adv_st sz ev pm dbe fl d j i s = (\<rho>, w, pR, tq, rb)"
    by (metis prod_cases5)
  have sz: "sz \<rho> = sz (fst s)"
    using size_frz_adv_st[of sz ev pm dbe fl d j i s] s1 by simp
  obtain us \<sigma> where e: "ev [] (Mapping.update pm (replicate (frz_cut po w i j) \<alpha>) dbe) \<rho> = (us, \<sigma>)"
    by fastforce
  show ?case
  proof (cases "drop (i - (pR - length rb)) (rb @ us)")
    case Nil
    then show ?thesis
      using Cons.prems s1 e sz by (auto simp: size_frz_adv_st)
  next
    case (Cons y r)
    obtain zs a l s2 where r: "frz_loop sz ev pm dbe fl d po j (Suc i) \<alpha>s (\<rho>, w, pR, tq, rb) = (zs, a, l, s2)"
      by (metis prod_cases4)
    have "s' = s2"
      using Cons.prems s1 e Cons r by simp
    then show ?thesis
      using Cons.IH[OF r] sz by simp
  qed
qed

lemma frz_live_loop_size:
  "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (ys, \<alpha>s', lv, s') \<Longrightarrow> sz (fst s') = sz (fst s)"
  using frz_loop_size[of sz ev pm dbe fl d po j _ _ s] size_frz_adv_st[of sz ev pm dbe fl d j i s]
  by (auto simp: frz_live_loop_def split: option.splits list.splits prod.splits)

lemma frz_adv_st_cong[fundef_cong]:
  assumes "\<And>ts db \<psi>. sz \<psi> = sz (fst s) \<Longrightarrow> ev ts db \<psi> = ev' ts db \<psi>"
  shows "frz_adv_st sz ev pm dbe fl d j i s = frz_adv_st sz ev' pm dbe fl d j i s"
  using assms by (auto simp: frz_adv_st_def split: prod.splits)

lemma frz_loop_cong[fundef_cong]:
  assumes "\<And>ts db \<psi>. sz \<psi> = sz (fst s) \<Longrightarrow> ev ts db \<psi> = ev' ts db \<psi>"
  shows "frz_loop sz ev pm dbe fl d po j i \<alpha>s s = frz_loop sz ev' pm dbe fl d po j i \<alpha>s s"
  using assms
proof (induction \<alpha>s arbitrary: i s)
  case Nil
  then show ?case
    using frz_adv_st_cong[of sz s ev ev'] by simp
next
  case (Cons \<alpha> \<alpha>s)
  obtain \<rho> w pR tq rb where s': "frz_adv_st sz ev' pm dbe fl d j i s = (\<rho>, w, pR, tq, rb)"
    by (metis prod_cases5)
  have adv: "frz_adv_st sz ev pm dbe fl d j i s = (\<rho>, w, pR, tq, rb)"
    using frz_adv_st_cong[of sz s ev ev', OF Cons.prems] s' by simp
  have sz: "sz \<rho> = sz (fst s)"
    using size_frz_adv_st[of sz ev' pm dbe fl d j i s] s' by simp
  have ev: "ev ts db \<rho> = ev' ts db \<rho>" for ts db
    using Cons.prems sz by simp
  have IH: "frz_loop sz ev pm dbe fl d po j (Suc i) \<alpha>s (\<rho>, w, pR, tq, rb) =
    frz_loop sz ev' pm dbe fl d po j (Suc i) \<alpha>s (\<rho>, w, pR, tq, rb)"
    by (rule Cons.IH) (use Cons.prems sz in simp)
  show ?case
    by (simp only: frz_loop.simps adv s' prod.case ev IH)
qed

lemma frz_live_loop_cong[fundef_cong]:
  assumes "\<And>ts db \<psi>. sz \<psi> = sz (fst s) \<Longrightarrow> ev ts db \<psi> = ev' ts db \<psi>"
  shows "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = frz_live_loop sz ev' pm dbe fl d po j i \<alpha>s lr s"
proof -
  have "frz_loop sz ev pm dbe fl d po j i' \<alpha>s' s = frz_loop sz ev' pm dbe fl d po j i' \<alpha>s' s" for i' \<alpha>s'
    using assms by (rule frz_loop_cong)
  moreover have "frz_adv_st sz ev pm dbe fl d j i s = frz_adv_st sz ev' pm dbe fl d j i s"
    using assms by (rule frz_adv_st_cong)
  ultimately show ?thesis
    by (simp only: frz_live_loop_def)
qed

subsubsection \<open>Separable mode\<close>

text \<open>The two copies replay the replay base with @{term L} and with the empty table; their verdicts
from the first pending time point on are kept in pairs.\<close>

definition frz_copies :: "('m \<Rightarrow> nat) \<Rightarrow> (ts list \<Rightarrow> ('k, 'a list) mapping \<Rightarrow> 'm \<Rightarrow> 't list \<times> 'm) \<Rightarrow> 'a \<Rightarrow>
    'k \<Rightarrow> ('k, 'a list) mapping \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> 'm \<times> nat \<times> nat \<times> ts list \<times> 't list \<Rightarrow>
    ('m \<times> 'm \<times> nat \<times> ('t \<times> 't) list) option" where
  "frz_copies sz ev emp pm dbe j i L \<sigma>S \<sigma>E s = (case s of (\<rho>, w, pR, tq, rb) \<Rightarrow>
     (case ev [] (Mapping.update pm (replicate (j - w) L) dbe) \<rho> of (uS, \<rho>S) \<Rightarrow>
      (case ev [] (Mapping.update pm (replicate (j - w) emp) dbe) \<rho> of (uE, \<rho>E) \<Rightarrow>
       if sz \<rho>S = sz \<sigma>S \<and> sz \<rho>E = sz \<sigma>E
       then Some (\<rho>S, \<rho>E, pR + length uS,
         drop (min i (pR + length uS) - (pR - length rb)) (zip (rb @ uS) (rb @ uE)))
       else None)))"

definition frz_emit :: "('t \<Rightarrow> 't \<Rightarrow> 'a \<Rightarrow> 't) \<Rightarrow> 'a list \<Rightarrow> ('t \<times> 't) list \<Rightarrow> 't list" where
  "frz_emit cmb \<alpha>s buf = map2 (\<lambda>\<alpha> (yS, yE). cmb yS yE \<alpha>) \<alpha>s buf"

subsubsection \<open>Choice of the mode\<close>

text \<open>Each mode accumulates the work the other would save and switches when that exceeds the cost
of switching. The choice affects only the work, never the verdicts.\<close>

definition frz_lambda :: nat where "frz_lambda = 6"
definition frz_c0 :: nat where "frz_c0 = 1000"
definition frz_epoch :: nat where "frz_epoch = 64"
definition frz_sample :: nat where "frz_sample = 8"
definition frz_keep :: nat where "frz_keep = 128"

definition frz_absorb :: "('a, 't) frz_ops \<Rightarrow> 'a list \<Rightarrow> 'a \<times> nat \<times> nat \<Rightarrow> 'a \<times> nat \<times> nat" where
  "frz_absorb ops xs = fold (\<lambda>\<alpha> (L, n, f). let c = fo_fr ops \<alpha> L in (fo_un ops L \<alpha>, n + c, f + c)) xs"

definition frz_unions :: "('a, 't) frz_ops \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "frz_unions ops xs = fold (\<lambda>\<alpha> L. fo_un ops L \<alpha>) xs"

text \<open>The replay mode measures, on samples over epochs, the size of @{term L} and the number of
steps with new tuples.\<close>

definition frz_meas :: "('a, 't) frz_ops \<Rightarrow> bool \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow>
    nat \<times> 'a \<times> nat \<times> nat \<times> nat \<Rightarrow> nat \<times> 'a \<times> nat \<times> nat \<times> nat" where
  "frz_meas ops g rs xsr m = (case m of (cy, Lm, nm, en, ep) \<Rightarrow>
     if g then
       (let c = cy mod frz_epoch in
          (case frz_absorb ops (map (fo_smp ops) xsr)
              (if c = 0 then frz_unions ops (map (fo_smp ops) rs) (fo_emp ops) else Lm, 0, 0) of
            (Lm1, _, nf) \<Rightarrow> let nm1 = nm + (if 0 < nf then 1 else 0) in
              if Suc c = frz_epoch then (Suc cy, fo_emp ops, 0, frz_sample * fo_cd ops Lm1, nm1)
              else (Suc cy, Lm1, nm1, en, ep)))
     else m)"

text \<open>The replay mode: the copies of @{const frz_live_loop}, then the decision.\<close>

definition frz_stock where
  "frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr lr c \<sigma>S \<sigma>E s = (case c of (rg, bo, cy, Lm, nm, en, ep, rs) \<Rightarrow>
     (case frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s of (ys, \<alpha>s', lv, s') \<Rightarrow>
      (case frz_meas ops (frz_lambda < frz_cut po (fst (snd s')) i j) rs xsr (cy, Lm, nm, en, ep) of
        (cy', Lm', nm', en', ep') \<Rightarrow>
       let k = j - fst (snd s');
           ct = frz_cut po (fst (snd s')) i j;
           rs' = take frz_keep (xsr @ rs);
           rg' = rg + ct * sum_list (map (fo_cd ops) xsr) - (frz_lambda * en' + ct * en' * ep' div frz_epoch)
       in if frz_epoch \<le> cy' \<and> bo * (k * en' + frz_c0) < rg'
          then (let L = frz_unions ops \<alpha>s' (frz_unions ops rs' (fo_emp ops)) in
            case frz_copies sz ev (fo_emp ops) pm dbe j (i + length ys) L \<sigma>S \<sigma>E s' of
              Some (\<rho>S, \<rho>E, pX, buf) \<Rightarrow> (ys, \<alpha>s', None, s', FSSep L (fo_cd ops L) pX buf 0 bo 0 (fo_emp ops), \<rho>S, \<rho>E)
            | None \<Rightarrow> (ys, \<alpha>s', lv, s', FSStock 0 bo cy' Lm' nm' en' ep' rs', \<sigma>S, \<sigma>E))
          else (ys, \<alpha>s', lv, s', FSStock rg' bo cy' Lm' nm' en' ep' rs', \<sigma>S, \<sigma>E))))"

text \<open>The separable mode rebuilds its copies if a new frozen table is not contained in @{term L} or
if @{term L} shrinks at the end of an epoch.\<close>

definition frz_step where
  "frz_step sz ev ops pm dbe fl d po j i \<alpha>s xsr lr fd sx \<sigma>S \<sigma>E s = (case sx of
     FSSep L nL pX buf rg bo tk Lr \<Rightarrow>
       (case frz_absorb ops xsr (L, nL, 0) of (L1, nL1, nf) \<Rightarrow>
        let Lr1 = frz_unions ops xsr Lr;
            ep = frz_epoch \<le> Suc tk;
            Lp = frz_unions ops \<alpha>s Lr1;
            nP = (if ep then fo_cd ops Lp else 0);
            pr = (nf = 0 \<and> ep \<and> 2 * nP + 256 < nL1);
            rb = (0 < nf \<or> pr);
            Ln = (if pr then Lp else L1);
            nLn = (if pr then nP else nL1);
            tk' = (if ep then 0 else Suc tk);
            Lr' = (if ep then fo_emp ops else Lr1);
            s2 = (if rb then frz_adv_st sz ev pm dbe fl d j i s else s);
            cp = (if rb then frz_copies sz ev (fo_emp ops) pm dbe j i Ln \<sigma>S \<sigma>E s2
              else (case fd of
                Some ((uS, \<rho>S), (uE, \<rho>E)) \<Rightarrow> if sz \<rho>S = sz \<sigma>S \<and> sz \<rho>E = sz \<sigma>E
                  then Some (\<rho>S, \<rho>E, pX + length uS,
                    drop (min i (pX + length uS) - (pX - length buf)) (buf @ zip uS uE))
                  else None
              | None \<Rightarrow> None))
        in (case cp of
          None \<Rightarrow> frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr None (0, bo, 0, fo_emp ops, 0, 0, 0, [Ln]) \<sigma>S \<sigma>E s2
        | Some (\<rho>S, \<rho>E, pX', buf') \<Rightarrow>
          (let ys = frz_emit (fo_cmb ops) \<alpha>s buf';
               s' = frz_adv_st sz ev pm dbe fl d j (i + length ys) s2;
               k = j - fst (snd s');
               rg' = rg + (frz_lambda * nLn + (if rb then k * nLn else 0)) -
                 frz_cut po (fst (snd s')) i j * sum_list (map (fo_cd ops) xsr)
           in if k * max 1 nLn + frz_c0 < rg'
             then (ys, drop (length ys) \<alpha>s, None, s', FSStock 0 (2 * bo) 0 (fo_emp ops) 0 0 0 [Ln], \<sigma>S, \<sigma>E)
             else (ys, drop (length ys) \<alpha>s, None, s', FSSep Ln nLn pX' (drop (length ys) buf') rg' bo tk' Lr', \<rho>S, \<rho>E))))
   | FSStock rg bo cy Lm nm en ep rs \<Rightarrow> frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr lr (rg, bo, cy, Lm, nm, en, ep, rs) \<sigma>S \<sigma>E s
   | FSOff \<Rightarrow> (case frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s of
       (ys, \<alpha>s', lv, s') \<Rightarrow> (ys, \<alpha>s', lv, s', FSOff, \<sigma>S, \<sigma>E)))"

lemma frz_copies_cong[fundef_cong]:
  assumes "\<And>ts db \<psi>. sz \<psi> = sz (fst s) \<Longrightarrow> ev ts db \<psi> = ev' ts db \<psi>"
  shows "frz_copies sz ev emp pm dbe j i L \<sigma>S \<sigma>E s = frz_copies sz ev' emp pm dbe j i L \<sigma>S \<sigma>E s"
  using assms by (auto simp: frz_copies_def split: prod.splits)

lemma frz_copies_size:
  "frz_copies sz ev emp pm dbe j i L \<sigma>S \<sigma>E s = Some (\<rho>S, \<rho>E, pX, buf) \<Longrightarrow> sz \<rho>S = sz \<sigma>S \<and> sz \<rho>E = sz \<sigma>E"
  by (auto simp: frz_copies_def split: prod.splits if_splits)

lemma frz_stock_cong[fundef_cong]:
  assumes "\<And>ts db \<psi>. sz \<psi> = sz (fst s) \<Longrightarrow> ev ts db \<psi> = ev' ts db \<psi>"
  shows "frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr lr c \<sigma>S \<sigma>E s =
    frz_stock sz ev' ops pm dbe fl d po j i \<alpha>s xsr lr c \<sigma>S \<sigma>E s"
proof -
  obtain ys \<alpha>s' lv s' where l: "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (ys, \<alpha>s', lv, s')"
    by (metis prod_cases4)
  have l': "frz_live_loop sz ev' pm dbe fl d po j i \<alpha>s lr s = (ys, \<alpha>s', lv, s')"
    using l frz_live_loop_cong[of sz s ev ev', OF assms] by simp
  have sz: "sz (fst s') = sz (fst s)"
    by (rule frz_live_loop_size[OF l])
  have cps: "frz_copies sz ev e pm dbe j i' L \<sigma>S \<sigma>E s' = frz_copies sz ev' e pm dbe j i' L \<sigma>S \<sigma>E s'" for e i' L
    by (rule frz_copies_cong) (use assms sz in simp)
  show ?thesis
    unfolding frz_stock_def l l' prod.case by (simp only: cps)
qed

lemma frz_stock_eq:
  assumes "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (ys0, \<alpha>s0, lv0, s0)"
    and "frz_meas ops (frz_lambda < frz_cut po (fst (snd s0)) i j) rs xsr (cy, Lm, nm, en, ep) =
      (cy', Lm', nm', en', ep')"
  shows "frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr lr (rg, bo, cy, Lm, nm, en, ep, rs) \<sigma>S \<sigma>E s =
    (let k = j - fst (snd s0);
         ct = frz_cut po (fst (snd s0)) i j;
         rs' = take frz_keep (xsr @ rs);
         rg' = rg + ct * sum_list (map (fo_cd ops) xsr) - (frz_lambda * en' + ct * en' * ep' div frz_epoch);
         L = frz_unions ops \<alpha>s0 (frz_unions ops rs' (fo_emp ops))
     in if frz_epoch \<le> cy' \<and> bo * (k * en' + frz_c0) < rg'
        then (case frz_copies sz ev (fo_emp ops) pm dbe j (i + length ys0) L \<sigma>S \<sigma>E s0 of
            Some (\<rho>S, \<rho>E, pX, buf) \<Rightarrow> (ys0, \<alpha>s0, None, s0, FSSep L (fo_cd ops L) pX buf 0 bo 0 (fo_emp ops), \<rho>S, \<rho>E)
          | None \<Rightarrow> (ys0, \<alpha>s0, lv0, s0, FSStock 0 bo cy' Lm' nm' en' ep' rs', \<sigma>S, \<sigma>E))
        else (ys0, \<alpha>s0, lv0, s0, FSStock rg' bo cy' Lm' nm' en' ep' rs', \<sigma>S, \<sigma>E))"
  unfolding frz_stock_def assms prod.case Let_def ..

lemma frz_stock_size:
  assumes "frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr lr c \<sigma>S \<sigma>E s = (ys, \<alpha>s', lv, s', sx', \<rho>S, \<rho>E)"
  shows "sz (fst s') = sz (fst s) \<and> sz \<rho>S = sz \<sigma>S \<and> sz \<rho>E = sz \<sigma>E"
proof -
  obtain ys0 \<alpha>s0 lv0 s0 where l: "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (ys0, \<alpha>s0, lv0, s0)"
    by (metis prod_cases4)
  have sz0: "sz (fst s0) = sz (fst s)"
    by (rule frz_live_loop_size[OF l])
  obtain rg bo cy Lm nm en ep rs where c: "c = (rg, bo, cy, Lm, nm, en, ep, rs)"
    by (metis prod.collapse)
  obtain cy' Lm' nm' en' ep' where ab: "frz_meas ops (frz_lambda < frz_cut po (fst (snd s0)) i j) rs xsr
      (cy, Lm, nm, en, ep) = (cy', Lm', nm', en', ep')"
    by (metis prod_cases5)
  have "case frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr lr c \<sigma>S \<sigma>E s of (_, _, _, s', _, \<rho>S, \<rho>E) \<Rightarrow>
      sz (fst s') = sz (fst s) \<and> sz \<rho>S = sz \<sigma>S \<and> sz \<rho>E = sz \<sigma>E"
    unfolding c frz_stock_eq[OF l ab] Let_def
    by (auto simp: sz0 split: option.split prod.split dest: frz_copies_size)
  then show ?thesis
    using assms by simp
qed

lemma frz_step_cong[fundef_cong]:
  assumes "\<And>ts db \<psi>. sz \<psi> = sz (fst s) \<Longrightarrow> ev ts db \<psi> = ev' ts db \<psi>"
  shows "frz_step sz ev ops pm dbe fl d po j i \<alpha>s xsr lr fd sx \<sigma>S \<sigma>E s =
    frz_step sz ev' ops pm dbe fl d po j i \<alpha>s xsr lr fd sx \<sigma>S \<sigma>E s"
proof -
  have adv: "frz_adv_st sz ev pm dbe fl d j i' s = frz_adv_st sz ev' pm dbe fl d j i' s" for i'
    by (rule frz_adv_st_cong) (rule assms)
  have sz_if: "sz (fst (if b then frz_adv_st sz ev' pm dbe fl d j i' s else s)) = sz (fst s)" for b i'
    using size_frz_adv_st[of sz ev' pm dbe fl d j i' s] by simp
  have cpG: "frz_copies sz ev e pm dbe j i' L \<sigma>S \<sigma>E s2 = frz_copies sz ev' e pm dbe j i' L \<sigma>S \<sigma>E s2"
    if "sz (fst s2) = sz (fst s)" for e i' L s2
    by (rule frz_copies_cong) (use assms that in simp)
  have stG: "frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr lr' c \<sigma>S \<sigma>E s2 =
      frz_stock sz ev' ops pm dbe fl d po j i \<alpha>s xsr lr' c \<sigma>S \<sigma>E s2"
    if "sz (fst s2) = sz (fst s)" for lr' c s2
    by (rule frz_stock_cong) (use assms that in simp)
  have advG: "frz_adv_st sz ev pm dbe fl d j i' s2 = frz_adv_st sz ev' pm dbe fl d j i' s2"
    if "sz (fst s2) = sz (fst s)" for i' s2
    by (rule frz_adv_st_cong) (use assms that in simp)
  have lp: "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = frz_live_loop sz ev' pm dbe fl d po j i \<alpha>s lr s"
    by (rule frz_live_loop_cong) (rule assms)
  show ?thesis
    unfolding frz_step_def Let_def
    by (simp only: adv sz_if cpG stG advG lp)
qed

lemma frz_step_sep_eq:
  assumes "frz_absorb ops xsr (L, nL, 0) = (L1, nL1, nf)"
  shows "frz_step sz ev ops pm dbe fl d po j i \<alpha>s xsr lr fd (FSSep L nL pX buf rg bo tk Lr) \<sigma>S \<sigma>E s =
    (let Lr1 = frz_unions ops xsr Lr;
         ep = frz_epoch \<le> Suc tk;
         Lp = frz_unions ops \<alpha>s Lr1;
         nP = (if ep then fo_cd ops Lp else 0);
         pr = (nf = 0 \<and> ep \<and> 2 * nP + 256 < nL1);
         rb = (0 < nf \<or> pr);
         Ln = (if pr then Lp else L1);
         nLn = (if pr then nP else nL1);
         tk' = (if ep then 0 else Suc tk);
         Lr' = (if ep then fo_emp ops else Lr1);
         s2 = (if rb then frz_adv_st sz ev pm dbe fl d j i s else s);
         cp = (if rb then frz_copies sz ev (fo_emp ops) pm dbe j i Ln \<sigma>S \<sigma>E s2
           else (case fd of
             Some ((uS, \<rho>S), (uE, \<rho>E)) \<Rightarrow> if sz \<rho>S = sz \<sigma>S \<and> sz \<rho>E = sz \<sigma>E
               then Some (\<rho>S, \<rho>E, pX + length uS,
                 drop (min i (pX + length uS) - (pX - length buf)) (buf @ zip uS uE))
               else None
           | None \<Rightarrow> None))
     in (case cp of
       None \<Rightarrow> frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr None (0, bo, 0, fo_emp ops, 0, 0, 0, [Ln]) \<sigma>S \<sigma>E s2
     | Some (\<rho>S, \<rho>E, pX', buf') \<Rightarrow>
       (let ys = frz_emit (fo_cmb ops) \<alpha>s buf';
            s' = frz_adv_st sz ev pm dbe fl d j (i + length ys) s2;
            k = j - fst (snd s');
            rg' = rg + (frz_lambda * nLn + (if rb then k * nLn else 0)) -
                 frz_cut po (fst (snd s')) i j * sum_list (map (fo_cd ops) xsr)
        in if k * max 1 nLn + frz_c0 < rg'
          then (ys, drop (length ys) \<alpha>s, None, s', FSStock 0 (2 * bo) 0 (fo_emp ops) 0 0 0 [Ln], \<sigma>S, \<sigma>E)
          else (ys, drop (length ys) \<alpha>s, None, s', FSSep Ln nLn pX' (drop (length ys) buf') rg' bo tk' Lr', \<rho>S, \<rho>E))))"
  unfolding frz_step_def frz_sep.case assms prod.case ..

lemma frz_step_size:
  assumes "frz_step sz ev ops pm dbe fl d po j i \<alpha>s xsr lr fd sx \<sigma>S \<sigma>E s = (ys, \<alpha>s', lv, s', sx', \<rho>S, \<rho>E)"
  shows "sz (fst s') = sz (fst s) \<and> sz \<rho>S = sz \<sigma>S \<and> sz \<rho>E = sz \<sigma>E"
proof (cases sx)
  case FSOff
  obtain ys0 \<alpha>s0 lv0 s0 where l: "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (ys0, \<alpha>s0, lv0, s0)"
    by (metis prod_cases4)
  show ?thesis
    using assms FSOff frz_live_loop_size[OF l] by (simp add: frz_step_def l)
next
  case (FSStock rg bo cy Lm nm en ep rs)
  with assms show ?thesis
    using frz_stock_size by (simp add: frz_step_def)
next
  case (FSSep L nL pX buf rg bo tk Lr)
  obtain L1 nL1 nf where ab: "frz_absorb ops xsr (L, nL, 0) = (L1, nL1, nf)"
    by (metis prod_cases3)
  define Lr1 where "Lr1 = frz_unions ops xsr Lr"
  define ep where "ep = (frz_epoch \<le> Suc tk)"
  define nP where "nP = (if ep then fo_cd ops (frz_unions ops \<alpha>s Lr1) else 0)"
  define pr where "pr = (nf = 0 \<and> ep \<and> 2 * nP + 256 < nL1)"
  define rb where "rb = (0 < nf \<or> pr)"
  define Ln where "Ln = (if pr then frz_unions ops \<alpha>s Lr1 else L1)"
  define nLn where "nLn = (if pr then nP else nL1)"
  define tk' where "tk' = (if ep then 0 else Suc tk)"
  define Lr' where "Lr' = (if ep then fo_emp ops else Lr1)"
  define sB where "sB = (if rb then frz_adv_st sz ev pm dbe fl d j i s else s)"
  define cq where "cq = (if rb then frz_copies sz ev (fo_emp ops) pm dbe j i Ln \<sigma>S \<sigma>E sB
    else (case fd of Some ((uS, \<rho>S), (uE, \<rho>E)) \<Rightarrow> if sz \<rho>S = sz \<sigma>S \<and> sz \<rho>E = sz \<sigma>E
        then Some (\<rho>S, \<rho>E, pX + length uS, drop (min i (pX + length uS) - (pX - length buf)) (buf @ zip uS uE))
        else None
      | None \<Rightarrow> None))"
  have stq: "frz_step sz ev ops pm dbe fl d po j i \<alpha>s xsr lr fd sx \<sigma>S \<sigma>E s = (case cq of
      None \<Rightarrow> frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr None (0, bo, 0, fo_emp ops, 0, 0, 0, [Ln]) \<sigma>S \<sigma>E sB
    | Some (\<rho>S2, \<rho>E2, pX', buf') \<Rightarrow>
      (let ys = frz_emit (fo_cmb ops) \<alpha>s buf';
           s'' = frz_adv_st sz ev pm dbe fl d j (i + length ys) sB;
           k = j - fst (snd s'');
           rg' = rg + (frz_lambda * nLn + (if rb then k * nLn else 0)) -
                 frz_cut po (fst (snd s'')) i j * sum_list (map (fo_cd ops) xsr)
       in if k * max 1 nLn + frz_c0 < rg'
         then (ys, drop (length ys) \<alpha>s, None, s'', FSStock 0 (2 * bo) 0 (fo_emp ops) 0 0 0 [Ln], \<sigma>S, \<sigma>E)
         else (ys, drop (length ys) \<alpha>s, None, s'', FSSep Ln nLn pX' (drop (length ys) buf') rg' bo tk' Lr', \<rho>S2, \<rho>E2)))"
    unfolding FSSep frz_step_sep_eq[OF ab] Let_def
    by (simp only: Lr1_def ep_def nP_def pr_def rb_def Ln_def nLn_def tk'_def Lr'_def sB_def cq_def)
  have szB: "sz (fst sB) = sz (fst s)"
    by (simp add: sB_def size_frz_adv_st)
  show ?thesis
  proof (cases cq)
    case None
    show ?thesis
      using frz_stock_size[OF assms[unfolded stq None option.case]] szB by simp
  next
    case (Some cc)
    then obtain \<rho>S2 \<rho>E2 pX2 buf2 where cqS: "cq = Some (\<rho>S2, \<rho>E2, pX2, buf2)"
      by (metis prod_cases4)
    have cqsz: "sz \<rho>S2 = sz \<sigma>S \<and> sz \<rho>E2 = sz \<sigma>E"
    proof (cases rb)
      case True
      then show ?thesis
        using cqS frz_copies_size[of sz ev "fo_emp ops" pm dbe j i Ln \<sigma>S \<sigma>E sB] by (simp add: cq_def)
    next
      case False
      then show ?thesis
        using cqS by (auto simp: cq_def split: option.splits if_splits)
    qed
    show ?thesis
      using assms[unfolded stq cqS option.case prod.case Let_def] cqsz szB
      by (auto simp: size_frz_adv_st split: if_splits)
  qed
qed

subsubsection \<open>Operations on kernel tables\<close>

text \<open>A sample keeps the tuples whose hash code is divisible by @{const frz_sample}.\<close>

definition frz_smask :: hashcode where "frz_smask = 7"

definition frz_sampled :: "event_data list \<Rightarrow> bool" where
  "frz_sampled x \<longleftrightarrow> Bit_Operations.and (hashcode x) frz_smask = 0"

definition frz_kops :: "nat \<Rightarrow> nat list \<Rightarrow> (event_data list set, event_data table) frz_ops" where
  "frz_kops m cs = FrzOps (\<lambda>yS yE \<alpha>. {x \<in> yS. val m cs x \<in> \<alpha>} \<union> {x \<in> yE. val m cs x \<notin> \<alpha>})
    (\<union>) (\<lambda>\<alpha> L. card (\<alpha> - L)) card {} (\<lambda>\<alpha>. {x \<in> \<alpha>. frz_sampled x})"

subsection \<open>Recursive evaluation\<close>

fun list_of_option :: "'a option \<Rightarrow> 'a list" where
  "list_of_option None = []"
| "list_of_option (Some x) = [x]"

fun eval_mtrm :: "mtrm \<Rightarrow> event_data \<Rightarrow> event_data table" where
  "eval_mtrm (MVar v) x = singleton_table x"
| "eval_mtrm (MConst c) x = (if c = x then unit_table else empty_table)"

definition pred_cols :: "Formula.trm list \<Rightarrow> nat list" where
  "pred_cols ts = fold (\<lambda>t cs. cols_union cs (Formula.fv_trm_list t)) ts []"

type_synonym database = "(Formula.name \<times> nat, event_data table list) mapping"

context maux_ops
begin

context
  fixes j :: nat
begin

text \<open>@{const MLet}, @{const MFrz} and @{const MLetPast} reorder a bound formula's tables to
@{term "[0..<m]"}. The @{const MFrz} equation returns each stage's values as a tuple, for speed.\<close>

function (sequential) meval :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> ('msaux, 'muaux, 'mtaux) mformula \<Rightarrow>
    event_data table list \<times> ('msaux, 'muaux, 'mtaux) mformula" where
  "meval n ts db (MRel rel) = (replicate (length ts) rel, MRel rel)"
| "meval n ts db (MPred e tms mode) =
    ((case Mapping.lookup db (e, length tms) of
        None \<Rightarrow> replicate (length ts) {}
      | Some xs \<Rightarrow> (case mode of
          Copy \<Rightarrow> xs
        | Simple \<Rightarrow> xs
        | Match \<Rightarrow> map (\<lambda>X. tabulate_match (pred_cols tms) ` Option.these (match tms ` X)) xs)),
    MPred e tms mode)"
| "meval n ts db (MLet p m cs \<phi> \<psi>) =
    (let (xs, \<phi>) = meval m ts db \<phi>;
      (ys, \<psi>) = meval n ts (Mapping.update (p, m) (map (reorder [0..<m] cs) xs) db) \<psi>
    in (ys, MLet p m cs \<phi> \<psi>))"
| "meval n ts db (MFrz p m cs \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E) =
    (let (xs, \<phi>) = meval m ts db \<phi>;
         db0 = Mapping.update (p, m) [] db;
         (zs0, \<psi>) = meval n ts db0 \<psi>;
         (rs, \<rho>) = meval n ts db0 \<rho>;
         (zs0_out, jfrz, fl, \<alpha>s, lr, xsr, fd) =
           (let zs0_out = drop (jfrz - jpsi0) zs0;
                xsr = map (reorder [0..<m] cs) xs;
                \<alpha>s0 = \<alpha>s @ xsr;
                \<alpha>s1 = drop (jfrz - jphi + length zs0_out) \<alpha>s0
            in (zs0_out, jfrz + length zs0_out, frz_fill ng \<alpha>s0, \<alpha>s1,
              case lv of None \<Rightarrow> None | Some g \<Rightarrow>
                if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
                then Some (g, meval n ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
                else None,
              xsr,
              case sx of FSSep L _ _ _ _ _ _ _ \<Rightarrow>
                Some (meval n ts (Mapping.update (p, m) (replicate (length ts) L) db) \<rho>S,
                  meval n ts (Mapping.update (p, m) (replicate (length ts) {}) db) \<rho>E)
              | _ \<Rightarrow> None));
         (ys, \<alpha>s', lv, (\<rho>, w, pR, tq, rb), sx, \<rho>S, \<rho>E) = frz_step size (meval n) (frz_kops m cS) (p, m)
           (Mapping.map_values (\<lambda>_ _. []) db) fl d po j jfrz \<alpha>s xsr lr fd sx \<rho>S \<rho>E
           (\<rho>, w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
             drop (min jfrz (pR + length rs) - (pR - length rb)) (rb @ rs))
     in (zs0_out @ ys, MFrz p m cs \<phi> \<psi> (jfrz + length ys) (jpsi0 + length zs0) (jphi + length xs) \<alpha>s' \<rho> w pR tq rb d po ng
       (frz_keep_lv (if po then None else lv) \<rho>L) (frz_keep_st (if po then None else lv) \<rho>L) sx cS \<rho>S \<rho>E))"
| "meval n ts db (MAnd A_\<phi> \<phi> pos A_\<psi> \<psi> buf) =
    (let (xs, \<phi>) = meval n ts db \<phi>; (ys, \<psi>) = meval n ts db \<psi>;
      (zs, buf) = mbuf2_take (\<lambda>r1 r2. bin_join A_\<phi> r1 pos A_\<psi> r2) (mbuf2_add xs ys buf)
    in (zs, MAnd A_\<phi> \<phi> pos A_\<psi> \<psi> buf))"
| "meval n ts db (MLetPast p m cs \<phi> \<psi> i buf) =
    (let (xs, i, buf, \<phi>) = letpast_meval0 (\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] cs)) (meval m ts db \<phi>))
           j i [] (list_of_option buf) (p, m) ts db \<phi>;
         (ys, \<psi>) = meval n ts (Mapping.update (p, m) xs db) \<psi>
    in (ys, MLetPast p m cs \<phi> \<psi> i buf))"
| "meval n ts db (MAndAssign cs \<phi> conf) =
    (let (xs, \<phi>) = meval n ts db \<phi> in
    (map (\<lambda>(r). (eval_assignment cs conf ` r)) xs, MAndAssign cs \<phi> conf))"
| "meval n ts db (MAndRel cs \<phi> conf) =
    (let (xs, \<phi>) = meval n ts db \<phi> in (map (\<lambda>(r). (Set.filter (eval_constraint cs conf) r)) xs, MAndRel cs \<phi> conf))"
| "meval n ts db (MAndTrigger V_\<phi> \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) = (let
    (as, \<phi>) = meval n ts db \<phi>;
    (xs, \<phi>') = meval n ts db \<phi>';
    (ys, \<psi>') = meval n ts db \<psi>';
    ((zs_trigger, aux), buf2, nts) = mbuf2T_take (\<lambda>r1 r2 t (zs, aux).
        let aux       = update_mtaux args t r1 r2 aux;
            (fv_z, z) = result_mtaux args aux
        in (zs @ [(fv_z, z)], aux)) ([], aux) (mbuf2_add xs ys buf2) (nts @ ts);
    (zs, buf1) = mbuf2_take (\<lambda>r1 (V_trigger, r2).
        bin_join V_\<phi> r1 True V_trigger r2
    ) (mbuf2_add as zs_trigger buf1)
    in
    (zs, MAndTrigger V_\<phi> \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux)
)"
| "meval n ts db (MAnds cs A_pos A_neg L buf) =
    (let R = map (meval n ts db) L in
    let buf = mbufn_add (map fst R) buf in
    let (zs, buf) = mbufn_take (\<lambda>xs zs. zs @ [mmulti_join cs A_pos A_neg xs]) [] buf in
    (zs, MAnds cs A_pos A_neg (map snd R) buf))"
| "meval n ts db (MOr cs1 \<phi> cs2 \<psi> buf) =
    (let (xs, \<phi>) = meval n ts db \<phi>; (ys, \<psi>) = meval n ts db \<psi>;
      (zs, buf) = mbuf2_take (\<lambda>(r1) (r2). (r1 \<union> reorder cs1 cs2 r2)) (mbuf2_add xs ys buf)
    in (zs, MOr cs1 \<phi> cs2 \<psi> buf))"
| "meval n ts db (MNeg \<phi>) =
    (let (xs, \<phi>) = meval n ts db \<phi> in (map (\<lambda>(r). (if r = empty_table then unit_table else empty_table)) xs, MNeg \<phi>))"
| "meval n ts db (MExists cs \<phi>) =
    (let (xs, \<phi>) = meval (Suc n) ts db \<phi> in (map (\<lambda>r. ex_proj cs ` r) xs, MExists cs \<phi>))"
| "meval n ts db (MAgg args \<phi>) =
    (let (xs, \<phi>) = meval (length (aggargs_tys args) + n) ts db \<phi> in (map (eval_aggargs args) xs, MAgg args \<phi>))"
| "meval n ts db (MPrev I \<phi> first buf nts) =
    (let (xs, \<phi>) = meval n ts db \<phi>
    in if first \<and> ts = [] then ([], MPrev I \<phi> True (buf @ xs) (nts @ ts))
    else let (zs, buf, nts) = mprev_next I (buf @ xs) (nts @ ts)
      in (if first then (empty_table) # zs else zs, MPrev I \<phi> False buf nts))"
| "meval n ts db (MNext I \<phi> first nts) =
    (let (xs, \<phi>) = meval n ts db \<phi>;
      (xs, first) = (case (xs, first) of (_ # xs, True) \<Rightarrow> (xs, False) | a \<Rightarrow> a);
      (zs, _, nts) = mprev_next I xs (nts @ ts)
    in (zs, MNext I \<phi> first nts))"
| "meval n ts db (MSince args \<phi> \<psi> buf aux) =
    (let (xs, \<phi>) = meval (args_n args) ts db \<phi>; (ys, \<psi>) = meval (args_n args) ts db \<psi>;
      (zs, buf, aux) = eval_since args [] (mbuf2S_add xs ys ts buf) aux
    in (zs, MSince args \<phi> \<psi> buf aux))"
| "meval n ts db (MUntil args \<phi> \<psi> buf nts t aux) =
    (let (xs, \<phi>) = meval (args_n args) ts db \<phi>; (ys, \<psi>) = meval (args_n args) ts db \<psi>;
      (aux, buf, nt, nts') = mbuf2t_take (add_new_muaux args) aux (mbuf2_add xs ys buf) t (nts @ ts);
      (zs, aux) = eval_muaux args nt aux
    in (zs, MUntil args \<phi> \<psi> buf nts' nt aux))"
| "meval n ts db (MTrigger args \<phi> \<psi> buf nts aux) =
    (let (xs, \<phi>) = meval n ts db \<phi>; (ys, \<psi>) = meval n ts db \<psi>;
      ((zs, aux), buf, nts) = mbuf2T_take (\<lambda>r1 r2 t (zs, aux).
        let aux       = update_mtaux args t r1 r2 aux;
            (fv_z, z) = result_mtaux args aux
        in (zs @ [(z)], aux)) ([], aux) (mbuf2_add xs ys buf) (nts @ ts)
    in (zs, MTrigger args \<phi> \<psi> buf nts aux))"
| "meval n ts db (MRelease args \<phi> \<psi> buf nts t aux) =
    (let (xs, \<phi>) = meval n ts db \<phi>; (ys, \<psi>) = meval n ts db \<psi>;
      (aux, buf, nt, nts') = mbuf2t_take (update_release args) aux (mbuf2_add xs ys buf) t (nts @ ts);
      (zs, aux) = eval_until (args_ivl args) nt aux
    in (zs, MRelease args \<phi> \<psi> buf nts' nt aux))"
| "meval n ts db (MMatchP I cs dss mr mrs \<phi>s buf nts aux) =
    (let (xss, \<phi>s) = map_split id (map (meval n ts db) \<phi>s);
      ((zs, aux), buf, _, nts) = mbufnt_take (\<lambda>rels t (zs, aux).
        let (z, aux) = update_matchP cs dss I mr mrs rels t aux
        in (zs @ [z], aux)) ([], aux) (mbufn_add xss buf) 0 (nts @ ts)
    in (zs, MMatchP I cs dss mr mrs \<phi>s buf nts aux))"
| "meval n ts db (MMatchF I cs dss mr mrs \<phi>s buf nts t aux) =
    (let (xss, \<phi>s) = map_split id (map (meval n ts db) \<phi>s);
      (aux, buf, nt, nts') = mbufnt_take (update_matchF cs dss I mr mrs) aux (mbufn_add xss buf) t (nts @ ts);
      (zs, aux) = eval_matchF I mr nt aux
    in (zs, MMatchF I cs dss mr mrs \<phi>s buf nts' nt aux))"
| "meval n ts db (MTP mt i) = (map (\<lambda>x. eval_mtrm mt (EInt (integer_of_nat x))) [i..<j], MTP mt j)"
| "meval n ts db (MTS mt) = (map (\<lambda>x. eval_mtrm mt (EInt (integer_of_nat x))) ts, MTS mt)"  by pat_completeness (simp_all only: prod.inject mformula.inject mformula.distinct simp_thms)

lemma
  psize_snd_meval: "meval_dom (n, t, db, \<phi>) \<Longrightarrow> size (snd (meval n t db \<phi>)) = size \<phi>"
proof (induct rule: meval.pinduct)
  case (6 n ts db p m cs \<phi> \<psi> i buf)
  let ?eval = "\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] cs)) (meval m ts db \<phi>)"
  obtain xs i' buf' \<phi>' where lp: "letpast_meval0 ?eval j i [] (list_of_option buf) (p, m) ts db \<phi> = (xs, i', buf', \<phi>')"
    by (metis prod_cases4)
  have "size (snd (snd (snd (letpast_meval0 ?eval j i [] (list_of_option buf) (p, m) ts db \<phi>)))) = size \<phi>"
    using 6(2) by (intro size_letpast_meval) simp
  then have size_\<phi>': "size \<phi>' = size \<phi>"
    by (simp add: lp)
  obtain ys \<psi>' where \<psi>': "meval n ts (Mapping.update (p, m) xs db) \<psi> = (ys, \<psi>')"
    by fastforce
  have size_\<psi>': "size \<psi>' = size \<psi>"
    using 6(3)[OF lp[symmetric] refl refl refl] \<psi>' by simp
  show ?case
    using size_\<phi>' size_\<psi>' by (simp add: meval.psimps(6)[OF 6(1)] lp \<psi>')next
  case (15 n ts db I \<phi> first buf nts)
  obtain xs \<phi>' where \<phi>': "meval n ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs buf' nts' where mp: "mprev_next I (buf @ xs) (nts @ ts) = (zs, buf', nts')"
    by (metis prod_cases3)
  have "size \<phi>' = size \<phi>"
    using 15(2) \<phi>' by simp
  then show ?case
    by (simp add: meval.psimps(15)[OF 15(1)] \<phi>' mp)
next
  case (4 n ts db p m cs \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E)
  let ?db0 = "Mapping.update (p, m) [] db"
  obtain xs \<phi>' where \<phi>': "meval m ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs0 \<psi>' where \<psi>': "meval n ts ?db0 \<psi> = (zs0, \<psi>')"
    by fastforce
  obtain rs \<rho>' where \<rho>': "meval n ts ?db0 \<rho> = (rs, \<rho>')"
    by fastforce
  have s\<phi>: "size \<phi>' = size \<phi>"
    using 4(2) \<phi>' by simp
  have s\<psi>: "size \<psi>' = size \<psi>"
    using 4(3)[OF \<phi>'[symmetric] refl refl] \<psi>' by simp
  have s\<rho>: "size \<rho>' = size \<rho>"
    using 4(4)[OF \<phi>'[symmetric] refl refl \<psi>'[symmetric] refl] \<rho>' by simp
  obtain zo jf fl as lr xsr fd where st: "(let zs0_out = drop (jfrz - jpsi0) zs0;
       xsr = map (reorder [0..<m] cs) xs;
       \<alpha>s0 = \<alpha>s @ xsr;
       \<alpha>s1 = drop (jfrz - jphi + length zs0_out) \<alpha>s0
     in (zs0_out, jfrz + length zs0_out, frz_fill ng \<alpha>s0, \<alpha>s1,
       case lv of None \<Rightarrow> None | Some g \<Rightarrow>
         if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
         then Some (g, meval n ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
         else None,
       xsr,
       case sx of FSSep L _ _ _ _ _ _ _ \<Rightarrow>
         Some (meval n ts (Mapping.update (p, m) (replicate (length ts) L) db) \<rho>S,
           meval n ts (Mapping.update (p, m) (replicate (length ts) {}) db) \<rho>E)
       | _ \<Rightarrow> None)) = (zo, jf, fl, as, lr, xsr, fd)"
    by (metis prod_cases7)
  obtain ys as' lv' s' sx' \<rho>S' \<rho>E' where lp0: "frz_step size (meval n) (frz_kops m cS) (p, m)
      (Mapping.map_values (\<lambda>_ _. []) db) fl d po j jf as xsr lr fd sx \<rho>S \<rho>E
      (\<rho>', w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
        drop (min jf (pR + length rs) - (pR - length rb)) (rb @ rs)) = (ys, as', lv', s', sx', \<rho>S', \<rho>E')"
    by (metis prod_cases7)
  obtain \<rho>'' w' pR' tq' rb' where s': "s' = (\<rho>'', w', pR', tq', rb')"
    by (metis prod_cases5)
  have s\<rho>'': "size \<rho>'' = size \<rho>" and sS: "size \<rho>S' = size \<rho>S" and sE: "size \<rho>E' = size \<rho>E"
    using frz_step_size[OF lp0] s\<rho> s' by simp_all
  have "snd (meval n ts db (MFrz p m cs \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E)) =
    MFrz p m cs \<phi>' \<psi>' (jf + length ys) (jpsi0 + length zs0) (jphi + length xs) as' \<rho>'' w' pR' tq' rb' d po ng
      (frz_keep_lv (if po then None else lv') \<rho>L) (frz_keep_st (if po then None else lv') \<rho>L) sx' cS \<rho>S' \<rho>E'"
    by (simp only: meval.psimps(4)[OF 4(1)] \<phi>' \<psi>' \<rho>' st lp0[unfolded s'] Let_def[where s = ?db0]
        Let_def[where s = "(xs, \<phi>')"] Let_def[where s = "(zs0, \<psi>')"] Let_def[where s = "(rs, \<rho>')"]
        Let_def[where s = "(zo, jf, fl, as, lr, xsr, fd)"]
        Let_def[where s = "(ys, as', lv', (\<rho>'', w', pR', tq', rb'), sx', \<rho>S', \<rho>E')"]
        prod.case snd_conv)
  then show ?case
    using s\<phi> s\<psi> s\<rho>'' sS sE by simp
qed (auto simp only: prod.inject meval.psimps Let_def snd_conv mformula.size map_split_map id_o map_split_eq_Pair_iff size_list_map o_apply size_frz_keep_st cong: size_list_cong split: prod.splits)

lemma total_meval: "All meval_dom"
proof (relation "measure (\<lambda>(_, _, _, \<phi>). size \<phi>)", goal_cases)
  case 7
  then show ?case
    by simp
next
  case 8
  then show ?case
    by simp
next
  case 9
  then show ?case
    by simp
next
  case (10 n ts db p m cs \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E x xa y xb xc xd ya xe
    xf yb xg xh yc xi yd xj yca xk ycb xl ycc xm ycd tsa dba \<psi>')
  have "size yb = size \<rho>"
    using psize_snd_meval[of n ts xb \<rho>] 10 by (metis snd_conv)
  then show ?case
    using 10 by simp
qed (auto simp: termination_simp dest!: psize_snd_meval dest: sym)
lemmas size_snd_meval = psize_snd_meval[OF total_meval[THEN spec]]

termination meval
  by (rule total_meval)

end

definition "letpast_meval m cs j =
  letpast_meval0 (\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] cs)) (meval j m ts db \<phi>)) j"

lemma letpast_meval_code[code]:
  "letpast_meval m cs j i ys xs p ts db \<phi> =
     (let (ys', \<phi>') = apfst (map (reorder [0..<m] cs)) (meval j m ts (Mapping.update p xs db) \<phi>) in
       (case ys' of
         [] \<Rightarrow> (ys @ ys', i + length xs, None, \<phi>')
       | y # _ \<Rightarrow> (if Suc (i + length xs) \<ge> j then (ys @ ys', i + length xs, Some y, \<phi>')
           else letpast_meval m cs j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>')))"
proof -
  obtain ys' \<phi>' where ev: "meval j m ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    by fastforce
  have "size \<phi>' = size \<phi>"
    using size_snd_meval[of j m ts "Mapping.update p xs db" \<phi>] ev by simp
  then show ?thesis
    unfolding letpast_meval_def by (subst (1) letpast_meval0.simps) (simp add: ev)
qed

declare meval.simps[simp del]
lemmas meval_simps[simp] = meval.simps[folded letpast_meval_def]
end

subsection \<open>Monitor steps\<close>

definition (in maux_ops) mstep :: "database \<times> ts \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate \<Rightarrow>
    (nat \<times> ts \<times> event_data table) list \<times> ('msaux, 'muaux, 'mtaux) mstate" where
  "mstep tdb st =
    (case meval (mstate_j st + 1) (mstate_n st) [snd tdb] (fst tdb) (mstate_m st) of
      (xs, m) \<Rightarrow> (List.indexed_from (mstate_i st) (zip (mstate_t st @ [snd tdb]) xs),
        \<lparr> mstate_i = mstate_i st + length xs,
          mstate_j = mstate_j st + 1,
          mstate_m = m,
          mstate_n = mstate_n st,
          mstate_t = drop (length xs) (mstate_t st @ [snd tdb]) \<rparr>))"

lift_definition mk_db :: "(Formula.name \<times> event_data list) set \<Rightarrow> database" is
  "\<lambda>X (p, n). (if (\<exists>ts. (p, ts) \<in> X \<and> n = length ts) 
    then Some [{ts. (p, ts) \<in> X \<and> n = length ts}] 
    else None)" .

context maux_ops
begin

primrec msteps0_stateless where
  "msteps0_stateless [] st = []"
| "msteps0_stateless (tdb # \<pi>) st = (let (V', st') = mstep (apfst mk_db tdb) st in V' @ msteps0_stateless \<pi> st')"

lift_definition msteps_stateless :: "Formula.prefix \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate 
  \<Rightarrow> (nat \<times> ts \<times> event_data table) list"
  is msteps0_stateless .

definition monitor where
  "monitor \<phi> \<pi> = msteps_stateless \<pi> (minit_safe \<phi>)"

end


(*<*)
end
(*>*)

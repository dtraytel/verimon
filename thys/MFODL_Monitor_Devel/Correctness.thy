(*<*)
theory Correctness
  imports
    Correct_Un_Ops
    Correct_Regex
    Correct_Since
    Correct_Trigger
    "MFOTL_Monitor_Devel.Abstract_Monitor"
begin
(*>*)


subsection \<open> Well-formed mformula invariant \<close>

definition (in maux) frz_qtable where
  "frz_qtable \<sigma> V m \<phi> k X =
    qtable m (Formula.fv \<phi>) (mem_restr UNIV) (\<lambda>v. Formula.sat \<sigma> V (map the v) k \<phi>) X"

definition (in maux) wf_frz_queue where
  "wf_frz_queue \<sigma> V m \<phi> ks Xs = list_all2 (\<lambda>k X. frz_qtable \<sigma> V m \<phi> k X) ks Xs"


definition (in maux) wf_frz_state where
  "wf_frz_state \<sigma> j P V p m \<phi> \<psi> jphi_val Xs =
    (let jphi = progress \<sigma> P \<phi> j;
         jfrz = progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j
     in jphi_val = jphi \<and> wf_frz_queue \<sigma> V m \<phi> [jfrz..<jphi] Xs)"

lemma (in maux) wf_frz_state_Nil[simp]:
  "wf_frz_state \<sigma> j P V p m \<phi> \<psi> jphi_val [] \<longleftrightarrow>
    jphi_val = progress \<sigma> P \<phi> j \<and>
    progress \<sigma> P \<phi> j \<le> progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j"
proof -
  let ?jphi = "progress \<sigma> P \<phi> j"
  let ?jfrz = "progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j"
  show ?thesis
    by (auto simp: wf_frz_state_def wf_frz_queue_def Let_def list_all2_conv_all_nth)
qed

text \<open>The windowed replay of @{const MFrz}: the replay base has absorbed the time points before
  @{term w} with, at each, the frozen predicate empty or holding the frozen formula's value at
  some time point (@{const frz_fill}); they lie beyond the past reach @{term d} of the body,
  seen from the first undecided time point @{term jfrz}.  The window's timestamps are kept
  (unless the reach is infinite, in which case the window never moves), and the verdicts of the
  replay base from @{term jfrz} on are those of the freeze.  A valuation of the frozen predicate
  of that kind is given by the time point whose frozen value it holds at each time point, if any
  (@{term frz_val}).\<close>

definition frz_val :: "Formula.trace \<Rightarrow> (Formula.name \<times> nat \<rightharpoonup> Formula.env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow>
    ty Formula.formula \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> Formula.env \<Rightarrow> nat \<Rightarrow> bool" where
  "frz_val \<sigma> V \<phi> L = (\<lambda>v k. case L k of None \<Rightarrow> False | Some i \<Rightarrow> Formula.sat \<sigma> V v i \<phi>)"

text \<open>A copy of the replay base for the frozen table of time point @{term i}: the frozen predicate
  holds that table from @{term w} on, and whatever the replay base absorbed before.\<close>

abbreviation frz_cv where
  "frz_cv \<sigma> V \<phi> N w i \<equiv> frz_val \<sigma> V \<phi> (\<lambda>k. if k < w then N k else Some i)"

lemma frz_cv_ge: "w \<le> k \<Longrightarrow> frz_cv \<sigma> V \<phi> N w i v k = Formula.sat \<sigma> V v i \<phi>"
  by (simp add: frz_val_def)

lemma frz_val_sat: "frz_val \<sigma> V \<phi> L v k \<Longrightarrow> \<exists>i. Formula.sat \<sigma> V v i \<phi>"
  by (auto simp: frz_val_def split: option.splits)

definition (in maux) wf_frz_win where
  "wf_frz_win \<sigma> j P V n R p m \<phi> \<psi> jfrz w pR tq rb d \<longleftrightarrow>
     w \<le> j \<and> d = past_reach \<psi> \<and>
     pR = progress \<sigma> (P((p, m) \<mapsto> w)) \<psi> j \<and>
     (\<forall>k<w. enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> jfrz)) \<and>
     tq = (if d = \<infinity> then [] else map (\<tau> \<sigma>) [w..<j]) \<and>
     list_all2 (\<lambda>k. qtable n (Formula.fv \<psi>) (mem_restr R)
       (\<lambda>v. Formula.sat \<sigma> V (map the v) k (Formula.Frz p \<phi> \<psi>))) [min jfrz pR..<pR] rb"

lemma (in maux) wf_frz_state_emptyD:
  assumes wf: "wf_frz_state \<sigma> j P V p m \<phi> \<psi> jphi_val Xs"
    and ge: "progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j \<ge> progress \<sigma> P \<phi> j"
  shows "Xs = []"
proof -
  let ?jphi = "progress \<sigma> P \<phi> j"
  let ?jfrz = "progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j"
  from wf have queue: "wf_frz_queue \<sigma> V m \<phi> [?jfrz..< ?jphi] Xs"
    by (auto simp: wf_frz_state_def Let_def)
  from ge have "[?jfrz..< ?jphi] = []"
    by simp
  with queue show ?thesis
    by (auto simp: wf_frz_queue_def)
qed


inductive (in maux) wf_mformula :: "Formula.trace \<Rightarrow> nat \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat 
  \<Rightarrow> event_data list set \<Rightarrow> ('msaux, 'muaux, 'mtaux) mformula \<Rightarrow> ty Formula.formula \<Rightarrow> bool" for \<sigma> j 
  where Eq: "is_simple_eq t1 t2 
    \<Longrightarrow> \<forall>x\<in>Formula.fv_trm t1. x < n \<Longrightarrow> \<forall>x\<in>Formula.fv_trm t2. x < n
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MRel (eq_rel n t1 t2)) (Formula.Eq t1 t2)"
  | Pred: "\<forall>x\<in>Formula.fv ((Formula.Pred e ts) :: ty Formula.formula). x < n 
    \<Longrightarrow> \<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MPred e ts (pred_mode_of n ts)) (Formula.Pred e ts)"
  | Let: "wf_mformula \<sigma> j P V m UNIV \<phi> \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j (P((p, m) \<mapsto> progress \<sigma> P \<phi>' j)) 
      (V((p, m) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>')) n R \<psi> \<psi>'
    \<Longrightarrow> {0..<m} \<subseteq> Formula.fv \<phi>' \<Longrightarrow> m = Formula.nfv \<phi>' \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MLet p m \<phi> \<psi>) (Formula.Let p \<phi>' \<psi>')"
  | Frz: "wf_mformula \<sigma> j P V m UNIV \<phi> \<phi>'
    \<Longrightarrow> \<forall>i. wf_mformula \<sigma> j (P((p, m) \<mapsto> 0)) (V((p, m) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w i \<phi>')) n R \<psi> \<psi>'
    \<Longrightarrow> wf_frz_state \<sigma> j P V p m \<phi>' \<psi>' jphi \<alpha>s
    \<Longrightarrow> jfrz = progress \<sigma> P (Formula.Frz p \<phi>' \<psi>') j
    \<Longrightarrow> jpsi0 = progress \<sigma> (P((p, m) \<mapsto> 0)) \<psi>' j
    \<Longrightarrow> \<forall>M. wf_mformula \<sigma> j (P((p, m) \<mapsto> w))
      (V((p, m) \<mapsto> frz_val \<sigma> V \<phi>' (\<lambda>k. if k < w then N k else M k))) n R \<rho> \<psi>'
    \<Longrightarrow> wf_frz_win \<sigma> j P V n R p m \<phi>' \<psi>' jfrz w pR tq rb d
    \<Longrightarrow> {0..<m} \<subseteq> Formula.fv \<phi>' \<Longrightarrow> m = Formula.nfv \<phi>' \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>'
    \<Longrightarrow> (po \<longrightarrow> safe_letpast (p, m) \<psi>' \<le> NonFutuRec)
    \<Longrightarrow> (\<forall>g. lv = Some g \<longrightarrow> \<not> po \<and> (\<exists>wL NL. (\<forall>k<wL. enat (\<tau> \<sigma> k) + past_reach \<psi>' < enat (\<tau> \<sigma> jfrz)) \<and>
      jfrz = progress \<sigma> (P((p, m) \<mapsto> j)) \<psi>' j + g \<and>
      wf_mformula \<sigma> j (P((p, m) \<mapsto> j)) (V((p, m) \<mapsto> frz_cv \<sigma> V \<phi>' NL wL jfrz)) n R \<rho>L \<psi>'))
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) (Formula.Frz p \<phi>' \<psi>')"
  | LetPast: "wf_mformula \<sigma> j (P((p, m)\<mapsto>i)) 
      (V((p, m) \<mapsto> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>'))) m UNIV \<phi> \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j (P((p, m) \<mapsto> letpast_progress \<sigma> P (p, m) \<phi>' j)) 
      (V((p, m) \<mapsto> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>'))) n R \<psi> \<psi>'
    \<Longrightarrow> (case buf of
      None \<Rightarrow> i = letpast_progress \<sigma> P (p, m) \<phi>' j
    | Some Z \<Rightarrow> Suc i = letpast_progress \<sigma> P (p, m) \<phi>' j \<and>
        qtable m (Formula.fv \<phi>') (mem_restr UNIV) 
          (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i) Z)
    \<Longrightarrow> safe_letpast (p, m) \<phi>' \<le> PastRec 
    \<Longrightarrow> \<comment> \<open>safe\<close> {0..<m} \<subseteq> Formula.fv \<phi>' \<Longrightarrow> m = Formula.nfv \<phi>'
    \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MLetPast p m \<phi> \<psi> i buf) (Formula.LetPast p \<phi>' \<psi>')"
  | And: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>'
    \<Longrightarrow> if pos then \<chi> = Formula.And \<phi>' \<psi>'
      else \<chi> = Formula.And \<phi>' (Formula.Neg \<psi>') \<and> Formula.fv \<psi>' \<subseteq> Formula.fv \<phi>'
    \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf
    \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MAnd (fv \<phi>') \<phi> pos (fv \<psi>') \<psi> buf) \<chi>"
  | AndAssign: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow>
    x < n \<Longrightarrow> x \<notin> Formula.fv \<phi>' \<Longrightarrow> Formula.fv_trm t \<subseteq> Formula.fv \<phi>' \<Longrightarrow> (x, t) = conf
    \<Longrightarrow> \<psi>' = Formula.Eq (Formula.Var x) t \<or> \<psi>' = Formula.Eq t (Formula.Var x)
    \<Longrightarrow> safe_formula \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MAndAssign \<phi> conf) (Formula.And \<phi>' \<psi>')"
  | AndRel: "wf_mformula \<sigma> j P V n R \<phi> \<phi>'
    \<Longrightarrow> \<psi>' = formula_of_constraint conf
    \<Longrightarrow> (let (t1, _, _, t2) = conf in Formula.fv_trm t1 \<union> Formula.fv_trm t2 \<subseteq> Formula.fv \<phi>')
    \<Longrightarrow> safe_formula \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MAndRel \<phi> conf) (Formula.And \<phi>' \<psi>')"
  | And_Trigger: "wf_mformula \<sigma> j P V n R \<alpha> \<alpha>' \<Longrightarrow> wf_mbuft2' \<sigma> P V j n R \<alpha>' \<phi>'' I \<psi>' buf1
    \<Longrightarrow> fv (Formula.Trigger \<phi>'' I \<psi>') \<subseteq> fv \<alpha>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>' \<Longrightarrow>
    if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<phi> \<phi>'
    \<Longrightarrow> safe_formula \<phi>'' = args_pos args \<Longrightarrow> args_ivl args = I \<Longrightarrow> args_n args = n
    \<Longrightarrow> args_L args = Formula.fv \<phi>' \<Longrightarrow> args_R args = Formula.fv \<psi>'
    \<Longrightarrow> \<forall>x\<in>Formula.fv \<psi>'. x < n 
    \<Longrightarrow> if mem I 0 then Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>' else Formula.fv \<phi>' = Formula.fv \<psi>'
    \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf2
    \<Longrightarrow> wf_ts \<sigma> P j \<phi>' \<psi>' nts
    \<Longrightarrow> wf_trigger_aux \<sigma> V R args \<phi>' \<psi>' aux (progress \<sigma> P (Formula.Trigger \<phi>'' I \<psi>') j)
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MAndTrigger (fv \<alpha>') \<alpha> buf1 args \<phi> \<psi> buf2 nts aux) 
      (Formula.And \<alpha>' (Formula.Trigger \<phi>'' I \<psi>'))"
  | And_Release: "\<not> mem I 0 \<Longrightarrow> bounded I \<Longrightarrow> Formula.fv \<phi>' = Formula.fv \<psi>' 
    \<Longrightarrow> Formula.fv \<psi>' \<subseteq> Formula.fv \<alpha>' \<Longrightarrow> safe_formula \<alpha>'
    \<Longrightarrow> safe_formula (release_safe_bounded \<phi>' I \<psi>')
    \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R (formula.And \<alpha>' (formula.Neg (Formula.eventually I Formula.TT))) (formula.And \<alpha>' (release_safe_bounded \<phi>' I \<psi>')) buf
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MOr L\<^sub>M R\<^sub>M buf) (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>')
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MOr L\<^sub>M R\<^sub>M buf) (Formula.And \<alpha>' (Formula.Release \<phi>' I \<psi>'))"
  | Ands: "list_all2 (\<lambda>\<phi> \<phi>'. wf_mformula \<sigma> j P V n R \<phi> \<phi>') l (l_pos @ map remove_neg l_neg)
    \<Longrightarrow> wf_mbufn (progress \<sigma> P (Formula.Ands l') j) 
      (map (\<lambda>\<psi>. progress \<sigma> P \<psi> j) (l_pos @ map remove_neg l_neg)) 
      (map (\<lambda>\<psi> i. qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>)) 
        (l_pos @ map remove_neg l_neg)) buf
    \<Longrightarrow> (l_pos, l_neg) = partition safe_formula l' \<Longrightarrow> l_pos \<noteq> []
    \<Longrightarrow> list_all safe_formula (map remove_neg l_neg)
    \<Longrightarrow> A_pos = map fv l_pos \<Longrightarrow> A_neg = map fv l_neg \<Longrightarrow> \<Union>(set A_neg) \<subseteq> \<Union>(set A_pos)
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MAnds A_pos A_neg l buf) (Formula.Ands l')"
  | Or: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>'
    \<Longrightarrow> Formula.fv \<phi>' = Formula.fv \<psi>' \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf
    \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MOr \<phi> \<psi> buf) (Formula.Or \<phi>' \<psi>')"
  | Neg: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> Formula.fv \<phi>' = {} \<Longrightarrow> safe_formula \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MNeg \<phi>) (Formula.Neg \<phi>')"
  | Exists: "wf_mformula \<sigma> j P V (Suc n) (lift_envs R) \<phi> \<phi>' \<Longrightarrow> safe_formula \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MExists \<phi>) (Formula.Exists t \<phi>')"
  | Agg: "wf_mformula \<sigma> j P V (length tys + n) (lift_envs' (length tys) R) \<phi> \<phi>'
    \<Longrightarrow> y < n \<Longrightarrow> y + (length tys) \<notin> Formula.fv \<phi>' \<Longrightarrow> {0..<length tys} \<subseteq> Formula.fv \<phi>'
    \<Longrightarrow> Formula.fv_trm f \<subseteq> Formula.fv \<phi>' \<Longrightarrow> aggargs_g0 args = (Formula.fv \<phi>' \<subseteq> {0..<length tys})
    \<Longrightarrow> aggargs_cols args = fv \<phi>' \<Longrightarrow> aggargs_n args = n \<Longrightarrow> aggargs_y args = y
    \<Longrightarrow> aggargs_\<omega> args = \<omega> \<Longrightarrow> aggargs_tys args = tys \<Longrightarrow> aggargs_f args = f \<Longrightarrow> safe_formula \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MAgg args \<phi>) (Formula.Agg y \<omega> tys f \<phi>')"
  | Prev: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> first \<longleftrightarrow> j = 0
    \<Longrightarrow> list_all2 (\<lambda>i (r). qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>') r)
      [min (progress \<sigma> P \<phi>' j) (j-1)..<progress \<sigma> P \<phi>' j] buf
    \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi>' j) (j-1)..<j] nts
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MPrev I \<phi> first buf nts) (Formula.Prev I \<phi>')"
  | Next: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> first \<longleftrightarrow> progress \<sigma> P \<phi>' j = 0
    \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress \<sigma> P \<phi>' j - 1..<j] nts
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MNext I \<phi> first nts) (Formula.Next I \<phi>')"
  | Since: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>'
    \<Longrightarrow> if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>'
    \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>' \<Longrightarrow> args_ivl args = I \<Longrightarrow> args_n args = n
    \<Longrightarrow> args_L args = Formula.fv \<phi>' \<Longrightarrow> args_R args = Formula.fv \<psi>'
    \<Longrightarrow> mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')
    \<Longrightarrow> Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>'
    \<Longrightarrow> wf_mbuf2S \<sigma> P V j n R \<phi>' I \<psi>' buf (min (progress \<sigma> P \<phi>' j) (progress \<sigma> P \<psi>' j)) 
      (progress \<sigma> P (Formula.Since \<phi>'' I \<psi>') j)
    \<Longrightarrow> wf_since_aux \<sigma> V R args \<phi>' \<psi>' aux (min (progress \<sigma> P \<phi>' j) (progress \<sigma> P \<psi>' j)) 
      (progress \<sigma> P (Formula.Since \<phi>'' I \<psi>') j)
    \<Longrightarrow> wf_mformula \<sigma> j P V (agg_n args) R' (MSince args \<phi> \<psi> buf aux) 
      (packagg args (Formula.Since \<phi>'' I \<psi>'))"
  | Until: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>'
    \<Longrightarrow> if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>'
    \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>' \<Longrightarrow> args_ivl args = I \<Longrightarrow> args_n args = n
    \<Longrightarrow> args_L args = Formula.fv \<phi>' \<Longrightarrow> args_R args = Formula.fv \<psi>'
    \<Longrightarrow> mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')
    \<Longrightarrow> Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>' \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf
    \<Longrightarrow> wf_ts \<sigma> P j \<phi>' \<psi>' nts
    \<Longrightarrow> t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (min (progress \<sigma> P \<phi>' j) (progress \<sigma> P \<psi>' j))))
    \<Longrightarrow> wf_until_aux \<sigma> V R args \<phi>' \<psi>' aux (progress \<sigma> P (Formula.Until \<phi>'' I \<psi>') j)
    \<Longrightarrow> progress \<sigma> P (Formula.Until \<phi>'' I \<psi>') j + length_muaux args aux 
      = min (progress \<sigma> P \<phi>' j) (progress \<sigma> P \<psi>' j)
    \<Longrightarrow> wf_mformula \<sigma> j P V (agg_n args) R' (MUntil args \<phi> \<psi> buf nts t aux) 
      (packagg args (Formula.Until \<phi>'' I \<psi>'))"
  | Trigger_0: "wf_mformula \<sigma> j P V n R \<psi> \<psi>'
    \<Longrightarrow> if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> safe_formula \<phi>'' = args_pos args \<Longrightarrow> args_ivl args = I
    \<Longrightarrow> args_n args = n \<Longrightarrow> args_L args = Formula.fv \<phi>' \<Longrightarrow> args_R args = Formula.fv \<psi>'
    \<Longrightarrow> \<forall>x\<in>Formula.fv \<psi>'. x < n \<Longrightarrow> mem I 0
    \<Longrightarrow> if mem I 0 then (Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>') else Formula.fv \<phi>' = Formula.fv \<psi>'
    \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf \<Longrightarrow> wf_ts \<sigma> P j \<phi>' \<psi>' nts
    \<Longrightarrow> wf_trigger_aux \<sigma> V R args \<phi>' \<psi>' aux (progress \<sigma> P (Formula.Trigger \<phi>'' I \<psi>') j)
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MTrigger args \<phi> \<psi> buf nts aux) (Formula.Trigger \<phi>'' I \<psi>')"
  | Release_0: "mem I 0 \<Longrightarrow> bounded I \<Longrightarrow> Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>' 
    \<Longrightarrow> safe_formula \<psi>' \<Longrightarrow> safe_formula (release_safe_0 \<phi>' I \<psi>')
    \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R (Formula.Until \<psi>' I (Formula.And \<psi>' \<phi>')) (always_safe_0 I \<psi>') buf
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MOr L\<^sub>M R\<^sub>M buf) (release_safe_0 \<phi>' I \<psi>')
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MOr L\<^sub>M R\<^sub>M buf) (Formula.Release \<phi>' I \<psi>')"
  | MatchP: "(case to_mregex r of (mr', \<phi>s') 
      \<Rightarrow> list_all2 (wf_mformula \<sigma> j P V n R) \<phi>s \<phi>s' \<and> mr = mr')
    \<Longrightarrow> mrs = sorted_list_of_set (RPDs mr) \<Longrightarrow> Regex.safe_regex fv rgx_safe_pred Past Strict r
    \<Longrightarrow> wf_mbufn' \<sigma> P V j n R r buf \<Longrightarrow> wf_ts_regex \<sigma> P j r nts
    \<Longrightarrow> wf_matchP_aux \<sigma> V n R I r aux (progress \<sigma> P (Formula.MatchP I r) j)
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MMatchP I mr mrs \<phi>s buf nts aux) (Formula.MatchP I r)"
  | MatchF: "(case to_mregex r of (mr', \<phi>s') 
      \<Rightarrow> list_all2 (wf_mformula \<sigma> j P V n R) \<phi>s \<phi>s' \<and> mr = mr')
    \<Longrightarrow> mrs = sorted_list_of_set (LPDs mr) \<Longrightarrow> Regex.safe_regex fv rgx_safe_pred Futu Strict r
    \<Longrightarrow> wf_mbufn' \<sigma> P V j n R r buf \<Longrightarrow> wf_ts_regex \<sigma> P j r nts
    \<Longrightarrow> t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (progress_regex \<sigma> P r j)))
    \<Longrightarrow> wf_matchF_aux \<sigma> V n R I r aux (progress \<sigma> P (Formula.MatchF I r) j) 0
    \<Longrightarrow> progress \<sigma> P (Formula.MatchF I r) j + length aux = progress_regex \<sigma> P r j
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MMatchF I mr mrs \<phi>s buf nts t aux) (Formula.MatchF I r)"
  | MTP: "\<forall>x\<in>Formula.fv_trm t. x < n \<Longrightarrow> Formula.is_Var t \<or> Formula.is_Const t
    \<Longrightarrow> mtrm_of_trm t = mt \<Longrightarrow> wf_mformula \<sigma> j P V n R (MTP mt j) (Formula.TP t)"
  | MTS: "\<forall>x\<in>Formula.fv_trm t. x < n \<Longrightarrow> Formula.is_Var t \<or> Formula.is_Const t
    \<Longrightarrow> mtrm_of_trm t = mt \<Longrightarrow> wf_mformula \<sigma> j P V n R (MTS mt) (Formula.TS t)"


definition (in maux) wf_mstate :: "sig \<Rightarrow> tyenv \<Rightarrow> ty Formula.formula \<Rightarrow> Formula.prefix 
  \<Rightarrow> event_data list set \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate \<Rightarrow> bool" 
  where "wf_mstate S E \<phi> \<pi> R st 
  \<longleftrightarrow> mstate_j st = plen \<pi> \<and> mstate_n st = Formula.nfv \<phi> \<and> S, E \<turnstile> \<phi> \<and> wty_prefix S \<pi> 
    \<and> (\<forall>\<sigma>. prefix_of \<pi> \<sigma> \<and> wty_trace S \<sigma> 
      \<longrightarrow> mstate_i st = progress \<sigma> Map.empty \<phi> (plen \<pi>) 
        \<and> wf_mformula \<sigma> (plen \<pi>) Map.empty Map.empty (mstate_n st) R (mstate_m st) \<phi>) 
        \<and> mstate_t st = drop (mstate_i st) (pts \<pi>)"



definition (in maux) letpast_meval_invar 
  where "letpast_meval_invar n V \<sigma> P \<phi>' m j' i ys xs p ts db \<phi> k 
  = (let j = j' - length ts in
    wf_mformula \<sigma> j (P((p, m)\<mapsto>i)) 
      (V((p, m) \<mapsto> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>'))) m UNIV \<phi> \<phi>' 
    \<and> i + length xs \<le> progress \<sigma> (P((p, m)\<mapsto>i)) \<phi>' j 
    \<and> i + length xs \<le> letpast_progress \<sigma> P (p, m) \<phi>' j 
    \<and> list_all2 
      (\<lambda>i X. qtable m (Formula.fv \<phi>') (mem_restr UNIV) 
        (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i) X)
      [i..<progress \<sigma> (P((p, m)\<mapsto>i)) \<phi>' j] xs
    \<and> list_all2 
      (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) 
        (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i))
      [k..<progress \<sigma> (P((p, m)\<mapsto>i)) \<phi>' j] ys 
    \<and> k \<le> progress \<sigma> (P((p, m)\<mapsto>i)) \<phi>' j)"

definition (in maux) letpast_meval_post 
  where "letpast_meval_post n V \<sigma> P \<phi>' m j i' xs buf' p \<phi>f k
  = (wf_mformula \<sigma> j (P((p, m)\<mapsto>i')) 
      (V((p, m) \<mapsto> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>'))) m UNIV \<phi>f \<phi>' 
    \<and> (case buf' of
      None \<Rightarrow> i' = letpast_progress \<sigma> P (p, m) \<phi>' j
    | Some Z \<Rightarrow> Suc i' = letpast_progress \<sigma> P (p, m) \<phi>' j 
      \<and> qtable m (Formula.fv \<phi>') (mem_restr UNIV) 
        (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i') Z) 
    \<and> list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) 
        (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i))
      [k..<letpast_progress \<sigma> P (p, m) \<phi>' j] xs)"

lemma (in maux) letpast_meval_invar_init:
  assumes "pred_mapping (\<lambda> x. x \<le> (j - length ts)) P"
  assumes "wf_mformula \<sigma> (j-length ts) P V n R (MLetPast p m \<phi> \<psi> i buf) (Formula.LetPast p \<phi>' \<psi>')"
  shows "letpast_meval_invar n V \<sigma> P \<phi>' m j i [] (list_of_option buf) p ts db \<phi> (letpast_progress \<sigma> P (p, m) \<phi>' (j-length ts))"
proof -
  from assms have
    1: "wf_mformula \<sigma> (j - length ts) (P((p, m)\<mapsto>i)) (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>'))) m UNIV \<phi> \<phi>'" 
    and 2: "case buf of
      None \<Rightarrow> i = letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts)
    | Some Z \<Rightarrow> Suc i = letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts) \<and>
        qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i) Z" 


    and 3: "safe_letpast (p, m) \<phi>' \<le> PastRec"
    by (auto elim: wf_mformula.cases)
  moreover have progress: "progress \<sigma> (P((p, m)\<mapsto>i)) \<phi>' (j-length ts) = letpast_progress \<sigma> P (p, m) \<phi>' (j-length ts)"
  proof (cases buf)
    case None
    with 2 have "i = letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts)" by simp
    then show ?thesis using assms(1) by (simp add: letpast_progress_fixpoint)
  next
    case (Some Z)
    with 2 have "Suc i = letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts)" by simp
    then show ?thesis
      using assms(1) 3 by (simp add: progress_Suc_letpast_progress_eq)
  qed
  moreover have "i + length (list_of_option buf) \<le> letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts)"
    using 2 by (cases buf) simp_all
  moreover have "list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>') (map the v) i))
      [i..<progress \<sigma> (P((p, m)\<mapsto>i)) \<phi>' (j-length ts)] (list_of_option buf)"
    unfolding progress using 2
    by (cases buf) (auto simp add: list_all2_Cons2 upt_eq_Cons_conv)
  ultimately show ?thesis unfolding letpast_meval_invar_def
    by (simp add: Let_def)
qed

lemma (in maux) invar_recursion_invar:
  assumes "pred_mapping (\<lambda> x. x\<le>(j-length ts)) P"
  assumes "pred_mapping (\<lambda> x. x\<le>j) P'"
  assumes "rel_mapping (\<le>) P P'"
  assumes meval: "case meval j m ts (Mapping.update (p, m) xs db) \<phi> of (xs', \<phi>\<^sub>n) \<Rightarrow>
    wf_mformula \<sigma> j (P'((p, m) \<mapsto> i + length xs)) (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>'))) m UNIV \<phi>\<^sub>n \<phi>' \<and>
    list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>') (map the v) i))
    [progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j-length ts)..<progress \<sigma> (P'((p, m) \<mapsto> i + length xs)) \<phi>' j] xs'"
  shows "letpast_meval_invar n V \<sigma> P \<phi>' m j i ys xs p ts db \<phi> k\<Longrightarrow>
  (ys', \<phi>f) = meval j m ts (Mapping.update (p, m) xs db) \<phi> \<Longrightarrow>
  ys' \<noteq> [] \<Longrightarrow>
  i + length xs < j \<Longrightarrow>
  letpast_meval_invar n V \<sigma> P' \<phi>' m j (i + length xs) (ys@ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>f k"
proof -
  let ?Q = "\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV)
    (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i)"
  let ?V = "V((p, m) \<mapsto> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>'))"
  let ?P' = "P'((p, m) \<mapsto> i + length xs)"
  let ?a = "progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j - length ts)"
  let ?b = "progress \<sigma> ?P' \<phi>' j"
  assume invar: "letpast_meval_invar n V \<sigma> P \<phi>' m j i ys xs p ts db \<phi> k"
    and eq: "(ys', \<phi>f) = meval j m ts (Mapping.update (p, m) xs db) \<phi>"
    and lt: "i + length xs < j"
  from invar have le_a: "i + length xs \<le> ?a"
    and le_lp: "i + length xs \<le> letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts)"
    and xs: "list_all2 ?Q [i..<?a] xs" and ys: "list_all2 ?Q [k..<?a] ys" and k: "k \<le> ?a"
    unfolding letpast_meval_invar_def Let_def by simp_all
  from meval have wf: "wf_mformula \<sigma> j ?P' ?V m UNIV \<phi>f \<phi>'" and ys': "list_all2 ?Q [?a..<?b] ys'"
    by (simp_all add: eq[symmetric])
  have "i \<le> j - length ts"
    using le_lp letpast_progress_le[OF assms(1), of \<sigma> "(p, m)" \<phi>'] by linarith
  then have "?a \<le> ?b"
    using assms(1-3) lt by (intro progress_mono_gen) simp_all
  have a: "i + length xs = ?a"
    using le_a list_all2_lengthD[OF xs] by simp
  have b: "i + length xs + length ys' = ?b"
    using a \<open>?a \<le> ?b\<close> list_all2_lengthD[OF ys'] by simp
  have "letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts) \<le> letpast_progress \<sigma> P' (p, m) \<phi>' j"
    using assms(1-3) by (intro letpast_progress_mono) simp_all
  with le_lp have "i + length xs \<le> letpast_progress \<sigma> P' (p, m) \<phi>' j"
    by (rule order_trans)
  then have "?b \<le> letpast_progress \<sigma> P' (p, m) \<phi>' j"
    using assms(2) by (intro le_letpast_progress_preservation) (simp_all add: rel_mapping_order_refl)
  with wf b ys' a k \<open>?a \<le> ?b\<close> list_all2_upt_append[OF ys ys' k \<open>?a \<le> ?b\<close>]
  show "letpast_meval_invar n V \<sigma> P' \<phi>' m j (i + length xs) (ys @ ys') ys' p []
    (Mapping.map_values (\<lambda>_ _. []) db) \<phi>f k"
    unfolding letpast_meval_invar_def Let_def by simp
qed

lemma (in maux) invar_recursion_post:
  assumes "safe_letpast (p, m) \<phi>' \<le> PastRec"
  assumes "pred_mapping (\<lambda> x. x\<le>(j-length ts)) P"
  assumes "pred_mapping (\<lambda> x. x\<le>j) P'"
  assumes "rel_mapping (\<le>) P P'"
  assumes meval: "case meval j m ts (Mapping.update (p, m) xs db) \<phi> of (xs', \<phi>\<^sub>n) \<Rightarrow>
    wf_mformula \<sigma> j (P'((p, m) \<mapsto> i + length xs)) (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>'))) m UNIV \<phi>\<^sub>n \<phi>' \<and>
    list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>') (map the v) i))
    [progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j-length ts)..<progress \<sigma> (P'((p, m) \<mapsto> i + length xs)) \<phi>' j] xs'"
  shows "letpast_meval_invar n V \<sigma> P \<phi>' m j i ys xs p ts db \<phi> k\<Longrightarrow>
  (ys', \<phi>f) = meval j m ts (Mapping.update (p, m) xs db) \<phi> \<Longrightarrow>
  i' = i + length xs \<Longrightarrow>
  (case ys' of [] \<Rightarrow> buf' = None | Z # _ \<Rightarrow> buf' = Some Z \<and> Suc i' \<ge> j) \<Longrightarrow>
  letpast_meval_post n V \<sigma> P' \<phi>' m j i' (ys@ys') buf' p \<phi>f k"
proof -
  let ?Q = "\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV)
    (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i)"
  let ?V = "V((p, m) \<mapsto> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>'))"
  let ?P' = "P'((p, m) \<mapsto> i + length xs)"
  let ?a = "progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j - length ts)"
  let ?b = "progress \<sigma> ?P' \<phi>' j"
  let ?lp = "letpast_progress \<sigma> P' (p, m) \<phi>' j"
  assume invar: "letpast_meval_invar n V \<sigma> P \<phi>' m j i ys xs p ts db \<phi> k"
    and eq: "(ys', \<phi>f) = meval j m ts (Mapping.update (p, m) xs db) \<phi>"
    and i': "i' = i + length xs"
    and buf': "case ys' of [] \<Rightarrow> buf' = None | Z # _ \<Rightarrow> buf' = Some Z \<and> Suc i' \<ge> j"
  from invar have le_a: "i + length xs \<le> ?a"
    and le_lp: "i + length xs \<le> letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts)"
    and xs: "list_all2 ?Q [i..<?a] xs" and ys: "list_all2 ?Q [k..<?a] ys" and k: "k \<le> ?a"
    unfolding letpast_meval_invar_def Let_def by simp_all
  from meval have wf: "wf_mformula \<sigma> j ?P' ?V m UNIV \<phi>f \<phi>'" and ys': "list_all2 ?Q [?a..<?b] ys'"
    by (simp_all add: eq[symmetric])
  have le_j: "i + length xs \<le> j - length ts"
    using le_lp letpast_progress_le[OF assms(2), of \<sigma> "(p, m)" \<phi>'] by linarith
  then have "?a \<le> ?b"
    using assms(2-4) by (intro progress_mono_gen) simp_all
  have a: "i + length xs = ?a"
    using le_a list_all2_lengthD[OF xs] by simp
  have "letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts) \<le> ?lp"
    using assms(2-4) by (intro letpast_progress_mono) simp_all
  with le_lp have le_lp': "i + length xs \<le> ?lp"
    by (rule order_trans)
  then have b_lp: "?b \<le> ?lp"
    using assms(3) by (intro le_letpast_progress_preservation) (simp_all add: rel_mapping_order_refl)
  have "(case buf' of None \<Rightarrow> i' = ?lp | Some Z \<Rightarrow> Suc i' = ?lp \<and> ?Q i' Z) \<and> ?b = ?lp"
  proof (cases ys')
    case Nil
    with list_all2_lengthD[OF ys'] have "?b \<le> ?a"
      by simp
    with \<open>?a \<le> ?b\<close> a have fp: "?b = i + length xs"
      by linarith
    have "?lp \<le> i + length xs"
      unfolding letpast_progress_def using fp le_j by (intro cInf_lower) simp_all
    with le_lp' fp Nil buf' i' show ?thesis
      by simp
  next
    case (Cons Z zs)
    with ys' a have "Suc (i + length xs) \<le> ?b" and Z: "?Q i' Z"
      by (simp_all add: list_all2_Cons2 upt_eq_Cons_conv i')
    with b_lp letpast_progress_le[OF assms(3), of \<sigma> "(p, m)" \<phi>'] Cons buf' i'
    have Suc_i': "Suc i' = ?lp"
      by simp
    with assms(1,3) have "progress \<sigma> (P'((p, m) \<mapsto> i')) \<phi>' j = ?lp"
      by (rule progress_Suc_letpast_progress_eq)
    with Suc_i' Z Cons buf' i' show ?thesis
      by simp
  qed
  with wf list_all2_upt_append[OF ys ys' k \<open>?a \<le> ?b\<close>] i'
  show "letpast_meval_post n V \<sigma> P' \<phi>' m j i' (ys @ ys') buf' p \<phi>f k"
    unfolding letpast_meval_post_def by simp
qed

lemma (in maux) letpast_meval_ys: "(ys', i', buf', \<phi>f) = letpast_meval m j i ys xs p ts db \<phi> \<Longrightarrow> \<exists> zs. ys' = ys@zs"
  \<comment> \<open>the same statement is already proved in theory Monitor\<close>
  by (fact letpast_meval_ys)

lemma fv_packagg_less:
  assumes valid: "valid_aggargs n (Formula.fv \<psi>) (args_agg args)"
    and fv_sub: "Formula.fv \<chi> \<subseteq> Formula.fv \<psi>"
    and args_n: "args_n args = n"
    and bound: "\<forall>x\<in>Formula.fv \<psi>. x < n"
  shows "\<forall>x\<in>Formula.fv (packagg args \<chi>). x < agg_n args"
proof (cases "args_agg args")
  case None
  with args_n have pk: "packagg args \<chi> = \<chi>" and an: "agg_n args = n"
    by (simp_all add: packagg_def agg_n_def)
  show ?thesis
    unfolding pk an using fv_sub bound by blast
next
  case (Some aggargs)
  let ?b = "length (aggargs_tys aggargs)"
  from Some valid have cols: "Formula.fv \<psi> = aggargs_cols aggargs" and safe: "safe_aggargs aggargs"
    by (simp_all add: valid_aggargs_def)
  from safe have y_less: "aggargs_y aggargs < aggargs_n aggargs"
    and cols_less: "\<forall>i\<in>aggargs_cols aggargs. i < ?b + aggargs_n aggargs"
    and f_cols: "Formula.fv_trm (aggargs_f aggargs) \<subseteq> aggargs_cols aggargs"
    by (simp_all add: safe_aggargs_def)
  have x_less: "x < aggargs_n aggargs" if x: "x \<in> Formula.fv (packagg args \<chi>)" for x
  proof -
    from Some x consider (chi) "x + ?b \<in> Formula.fv \<chi>"
      | (f) "x + ?b \<in> Formula.fv_trm (aggargs_f aggargs)" | (y) "x = aggargs_y aggargs"
      by (auto simp: packagg_def fvi_iff_fv[where b="length (aggargs_tys aggargs)"]
          fvi_trm_iff_fv_trm[where b="length (aggargs_tys aggargs)"])
    then show ?thesis
    proof cases
      case chi
      with fv_sub cols have "x + ?b \<in> aggargs_cols aggargs"
        by blast
      with cols_less have "x + ?b < ?b + aggargs_n aggargs"
        by (rule bspec)
      then show ?thesis
        by simp
    next
      case f
      with f_cols have "x + ?b \<in> aggargs_cols aggargs"
        by blast
      with cols_less have "x + ?b < ?b + aggargs_n aggargs"
        by (rule bspec)
      then show ?thesis
        by simp
    next
      case y
      with y_less show ?thesis
        by simp
    qed
  qed
  from Some have "agg_n args = aggargs_n aggargs"
    by (simp add: agg_n_def)
  with x_less show ?thesis
    by simp
qed

lemma (in maux) wf_mformula_wf_set: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_set n (Formula.fv \<phi>')"
  unfolding wf_set_def
proof (induction rule: wf_mformula.induct)
  case (AndRel P V n R \<phi> \<phi>' \<psi>' conf)
  then show ?case by (auto simp: fv_formula_of_constraint subset_eq)
next
  case (And_Release I \<phi>' \<psi>' P V n R aux \<alpha>')
  then show ?case using release_fvi(3) by auto
next
  case (Ands P V n R l l_pos l_neg l' buf A_pos A_neg)
  from Ands.IH have "\<forall>\<phi>'\<in>set (l_pos @ map remove_neg l_neg). \<forall>x\<in>fv \<phi>'. x < n"
    unfolding list_all2_iff
    by (metis (no_types, lifting) case_prodD in_set_impl_in_set_zip2)
  then have "\<forall>\<phi>'\<in>set (l_pos @ l_neg). \<forall>x\<in>fv \<phi>'. x < n"
    using fv_remove_neg
    by fastforce
  then show ?case using Ands by auto
next
  case (Agg P V tys n R \<phi> \<phi>' y f args \<omega>)
  then have "Formula.fvi_trm (length tys) f \<subseteq> Formula.fvi (length tys) \<phi>'"
    by (auto simp: fvi_trm_iff_fv_trm[where b="length (aggargs_tys args)"] 
        fvi_iff_fv[where b="length (aggargs_tys args)"])
  with Agg show ?case by (auto 0 3 simp: Un_absorb2 fvi_iff_fv[where b="length (aggargs_tys args)"])
next
  case (Release_0)
  then show ?case using release_fvi(1) by auto
next
  case (MatchP r P V n R \<phi>s mr mrs buf nts I aux)
  then obtain \<phi>s' where conv: "to_mregex r = (mr, \<phi>s')" by blast
  with MatchP have "\<forall>\<phi>'\<in>set \<phi>s'. \<forall>x\<in>fv \<phi>'. x < n"
    by (simp add: list_all2_conv_all_nth all_set_conv_all_nth[of \<phi>s'])
  with conv show ?case
    thm fv_regex_alt
    by (simp add: to_mregex_ok[THEN conjunct1] fv_regex_alt2[OF \<open>Regex.safe_regex _ _ _ _ r\<close>])
next
  case (MatchF r  P V n R \<phi>s mr mrs buf nts I aux)
  then obtain \<phi>s' where conv: "to_mregex r = (mr, \<phi>s')" by blast
  with MatchF have "\<forall>\<phi>'\<in>set \<phi>s'. \<forall>x\<in>fv \<phi>'. x < n"
    by (simp add: list_all2_conv_all_nth all_set_conv_all_nth[of \<phi>s'])
  with conv show ?case
    by (simp add: to_mregex_ok[THEN conjunct1] fv_regex_alt2[OF \<open>Regex.safe_regex _ _ _ _ r\<close>])
next
  case (Until P V n R \<phi> \<phi>' \<psi> \<psi>' args \<phi>'' I R' buf nts t aux)
  from \<open>wf_until_aux \<sigma> V R args \<phi>' \<psi>' aux (progress \<sigma> P (Formula.Until \<phi>'' I \<psi>') j)\<close>
    \<open>args_n args = n\<close>
  have valid: "valid_aggargs n (Formula.fv \<psi>') (args_agg args)"
    by (simp add: wf_until_aux_def)
  have "Formula.fv (Formula.Until \<phi>'' I \<psi>') \<subseteq> Formula.fv \<psi>'"
    using \<open>if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>'\<close>
      \<open>Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>'\<close>
    by (cases "args_pos args") auto
  from fv_packagg_less[OF valid this \<open>args_n args = n\<close> Until.IH(2)] show ?case .
next
  case (Since P V n R \<phi> \<phi>' \<psi> \<psi>' args \<phi>'' I R' buf aux)
  from \<open>wf_since_aux \<sigma> V R args \<phi>' \<psi>' aux (min (progress \<sigma> P \<phi>' j) (progress \<sigma> P \<psi>' j))
      (progress \<sigma> P (Formula.Since \<phi>'' I \<psi>') j)\<close> \<open>args_n args = n\<close>
  have valid: "valid_aggargs n (Formula.fv \<psi>') (args_agg args)"
    by (simp add: wf_since_aux_def)
  have "Formula.fv (Formula.Since \<phi>'' I \<psi>') \<subseteq> Formula.fv \<psi>'"
    using \<open>if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>'\<close>
      \<open>Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>'\<close>
    by (cases "args_pos args") auto
  from fv_packagg_less[OF valid this \<open>args_n args = n\<close> Since.IH(2)] show ?case .
qed (auto simp: fvi_Suc split: if_splits)

lemma (in maux) wf_mformula_release: "wf_mformula \<sigma> j P V n R \<phi> (release_safe_0 \<phi>' I \<psi>') 
  \<Longrightarrow> (case \<phi> of (MOr \<alpha> \<beta> buf) \<Rightarrow> True | _ \<Rightarrow> False)"
  by (cases rule: wf_mformula.cases) 
    (auto simp add: release_safe_0_def packagg_def split: if_splits option.splits)


subsection \<open> Correct initialisation \<close>

lemma (in maux) wf_minit0_op:
  assumes "safe_formula \<psi>" "fv \<phi> \<subseteq> fv \<psi>"
    "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>" "wf_mformula \<sigma> 0 P V n R (minit0 n \<psi>) \<psi>"
    "valid_aggargs n (fv \<psi>) (args_agg args)"
    "pred_mapping (\<lambda>x. x = 0) P"
    "mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')"
    "args = init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) (safe_formula \<phi>') agg"
    "safe_formula \<phi>' \<Longrightarrow> \<phi>' = \<phi>"
    "\<not>safe_formula \<phi>' \<Longrightarrow> \<phi>' = Formula.Neg \<phi> \<and> safe_formula \<phi>"
    "(op = formula.Since \<and> init = init_since) \<or> (op = formula.Until \<and> init = init_until)"
  shows "wf_mformula \<sigma> 0 P V (agg_n args) R' (init minit0 n agg \<phi>' I \<psi>) (packagg args (op \<phi>' I \<psi>))"
proof -
  have args_props: "args_n args = n" "args_pos args = safe_formula \<phi>'" "args_ivl args = I"
    "args_L args = fv \<phi>" "args_R args = fv \<psi>" "args_agg args = agg"
    by (auto simp: assms(8) init_args_def agg_n_def agg_tys_def packagg_def split: option.splits)
  have args_fold: "safe_formula \<phi>' \<Longrightarrow> init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True agg = args"
    "\<not>safe_formula \<phi>' \<Longrightarrow> init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False agg = args"
    using assms(8)
    by auto
  show ?thesis
    using assms(11)
  proof (rule disjE)
    assume "op = formula.Since \<and> init = init_since"
    then have unf: "op = formula.Since" "init = init_since" by auto
    show ?thesis 
    proof(cases "safe_formula \<phi>'")
      case True
      note \<phi>_eq = assms(9)[OF True]
      have wf_since: "wf_since_aux \<sigma> V R args \<phi> \<psi> (init_msaux args) (min (Progress.progress \<sigma> P \<phi> 0) (Progress.progress \<sigma> P \<psi> 0)) (Progress.progress \<sigma> P (formula.Since \<phi>' I \<psi>) 0)"
        using wf_since_aux_Nil[OF assms(2)[unfolded \<phi>_eq] assms(5), unfolded args_props(6), of _ _ _ I "safe_formula \<phi>'", folded assms(8), of \<sigma> V R]
        assms(6) by force
      show ?thesis unfolding unf init_since_def Let_def args_fold(1)[OF True, folded \<phi>_eq] 
        using wf_mformula.Since[OF assms(3, 4) _ True[unfolded \<phi>_eq] assms(1) args_props(3,1,4,5) assms(7,2) _ wf_since]
        using True args_props(2) assms(9) assms(6) by auto
    next
      case False
      have \<phi>_eq: "\<phi>' = Formula.Neg \<phi>" "safe_formula \<phi>" "fv \<phi>' = fv \<phi>"
        using assms(10)[OF False] by auto
      have wf_since: "wf_since_aux \<sigma> V R args \<phi> \<psi> (init_msaux args) (min (Progress.progress \<sigma> P \<phi> 0) (Progress.progress \<sigma> P \<psi> 0)) (Progress.progress \<sigma> P (formula.Since \<phi>' I \<psi>) 0)"
        using wf_since_aux_Nil[OF assms(2)[unfolded \<phi>_eq] assms(5), unfolded args_props(6), of _ _ _ I "safe_formula \<phi>'", folded assms(8), of \<sigma> V R]
        assms(6) by force
      show ?thesis unfolding unf init_since_def Let_def args_fold(2)[OF False, folded \<phi>_eq(3)] using \<phi>_eq(1-2) False
        wf_mformula.Since[OF assms(3, 4) _ \<phi>_eq(2) assms(1) args_props(3,1,4,5) assms(7,2) _ wf_since]
        by (simp add: args_props(2) assms(6))
    qed
next
    assume "op = formula.Until \<and> init = init_until"
    then have unf: "op = formula.Until" "init = init_until" by auto
    show ?thesis 
    proof(cases "safe_formula \<phi>'")
      case True
      note \<phi>_eq = assms(9)[OF True]
      have wf_until: "wf_until_aux \<sigma> V R args \<phi> \<psi> (init_muaux args) (Progress.progress \<sigma> P (formula.Until \<phi>' I \<psi>) 0)"
        using wf_until_aux_Nil[OF assms(2)[unfolded \<phi>_eq] assms(5), unfolded args_props(6), of _ _ _ I "safe_formula \<phi>'", folded assms(8), of \<sigma> V R]
        assms(6) by (metis progress_0_gen)
      show ?thesis unfolding unf init_until_def Let_def args_fold(1)[OF True, folded \<phi>_eq] 
        using wf_mformula.Until[OF assms(3, 4) _ True[unfolded \<phi>_eq] assms(1) args_props(3,1,4,5) assms(7,2) wf_mbuf2'_0[OF assms(6)] wf_ts_0 _ wf_until]
        unfolding valid_length_muaux[OF valid_init_muaux[OF assms(2)], of n agg I "safe_formula \<phi>'", folded assms(8), OF assms(5)[unfolded args_props(6)]] args_props(2)
        using True \<phi>_eq by (simp add: Inf_UNIV_nat assms(6))
    next
      case False
      have \<phi>_eq: "\<phi>' = Formula.Neg \<phi>" "safe_formula \<phi>" "fv \<phi>' = fv \<phi>"
        using assms(10)[OF False] by auto
      have wf_until: "wf_until_aux \<sigma> V R args \<phi> \<psi> (init_muaux args) (Progress.progress \<sigma> P (formula.Until \<phi>' I \<psi>) 0)"
        using wf_until_aux_Nil[OF assms(2)[unfolded \<phi>_eq] assms(5), unfolded args_props(6), of _ _ _ I "safe_formula \<phi>'", folded assms(8), of \<sigma> V R]
        assms(6) by (metis progress_0_gen)
      show ?thesis unfolding unf init_until_def Let_def args_fold(2)[OF False, folded \<phi>_eq(3)] 
        using wf_mformula.Until[OF assms(3, 4) _ \<phi>_eq(2) assms(1) args_props(3,1,4,5) assms(7,2) wf_mbuf2'_0[OF assms(6)] wf_ts_0 _ wf_until]
        unfolding valid_length_muaux[OF valid_init_muaux[OF assms(2)], of n agg I "safe_formula \<phi>'", folded assms(8), OF assms(5)[unfolded args_props(6)]] args_props(2)
        using False \<phi>_eq by (simp add: Inf_UNIV_nat assms(6))
    qed
  qed
qed

lemma (in maux) wf_minit0: "safe_formula \<phi> \<Longrightarrow> \<forall>x\<in>Formula.fv \<phi>. x < n \<Longrightarrow>
  pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow>
  wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
proof (induction arbitrary: n R P V rule: safe_formula_induct)
  case (Eq_Const c d)
  then have wf_props:
    "is_simple_eq (trm.Const c) (trm.Const d)"
    "\<forall>x\<in>fv_trm (trm.Const c). x < n"
    "\<forall>x\<in>fv_trm (trm.Const d). x < n"
    by (auto simp add: is_simple_eq_def simp del: eq_rel.simps)
  show ?case
    using wf_mformula.Eq[OF wf_props]
    by auto
next
  case (Eq_Var1 c x)
  then have wf_props:
    "is_simple_eq (trm.Const c) (trm.Var x)"
    "\<forall>x\<in>fv_trm (trm.Const c). x < n"
    "\<forall>x\<in>fv_trm (trm.Var x). x < n"
    by (auto simp add: is_simple_eq_def simp del: eq_rel.simps)
  show ?case
    using wf_mformula.Eq[OF wf_props]
    by auto
next
  case (Eq_Var2 c x)
  then have wf_props:
    "is_simple_eq (trm.Var x) (trm.Const c)"
    "\<forall>x\<in>fv_trm (trm.Var x). x < n"
    "\<forall>x\<in>fv_trm (trm.Const c). x < n"
    by (auto simp add: is_simple_eq_def simp del: eq_rel.simps)
  show ?case
    using wf_mformula.Eq[OF wf_props]
    by auto
next
  case (Pred e ts)
  then show ?case by (auto intro!: wf_mformula.Pred)
next
  case (Let p \<phi> \<psi>)
  with fvi_less_nfv show ?case
    by (auto simp: pred_mapping_alt dom_def intro!: wf_mformula.Let Let(4,5))
next
  case (Frz p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  have wf_\<psi>0: "\<forall>f. wf_mformula \<sigma> 0 (P(?pn \<mapsto> 0)) (V(?pn \<mapsto> f)) n R (minit0 n \<psi>) \<psi>"
  proof (intro allI Frz.IH(2))
    show "\<forall>x\<in>fv \<psi>. x < n"
      using Frz by auto
    show "pred_mapping (\<lambda>x. x = 0) (P(?pn \<mapsto> 0))"
      using Frz.prems by (auto simp: pred_mapping_alt)
  qed
  have wf_state: "wf_frz_state \<sigma> 0 P V p (Formula.nfv \<phi>) \<phi> \<psi> 0 []"
  proof -
    have "progress \<sigma> P (Formula.Frz p \<phi> \<psi>) 0 = 0"
      using Frz.prems progress_0_gen by blast
    moreover have "progress \<sigma> P \<phi> 0 = 0"
      using Frz.prems by simp
    ultimately show ?thesis
      by simp
  qed
  have pm: "pred_mapping (\<lambda>x. x = 0) (P(?pn \<mapsto> 0))"
    using Frz.prems by (auto simp: pred_mapping_alt)
  have wf_\<phi>: "wf_mformula \<sigma> 0 P V (Formula.nfv \<phi>) UNIV (minit0 (Formula.nfv \<phi>) \<phi>) \<phi>"
    by (rule Frz.IH(1)[OF fvi_less_nfv Frz.prems(2)])
  have wf_\<psi>: "\<forall>i. wf_mformula \<sigma> 0 (P(?pn \<mapsto> 0)) (V(?pn \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w i \<phi>)) n R
      (minit0 n \<psi>) \<psi>"
    using wf_\<psi>0 by blast
  have minit0_eq: "minit0 n (Formula.Frz p \<phi> \<psi>) =
      MFrz p (Formula.nfv \<phi>) (minit0 (Formula.nfv \<phi>) \<phi>) (minit0 n \<psi>) 0 0 0 []
        (minit0 n \<psi>) 0 0 [] [] (past_reach \<psi>) (safe_letpast (p, Formula.nfv \<phi>) \<psi> \<le> NonFutuRec)
        (neg_pred (p, Formula.nfv \<phi>) \<psi>) None (minit0 n \<psi>)"
    by simp
  show ?case
    unfolding minit0_eq
  proof (rule wf_mformula.Frz[OF wf_\<phi> wf_\<psi> wf_state _ _ _ _ Frz.hyps(1) refl Frz.hyps(2,3)])
    show "0 = progress \<sigma> P (Formula.Frz p \<phi> \<psi>) 0"
      by (rule progress_0_gen[OF Frz.prems(2), symmetric])
    show "0 = progress \<sigma> (P(?pn \<mapsto> 0)) \<psi> 0"
      by (rule progress_0_gen[OF pm, symmetric])
    show "\<forall>M. wf_mformula \<sigma> 0 (P(?pn \<mapsto> 0))
      (V(?pn \<mapsto> frz_val \<sigma> V \<phi> (\<lambda>k. if k < 0 then Map.empty k else M k))) n R (minit0 n \<psi>) \<psi>"
      using wf_\<psi>0 by blast
    show "wf_frz_win \<sigma> 0 P V n R p (Formula.nfv \<phi>) \<phi> \<psi> 0 0 0 [] [] (past_reach \<psi>)"
      using progress_0_gen[OF pm, of \<sigma> \<psi>] by (simp add: wf_frz_win_def)
  qed simp_all
next
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (auto simp: pred_mapping_alt dom_def letpast_progress0 fvi_less_nfv
        intro!: wf_mformula.LetPast)
next
  case (And_assign \<phi> \<psi>)
  then have 1: "\<forall>x\<in>fv \<psi>. x < n" by simp
  from 1 \<open>safe_assignment (fv \<phi>) \<psi>\<close>
  obtain x t where
    "x < n" "x \<notin> fv \<phi>" "fv_trm t \<subseteq> fv \<phi>"
    "\<psi> = Formula.Eq (Formula.Var x) t \<or> \<psi> = Formula.Eq t (Formula.Var x)"
    unfolding safe_assignment_def by (force split: formula.splits trm.splits)
  with And_assign show ?case
    by (auto intro!: wf_mformula.AndAssign split: trm.splits)
next
  case (And_safe \<phi> \<psi>)
  then show ?case by (auto intro!: wf_mformula.And wf_mbuf2'_0)
next
  case (And_constraint \<phi> \<psi>)
  from \<open>fv \<psi> \<subseteq> fv \<phi>\<close> \<open>is_constraint \<psi>\<close>
  obtain t1 p c t2 where
    "(t1, p, c, t2) = split_constraint \<psi>"
    "formula_of_constraint (split_constraint \<psi>) = \<psi>"
    "fv_trm t1 \<union> fv_trm t2 \<subseteq> fv \<phi>"
    by (induction rule: is_constraint.induct) auto
  with And_constraint show ?case
    by (auto 0 3 intro!: wf_mformula.AndRel)
next
  case (And_Not \<phi> \<psi>)
  then show ?case by (auto intro!: wf_mformula.And wf_mbuf2'_0)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  have wf_\<phi>: "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
    using And_Trigger(5,8,9)
    by auto
  define t where "t = formula.Trigger \<phi>' I \<psi>'"
  define f where "f = formula.And \<phi> t"
  define args where "args = init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') True None"
  define aux where "aux = (init_mtaux args)"

 have t_not_safe_assign: "\<not> safe_assignment (fv \<phi>) t"
  unfolding safe_assignment_def
  by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  have wf_\<phi>': "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>') \<phi>'"
    using And_Trigger(6,8,9)
    by auto
  have wf_\<psi>': "wf_mformula \<sigma> 0 P V n R (minit0 n \<psi>') \<psi>'"
    using And_Trigger(7,8,9)
    by auto
  have if_pos: "if args_pos args then \<phi>' = \<phi>' else \<phi>' = formula.Neg \<phi>'"
    unfolding args_def init_args_def
    by auto
  have args: "safe_formula \<phi>' = args_pos args"
    "args_ivl args = I"
    "args_n args = n"
    "args_L args = fv \<phi>'"
    "args_R args = fv \<psi>'"
    "\<forall>x\<in>fv \<psi>'. x < n"
    "if mem I 0 then fv \<phi>' \<subseteq> fv \<psi>' else fv \<phi>' = fv \<psi>'"
    using And_Trigger(2,3,8)
    unfolding args_def init_args_def safe_dual_def
    by auto
  hence fv_union: "fv \<phi>' \<union> fv \<psi>' = fv \<psi>'"
    by (auto split: if_splits)

  have buf_ts:
    "wf_mbuf2' \<sigma> P V 0 n R \<phi>' \<psi>' ([], [])"
    "wf_ts \<sigma> P 0 \<phi>' \<psi>' []"
    unfolding wf_mbuf2'_def wf_mbuf2_def wf_ts_def
    by (auto simp add: And_Trigger(9))

  have aux: "wf_trigger_aux \<sigma> V R args \<phi>' \<psi>' aux (Progress.progress \<sigma> P (formula.Trigger \<phi>' I \<psi>') 0)"
    using And_Trigger(3) valid_init_mtaux[of I "fv \<phi>'" "fv \<psi>'" True n]
    unfolding safe_dual_def wf_trigger_aux_def aux_def args_def
    by (auto simp add: Let_def And_Trigger(9) split: if_splits)

  have if_pos: "if args_pos args then \<phi>' = \<phi>' else \<phi>' = formula.Neg \<phi>'"
    unfolding args_def init_args_def
    by auto
  have wf_buf:
    "wf_mbuf2' \<sigma> P V 0 n R \<phi> t ([], [])"
    "wf_mbuft2' \<sigma> P V 0 n R \<phi> \<phi>' I \<psi>' ([], [])"
    "wf_mbuf2' \<sigma> P V 0 n R \<phi>' \<psi>' ([],[])"
    "wf_ts \<sigma> P 0  \<phi>' \<psi>' []"
    unfolding wf_mbuf2'_def wf_mbuft2'_def wf_mbuf2_def wf_mbuf2_def wf_ts_def
    by (auto simp add: And_Trigger(9))

  show ?case
  proof (cases "safe_formula t")
    case True
    then have mem: "mem I 0"
      unfolding t_def
      by (auto simp add: safe_dual_def split: if_splits)

    have wf_t: "wf_mformula \<sigma> 0 P V n R (minit0 n t) t"
      using And_Trigger(2) 
        wf_mformula.Trigger_0[OF wf_\<psi>' if_pos wf_\<phi>' args(1-6) mem args(7) buf_ts aux]
      unfolding t_def aux_def args_def
      by (auto simp: init_trigger_def split: if_splits)
    show ?thesis 
      using wf_mformula.And[OF wf_\<phi> wf_t _ wf_buf(1) And_Trigger(1) True]
      using True And_Trigger(2) t_not_safe_assign t_not_constraint fv_union
      unfolding f_def t_def args_def aux_def
      by (auto simp: init_trigger_def split: if_splits)
  next
    case False
    then show ?thesis 
      using wf_mformula.And_Trigger[OF wf_\<phi> wf_buf(2)[unfolded t_def] And_Trigger(4) 
          wf_\<psi>' if_pos wf_\<phi>' args wf_buf(3-4) aux]
      using And_Trigger(2) t_not_safe_assign t_not_constraint
      unfolding f_def t_def args_def aux_def
      by (auto simp: init_trigger_def init_and_trigger_def split: if_splits)
  qed
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  note fvs = release_fvi(3)[of 0 \<phi> \<phi>' I \<psi>']
  have safe_release_bdd: "safe_formula (release_safe_bounded \<phi>' I \<psi>')"
    using And_Release(1-7) 
    by (auto simp: safe_release_bdd_iff)
  have "fv \<psi>' \<subseteq> fv \<phi>"
    using And_Release(7) by auto
  have fv_eq: "fv (formula.And \<phi> (formula.Release \<phi>' I \<psi>')) = fv \<phi>"
    using And_Release(7)
    by auto
  then have release_subformulas:
    "\<forall>x\<in>fv \<phi>'. x < n"
    "\<forall>x\<in>fv \<psi>'. x < n"
    using And_Release(7) And_Release.prems(1)
    unfolding fvi.simps
    by auto
  have wf_formula:
    "wf_mformula \<sigma> 0 P V n R (minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>')) 
      (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
    "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
    "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>') \<phi>'"
    "wf_mformula \<sigma> 0 P V n R (minit0 n \<psi>') \<psi>'"
    using And_Release.IH(1)[OF And_Release.prems(1)[unfolded fvs]]
          And_Release.IH(2)[OF And_Release.prems(1)[unfolded fv_eq]]
          And_Release.IH(3)[OF release_subformulas(1)]
          And_Release.IH(4)[OF release_subformulas(2)]
      And_Release.prems(2)
    by auto
  let ?L = "MAnd (fv \<phi>) (minit0 n \<phi>) True {} (MNeg (minit0 n (Formula.eventually I Formula.TT))) ([], [])"
  let ?R = "MAnd (fv \<phi>) (minit0 n \<phi>) True (fv \<phi>' \<union> fv \<psi>') (minit0 n (release_safe_bounded \<phi>' I \<psi>')) ([], [])"
  have minit0_eq: "minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>') = MOr ?L ?R ([], [])"
    using safe_release_bdd And_Release(1-7)
    by (auto simp: eventually_def release_safe_bounded_def always_safe_bounded_def
        safe_assignment_iff and_release_safe_bounded_def)
  have buf: "wf_mbuf2' \<sigma> P V 0 n R (formula.And \<phi> (formula.Neg (Formula.eventually I Formula.TT)))
      (formula.And \<phi> (release_safe_bounded \<phi>' I \<psi>')) ([], [])"
    using And_Release.prems(2) by (simp add: wf_mbuf2'_def wf_mbuf2_def)
  note obs = buf wf_formula(1)[unfolded minit0_eq] minit0_eq
  have "\<not> safe_assignment (fv \<phi>) (formula.Release \<phi>' I \<psi>')"
    unfolding safe_assignment_def
    by auto
  moreover have "\<not> safe_formula (formula.Release \<phi>' I \<psi>')"
    using And_Release(6)
    by auto
  moreover have "\<not> is_constraint (formula.Release \<phi>' I \<psi>')"
    by auto
  ultimately have "minit0 n (formula.And \<phi> (formula.Release \<phi>' I \<psi>'))
    = minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>') "
    by auto
  then show ?case 
    using wf_mformula.And_Release[OF And_Release(6,5,4) \<open>fv \<psi>' \<subseteq> fv \<phi>\<close> 
        And_Release(1) safe_release_bdd obs(1,2)]
    by (clarsimp simp: obs)
next
  case (Ands l pos neg)
  note posneg = "Ands.hyps"(1)
  let ?wf_minit = "\<lambda>x. wf_mformula \<sigma> 0 P V n R (minit0 n x)"
  let ?pos = "filter safe_formula l"
  let ?neg = "filter (Not \<circ> safe_formula) l"
  have "list_all2 ?wf_minit ?pos pos"
    using Ands.IH(1) Ands.prems posneg by (auto simp: list_all_iff intro!: list.rel_refl_strong)
  moreover have "list_all2 ?wf_minit (map remove_neg ?neg) (map remove_neg neg)"
    using Ands.IH(2) Ands.prems posneg by (auto simp: list.rel_map list_all_iff intro!: list.rel_refl_strong)
  moreover have "list_all3 (\<lambda>_ _ _. True) (?pos @ map remove_neg ?neg) (?pos @ map remove_neg ?neg) l"
    by (auto simp: list_all3_conv_all_nth comp_def sum_length_filter_compl)
  moreover have "l \<noteq> [] \<Longrightarrow> (MIN \<phi>\<in>set l. (0 :: nat)) = 0"
    by (cases l) (auto simp: Min_eq_iff)
  ultimately show ?case using Ands.hyps Ands.prems(2)
    by (auto simp: wf_mbufn_def list_all3_map list.rel_map map_replicate_const[symmetric] subset_eq
        map_map[symmetric] map_append[symmetric] simp del: map_map map_append
        intro!: wf_mformula.Ands list_all2_appendI)
next
  case (Neg \<phi>)
  then show ?case 
    by (auto intro!: wf_mformula.Neg)
next
  case (Or \<phi> \<psi>)
  then show ?case 
    by (auto intro!: wf_mformula.Or wf_mbuf2'_0)
next
  case (Exists \<phi>)
  then show ?case 
    by (auto simp: fvi_Suc_bound intro!: wf_mformula.Exists[unfolded fvi.simps])
next
  case (Agg y \<omega> tys f \<phi>)
  define default where "default = MAgg (init_aggargs (fv \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f) (minit0 (length tys + n) \<phi>)"
  have fv_le: "\<forall>x\<in>fv \<phi>. x < length tys + n"
    using Agg
    by (auto intro!: fvi_plus_bound)
  have wf_default: "wf_mformula \<sigma> 0 P V n R default (formula.Agg y \<omega> tys f \<phi>)"
    using Agg
    by (auto simp: default_def init_aggargs_def intro!: wf_mformula.Agg Agg.IH fvi_plus_bound)
  {
    fix y0 \<phi>' I \<psi>' 
      and op :: "ty Formula.formula \<Rightarrow> \<I> \<Rightarrow> ty Formula.formula \<Rightarrow> ty Formula.formula"
      and init :: "(nat \<Rightarrow> ty Formula.formula \<Rightarrow> ('msaux, 'muaux, 'mtaux) mformula) 
        \<Rightarrow> nat \<Rightarrow> aggargs option \<Rightarrow> ty Formula.formula \<Rightarrow> \<I> \<Rightarrow> ty Formula.formula 
        \<Rightarrow> ('msaux, 'muaux, 'mtaux) mformula"
    assume op_def: "(op = formula.Since \<and> init = init_since) 
      \<or> (op = formula.Until \<and> init = init_until)"
    assume agg_def: "\<phi> = op \<phi>' I \<psi>'"
    define \<phi>'' where "\<phi>'' = (if safe_formula \<phi>' then \<phi>' else remove_neg \<phi>')"
    define aggargs where "aggargs = Some (init_aggargs (fv \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f)"
    define args where "args = init_args I (length tys + n) (fv \<phi>') (fv \<psi>') (safe_formula \<phi>') aggargs"
    have "wf_mformula \<sigma> 0 P V (agg_n args) R (init minit0 (length tys + n) aggargs \<phi>' I \<psi>') (packagg args (op \<phi>' I \<psi>'))"
    proof (rule wf_minit0_op[where op=op])
      have Neg_case: "\<not> safe_formula \<phi>' 
        \<Longrightarrow> \<phi>' = formula.Neg (remove_neg \<phi>') \<and> safe_formula (remove_neg \<phi>') 
          \<and> size' (remove_neg \<phi>') \<le> size' \<phi>"
      proof -
        assume unsafe: "\<not> safe_formula \<phi>'"
        from Agg.hyps(4) op_def unsafe have "case \<phi>' of formula.Neg \<phi>0 \<Rightarrow> safe_formula \<phi>0 | _ \<Rightarrow> False"
          unfolding agg_def by auto
        then obtain \<phi>0 where \<phi>0: "\<phi>' = formula.Neg \<phi>0" "safe_formula \<phi>0"
          by (cases \<phi>') simp_all
        from op_def \<phi>0(2) show ?thesis
          unfolding agg_def \<phi>0(1) by auto
      qed
      show safe_\<psi>': "safe_formula \<psi>'"
        using Agg.hyps op_def by (auto simp: agg_def)
      show "fv \<phi>'' \<subseteq> fv \<psi>'"
        using Agg.hyps op_def by (auto simp: agg_def \<phi>''_def)
      show "wf_mformula \<sigma> 0 P V (length tys + n) (lift_envs' (length tys) R) (minit0 (length tys + n) \<phi>'') \<phi>''"
      proof (cases "safe_formula \<phi>'")
        case True
        then show ?thesis
          using Agg.prems op_def fv_le
          by (auto simp: agg_def \<phi>''_def intro!: Agg.IH)
      next
        case False
        then show ?thesis
          using Agg.prems op_def fv_le Neg_case
          by (auto simp: agg_def \<phi>''_def intro!: Agg.IH)
      qed
      show "wf_mformula \<sigma> 0 P V (length tys + n) (lift_envs' (length tys) R) (minit0 (length tys + n) \<psi>') \<psi>'"
        using Agg.prems op_def fv_le safe_\<psi>'
        by (auto simp: agg_def intro!: Agg.IH)
      show "valid_aggargs (length tys + n) (fv \<psi>') (args_agg args)"
        using Agg op_def fv_le
        by (auto simp: valid_aggargs_def args_def init_args_def aggargs_def init_aggargs_def
            safe_aggargs_def agg_def)
      show "mem_restr (lift_envs' (length tys) R) = mem_restr (lift_envs' (length (agg_tys args)) R)"
        by (simp add: args_def init_args_def agg_tys_def aggargs_def init_aggargs_def)
      show "args = init_args I (length tys + n) (fv \<phi>'') (fv \<psi>') (safe_formula \<phi>') aggargs"
        by (simp add: args_def \<phi>''_def)
      show "\<not> safe_formula \<phi>' \<Longrightarrow> \<phi>' = formula.Neg \<phi>'' \<and> safe_formula \<phi>''"
        using Neg_case by (auto simp: \<phi>''_def)
    qed (simp_all add: Agg.prems \<phi>''_def op_def)
    then have "wf_mformula \<sigma> 0 P V n R (init minit0 (length tys + n) aggargs \<phi>' I \<psi>') (formula.Agg y \<omega> tys f (op \<phi>' I \<psi>'))"
      by (simp add: args_def init_args_def aggargs_def init_aggargs_def agg_n_def packagg_def)
  }
  then show ?case
    using wf_default
    by (fastforce simp: default_def[symmetric] split: formula.splits prod.splits agg_type.splits)
next
  case (Prev I \<phi>)
  then show ?case 
    by (auto intro!: wf_mformula.Prev)
next
  case (Next I \<phi>)
  then show ?case 
    by (auto intro!: wf_mformula.Next)
next
  case (Since \<phi> I \<psi>)
  then show ?case
    using wf_minit0_op[where \<phi>=\<phi> and \<phi>'=\<phi> and ?agg=None]
    by (auto simp: init_args_def agg_n_def agg_tys_def packagg_def valid_aggargs_def)
next
  case (Not_Since \<phi> I \<psi>)
  then show ?case
    using wf_minit0_op[where \<phi>=\<phi> and \<phi>'="Formula.Neg \<phi>" and ?agg=None]
    by (auto simp: init_args_def agg_n_def agg_tys_def packagg_def valid_aggargs_def)
next
  case (Until \<phi> I \<psi>)
  then show ?case
    using wf_minit0_op[where \<phi>=\<phi> and \<phi>'=\<phi> and ?agg=None]
    by (auto simp: init_args_def agg_n_def agg_tys_def packagg_def valid_aggargs_def)
next
  case (Not_Until \<phi> I \<psi>)
  then show ?case
    using wf_minit0_op[where \<phi>=\<phi> and \<phi>'="Formula.Neg \<phi>" and ?agg=None]
    by (auto simp: init_args_def agg_n_def agg_tys_def packagg_def valid_aggargs_def)
next
  case (Trigger_0 \<phi> I \<psi>)
  have wf_\<psi>: "wf_mformula \<sigma> 0 P V n R (minit0 n \<psi>) \<psi>"
    using Trigger_0
    by auto
  show ?case
  proof (cases "safe_formula \<phi> \<and> (\<forall>x. (\<forall>xa\<in>fv \<phi>. xa < x) \<longrightarrow> (\<forall>xa xaa. pred_mapping (\<lambda>x. x = 0) xaa \<longrightarrow> (\<forall>xaaa. wf_mformula \<sigma> 0 xaa xaaa x xa (minit0 x \<phi>) \<phi>)))")
    define args where "args = init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None"
    define aux where "aux = init_mtaux args"
    case True
    then have wf_\<phi>: "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
      using Trigger_0
      by auto
    have if_pos: "if args_pos args then \<phi> = \<phi> else \<phi> = formula.Neg \<phi>"
      unfolding args_def init_args_def
      by auto
    have args:
      "safe_formula \<phi> = args_pos args"
      "args_ivl args = I"
      "args_n args = n"
      "args_L args = fv \<phi>"
      "args_R args = fv \<psi>"
      "\<forall>x\<in>fv \<psi>. x < n"
      "if mem I 0 then fv \<phi> \<subseteq> fv \<psi> else fv \<phi> = fv \<psi>"
      and mem: "mem I 0"
      using Trigger_0(1,3,6) True
      unfolding args_def init_args_def
      by auto
    have aux: "wf_trigger_aux \<sigma> V R args \<phi> \<psi> aux (Progress.progress \<sigma> P (formula.Trigger \<phi> I \<psi>) 0)"
      using Trigger_0(1,3) valid_init_mtaux[of I "fv \<phi>" "fv \<psi>" True n]
      unfolding safe_dual_def wf_trigger_aux_def aux_def args_def
      by (auto simp add: Let_def Trigger_0(7) split: if_splits)

    show ?thesis
      using True wf_mformula.Trigger_0[OF wf_\<psi> if_pos wf_\<phi> args(1-6) mem args(7) 
          wf_mbuf2'_0[OF Trigger_0(7)] wf_ts_0 aux ]
      unfolding aux_def args_def
      by (auto simp: init_trigger_def)
  next
    define args where "args = init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None"
    define aux where "aux = init_mtaux args"
    case False
    then obtain \<phi>' where \<phi>'_props: "\<phi> = Formula.Neg \<phi>'" "safe_formula \<phi>'"
      "(\<forall>x. (\<forall>xa\<in>fv \<phi>'. xa < x) 
        \<longrightarrow> (\<forall>xa xaa. pred_mapping (\<lambda>x. x = 0) xaa 
          \<longrightarrow> (\<forall>xaaa. wf_mformula \<sigma> 0 xaa xaaa x xa (minit0 x \<phi>') \<phi>')))"
      using Trigger_0(4)
      by (cases \<phi>) (auto)
    show ?thesis
    proof (cases "safe_formula \<phi>")
      case True
      then have "fv \<phi>' = {}"
        using \<phi>'_props(1,2)
        by auto
      moreover have "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>') \<phi>'"
        using Trigger_0(6,7) \<phi>'_props(1,3)
        by auto
      ultimately have wf_\<phi>: "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
        using \<phi>'_props(1) True
        by (auto intro!: wf_mformula.Neg)
      have if_pos: "if args_pos args then \<phi> = \<phi> else \<phi> = formula.Neg \<phi>"
        unfolding args_def init_args_def
        by auto
      have args:
        "safe_formula \<phi> = args_pos args"
        "args_ivl args = I"
        "args_n args = n"
        "args_L args = fv \<phi>"
        "args_R args = fv \<psi>"
        "\<forall>x\<in>fv \<psi>. x < n"
        "if mem I 0 then fv \<phi> \<subseteq> fv \<psi> else fv \<phi> = fv \<psi>"
        and mem: "mem I 0"
        using Trigger_0(1,3,6) True
        unfolding args_def init_args_def
        by auto
      have aux: "wf_trigger_aux \<sigma> V R args \<phi> \<psi> aux (Progress.progress \<sigma> P (formula.Trigger \<phi> I \<psi>) 0)"
        using Trigger_0(1,3) valid_init_mtaux[of I "fv \<phi>" "fv \<psi>" True n]
        unfolding safe_dual_def wf_trigger_aux_def aux_def args_def
        by (auto simp add: Let_def Trigger_0(7) split: if_splits)
  
      show ?thesis
        using True wf_mformula.Trigger_0[OF wf_\<psi> if_pos wf_\<phi> args(1-6) mem args(7) 
            wf_mbuf2'_0[OF Trigger_0(7)] wf_ts_0 aux]
        unfolding aux_def args_def
        by (auto simp: init_trigger_def)
    next
      define args where "args = init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>) False None"
      define aux where "aux = init_mtaux args"
      case False
      have wf_\<phi>': "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>') \<phi>'"
        using \<phi>'_props Trigger_0
        by auto
      have if_pos: "if args_pos args then \<phi> = \<phi>' else \<phi> = formula.Neg \<phi>'"
        unfolding \<phi>'_props(1) args_def init_args_def
        by auto
      have args:
        "safe_formula \<phi> = args_pos args"
        "args_ivl args = I"
        "args_n args = n"
        "args_L args = fv \<phi>'"
        "args_R args = fv \<psi>"
        "\<forall>x\<in>fv \<psi>. x < n"
        "if mem I 0 then fv \<phi>' \<subseteq> fv \<psi> else fv \<phi>' = fv \<psi>"
        and mem: "mem I 0"
        using \<phi>'_props(1) Trigger_0(1,3,6) False
        unfolding args_def init_args_def
        by auto
      have aux: "wf_trigger_aux \<sigma> V R args \<phi>' \<psi> aux (Progress.progress \<sigma> P (formula.Trigger \<phi> I \<psi>) 0)"
        using Trigger_0(1,3) valid_init_mtaux[of I "fv \<phi>'" "fv \<psi>" False n] \<phi>'_props(1)
        unfolding safe_dual_def wf_trigger_aux_def aux_def args_def
        by (auto simp add: Let_def Trigger_0(7) split: if_splits)
  
      show ?thesis
        using False \<phi>'_props(1) wf_mformula.Trigger_0[OF wf_\<psi> if_pos wf_\<phi>' args(1-6) mem args(7) 
            wf_mbuf2'_0[OF Trigger_0(7)] wf_ts_0 aux]
        unfolding aux_def args_def
        by (auto simp: init_trigger_def)
    qed
  qed
next
  case (Trigger \<phi> I \<psi>)
  then show ?case by auto
next
  case (Release_0 \<phi> I \<psi>)
  hence "safe_formula \<psi>"
    by auto
  moreover have "wf_mformula \<sigma> 0 P V n R (minit0 n (release_safe_0 \<phi> I \<psi>)) (release_safe_0 \<phi> I \<psi>)"
    using Release_0.IH[OF Release_0.prems[unfolded release_fvi(1)]]
    by auto
  moreover with this have "safe_formula (release_safe_0 \<phi> I \<psi>)"
    unfolding release_safe_0_def
    by (cases rule: wf_mformula.cases)
      (auto simp: packagg_def split: option.splits)
  moreover have "wf_mbuf2' \<sigma> P V 0 n R (formula.Until \<psi> I (formula.And \<psi> \<phi>)) (always_safe_0 I \<psi>) ([],[])"
    by (auto simp: wf_mbuf2'_def wf_mbuf2_def)
  ultimately show ?case
    using minit0_release_0[OF Release_0(1)] wf_mformula.Release_0[OF Release_0(1-2,4)]
    by (auto simp: release_safe_0_def)
next
  case (Release \<phi> I \<psi>)
  then show ?case 
    by auto
next
  case (MatchP I r)
  then show ?case
    by (auto simp: list.rel_map fv_regex_alt2 simp del: progress_simps split: prod.split
        intro!: wf_mformula.MatchP list.rel_refl_strong wf_mbufn'_0 wf_ts_regex_0 wf_matchP_aux_Nil
        dest!: to_mregex_safe_atms)
next
  case (MatchF I r)
  then show ?case
    by (auto simp: list.rel_map fv_regex_alt2 progress_le Min_eq_iff progress_regex_def
        simp del: progress_simps split: prod.split
        intro!: wf_mformula.MatchF list.rel_refl_strong wf_mbufn'_0 wf_ts_regex_0 wf_matchF_aux_Nil
        dest!: to_mregex_safe_atms)
next
  case (TP t)
  then show ?case 
    by (auto intro!: wf_mformula.MTP)
next
  case (TS t)
  then show ?case 
    by (auto intro!: wf_mformula.MTS)
qed

lemma (in maux) wf_mstate_minit: 
  "safe_formula \<phi> \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> wf_mstate S E \<phi> pnil R (minit \<phi>)"
  unfolding wf_mstate_def minit_def Let_def
  by (auto simp add: pts.rep_eq pnil.rep_eq intro!: wf_minit0 fvi_less_nfv wty_pnil)


subsection \<open> Main correctness result \<close>

lemma (in maux) letpast_meval_invar_post:
  assumes "safe_letpast (p, m) \<phi>' \<le> PastRec"
  assumes "pred_mapping (\<lambda> x. x\<le>(j-length ts)) P"
  assumes "pred_mapping (\<lambda> x. x\<le>j) P'"
  assumes "rel_mapping (\<le>) P P'"
  assumes "m = Formula.nfv \<phi>'" and "{0..<m} \<subseteq> fv \<phi>'"
  assumes "wf_mformula \<sigma> (j-length ts) (P((p,m)\<mapsto>i)) (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>'))) m UNIV \<phi> \<phi>'"
  assumes "wf_envs S \<sigma> (j-length ts) (length ts) P P' V db"
  assumes "\<And> xs db \<phi>_m us P P' V S E. size \<phi>_m = size \<phi> \<Longrightarrow> wf_mformula \<sigma> (j-length us) P V m UNIV \<phi>_m \<phi>' \<Longrightarrow>
    wf_envs S \<sigma> (j-length us) (length us) P P' V (Mapping.update (p, m) xs db) \<Longrightarrow>
    S, E \<turnstile> \<phi>' \<Longrightarrow>
    us=[]\<or>us = ts \<Longrightarrow>
    case meval j m us (Mapping.update (p, m) xs db) \<phi>_m of (xs', \<phi>\<^sub>n) \<Rightarrow>
    wf_mformula \<sigma> j P' V m UNIV \<phi>\<^sub>n \<phi>' \<and>
    list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'))
    [progress \<sigma> P \<phi>' (j-length us)..<progress \<sigma> P' \<phi>' j] xs'"
  assumes "length ts \<le> j"
  assumes "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>')), E' \<turnstile> \<phi>'"
  assumes "safe_formula \<phi>'"
  shows "letpast_meval_invar n V \<sigma> P \<phi>' m j i ys xs p ts db \<phi> k\<Longrightarrow>
  (ys', i', buf', \<phi>f) = letpast_meval m j i ys xs (p, m) ts db \<phi> \<Longrightarrow>
  letpast_meval_post n V \<sigma> P' \<phi>' m j i' ys' buf' p \<phi>f k"
  using assms
proof (induction i ys xs "(p, m)" ts db \<phi> arbitrary: p i' buf' ys' \<phi>f P P' taking: m j rule: letpast_meval_induct)
  case (step i ys xs ts db \<phi>)
  note invar = step.prems(1)
  note eq = step.prems(2)
  note safe = step.prems(3)
  note PP' = step.prems(4-6)
  note fv = step.prems(7-8)
  note mformula = step.prems(9)
  note envs = step.prems(10)
  note meval = step.prems(11)
  note wty = step.prems(13)
  note safe_formula = step.prems(14)
  define ysp where "ysp = meval j m ts (Mapping.update (p, m) xs db) \<phi>"
  let ?P = "P((p, m) \<mapsto> i)"
  let ?V = "V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>'))"
  let ?S = "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>'))"
  have i'_j: "i + length xs \<le> j - length ts"
  proof -
    from invar have "i + length xs \<le> letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts)"
      unfolding letpast_meval_invar_def Let_def by simp
    also have "\<dots> \<le> j - length ts"
      using PP'(1) by (rule letpast_progress_le)
    finally show ?thesis .
  qed
  have "list_all2
     (\<lambda>i. qtable m (fv \<phi>') (mem_restr UNIV)
           (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i))
     [i..<Progress.progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j - length ts)] xs" (is "list_all2 ?Q _ _")
    using invar unfolding letpast_meval_invar_def Let_def by simp
  then have xs: "list_all2 ?Q [i..<i + length xs] xs"
    by (smt (verit, del_insts) add_diff_cancel_left' eq_diff_iff length_upt list_all2_lengthD nat_le_linear upt_conv_Nil)
  \<comment> \<open>results of @{term meval} can be stated in terms of @{term letpast_sat}\<close>
  have sat_letpast: "Formula.sat \<sigma> ?V w k \<phi>' =
    letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>') w k" for w k
    by (subst letpast_sat.simps) (rule V_subst_letpast[OF safe], simp)

  show ?case
  proof (cases "fst ysp = [] \<or> j \<le> Suc (i + length xs)")
    case stop: True
    then have eqs: "i' = i + length xs" "ys' = ys @ fst ysp" "\<phi>f = snd ysp"
      "buf' = (case fst ysp of [] \<Rightarrow> None | Z # _ \<Rightarrow> Some Z)"
      using eq by (simp_all add: letpast_meval_code split_beta flip: ysp_def split: list.splits)
    let ?P' = "P'((p, m) \<mapsto> i')"
    have "case ysp of (ys, \<phi>\<^sub>n) \<Rightarrow> wf_mformula \<sigma> j ?P' ?V m UNIV \<phi>\<^sub>n \<phi>' \<and>
      list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. Formula.sat \<sigma> ?V (map the v) i \<phi>'))
      [progress \<sigma> ?P \<phi>' (j-length ts)..<progress \<sigma> ?P' \<phi>' j] ys"
    proof (rule meval[of \<phi> ts ?P ?V ?S ?P' xs db, folded ysp_def])
      show "wf_mformula \<sigma> (j - length ts) ?P ?V m UNIV \<phi> \<phi>'" by fact
      show "wf_envs ?S \<sigma> (j - length ts) (length ts) ?P ?P' ?V (Mapping.update (p, m) xs db)"
        unfolding eqs by (intro wf_envs_update2) (fact | use i'_j in simp)+
      show " S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>')), E' \<turnstile> \<phi>'" using wty by auto
    qed simp_all
    then have ysp: "case ysp of (ys, \<phi>\<^sub>n) \<Rightarrow> wf_mformula \<sigma> j ?P' ?V m UNIV \<phi>\<^sub>n \<phi>' \<and>
      list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>') (map the v) i))
      [progress \<sigma> ?P \<phi>' (j-length ts)..<progress \<sigma> ?P' \<phi>' j] ys"
      unfolding sat_letpast .
    show ?thesis
      unfolding eqs
    proof (rule invar_recursion_post[OF safe PP' ysp[unfolded ysp_def eqs] invar])
      show "(fst ysp, snd ysp) = meval j m ts (Mapping.update (p, m) xs db) \<phi>"
        by (simp add: ysp_def)
      show "case fst ysp of [] \<Rightarrow> (case fst ysp of [] \<Rightarrow> None | Z # _ \<Rightarrow> Some Z) = None
        | Z # _ \<Rightarrow> (case fst ysp of [] \<Rightarrow> None | Z # _ \<Rightarrow> Some Z) = Some Z \<and> j \<le> Suc (i + length xs)"
        using stop by (cases "fst ysp") simp_all
    qed simp
  next
    case cont: False
    then have eqs: "(ys', i', buf', \<phi>f) =
      letpast_meval m j (i + length xs) (ys @ fst ysp)
       (fst ysp) (p, m) []
       (Mapping.map_values (\<lambda>_ _. []) db) (snd ysp)"
      using eq
      by (subst (asm) letpast_meval_code) (simp_all add: split_beta flip: ysp_def split: list.splits)
    let ?P' = "P'((p, m) \<mapsto> i + length xs)"
    have "case ysp of (ys, \<phi>\<^sub>n) \<Rightarrow> wf_mformula \<sigma> j ?P' ?V m UNIV \<phi>\<^sub>n \<phi>' \<and>
      list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. Formula.sat \<sigma> ?V (map the v) i \<phi>'))
      [progress \<sigma> ?P \<phi>' (j-length ts)..<progress \<sigma> ?P' \<phi>' j] ys"
    proof (rule meval[of \<phi> ts ?P ?V ?S ?P' xs db, folded ysp_def])
      show "wf_mformula \<sigma> (j - length ts) ?P ?V m UNIV \<phi> \<phi>'" by fact
      show "wf_envs ?S \<sigma> (j - length ts) (length ts) ?P ?P' ?V (Mapping.update (p, m) xs db)"
        by (intro wf_envs_update2) (fact | use i'_j in simp)+
      show "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>')), E' \<turnstile> \<phi>'" using wty by auto
    qed simp_all
    then have ysp: "case ysp of (ys, \<phi>\<^sub>n) \<Rightarrow> wf_mformula \<sigma> j ?P' ?V m UNIV \<phi>\<^sub>n \<phi>' \<and>
      list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>') (map the v) i))
      [progress \<sigma> ?P \<phi>' (j-length ts)..<progress \<sigma> ?P' \<phi>' j] ys"
      unfolding sat_letpast .
    have size_eq: "size (snd ysp) = size \<phi>"
      by (simp add: ysp_def size_snd_meval)
    show ?thesis
    proof (rule step.hyps[of "fst ysp" "snd ysp" P'], goal_cases)
      show "(fst ysp, snd ysp) = meval j m ts (Mapping.update (p, m) xs db) \<phi>"
        by (simp add: ysp_def)
      from cont show "fst ysp \<noteq> []" and "Suc (i + length xs) < j"
        by simp_all
      from cont show "letpast_meval_invar n V \<sigma> P' \<phi>' m j (i + length xs) (ys @ fst ysp) (fst ysp) p []
        (Mapping.map_values (\<lambda>_ _. []) db) (snd ysp) k"
        by (intro invar_recursion_invar[OF PP' ysp[unfolded ysp_def] invar]) (simp_all add: ysp_def)
      from ysp show "wf_mformula \<sigma> (j - length []) ?P' ?V m UNIV (snd ysp) \<phi>'"
        by (simp add: split_beta)
      from wf_envs_empty[OF envs] step.prems(12)
      show "wf_envs S \<sigma> (j - length []) (length []) P' P' V (Mapping.map_values (\<lambda>_ _. []) db)"
        by simp
    next
      case (14 \<phi>_m us)
      \<comment> \<open>the induction hypothesis may use the assumption on @{term meval} for the next iteration\<close>
      with size_eq show ?case
        by (intro meval) simp_all
    qed (use eqs safe PP'(2) fv wty safe_formula in \<open>simp_all add: rel_mapping_order_refl\<close>)
  qed
qed

lemma (in maux) wf_mformula_and_release_safe_bddE:
  "wf_mformula \<sigma> j P V n R \<phi>\<^sub>M (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>') 
  \<Longrightarrow> \<exists>\<phi>\<^sub>M' \<psi>\<^sub>M' buf1 buf2. \<phi>\<^sub>M = MOr \<phi>\<^sub>M' \<psi>\<^sub>M' (buf1, buf2)"
  by (erule wf_mformula.cases; clarsimp simp: and_release_safe_bounded_def
      packagg_def split: option.splits if_splits)

lemma (in maux) wf_mformula_and_release_safe0E:
  "wf_mformula \<sigma> j P V n R \<phi>\<^sub>M (release_safe_0 \<phi>' I \<psi>') 
  \<Longrightarrow> \<exists>\<phi>\<^sub>M' \<psi>\<^sub>M' buf1 buf2. \<phi>\<^sub>M = MOr \<phi>\<^sub>M' \<psi>\<^sub>M' (buf1, buf2)"
  by (erule wf_mformula.cases; clarsimp simp: release_safe_0_def
      packagg_def split: option.splits if_splits)

unbundle MFODL_notation

text \<open>Drop-based queue infrastructure (replaces old discharge_skip machinery).\<close>

lemma (in maux) wf_frz_queue_drop:
  assumes q: "wf_frz_queue \<sigma> V m \<phi> ks xs"
  shows "wf_frz_queue \<sigma> V m \<phi> (drop n ks) (drop n xs)"
  using assms by (auto simp: wf_frz_queue_def intro: list_all2_dropI)

lemma (in maux) wf_frz_queue_append:
  assumes q1: "wf_frz_queue \<sigma> V m \<phi> ks1 xs1"
    and q2: "wf_frz_queue \<sigma> V m \<phi> ks2 xs2"
  shows "wf_frz_queue \<sigma> V m \<phi> (ks1 @ ks2) (xs1 @ xs2)"
  using assms by (auto simp: wf_frz_queue_def intro: list_all2_appendI)

text \<open>After extending the queue with new phi results and dropping a prefix,
we obtain a queue over the appropriate interval.\<close>

lemma (in maux) wf_frz_queue_length:
  assumes wfq: "wf_frz_queue \<sigma> V m \<phi> [a..<b] xs"
  shows "length xs = b - a"
  using wfq by (auto simp: wf_frz_queue_def dest!: list_all2_lengthD)

lemma (in maux) wf_envs_update3:
  assumes wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db"
  and m_eq: "m = Formula.nfv \<phi>"
  and in_fv: "{0..<m} \<subseteq> FV \<phi>"
  and safe: "safe_formula \<phi>"
  and wty: "S, E \<turnstile> \<phi>"
  shows "wf_envs (S((p, m) \<mapsto> tabulate E 0 (Formula.nfv \<phi>))) \<sigma> j \<delta> (P((p, m) \<mapsto> 0)) (P'((p, m) \<mapsto> 0)) (V((p, m) \<mapsto> \<lambda>w j. \<langle>\<sigma>, V, w, i\<rangle> \<Turnstile> \<phi>)) (Mapping.update (p, m) [] db)"
  unfolding wf_envs_def
proof (intro conjI ballI, goal_cases)
  case 1
  with assms show ?case unfolding wf_envs_def by auto
next
  case 2
  with assms show ?case unfolding wf_envs_def by (auto simp: subset_iff)
next
  case 3
  with assms show ?case by auto
next
  case 4
  with assms show ?case by auto
next
  case 5
  with assms show ?case by auto
next
  case (6 q)
  with assms show ?case unfolding wf_envs_def by (cases "q \<in> dom P") auto
next
  case (7 q)
  with assms show ?case unfolding wf_envs_def by auto
next
  case 8
  from wf_envs have "wty_envs S \<sigma> V" unfolding wf_envs_def by simp
  then show ?case unfolding wty_envs_def
    using ty_of_sat_safe[OF safe wty] in_fv
    by (auto simp: wty_envs_def wty_event_def wty_tuple_def list_all2_conv_all_nth m_eq domIff)
qed

lemma (in maux) wf_envs_update4:
  assumes wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db"
  and m_eq: "m = Formula.nfv \<phi>"
  and in_fv: "{0..<m} \<subseteq> FV \<phi>"
  and \<alpha>: "qtable m (FV \<phi>) (mem_restr UNIV) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>) \<alpha>"
  and safe: "safe_formula \<phi>"
  and wty: "S, E \<turnstile> \<phi>"
  shows "wf_envs (S((p, m) \<mapsto> tabulate E 0 (Formula.nfv \<phi>))) \<sigma> j \<delta> (P((p, m) \<mapsto> 0)) (P'((p, m) \<mapsto> j)) (V((p, m) \<mapsto> \<lambda>w j. \<langle>\<sigma>, V, w, i\<rangle> \<Turnstile> \<phi>)) (Mapping.update (p, m) (replicate j \<alpha>) db)"
  unfolding wf_envs_def
proof (intro conjI ballI, goal_cases)
  case 1
  with assms show ?case unfolding wf_envs_def by auto
next
  case 2
  with assms show ?case unfolding wf_envs_def by (auto simp: subset_iff)
next
  case 3
  with assms show ?case by auto
next
  case 4
  with assms show ?case by auto
next
  case 5
  with assms show ?case by auto
next
  case (6 q)
  with assms show ?case unfolding wf_envs_def by (cases "q \<in> dom P") auto
next
  case (7 q)
  from \<alpha> in_fv have "\<alpha> = map Some ` {v. length v = m \<and> Formula.sat \<sigma> V v i \<phi>}"
  proof (intro set_eqI iffI)
    fix x
    assume "x \<in> \<alpha>"
    with \<alpha> have wf: "wf_tuple m (FV \<phi>) x" and sat: "\<langle>\<sigma>, V, x, i\<rangle> \<Turnstile>\<^sub>M \<phi>"
      by (auto elim: in_qtableE)
    \<comment> \<open>all variables of the tuple are defined\<close>
    from wf in_fv have "x = map Some (map the x)"
      by (intro nth_equalityI) (auto simp: wf_tuple_def)
    with wf sat show "x \<in> map Some ` {v. length v = m \<and> Formula.sat \<sigma> V v i \<phi>}"
      by (intro image_eqI[where x="map the x"]) (simp_all add: wf_tuple_def)
  next
    fix x
    assume "x \<in> map Some ` {v. length v = m \<and> Formula.sat \<sigma> V v i \<phi>}"
    then obtain v where "x = map Some v" "length v = m" "Formula.sat \<sigma> V v i \<phi>"
      by blast
    with \<alpha> in_fv show "x \<in> \<alpha>"
      by (intro in_qtableI[OF \<alpha>]) (auto simp: wf_tuple_def)
  qed
  moreover have "list_all2 (\<lambda>i X. X = map Some ` {v. length v = snd q \<and> the (V q) v i}) [the (P q)..<the (P' q)] (the (Mapping.lookup db q))"
    if "(p, m) \<noteq> q"
  proof -
    from that 7 have "q \<in> dom P" by simp
    with wf_envs show ?thesis unfolding wf_envs_def by blast
  qed
  ultimately show ?case
    by (auto simp add: list.rel_map image_iff lookup_update')
next
  case 8
  from wf_envs have "wty_envs S \<sigma> V" unfolding wf_envs_def by simp
  then show ?case unfolding wty_envs_def
    using ty_of_sat_safe[OF safe wty] in_fv
    by (auto simp: wty_envs_def wty_event_def wty_tuple_def list_all2_conv_all_nth m_eq domIff)
qed

lemma sat_V_cong:
  fixes \<phi> :: "ty Formula.formula"
  assumes "i < progress \<sigma> P \<phi> j" "dom V = dom V'" "dom P = dom V"
    "pred_mapping (\<lambda>x. x \<le> j) P"
    "\<And>p n v i. (p, n) \<in> dom V \<Longrightarrow> i < the (P (p, n)) \<Longrightarrow> n = length v \<Longrightarrow>
      the (V (p, n)) v i = the (V' (p, n)) v i"
  shows "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat \<sigma> V' v i \<phi>"
proof -
  obtain \<pi> where pf: "prefix_of \<pi> \<sigma>" and pl: "plen \<pi> = j"
    by (metis plen_take_prefix prefix_of_take_prefix)
  show ?thesis
    using sat_prefix_conv_gen[OF pf pf, unfolded pl, OF assms] by auto
qed

lemma (in maux) freeze_meval0_post_exact:
  assumes wfq: "wf_frz_queue \<sigma> V m \<phi> ks xs"
  shows "case freeze_meval0 eval k0 xs of (ys, xs') \<Rightarrow>
    wf_frz_queue \<sigma> V m \<phi> (drop (length ys) ks) xs' \<and> length ys + length xs' = length xs"
  using wfq
proof (induction xs arbitrary: ks k0)
  case Nil
  then show ?case
    by (cases ks) (simp_all add: wf_frz_queue_def)
next
  case (Cons \<alpha> \<alpha>s)
  from Cons.prems obtain k ks' where ks: "ks = k # ks'"
    and q\<alpha>: "frz_qtable \<sigma> V m \<phi> k \<alpha>"
    and qrest: "wf_frz_queue \<sigma> V m \<phi> ks' \<alpha>s"
    by (cases ks) (auto simp: wf_frz_queue_def)
  obtain us \<psi>' where ev: "eval \<alpha> = (us, \<psi>')"
    by (cases "eval \<alpha>")
  show ?case
  proof (cases "drop k0 us")
    case Nil
    with ev ks Cons.prems show ?thesis
      by (simp add: wf_frz_queue_def)
  next
    case (Cons y ys0)
    obtain zs xs' where rec: "freeze_meval0 eval (Suc k0) \<alpha>s = (zs, xs')"
      by (cases "freeze_meval0 eval (Suc k0) \<alpha>s")
    have IH': "case freeze_meval0 eval (Suc k0) \<alpha>s of (ys, xs') \<Rightarrow>
        wf_frz_queue \<sigma> V m \<phi> (drop (length ys) ks') xs' \<and> length ys + length xs' = length \<alpha>s"
      using Cons.IH[OF qrest] .
    from IH'[unfolded rec] have queue': "wf_frz_queue \<sigma> V m \<phi> (drop (length zs) ks') xs'"
      and len': "length zs + length xs' = length \<alpha>s"
      by simp_all
    from ev Cons rec ks queue' len' show ?thesis
      by simp
  qed
qed

lemma freeze_meval0_diagonal:
  assumes ef: "freeze_meval0 eval k0 \<alpha>s = (ys, \<alpha>s')"
    and replay: "\<And>\<alpha>. \<alpha> \<in> set \<alpha>s \<Longrightarrow> \<exists>us \<psi>'. eval \<alpha> = (us, \<psi>') \<and> length us = L"
    and k0_bound: "k0 \<le> L"
  shows "length ys = min (length \<alpha>s) (L - k0)
    \<and> (\<forall>i < length ys. ys ! i = fst (eval (\<alpha>s ! i)) ! (k0 + i))"
  using ef replay k0_bound
proof (induction \<alpha>s arbitrary: k0 ys \<alpha>s')
  case Nil
  then show ?case by simp
next
  case (Cons \<alpha> \<alpha>s0)
  obtain us \<psi>' where ev: "eval \<alpha> = (us, \<psi>')" and len_us: "length us = L"
    using Cons.prems(2)[of \<alpha>] by auto
  show ?case
  proof (cases "drop k0 us")
    case Nil
    then have "k0 \<ge> L" using len_us by simp
    with Cons.prems(3) have "k0 = L" by simp
    with Nil ev Cons.prems(1) have "ys = []" and "\<alpha>s' = \<alpha> # \<alpha>s0"
      by (simp_all add: Let_def)
    then show ?thesis using \<open>k0 = L\<close> by simp
  next
    case (Cons y rest)
    then have k0_lt: "k0 < L" using len_us
      by (metis drop_eq_Nil leI list.distinct(1))
    have y_eq: "y = us ! k0"
    proof -
      have "hd (drop k0 us) = us ! k0"
        using k0_lt len_us by (simp add: hd_drop_conv_nth)
      moreover have "hd (drop k0 us) = y" using Cons by simp
      ultimately show ?thesis by simp
    qed
    obtain zs \<alpha>s'' where rec: "freeze_meval0 eval (Suc k0) \<alpha>s0 = (zs, \<alpha>s'')"
      by (cases "freeze_meval0 eval (Suc k0) \<alpha>s0")
    from Cons ev rec have ys_eq: "ys = y # zs" and \<alpha>s'_eq: "\<alpha>s' = \<alpha>s''"
      using Cons.prems(1) by (simp_all add: Let_def)
    have IH: "length zs = min (length \<alpha>s0) (L - Suc k0) \<and>
      (\<forall>i < length zs. zs ! i = fst (eval (\<alpha>s0 ! i)) ! (Suc k0 + i))"
      using Cons.IH[OF rec] Cons.prems(2) k0_lt by auto
    have len_ys: "length ys = min (length (\<alpha> # \<alpha>s0)) (L - k0)"
    proof -
      have "length ys = Suc (length zs)" using ys_eq by simp
      also have "\<dots> = Suc (min (length \<alpha>s0) (L - Suc k0))" using IH by simp
      also have "\<dots> = min (Suc (length \<alpha>s0)) (Suc (L - Suc k0))"
        by (simp add: min_def)
      also have "Suc (L - Suc k0) = L - k0" using k0_lt by simp
      finally show ?thesis by simp
    qed
    have nth_ys: "\<forall>i < length ys. ys ! i = fst (eval ((\<alpha> # \<alpha>s0) ! i)) ! (k0 + i)"
    proof (intro allI impI)
      fix i assume "i < length ys"
      show "ys ! i = fst (eval ((\<alpha> # \<alpha>s0) ! i)) ! (k0 + i)"
      proof (cases i)
        case 0
        then show ?thesis using ys_eq y_eq ev by simp
      next
        case (Suc i')
        then have "i' < length zs" using \<open>i < length ys\<close> ys_eq by simp
        then have "zs ! i' = fst (eval (\<alpha>s0 ! i')) ! (Suc k0 + i')" using IH by simp
        then show ?thesis using Suc ys_eq by simp
      qed
    qed
    show ?thesis using len_ys nth_ys by blast
  qed
qed

lemma freeze_meval0_drop: "freeze_meval0 eval k \<alpha>s = (ys, \<alpha>s') \<Longrightarrow> \<alpha>s' = drop (length ys) \<alpha>s"
  by (induction eval k \<alpha>s arbitrary: ys \<alpha>s' rule: freeze_meval0.induct)
    (auto split: prod.splits list.splits)

text \<open>Resuming the live copy: the step computes the verdicts of the fresh copies, except for the
  first one, which is read off the live copy, as long as the live copy has its verdict exactly when
  the fresh copy of the first frozen table would have it.\<close>

lemma frz_live_step_spec:
  assumes st: "frz_live_step eval k \<alpha>s lr = (ys, \<alpha>s', lv)"
    and live: "case lr of None \<Rightarrow> True | Some (g, us, st) \<Rightarrow>
      \<alpha>s \<noteq> [] \<and> (length us \<le> g \<longleftrightarrow> length (fst (eval (hd \<alpha>s))) \<le> k)"
  shows "\<exists>ys0. freeze_meval0 eval k \<alpha>s = (ys0, \<alpha>s') \<and> length ys0 = length ys \<and>
      (\<forall>i<length ys. ys ! i = (case lr of Some (g, us, _) \<Rightarrow> if i = 0 then us ! g else ys0 ! i
        | None \<Rightarrow> ys0 ! i))" (is ?A)
    and "(\<exists>g us st. lr = Some (g, us, st) \<and> ys = [] \<and> length us \<le> g \<and> lv = Some (g - length us, st)) \<or>
      lv = (case \<alpha>s' of [] \<Rightarrow> None | \<alpha> # _ \<Rightarrow> (case eval \<alpha> of (us, st) \<Rightarrow> Some (k + length ys - length us, st)))"
      (is ?B)
    and "\<And>g us st. lr = Some (g, us, st) \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> g < length us"
proof -
  have "?A \<and> ?B \<and> (\<forall>g us st. lr = Some (g, us, st) \<longrightarrow> ys \<noteq> [] \<longrightarrow> g < length us)"
  proof (cases lr)
    case None
    with st have "freeze_meval1 eval k \<alpha>s = (ys, \<alpha>s', lv)"
      by (simp add: frz_live_step_def)
    with None show ?thesis
      using freeze_meval1_freeze_meval0[of eval k \<alpha>s] freeze_meval1_live[of eval k \<alpha>s ys \<alpha>s' lv]
      by (auto intro!: exI[of _ ys])
  next
    case (Some x)
    then obtain g us st where lr: "lr = Some (g, us, st)"
      by (cases x) auto
    from live lr obtain \<alpha> \<alpha>t where \<alpha>s: "\<alpha>s = \<alpha> # \<alpha>t"
      and iff: "length us \<le> g \<longleftrightarrow> length (fst (eval \<alpha>)) \<le> k"
      by (cases \<alpha>s) auto
    obtain us0 st0 where ev: "eval \<alpha> = (us0, st0)"
      by (cases "eval \<alpha>")
    show ?thesis
    proof (cases "length us \<le> g")
      case True
      with st lr \<alpha>s ev iff show ?thesis
        by (auto simp: frz_live_step_def)
    next
      case False
      then obtain y ut where dg: "drop g us = y # ut"
        by (cases "drop g us") auto
      obtain y0 ut0 where dk: "drop k us0 = y0 # ut0"
        using False iff ev by (cases "drop k us0") auto
      obtain zs \<alpha>s'' lv' where rec: "freeze_meval1 eval (Suc k) \<alpha>t = (zs, \<alpha>s'', lv')"
        by (cases "freeze_meval1 eval (Suc k) \<alpha>t")
      from st lr \<alpha>s dg rec have ys: "ys = y # zs" and \<alpha>s': "\<alpha>s' = \<alpha>s''" and lv: "lv = lv'"
        by (auto simp: frz_live_step_def)
      have y: "y = us ! g"
        using dg False by (metis hd_drop_conv_nth list.sel(1) not_le)
      have f0: "freeze_meval0 eval (Suc k) \<alpha>t = (zs, \<alpha>s'')"
        using freeze_meval1_freeze_meval0[of eval "Suc k" \<alpha>t] rec by simp
      have "freeze_meval0 eval k \<alpha>s = (y0 # zs, \<alpha>s'')"
        using \<alpha>s ev dk f0 by simp
      moreover have "lv = (case \<alpha>s' of [] \<Rightarrow> None
        | \<alpha> # _ \<Rightarrow> (case eval \<alpha> of (us, st) \<Rightarrow> Some (k + length ys - length us, st)))"
        using freeze_meval1_live[OF rec] unfolding lv \<alpha>s' ys by (auto split: list.splits prod.splits)
      ultimately show ?thesis
        using False lr ys y \<alpha>s' by (auto simp: nth_Cons split: nat.splits)
    qed
  qed
  then show ?A ?B "\<And>g us st. lr = Some (g, us, st) \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> g < length us"
    by blast+
qed

lemma (in maux) frz_step_post:
  assumes state: "wf_frz_state \<sigma> j P V p m \<phi> \<psi> jphi0 alphas"
    and phi_res: "list_all2 (\<lambda>i. qtable m (FV \<phi>) (mem_restr UNIV) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>))
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> (j + \<delta>)] xs"
    and phi_mono: "progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> (j + \<delta>)"
    and d_eq: "d = progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j - jphi0 + length zs0_out"
    and alphas1_eq: "alphas1 = drop d (alphas @ xs)"
    and ef: "freeze_meval0 eval k0 alphas1 = (ys, alphas2)"
    and frz_prog: "progress \<sigma> P' (Formula.Frz p \<phi> \<psi>) (j + \<delta>) =
      progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j + length zs0_out + length ys"
  shows "wf_frz_state \<sigma> (j + \<delta>) P' V p m \<phi> \<psi> (jphi0 + length xs) alphas2"
proof -
  let ?pn = "(p, m)"
  let ?jfrz = "progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j"
  let ?jphi = "progress \<sigma> P \<phi> j"
  let ?jphi' = "progress \<sigma> P' \<phi> (j + \<delta>)"
  let ?jfrz' = "progress \<sigma> P' (Formula.Frz p \<phi> \<psi>) (j + \<delta>)"
  from state have jphi0_eq: "jphi0 = ?jphi"
    and old_queue: "wf_frz_queue \<sigma> V m \<phi> [?jfrz..<?jphi] alphas"
    by (auto simp: wf_frz_state_def Let_def)
  have d_val: "d = ?jfrz - ?jphi + length zs0_out"
    using d_eq jphi0_eq by simp
  have queue_phi: "wf_frz_queue \<sigma> V m \<phi> [?jphi..<?jphi'] xs"
    using phi_res by (simp add: wf_frz_queue_def frz_qtable_def)
  have len_old: "length alphas = ?jphi - ?jfrz"
    using wf_frz_queue_length[OF old_queue] .
  have len_new: "length xs = ?jphi' - ?jphi"
    using phi_res by (auto dest: list_all2_lengthD)
  have jfrz'_eq: "?jfrz' = ?jfrz + length zs0_out + length ys"
    using frz_prog .
  have jphi'_eq: "jphi0 + length xs = ?jphi'"
  proof -
    show ?thesis using jphi0_eq len_new phi_mono by simp
  qed

  text \<open>Prove the queue property by case split on whether the drop stays within bounds\<close>
  have queue1': "wf_frz_queue \<sigma> V m \<phi> [?jfrz + length zs0_out..<?jphi'] alphas1"
  proof (cases "?jfrz + length zs0_out \<le> ?jphi'")
    case True
    show ?thesis
    proof (cases "?jfrz \<le> ?jphi")
      case jfrz_le: True
      then have d_simp: "d = length zs0_out" using d_val by simp
      have interval: "[?jfrz..<?jphi'] = [?jfrz..<?jphi] @ [?jphi..<?jphi']"
        using phi_mono jfrz_le by (intro upt_add_eq_append') auto
      have queue_all: "wf_frz_queue \<sigma> V m \<phi> [?jfrz..<?jphi'] (alphas @ xs)"
        unfolding wf_frz_queue_def interval using old_queue queue_phi
        by (meson list_all2_appendI wf_frz_queue_def)
      have "length zs0_out \<le> ?jphi' - ?jfrz"
        using True by simp
      then have "drop (length zs0_out) [?jfrz..<?jphi'] = [?jfrz + length zs0_out..<?jphi']"
        by simp
      then show ?thesis
        using wf_frz_queue_drop[OF queue_all, of "length zs0_out"] alphas1_eq d_simp by simp
    next
      case jfrz_gt: False
      then have "?jfrz > ?jphi" by simp
      then have alphas_nil: "alphas = []"
        using wf_frz_state_emptyD[OF state] by simp
      have drop_xs: "alphas1 = drop (?jfrz - ?jphi + length zs0_out) xs"
        using alphas1_eq d_val alphas_nil by simp
      have tail_queue: "wf_frz_queue \<sigma> V m \<phi> [?jfrz..<?jphi'] (drop (?jfrz - ?jphi) xs)"
      proof -
        have "drop (?jfrz - ?jphi) [?jphi..<?jphi'] = [?jfrz..<?jphi']"
          using \<open>?jfrz > ?jphi\<close> phi_mono by simp
        then show ?thesis
          using wf_frz_queue_drop[OF queue_phi, of "?jfrz - ?jphi"] by simp
      qed
      have zs0_out_bound: "length zs0_out \<le> ?jphi' - ?jfrz"
        using True by simp
      have "drop (length zs0_out) [?jfrz..<?jphi'] = [?jfrz + length zs0_out..<?jphi']"
        using zs0_out_bound by simp
      moreover have "drop (length zs0_out) (drop (?jfrz - ?jphi) xs) = drop (?jfrz - ?jphi + length zs0_out) xs"
        by (simp add: add.commute)
      ultimately show ?thesis
        using wf_frz_queue_drop[OF tail_queue, of "length zs0_out"] drop_xs by simp
    qed
  next
    case overflow: False
    text \<open>When jfrz + |zs0_out| > jphi', the drop exceeds the list, giving an empty queue\<close>
    then have "?jfrz + length zs0_out > ?jphi'" by simp
    then have interval_empty: "[?jfrz + length zs0_out..<?jphi'] = []" by simp
    have "alphas1 = []"
    proof -
      have len_ax: "length (alphas @ xs) = (?jphi - ?jfrz) + (?jphi' - ?jphi)"
        using len_old len_new by simp
      have "d \<ge> length (alphas @ xs)"
      proof (cases "?jfrz \<le> ?jphi")
        case True
        then have "d = length zs0_out" using d_val by simp
        moreover have "length (alphas @ xs) = ?jphi' - ?jfrz"
          using len_ax True phi_mono by linarith
        moreover have "length zs0_out \<ge> ?jphi' - ?jfrz"
          using overflow by simp
        ultimately show ?thesis by simp
      next
        case False
        then have "alphas = []" using wf_frz_state_emptyD[OF state] by simp
        then have "length (alphas @ xs) = ?jphi' - ?jphi" using len_new by simp
        moreover have "d = ?jfrz - ?jphi + length zs0_out" using d_val by simp
        moreover have "?jfrz - ?jphi + length zs0_out \<ge> ?jphi' - ?jphi"
          using overflow False by simp
        ultimately show ?thesis by simp
      qed
      then show ?thesis using alphas1_eq by simp
    qed
    then have "alphas1 = []" .
    then show ?thesis using interval_empty by (simp add: wf_frz_queue_def)
  qed
  have replay_post:
    "case freeze_meval0 eval k0 alphas1 of (ys', xs') \<Rightarrow>
       wf_frz_queue \<sigma> V m \<phi> (drop (length ys') [?jfrz + length zs0_out..<?jphi']) xs' \<and>
       length ys' + length xs' = length alphas1"
    using freeze_meval0_post_exact[OF queue1'] .
  from replay_post[unfolded ef] have replay_queue:
    "wf_frz_queue \<sigma> V m \<phi> (drop (length ys) [?jfrz + length zs0_out..<?jphi']) alphas2"
    and replay_len: "length ys + length alphas2 = length alphas1"
    by simp_all
  show "wf_frz_state \<sigma> (j + \<delta>) P' V p m \<phi> \<psi> (jphi0 + length xs) alphas2"
  proof -
    have queue_interval: "drop (length ys) [?jfrz + length zs0_out..<?jphi'] = [?jfrz'..<?jphi']"
      using jfrz'_eq by simp
    have queue_goal: "wf_frz_queue \<sigma> V m \<phi> [?jfrz'..<?jphi'] alphas2"
      using replay_queue queue_interval by simp
    show ?thesis
      unfolding wf_frz_state_def Let_def using jphi'_eq queue_goal by simp
  qed
qed

text \<open>The windowed replay of @{const MFrz}: helper facts.\<close>

lemma (in maux) wf_envs_update_frz:
  assumes wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db"
  and m_eq: "m = Formula.nfv \<phi>"
  and in_fv: "{0..<m} \<subseteq> FV \<phi>"
  and safe: "safe_formula \<phi>"
  and wty: "S, E \<turnstile> \<phi>"
  and X: "\<And>v k. X v k \<Longrightarrow> \<exists>i. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>"
  and w: "w \<le> j" "w \<le> w'" "w' \<le> j + \<delta>"
  and Ys: "list_all2 (\<lambda>k Y. Y = map Some ` {v. length v = m \<and> X v k}) [w..<w'] Ys"
  shows "wf_envs (S((p, m) \<mapsto> tabulate E 0 (Formula.nfv \<phi>))) \<sigma> j \<delta> (P((p, m) \<mapsto> w)) (P'((p, m) \<mapsto> w'))
    (V((p, m) \<mapsto> X)) (Mapping.update (p, m) Ys db)"
  unfolding wf_envs_def
proof (intro conjI ballI, goal_cases)
  case 1
  with assms show ?case unfolding wf_envs_def by auto
next
  case 2
  with assms show ?case unfolding wf_envs_def by (auto simp: subset_iff)
next
  case 3
  with assms show ?case by (auto intro!: rel_mapping_map_upd)
next
  case 4
  with assms show ?case by auto
next
  case 5
  with assms show ?case by auto
next
  case (6 q)
  with assms show ?case unfolding wf_envs_def by (cases "q \<in> dom P") auto
next
  case (7 q)
  show ?case
  proof (cases "q = (p, m)")
    case True
    with Ys show ?thesis by simp
  next
    case False
    with 7 have "q \<in> dom P" by simp
    with wf_envs False show ?thesis unfolding wf_envs_def by auto
  qed
next
  case 8
  from wf_envs have wty_V: "wty_envs S \<sigma> V" unfolding wf_envs_def by simp
  have ty: "ty_of (xs ! x) = E x" if "X xs k" "x < length xs" "length xs = m" for xs k x
  proof -
    from X[OF that(1)] obtain i where "\<langle>\<sigma>, V, xs, i\<rangle> \<Turnstile> \<phi>"
      by blast
    then show ?thesis
      using ty_of_sat_safe[OF safe wty wty_V] in_fv that(2,3) by auto
  qed
  with wty_V show ?case unfolding wty_envs_def
    by (auto simp: wty_event_def wty_tuple_def list_all2_conv_all_nth m_eq domIff)
qed

lemma (in maux) qtable_frz_alpha:
  assumes \<alpha>: "qtable m (FV \<phi>) (mem_restr UNIV) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>) \<alpha>"
    and in_fv: "{0..<m} \<subseteq> FV \<phi>"
  shows "\<alpha> = map Some ` {v. length v = m \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>}"
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> \<alpha>"
  with \<alpha> have wf: "wf_tuple m (FV \<phi>) x" and sat: "\<langle>\<sigma>, V, x, i\<rangle> \<Turnstile>\<^sub>M \<phi>"
    by (auto elim: in_qtableE)
  from wf in_fv have "x = map Some (map the x)"
    by (intro nth_equalityI) (auto simp: wf_tuple_def)
  with wf sat show "x \<in> map Some ` {v. length v = m \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>}"
    by (intro image_eqI[where x="map the x"]) (simp_all add: wf_tuple_def)
next
  fix x
  assume "x \<in> map Some ` {v. length v = m \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>}"
  then obtain v where "x = map Some v" "length v = m" "\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>"
    by blast
  with \<alpha> in_fv show "x \<in> \<alpha>"
    by (intro in_qtableI[OF \<alpha>]) (auto simp: wf_tuple_def)
qed

text \<open>The table with which the replay base absorbs the time points that leave the window is the
  frozen formula's value at some time point, or empty.\<close>

lemma (in maux) frz_fill_val:
  assumes \<alpha>s: "\<forall>\<alpha>\<in>set \<alpha>s. \<exists>i. qtable m (FV \<phi>) (mem_restr UNIV) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>) \<alpha>"
    and in_fv: "{0..<m} \<subseteq> FV \<phi>"
  obtains L where "frz_fill ng \<alpha>s = map Some ` {v. length v = m \<and>
    (case L of None \<Rightarrow> False | Some i \<Rightarrow> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>)}"
proof (cases "ng \<and> \<alpha>s \<noteq> []")
  case True
  then have "last \<alpha>s \<in> set \<alpha>s" and fill: "frz_fill ng \<alpha>s = last \<alpha>s"
    by (auto simp: frz_fill_def)
  with \<alpha>s obtain i where "qtable m (FV \<phi>) (mem_restr UNIV) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>) (last \<alpha>s)"
    by blast
  from qtable_frz_alpha[OF this in_fv] show ?thesis
    by (intro that[of "Some i"]) (simp add: fill)
next
  case False
  then show ?thesis
    by (intro that[of None]) (auto simp: frz_fill_def)
qed

lemma progress_Frz_eq:
  assumes pm: "pred_mapping (\<lambda>x. x \<le> j) P"
  shows "progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j =
    (let pn = (p, Formula.nfv \<phi>); jphi = progress \<sigma> P \<phi> j;
         a = progress \<sigma> (P(pn \<mapsto> 0)) \<psi> j; b = progress \<sigma> (P(pn \<mapsto> j)) \<psi> j
     in if b < jphi then b else if a \<le> jphi then jphi else a)"
proof -
  define pn where "pn = (p, Formula.nfv \<phi>)"
  define jphi where "jphi = progress \<sigma> P \<phi> j"
  define a where "a = progress \<sigma> (P(pn \<mapsto> 0)) \<psi> j"
  define b where "b = progress \<sigma> (P(pn \<mapsto> j)) \<psi> j"
  have F: "progress \<sigma> (P(pn \<mapsto> (if i < jphi then j else 0))) \<psi> j = (if i < jphi then b else a)" for i
    by (simp add: a_def b_def)
  have ab: "a \<le> b"
    unfolding a_def b_def using pm
    by (intro progress_mono_gen[OF order_refl])
      (auto intro!: rel_mapping_map_upd simp: rel_mapping_reflp reflp_def)
  have bj: "b \<le> j"
    unfolding b_def using pm by (intro progress_le_gen) auto
  have jphi_j: "jphi \<le> j"
    unfolding jphi_def by (rule progress_le_gen[OF pm])
  have "progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j =
    (LEAST i. i \<le> j \<and> progress \<sigma> (P(pn \<mapsto> (if i < jphi then j else 0))) \<psi> j \<le> i)"
    by (simp add: frz_progress_def pn_def jphi_def)
  also have "\<dots> = (if b < jphi then b else if a \<le> jphi then jphi else a)"
    unfolding F by (rule Least_equality) (use ab bj jphi_j in \<open>auto split: if_splits\<close>)
  finally show ?thesis
    by (simp add: Let_def pn_def jphi_def a_def b_def)
qed

lemma list_all2_diag:
  assumes "\<And>i. list_all2 (\<lambda>k X. Q i k X) ks xs"
  shows "list_all2 (\<lambda>k X. Q k k X) ks xs"
proof -
  have "length ks = length xs"
    using assms by (rule list_all2_lengthD)
  with assms show ?thesis
    by (auto simp: list_all2_conv_all_nth)
qed

lemma frz_win_le:
  assumes "\<forall>k<w. enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> i)"
  shows "w \<le> i"
proof (rule ccontr)
  assume "\<not> w \<le> i"
  with assms have "enat (\<tau> \<sigma> i) + d < enat (\<tau> \<sigma> i)"
    by simp
  then show False
    by (simp add: not_less le_iff_add[symmetric])
qed

lemma frz_win_mono:
  assumes "\<forall>k<w. enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> i)" "i \<le> i'"
  shows "\<forall>k<w. enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> i')"
proof (intro allI impI)
  fix k
  assume "k < w"
  with assms(1) have "enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> i)"
    by simp
  also have "\<dots> \<le> enat (\<tau> \<sigma> i')"
    using assms(2) by simp
  finally show "enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> i')" .
qed

text \<open>A verdict computed with the frozen predicate empty before a time point @{term w} is the
  verdict of the freeze, provided @{term w} lies beyond the reach of the body.\<close>

lemma qtable_Frz_window:
  assumes q: "qtable n (FV \<psi>) R (\<lambda>v. \<langle>\<sigma>, V((p, Formula.nfv \<phi>) \<mapsto> Q), v, i\<rangle> \<Turnstile>\<^sub>M \<psi>) X"
    and agree: "\<And>v k. w \<le> k \<Longrightarrow> Q v k = \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>"
    and win: "\<forall>k<w. enat (\<tau> \<sigma> k) + past_reach \<psi> < enat (\<tau> \<sigma> i)"
  shows "qtable n (FV (Formula.Frz p \<phi> \<psi>)) R (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M Formula.Frz p \<phi> \<psi>) X"
proof -
  let ?pn = "(p, Formula.nfv \<phi>)"
  have ag: "agree_from \<sigma> (past_reach \<psi>) i (V(?pn \<mapsto> Q)) (V(?pn \<mapsto> \<lambda>v k. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>))"
    unfolding agree_from_def
  proof
    fix pn'
    show "rel_option (\<lambda>X X'. \<forall>v k. enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + past_reach \<psi> \<longrightarrow> X v k = X' v k)
      ((V(?pn \<mapsto> Q)) pn') ((V(?pn \<mapsto> \<lambda>v k. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>)) pn')"
    proof (cases "pn' = ?pn")
      case True
      have "w \<le> k" if "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + past_reach \<psi>" for k
        using win that by (meson leD leI)
      with True agree show ?thesis
        by auto
    next
      case False
      then show ?thesis
        by (cases "V pn'") auto
    qed
  qed
  have "\<langle>\<sigma>, V(?pn \<mapsto> Q), u, i\<rangle> \<Turnstile> \<psi> \<longleftrightarrow> \<langle>\<sigma>, V(?pn \<mapsto> \<lambda>v k. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>), u, i\<rangle> \<Turnstile> \<psi>" for u
    by (rule sat_agree_from[OF order_refl ag])
  then show ?thesis
    using q by (auto intro: qtable_cong[OF _ refl])
qed

lemma (in maux) meval_correct:
  assumes "wf_mformula \<sigma> j P V n R \<phi> \<phi>'" "wf_envs S \<sigma> j \<delta> P P' V db" "S, E \<turnstile> \<phi>'"
  shows "case meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi> 
    of (xs, \<phi>\<^sub>n) \<Rightarrow> wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<phi>' 
      \<and> list_all2 (\<lambda>i. qtable n (FV \<phi>') (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>'))
          [progress \<sigma> P \<phi>' j..<progress \<sigma> P' \<phi>' (j + \<delta>)] xs"
  using assms
proof (induction \<phi> arbitrary: db P P' V n R \<phi>' j \<delta> S E rule: mformula_induct)
  case (MRel rel) (* other repo-branches have ?case2 and ?case3 *)
  let ?case1 = "\<lambda>t1 t2. \<phi>' = t1 =\<^sub>F t2 \<and> rel = eq_rel n t1 t2
  \<and> is_simple_eq t1 t2 \<and> (\<forall>x\<in>FV\<^sub>t t1. x < n) \<and> (\<forall>x\<in>FV\<^sub>t t2. x < n)"
  obtain t1 and t2 where cases: "?case1 t1 t2"
    using MRel(1)
    by (cases rule: wf_mformula.cases)
      (auto simp: and_release_safe_bounded_def release_safe_0_def always_safe_0_def
        elim: wf_mformula.cases)
  moreover have "?case1 t1 t2 \<Longrightarrow> ?case"
    by (auto split: prod.splits intro!: qtable_eq_relI wf_mformula.Eq)
  ultimately show ?case
    using cases by (metis (no_types, lifting))
next
  case (MPred p ts mode)
  let ?p = "(p, length ts)"
  have inits: "\<phi>' = p \<dagger> ts" "\<forall>x\<in>FV (p \<dagger> ts). x < n" 
    "\<forall>t\<in>set ts. trm.is_Var t \<or> trm.is_Const t"
    using MPred(1) 
    by (cases rule: wf_mformula.cases, 
        auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)+
  have wfmf: "wf_mformula \<sigma> (j + \<delta>) P' V n R (MPred p ts mode) (p \<dagger> ts)"
    "MPred p ts mode = MPred p ts (pred_mode_of n ts)"
    using MPred(1) by (cases rule: wf_mformula.cases, auto intro!: wf_mformula.Pred
        dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)+
  show ?case
  proof (cases "?p \<in> dom P") \<comment> \<open>notice @{term "dom P = dom V"}\<close>
    case True
    hence "?p \<in> Mapping.keys db" "?p \<in> dom P'" "?p \<in> dom V" and
      "list_all2 (\<lambda>i X. X = map Some ` {v. length v = length ts \<and> the (V ?p) v i}) 
        [the (P ?p)..<the (P' ?p)] (the (Mapping.lookup db ?p))" 
      using MPred(2) unfolding wf_envs_def 
      by (auto simp: dom_def rel_mapping_alt dest: bspec[where x="?p"])
    then obtain m m' Rs and pred 
      where wtnss: "P ?p = Some m" "P' ?p = Some m'" 
        "V ?p = Some pred" "Mapping.lookup db ?p = Some Rs" 
        and key: "list_all2 (\<lambda>i X. X = map Some ` {v. length v = length ts \<and> pred v i}) [m..<m'] Rs"
      using True by (auto simp: dom_def keys_dom_lookup)
    hence case1: "is_copy_pattern n ts 
      \<Longrightarrow> list_all2 (\<lambda>i. qtable n (FV \<phi>') (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>')) [m..<m'] Rs"
      using qtable_copy_pattern(1)
      by - (erule list.rel_mono_strong, clarsimp simp: inits)
    moreover have case2: "is_simple_pattern ts 0 
      \<Longrightarrow> list_all2 (\<lambda>i T. qtable n (FV \<phi>') (mem_restr R) 
        (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>') (simple_match n 0 ts ` T)) [m..<m'] Rs"
      using key wtnss inits qtable_simple_pattern 
      by - (erule list.rel_mono_strong, clarsimp)
    moreover have case3: "\<not> is_copy_pattern n ts \<Longrightarrow> \<not> is_simple_pattern ts 0 
      \<Longrightarrow> list_all2 (\<lambda>i T. qtable n (FV \<phi>') (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>')
             ((\<lambda>x. tabulate x 0 n) ` Option.these (match ts ` T)))
          [m..<m'] Rs"
      using key wtnss inits qtable_no_pattern(1)
      by - (erule list.rel_mono_strong, clarsimp)
    ultimately show ?thesis
      using wtnss wfmf inits 
      by (clarsimp simp: list.rel_map split: pred_mode.split)
  next
    let ?next_keys = "\<Union>k \<in> {j ..< j + \<delta>}. {(p, n). \<exists>x. (p, x) \<in> \<Gamma> \<sigma> k \<and> n = length x}"
    let "?option_sats_at" = "\<lambda>k. map Some ` {v. (p, v) \<in> \<Gamma> \<sigma> k \<and> length v = length ts}"
    case False
    hence obs: "?p \<notin> dom P'" "?p \<notin> dom V" "?p \<in> ?next_keys \<longrightarrow> ?p \<in> Mapping.keys db"
      using MPred(2)
      unfolding wf_envs_def rel_mapping_alt 
      by (auto simp: subset_iff)
    have key: "?p \<in> Mapping.keys db \<Longrightarrow> Mapping.lookup db ?p 
      = Some (map ?option_sats_at [j ..< j + \<delta>])"
      using False MPred(2) 
      unfolding wf_envs_def keys_dom_lookup
      by (clarsimp, erule_tac x="?p" in ballE, auto)
    hence case1: "Mapping.lookup db ?p = None \<Longrightarrow> ?thesis"
      using wfmf inits obs False
      by (clarsimp simp: keys_dom_lookup dom_def list.rel_map wf_tuple_def 
          qtable_empty_iff[unfolded empty_table_def])
        (erule_tac x="j+i" in ballE; force)
    moreover have case2: "\<exists>x. Mapping.lookup db ?p = Some x \<Longrightarrow> is_copy_pattern n ts \<Longrightarrow> ?thesis"
      using wfmf inits False obs key qtable_copy_pattern(2) 
      by (clarsimp simp: keys_dom_lookup dom_def list.rel_map image_image 
          split: pred_mode.split intro!: list.rel_refl_strong)
    moreover have case3: "\<exists>x. Mapping.lookup db ?p = Some x \<Longrightarrow> \<not> is_copy_pattern n ts 
      \<Longrightarrow> is_simple_pattern ts 0 \<Longrightarrow> ?thesis"
      using wfmf inits False obs key qtable_simple_pattern(2)
      by (clarsimp simp: keys_dom_lookup dom_def list.rel_map image_image 
          split: pred_mode.split intro!: list.rel_refl_strong)
    moreover have case4: "\<exists>x. Mapping.lookup db ?p = Some x \<Longrightarrow> \<not> is_copy_pattern n ts 
      \<Longrightarrow> \<not> is_simple_pattern ts 0 \<Longrightarrow> ?thesis"
      using wfmf inits False obs key qtable_no_pattern(2)
      by (clarsimp simp: keys_dom_lookup dom_def list.rel_map image_image 
          split: pred_mode.split intro!: list.rel_refl_strong)
    ultimately show ?thesis
      by (meson not_None_eq)
  qed
next
  case (MLet p m \<phi>1 \<phi>2)
  let ?pn = "(p, m)"
  from MLet.prems(1) obtain \<phi>1' \<phi>2' where Let: "\<phi>' = Formula.Let p \<phi>1' \<phi>2'" and
    1: "wf_mformula \<sigma> j P V m UNIV \<phi>1 \<phi>1'" and
    fv: "m = Formula.nfv \<phi>1'" "{0..<m} \<subseteq> fv \<phi>1'" and
    2: "wf_mformula \<sigma> j (P(?pn \<mapsto> progress \<sigma> P \<phi>1' j))
      (V(?pn \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>1'))
      n R \<phi>2 \<phi>2'" and
    safe1: "safe_formula \<phi>1'" and
    safe2: "safe_formula \<phi>2'" 
    by (cases rule: wf_mformula.cases) 
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MLet.prems(3) Let obtain E' where
    wty1: "S, E' \<turnstile> \<phi>1'" and
    wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1')), E \<turnstile> \<phi>2'"
    unfolding fv by (cases pred: wty_formula) simp_all
  obtain xs \<phi>1_new where e1: "meval (j + \<delta>) m (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>1 = (xs, \<phi>1_new)" and
      wf1: "wf_mformula \<sigma> (j + \<delta>) P' V m UNIV \<phi>1_new \<phi>1'" and
      res1: "list_all2 (\<lambda>i. qtable m (fv \<phi>1') (mem_restr UNIV) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>1'))
       [progress \<sigma> P \<phi>1' j..<progress \<sigma> P' \<phi>1' (j + \<delta>)] xs"
    using MLet(1)[OF 1(1) MLet.prems(2) wty1] by (auto simp: eqTrueI[OF mem_restr_UNIV, abs_def])
  from MLet(2)[OF 2 wf_envs_update[OF MLet.prems(2) fv res1 safe1 wty1] wty2] wf1 e1 fv safe1 safe2
  show ?case unfolding Let
    by (auto simp: fun_upd_def intro!: wf_mformula.Let)
next
  case (MFrz p m \<phi> \<psi> jfrz0 jpsi0_val jphi0 \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L)
  let ?pn = "(p, m)"
  let ?db0 = "Mapping.update ?pn [] db"
  let ?dbe = "Mapping.map_values (\<lambda>_ _. []) db"
  let ?ts = "map (\<tau> \<sigma>) [j ..< j + \<delta>]"
  from MFrz.prems(1) obtain \<phi>1 \<psi>1 N where Frz_eq: "\<phi>' = Formula.Frz p \<phi>1 \<psi>1" and
    wf_\<phi>: "wf_mformula \<sigma> j P V m UNIV \<phi> \<phi>1" and
    wf_\<psi>: "\<And>i. wf_mformula \<sigma> j (P(?pn \<mapsto> 0)) (V(?pn \<mapsto> \<lambda>v j. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>1)) n R \<psi> \<psi>1" and
    wf_state: "wf_frz_state \<sigma> j P V p m \<phi>1 \<psi>1 jphi0 \<alpha>s" and
    jfrz0_eq: "jfrz0 = progress \<sigma> P (Formula.Frz p \<phi>1 \<psi>1) j" and
    jpsi0_eq: "jpsi0_val = progress \<sigma> (P(?pn \<mapsto> 0)) \<psi>1 j" and
    wf_\<rho>: "\<And>M. wf_mformula \<sigma> j (P(?pn \<mapsto> w))
      (V(?pn \<mapsto> frz_val \<sigma> V \<phi>1 (\<lambda>k. if k < w then N k else M k))) n R \<rho> \<psi>1" and
    win: "wf_frz_win \<sigma> j P V n R p m \<phi>1 \<psi>1 jfrz0 w pR tq rb d" and
    fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> fv \<phi>1" and
    safe1: "safe_formula \<phi>1" and safe2: "safe_formula \<psi>1" and
    po: "po \<longrightarrow> safe_letpast (p, m) \<psi>1 \<le> NonFutuRec" and
    live: "\<And>g. lv = Some g \<Longrightarrow> \<not> po \<and> (\<exists>wL NL. (\<forall>k<wL. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz0)) \<and>
      jfrz0 = progress \<sigma> (P(?pn \<mapsto> j)) \<psi>1 j + g \<and>
      wf_mformula \<sigma> j (P(?pn \<mapsto> j)) (V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz0)) n R \<rho>L \<psi>1)"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from win have w_le: "w \<le> j" and d_eq: "d = past_reach \<psi>1"
    and pR_eq: "pR = progress \<sigma> (P(?pn \<mapsto> w)) \<psi>1 j"
    and win_old: "\<forall>k<w. enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> jfrz0)"
    and tq_eq: "tq = (if d = \<infinity> then [] else map (\<tau> \<sigma>) [w..<j])"
    and rb_rows: "list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, k\<rangle> \<Turnstile>\<^sub>M Formula.Frz p \<phi>1 \<psi>1))
      [min jfrz0 pR..<pR] rb"
    unfolding wf_frz_win_def by auto
  from MFrz.prems(3) Frz_eq obtain E' where
    wty1: "S, E' \<turnstile> \<phi>1" and
    wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    unfolding fv by (cases pred: wty_formula) simp_all
  from MFrz.prems(2) have pm: "pred_mapping (\<lambda>x. x \<le> j) P"
    and pm': "pred_mapping (\<lambda>x. x \<le> j + \<delta>) P'" and rm: "rel_mapping (\<le>) P P'"
    by auto
  have fv_Frz: "FV (Formula.Frz p \<phi>1 \<psi>1) = FV \<psi>1"
    by simp
  define good where "good k X \<longleftrightarrow>
    qtable n (FV \<psi>1) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, k\<rangle> \<Turnstile>\<^sub>M Formula.Frz p \<phi>1 \<psi>1) X" for k X
  \<comment> \<open>the progress of the parts\<close>
  define jphi where "jphi = progress \<sigma> P \<phi>1 j"
  define jphi' where "jphi' = progress \<sigma> P' \<phi>1 (j + \<delta>)"
  define jpsi0 where "jpsi0 = progress \<sigma> (P(?pn \<mapsto> 0)) \<psi>1 j"
  define jpsij where "jpsij = progress \<sigma> (P(?pn \<mapsto> j)) \<psi>1 j"
  define jpsi0' where "jpsi0' = progress \<sigma> (P'(?pn \<mapsto> 0)) \<psi>1 (j + \<delta>)"
  define jpsij' where "jpsij' = progress \<sigma> (P'(?pn \<mapsto> j + \<delta>)) \<psi>1 (j + \<delta>)"
  define jfrz' where "jfrz' = progress \<sigma> P' (Formula.Frz p \<phi>1 \<psi>1) (j + \<delta>)"
  define pR1 where "pR1 = progress \<sigma> (P'(?pn \<mapsto> w)) \<psi>1 (j + \<delta>)"
  have frz_eq: "jfrz0 = (if jpsij < jphi then jpsij else if jpsi0 \<le> jphi then jphi else jpsi0)"
    using progress_Frz_eq[OF pm, of \<sigma> p \<phi>1 \<psi>1]
    by (simp add: jfrz0_eq jphi_def jpsi0_def jpsij_def fv(1) Let_def)
  have frz_eq': "jfrz' = (if jpsij' < jphi' then jpsij' else if jpsi0' \<le> jphi' then jphi' else jpsi0')"
    using progress_Frz_eq[OF pm', of \<sigma> p \<phi>1 \<psi>1]
    by (simp add: jfrz'_def jphi'_def jpsi0'_def jpsij'_def fv(1) Let_def)
  have mono_pn: "progress \<sigma> (P'(?pn \<mapsto> k)) \<psi>1 (j + \<delta>) \<le> progress \<sigma> (P'(?pn \<mapsto> k')) \<psi>1 (j + \<delta>)"
    if "k \<le> k'" "k' \<le> j + \<delta>" for k k'
    using pm' that by (intro progress_mono_gen[OF order_refl])
      (auto intro!: rel_mapping_map_upd simp: rel_mapping_reflp reflp_def)
  have mono_pn0: "progress \<sigma> (P(?pn \<mapsto> k)) \<psi>1 j \<le> progress \<sigma> (P(?pn \<mapsto> k')) \<psi>1 j"
    if "k \<le> k'" "k' \<le> j" for k k'
    using pm that by (intro progress_mono_gen[OF order_refl])
      (auto intro!: rel_mapping_map_upd simp: rel_mapping_reflp reflp_def)
  have mono_time: "progress \<sigma> (P(?pn \<mapsto> k)) \<psi>1 j \<le> progress \<sigma> (P'(?pn \<mapsto> k)) \<psi>1 (j + \<delta>)"
    if "k \<le> j" for k
    using pm pm' rm that by (intro progress_mono_gen[OF le_add1])
      (auto intro!: rel_mapping_map_upd)
  have jphi_le: "jphi \<le> jphi'"
    unfolding jphi_def jphi'_def by (rule progress_mono_gen[OF le_add1 pm pm' rm])
  have jfrz_le: "jfrz0 \<le> jfrz'"
    unfolding jfrz0_eq jfrz'_def by (rule progress_mono_gen[OF le_add1 pm pm' rm])
  have jfrz'_le: "jfrz' \<le> j + \<delta>"
    unfolding jfrz'_def by (rule progress_le_gen[OF pm'])
  have jpsi0_le: "jpsi0 \<le> jpsi0'"
    unfolding jpsi0_def jpsi0'_def by (rule mono_time) simp
  have jpsi0_jpsij: "jpsi0 \<le> jpsij"
    unfolding jpsi0_def jpsij_def by (rule mono_pn0) simp_all
  have jpsi0'_jpsij': "jpsi0' \<le> jpsij'"
    unfolding jpsi0'_def jpsij'_def by (rule mono_pn) simp_all
  have jpsi0_jfrz: "jpsi0 \<le> jfrz0"
    using frz_eq jpsi0_jpsij by (auto split: if_splits)
  have jfrz_jphi: "jphi < jfrz0 \<Longrightarrow> jfrz0 = jpsi0"
    using frz_eq by (auto split: if_splits)
  have jfrz'_jpsij': "jfrz' \<le> jpsij'"
    using frz_eq' jpsi0'_jpsij' by (auto split: if_splits)
  have pR_le: "pR \<le> pR1"
    unfolding pR_eq pR1_def by (rule mono_time[OF w_le])
  have pR1_le: "pR1 \<le> jpsij'"
    unfolding pR1_def jpsij'_def by (rule mono_pn) (use w_le in simp_all)
  have jpsi0'_pR1: "jpsi0' \<le> pR1"
    unfolding pR1_def jpsi0'_def by (rule mono_pn) (use w_le in simp_all)
  have w_jfrz0: "w \<le> jfrz0"
    by (rule frz_win_le[OF win_old])
  \<comment> \<open>the frozen formula\<close>
  obtain xs \<phi>_new where e\<phi>: "meval (j + \<delta>) m ?ts db \<phi> = (xs, \<phi>_new)"
    by (cases "meval (j + \<delta>) m ?ts db \<phi>")
  have wf_\<phi>_new: "wf_mformula \<sigma> (j + \<delta>) P' V m UNIV \<phi>_new \<phi>1"
    and phi_res: "list_all2 (\<lambda>i. qtable m (FV \<phi>1) (mem_restr UNIV) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>1))
      [jphi..<jphi'] xs"
    using MFrz(1)[OF wf_\<phi> MFrz.prems(2) wty1] e\<phi>
    by (auto simp: jphi_def jphi'_def eqTrueI[OF mem_restr_UNIV, abs_def])
  have len_xs: "length xs = jphi' - jphi"
    using phi_res by (auto dest: list_all2_lengthD)
  \<comment> \<open>the body, with the frozen predicate empty\<close>
  obtain zs0 \<psi>_new where e\<psi>0: "meval (j + \<delta>) n ?ts ?db0 \<psi> = (zs0, \<psi>_new)"
    by (cases "meval (j + \<delta>) n ?ts ?db0 \<psi>")
  have IH\<psi>: "wf_mformula \<sigma> (j + \<delta>) (P'(?pn \<mapsto> 0)) (V(?pn \<mapsto> \<lambda>v j. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>1)) n R \<psi>_new \<psi>1 \<and>
    list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R)
      (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> \<lambda>v j. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>1), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [jpsi0..<jpsi0'] zs0" for i
    using MFrz(2)[OF refl wf_\<psi> wf_envs_update3[OF MFrz.prems(2) fv safe1 wty1] wty2] e\<psi>0
    by (simp add: jpsi0_def jpsi0'_def fun_upd_def)
  have len_zs0: "length zs0 = jpsi0' - jpsi0"
    using IH\<psi>[of 0] by (auto dest: list_all2_lengthD)
  define zs0_out where "zs0_out = drop (jfrz0 - jpsi0_val) zs0"
  define jfrzM where "jfrzM = jfrz0 + length zs0_out"
  have jfrzM_eq: "jfrzM = max jfrz0 jpsi0'"
    using len_zs0 jpsi0_jfrz jpsi0_le unfolding jfrzM_def zs0_out_def jpsi0_eq jpsi0_def[symmetric]
    by simp
  have zs0_out_rows: "list_all2 good [jfrz0..<jfrzM] zs0_out"
  proof -
    have "list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R)
      (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> \<lambda>v j. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>1), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [jfrz0..<jpsi0'] zs0_out" for i
      using list_all2_dropI[OF conjunct2[OF IH\<psi>[of i]], of "jfrz0 - jpsi0"] jpsi0_jfrz
      unfolding zs0_out_def jpsi0_eq jpsi0_def[symmetric] by simp
    then have diag: "list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R)
      (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> \<lambda>v j. \<langle>\<sigma>, V, v, k\<rangle> \<Turnstile> \<phi>1), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [jfrz0..<jpsi0'] zs0_out"
      by (rule list_all2_diag)
    have "[jfrz0..<jpsi0'] = [jfrz0..<jfrzM]"
      unfolding jfrzM_eq by (cases "jfrz0 \<le> jpsi0'") auto
    with diag show ?thesis
      by (auto simp: good_def fv(1) elim!: list.rel_mono_strong intro: qtable_cong[OF _ refl])
  qed
  \<comment> \<open>the queue of frozen tables still to be replayed\<close>
  define \<alpha>s1 where "\<alpha>s1 = drop (jfrz0 - jphi0 + length zs0_out) (\<alpha>s @ xs)"
  have jphi0_eq: "jphi0 = jphi"
    using wf_state by (auto simp: wf_frz_state_def Let_def jphi_def)
  have old_queue: "wf_frz_queue \<sigma> V m \<phi>1 [jfrz0..<jphi] \<alpha>s"
    using wf_state by (auto simp: wf_frz_state_def Let_def jfrz0_eq jphi_def)
  have new_queue: "wf_frz_queue \<sigma> V m \<phi>1 [jphi..<jphi'] xs"
    using phi_res by (simp add: wf_frz_queue_def frz_qtable_def)
  have queue1: "wf_frz_queue \<sigma> V m \<phi>1 [jfrzM..<jphi'] \<alpha>s1"
  proof (cases "jfrz0 \<le> jphi")
    case True
    have "wf_frz_queue \<sigma> V m \<phi>1 ([jfrz0..<jphi] @ [jphi..<jphi']) (\<alpha>s @ xs)"
      by (rule wf_frz_queue_append[OF old_queue new_queue])
    then have "wf_frz_queue \<sigma> V m \<phi>1 [jfrz0..<jphi'] (\<alpha>s @ xs)"
      using True jphi_le by (simp add: upt_add_eq_append'[symmetric])
    from wf_frz_queue_drop[OF this, of "length zs0_out"] show ?thesis
      using True unfolding \<alpha>s1_def jphi0_eq jfrzM_def by simp
  next
    case False
    then have "\<alpha>s = []" and jfrz_eq: "jfrz0 = jpsi0"
      using old_queue jfrz_jphi by (auto simp: wf_frz_queue_def)
    from wf_frz_queue_drop[OF new_queue, of "jfrz0 - jphi + length zs0_out"] show ?thesis
      using False \<open>\<alpha>s = []\<close> unfolding \<alpha>s1_def jphi0_eq jfrzM_def by simp
  qed
  have len_\<alpha>s1: "length \<alpha>s1 = jphi' - jfrzM"
    using wf_frz_queue_length[OF queue1] .
  have qtab_\<alpha>s1: "qtable m (FV \<phi>1) (mem_restr UNIV) (\<lambda>v. \<langle>\<sigma>, V, v, jfrzM + i\<rangle> \<Turnstile>\<^sub>M \<phi>1) (\<alpha>s1 ! i)"
    if "i < length \<alpha>s1" for i
    using queue1 that len_\<alpha>s1 by (auto simp: wf_frz_queue_def frz_qtable_def list_all2_conv_all_nth)
  have \<alpha>s1_qtab: "\<exists>k. qtable m (FV \<phi>1) (mem_restr UNIV) (\<lambda>v. \<langle>\<sigma>, V, v, k\<rangle> \<Turnstile>\<^sub>M \<phi>1) \<alpha>"
    if "\<alpha> \<in> set \<alpha>s1" for \<alpha>
    using that qtab_\<alpha>s1 by (auto simp: in_set_conv_nth)
  \<comment> \<open>the replay base absorbs the new time points, with no new frozen tables\<close>
  obtain rs \<rho>1 where e\<rho>1: "meval (j + \<delta>) n ?ts ?db0 \<rho> = (rs, \<rho>1)"
    by (cases "meval (j + \<delta>) n ?ts ?db0 \<rho>")
  have size_\<rho>1: "size \<rho>1 = size \<rho>"
    using size_snd_meval[of "j + \<delta>" n ?ts ?db0 \<rho>] e\<rho>1 by simp
  have IH\<rho>: "wf_mformula \<sigma> (j + \<delta>) (P'(?pn \<mapsto> w))
      (V(?pn \<mapsto> frz_val \<sigma> V \<phi>1 (\<lambda>k. if k < w then N k else M k))) n R \<rho>1 \<psi>1 \<and>
    list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R)
      (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_val \<sigma> V \<phi>1 (\<lambda>k. if k < w then N k else M k)), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [pR..<pR1] rs"
    for M
  proof -
    have envs: "wf_envs (S(?pn \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1))) \<sigma> j \<delta> (P(?pn \<mapsto> w)) (P'(?pn \<mapsto> w))
      (V(?pn \<mapsto> frz_val \<sigma> V \<phi>1 (\<lambda>k. if k < w then N k else M k))) ?db0"
      by (rule wf_envs_update_frz[OF MFrz.prems(2) fv safe1 wty1]) (use w_le frz_val_sat in auto)
    show ?thesis
      using MFrz(3)[OF refl wf_\<rho> envs wty2] e\<rho>1 by (simp add: pR_eq pR1_def fun_upd_def)
  qed
  \<comment> \<open>the verdicts of the replay base are those of the freeze from the first undecided time point on\<close>
  have rs_good: "list_all2 (\<lambda>k X. jfrz0 \<le> k \<longrightarrow> good k X) [pR..<pR1] rs"
  proof -
    have "list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R)
      (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 N w i), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [pR..<pR1] rs" for i
      using IH\<rho>[of "\<lambda>_. Some i"] by blast
    then have "list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R)
      (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 N w k), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [pR..<pR1] rs"
      by (rule list_all2_diag)
    then show ?thesis
    proof (rule list.rel_mono_strong, intro impI)
      fix k X
      assume "qtable n (FV \<psi>1) (mem_restr R)
        (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 N w k), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1) X" "jfrz0 \<le> k"
      then show "good k X"
        unfolding good_def fv_Frz[symmetric]
        by (intro qtable_Frz_window[where w = w and i = k and Q = "frz_cv \<sigma> V \<phi>1 N w k"])
          (simp_all add: fv(1) frz_cv_ge frz_win_mono[OF win_old[unfolded d_eq]])
    qed
  qed
  define rb0 where "rb0 = pR - length rb"
  have rb0_eq: "rb0 = min jfrz0 pR"
    using rb_rows unfolding rb0_def by (auto dest!: list_all2_lengthD)
  define rb1 where "rb1 = rb @ rs"
  have rb1_good: "list_all2 (\<lambda>k X. jfrz0 \<le> k \<longrightarrow> good k X) [rb0..<pR1] rb1"
    unfolding rb1_def
    by (rule list_all2_upt_append[OF _ rs_good])
      (use rb_rows pR_le in \<open>auto simp: rb0_eq good_def elim!: list.rel_mono_strong\<close>)
  have len_rb1: "length rb1 = pR1 - rb0"
    using rb1_good by (auto dest: list_all2_lengthD)
  have rb0_le: "rb0 \<le> jfrz0" "rb0 \<le> pR1"
    using pR_le by (auto simp: rb0_eq)
  \<comment> \<open>the replays are fed the frozen table up to @{term "w + c"}: up to the frozen formula's
    progress when the body does not use the frozen predicate beyond the current time point\<close>
  define c where "c = frz_cut po w jphi0 (length xs) (j + \<delta>)"
  have c_le: "w + c \<le> j + \<delta>"
    using w_le by (auto simp: c_def frz_cut_def)
  define jpsic where "jpsic = progress \<sigma> (P'(?pn \<mapsto> w + c)) \<psi>1 (j + \<delta>)"
  have jpsic_le: "jpsic \<le> jpsij'"
    unfolding jpsic_def jpsij'_def by (rule mono_pn) (use c_le in simp_all)
  have pR1_jpsic: "pR1 \<le> jpsic"
    unfolding pR1_def jpsic_def by (rule mono_pn) (use c_le in simp_all)
  have jphi'_le: "jphi' \<le> j + \<delta>"
    unfolding jphi'_def by (rule progress_le_gen[OF pm'])
  have jpsic_min: "min jphi' jpsic = min jphi' jpsij'"
  proof (cases po)
    case True
    have pmJ: "pred_mapping (\<lambda>x. x \<le> j + \<delta>) (P'(?pn \<mapsto> j + \<delta>))"
      using pm' by (simp add: pred_mapping_alt)
    have "min (if safe_letpast ?pn \<psi>1 = NonFutuRec then w + c else min (Suc (w + c)) (j + \<delta>)) jpsij'
        \<le> jpsic"
      using safe_letpast_progress_upd'[where \<sigma>=\<sigma>, OF po[rule_format, OF True] pmJ c_le refl]
      unfolding jpsic_def jpsij'_def by simp
    then have "min (w + c) jpsij' \<le> jpsic"
      using c_le by (auto split: if_splits)
    moreover have "jphi' \<le> w + c"
      using True jphi_le jphi'_le unfolding c_def frz_cut_def len_xs jphi0_eq jphi_def by auto
    ultimately show ?thesis
      using jpsic_le by linarith
  qed (use w_le in \<open>simp add: c_def frz_cut_def jpsic_def jpsij'_def\<close>)
  have jfrzM_jpsic: "jfrzM \<le> jpsic"
  proof (cases "jfrz0 \<le> jphi")
    case True
    then have "jfrz0 \<le> min jphi' jpsij'"
      using jphi_le jfrz_le jfrz'_jpsij' by simp
    then have "jfrz0 \<le> jpsic"
      unfolding jpsic_min[symmetric] by simp
    then show ?thesis
      using jpsi0'_pR1 pR1_jpsic unfolding jfrzM_eq by simp
  next
    case False
    then show ?thesis
      using jfrz_jphi jpsi0_le jpsi0'_pR1 pR1_jpsic unfolding jfrzM_eq by simp
  qed
  \<comment> \<open>the replays: the window from @{term w} on, with the frozen table\<close>
  define cp where "cp \<alpha> = (case meval (j + \<delta>) n []
      (Mapping.update ?pn (replicate c \<alpha>) ?dbe) \<rho>1 of (us, \<rho>') \<Rightarrow> (rb1 @ us, \<rho>'))" for \<alpha>
  have cp_eq: "cp \<alpha> = (rb1 @ fst (meval (j + \<delta>) n [] (Mapping.update ?pn (replicate c \<alpha>) ?dbe) \<rho>1),
      snd (meval (j + \<delta>) n [] (Mapping.update ?pn (replicate c \<alpha>) ?dbe) \<rho>1))" for \<alpha>
    by (simp add: cp_def split: prod.splits)
  have cp_full: "wf_mformula \<sigma> (j + \<delta>) (P'(?pn \<mapsto> w + c)) (V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 N w k)) n R
      (snd (meval (j + \<delta>) n [] (Mapping.update ?pn (replicate c \<alpha>) ?dbe) \<rho>1)) \<psi>1 \<and>
    list_all2 (\<lambda>k'. qtable n (FV \<psi>1) (mem_restr R)
      (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 N w k), v, k'\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [pR1..<jpsic]
      (fst (meval (j + \<delta>) n [] (Mapping.update ?pn (replicate c \<alpha>) ?dbe) \<rho>1))"
    if \<alpha>: "qtable m (FV \<phi>1) (mem_restr UNIV) (\<lambda>v. \<langle>\<sigma>, V, v, k\<rangle> \<Turnstile>\<^sub>M \<phi>1) \<alpha>" for \<alpha> k
  proof -
    have envs: "wf_envs (S(?pn \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1))) \<sigma> (j + \<delta>) 0 (P'(?pn \<mapsto> w))
      (P'(?pn \<mapsto> w + c)) (V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 N w k))
      (Mapping.update ?pn (replicate c \<alpha>) ?dbe)"
    proof (rule wf_envs_update_frz[OF wf_envs_empty[OF MFrz.prems(2)] fv safe1 wty1])
      show "list_all2 (\<lambda>k' Y. Y = map Some ` {v. length v = m \<and> frz_cv \<sigma> V \<phi>1 N w k v k'})
        [w..<w + c] (replicate c \<alpha>)"
        using qtable_frz_alpha[OF \<alpha> fv(2)] by (auto simp: list_all2_conv_all_nth frz_cv_ge)
    qed (use w_le c_le frz_val_sat in auto)
    obtain us \<rho>' where ev: "meval (j + \<delta>) n [] (Mapping.update ?pn (replicate c \<alpha>) ?dbe) \<rho>1 = (us, \<rho>')"
      by (cases "meval (j + \<delta>) n [] (Mapping.update ?pn (replicate c \<alpha>) ?dbe) \<rho>1")
    show ?thesis
      using MFrz(3)[OF size_\<rho>1 conjunct1[OF IH\<rho>[of "\<lambda>_. Some k"]] envs wty2] ev
      by (simp add: pR1_def jpsic_def fun_upd_def)
  qed
  note cp_res = conjunct2[OF cp_full]
  define L where "L = jpsic - rb0"
  define k0 where "k0 = jfrzM - rb0"
  have replay: "\<exists>us \<rho>'. cp \<alpha> = (us, \<rho>') \<and> length us = L" if "\<alpha> \<in> set \<alpha>s1" for \<alpha>
  proof -
    from \<alpha>s1_qtab[OF that] obtain k where
      "qtable m (FV \<phi>1) (mem_restr UNIV) (\<lambda>v. \<langle>\<sigma>, V, v, k\<rangle> \<Turnstile>\<^sub>M \<phi>1) \<alpha>" ..
    from cp_res[OF this] show ?thesis
      using len_rb1 rb0_le pR1_jpsic by (auto simp: cp_eq L_def dest!: list_all2_lengthD)
  qed
  \<comment> \<open>the live copy: the copy of the first frozen table, fed the new time points\<close>
  define lr where "lr = (case lv of None \<Rightarrow> None | Some g \<Rightarrow>
    if zs0_out = [] \<and> \<alpha>s1 \<noteq> [] then Some (g, meval (j + \<delta>) n ?ts
      (Mapping.update ?pn (replicate (length ?ts) (hd \<alpha>s1)) db) \<rho>L) else None)"
  have jpsij_le: "jpsij \<le> jpsij'"
    unfolding jpsij_def jpsij'_def using pm pm' rm
    by (intro progress_mono_gen[OF le_add1]) (auto intro!: rel_mapping_map_upd)
  have nopo_jpsic: "jpsic = jpsij'" if "\<not> po"
    using w_le that by (simp add: c_def frz_cut_def jpsic_def jpsij'_def)
  have lr_facts: "\<exists>wL NL. \<not> po \<and> (\<forall>k<wL. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz0)) \<and>
      jfrz0 = jpsij + g \<and> zs0_out = [] \<and> \<alpha>s1 \<noteq> [] \<and>
      wf_mformula \<sigma> (j + \<delta>) (P'(?pn \<mapsto> j + \<delta>)) (V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz0)) n R st \<psi>1 \<and>
      list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R)
        (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz0), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [jpsij..<jpsij'] us"
    if "lr = Some (g, us, st)" for g us st
  proof -
    from that have lv: "lv = Some g" and cond: "zs0_out = [] \<and> \<alpha>s1 \<noteq> []" and
      ev: "meval (j + \<delta>) n ?ts (Mapping.update ?pn (replicate (length ?ts) (hd \<alpha>s1)) db) \<rho>L = (us, st)"
      by (auto simp: lr_def split: option.splits if_splits)
    from live[OF lv] obtain wL NL where npo: "\<not> po"
      and winL: "\<forall>k<wL. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz0)"
      and gap: "jfrz0 = jpsij + g"
      and wfL: "wf_mformula \<sigma> j (P(?pn \<mapsto> j)) (V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz0)) n R \<rho>L \<psi>1"
      by (auto simp: jpsij_def)
    have wL_le: "wL \<le> jfrz0"
      by (rule frz_win_le[OF winL])
    have jfrz0_j: "jfrz0 \<le> j"
      unfolding jfrz0_eq by (rule progress_le_gen[OF pm])
    have hd_q: "qtable m (FV \<phi>1) (mem_restr UNIV) (\<lambda>v. \<langle>\<sigma>, V, v, jfrz0\<rangle> \<Turnstile>\<^sub>M \<phi>1) (hd \<alpha>s1)"
      using qtab_\<alpha>s1[of 0] cond by (simp add: hd_conv_nth jfrzM_def)
    have envs: "wf_envs (S(?pn \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1))) \<sigma> j \<delta> (P(?pn \<mapsto> j)) (P'(?pn \<mapsto> j + \<delta>))
      (V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz0))
      (Mapping.update ?pn (replicate (length ?ts) (hd \<alpha>s1)) db)"
    proof (rule wf_envs_update_frz[OF MFrz.prems(2) fv safe1 wty1])
      show "list_all2 (\<lambda>k Y. Y = map Some ` {v. length v = m \<and> frz_cv \<sigma> V \<phi>1 NL wL jfrz0 v k})
        [j..<j + \<delta>] (replicate (length ?ts) (hd \<alpha>s1))"
        using qtable_frz_alpha[OF hd_q fv(2)] wL_le jfrz0_j
        by (auto simp: list_all2_conv_all_nth frz_cv_ge)
    qed (auto dest: frz_val_sat)
    show ?thesis
      using MFrz(4)[OF wfL envs wty2] ev npo winL gap cond
      by (auto simp: jpsij_def jpsij'_def fun_upd_def)
  qed
  have lr_iff: "case lr of None \<Rightarrow> True | Some (g, us, st) \<Rightarrow>
    \<alpha>s1 \<noteq> [] \<and> (length us \<le> g \<longleftrightarrow> length (fst (cp (hd \<alpha>s1))) \<le> k0)"
  proof (cases lr)
    case (Some x)
    then obtain g us st where lr: "lr = Some (g, us, st)"
      by (cases x) auto
    from lr_facts[OF lr] have npo: "\<not> po" and gap: "jfrz0 = jpsij + g"
      and cond: "zs0_out = [] \<and> \<alpha>s1 \<noteq> []" and len_us: "length us = jpsij' - jpsij"
      by (auto dest: list_all2_lengthD)
    have "length (fst (cp (hd \<alpha>s1))) = L"
      using replay[OF hd_in_set[OF conjunct2[OF cond]]] by auto
    then show ?thesis
      using cond gap len_us jpsij_le nopo_jpsic[OF npo] rb0_le pR1_jpsic unfolding lr
      by (auto simp: L_def k0_def jfrzM_def)
  qed simp
  obtain ysL \<alpha>s2 lv1 where els: "frz_live_step cp k0 \<alpha>s1 lr = (ysL, \<alpha>s2, lv1)"
    by (metis prod_cases3)
  obtain ys where ef: "freeze_meval0 cp k0 \<alpha>s1 = (ys, \<alpha>s2)" and len_ysL: "length ys = length ysL"
    and nth_ysL: "\<forall>i<length ysL. ysL ! i = (case lr of Some (g, us, _) \<Rightarrow> if i = 0 then us ! g else ys ! i
      | None \<Rightarrow> ys ! i)"
    using frz_live_step_spec(1)[OF els lr_iff] by blast
  note lv1_cases = frz_live_step_spec(2)[OF els lr_iff]
  note lr_len = frz_live_step_spec(3)[OF els lr_iff]
  have diag: "length ys = min (length \<alpha>s1) (L - k0) \<and>
      (\<forall>i < length ys. ys ! i = fst (cp (\<alpha>s1 ! i)) ! (k0 + i))"
    by (rule freeze_meval0_diagonal[OF ef replay])
      (use jfrzM_jpsic rb0_le in \<open>auto simp: L_def k0_def jfrzM_def\<close>)
  have len_ys: "length ys = min (jphi' - jfrzM) (jpsij' - jfrzM)"
  proof -
    have "length ys = min (jphi' - jfrzM) (jpsic - jfrzM)"
      using diag rb0_le unfolding len_\<alpha>s1 L_def k0_def jfrzM_def by auto
    also have "\<dots> = min jphi' jpsic - jfrzM"
      by linarith
    finally show ?thesis
      unfolding jpsic_min by linarith
  qed
  define jfrz1 where "jfrz1 = jfrzM + length ys"
  have jfrz1_eq: "jfrz1 = jfrz'"
    using frz_eq' jfrz_le jpsi0'_jpsij' unfolding jfrz1_def len_ys jfrzM_eq
    by (auto split: if_splits)
  have ys_rows: "list_all2 good [jfrzM..<jfrz1] ys"
  proof (unfold list_all2_conv_all_nth, intro conjI allI impI)
    show "length [jfrzM..<jfrz1] = length ys"
      unfolding jfrz1_def by simp
  next
    fix i
    assume "i < length [jfrzM..<jfrz1]"
    then have i: "i < length ys"
      unfolding jfrz1_def by simp
    then have i\<alpha>: "i < length \<alpha>s1" and iL: "k0 + i < L"
      using diag by auto
    let ?k = "jfrzM + i"
    have jfrz0_k: "jfrz0 \<le> ?k"
      by (simp add: jfrzM_def)
    let ?us = "fst (meval (j + \<delta>) n [] (Mapping.update ?pn (replicate c (\<alpha>s1 ! i)) ?dbe) \<rho>1)"
    have us: "list_all2 (\<lambda>k'. qtable n (FV \<psi>1) (mem_restr R)
      (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 N w ?k), v, k'\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [pR1..<jpsic] ?us"
      by (rule cp_res[OF qtab_\<alpha>s1[OF i\<alpha>]])
    have ys_i: "ys ! i = (rb1 @ ?us) ! (k0 + i)"
      using diag i by (simp add: cp_eq)
    show "good ([jfrzM..<jfrz1] ! i) (ys ! i)"
    proof (cases "k0 + i < length rb1")
      case True
      then have "good (rb0 + (k0 + i)) (rb1 ! (k0 + i))"
        using rb1_good jfrz0_k rb0_le by (auto simp: list_all2_conv_all_nth k0_def jfrzM_def)
      then show ?thesis
        using True i rb0_le unfolding ys_i jfrz1_def by (simp add: nth_append k0_def jfrzM_def)
    next
      case False
      then have idx: "k0 + i - length rb1 < length [pR1..<jpsic]" and
        pos: "[pR1..<jpsic] ! (k0 + i - length rb1) = ?k"
        using iL len_rb1 rb0_le pR1_jpsic by (auto simp: L_def k0_def jfrzM_def)
      have "qtable n (FV \<psi>1) (mem_restr R)
        (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 N w ?k), v, ?k\<rangle> \<Turnstile>\<^sub>M \<psi>1) (?us ! (k0 + i - length rb1))"
        using list_all2_nthD[OF us idx] unfolding pos .
      then have "good ?k (?us ! (k0 + i - length rb1))"
        unfolding good_def fv_Frz[symmetric]
        by (intro qtable_Frz_window[where w = w and i = ?k and Q = "frz_cv \<sigma> V \<phi>1 N w ?k"])
          (simp_all add: fv(1) frz_cv_ge frz_win_mono[OF win_old[unfolded d_eq] jfrz0_k])
      then show ?thesis
        using False i unfolding ys_i jfrz1_def by (simp add: nth_append)
    qed
  qed
  have ysL_rows: "list_all2 good [jfrzM..<jfrz1] ysL"
  proof (unfold list_all2_conv_all_nth, intro conjI allI impI)
    show "length [jfrzM..<jfrz1] = length ysL"
      using len_ysL unfolding jfrz1_def by simp
  next
    fix i
    assume "i < length [jfrzM..<jfrz1]"
    then have i: "i < length ysL" and i': "i < length ys"
      using len_ysL unfolding jfrz1_def by simp_all
    show "good ([jfrzM..<jfrz1] ! i) (ysL ! i)"
    proof (cases "\<exists>g us st. lr = Some (g, us, st) \<and> i = 0")
      case False
      then have "ysL ! i = ys ! i"
        using nth_ysL i by (auto split: option.splits)
      then show ?thesis
        using list_all2_nthD[OF ys_rows, of i] i' unfolding jfrz1_def by simp
    next
      case True
      then obtain g us st where lr: "lr = Some (g, us, st)" and i0: "i = 0"
        by blast
      from lr_facts[OF lr] obtain wL NL where
        winL: "\<forall>k<wL. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz0)" and
        gap: "jfrz0 = jpsij + g" and cond: "zs0_out = [] \<and> \<alpha>s1 \<noteq> []" and
        us: "list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R)
          (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz0), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [jpsij..<jpsij'] us"
        by blast
      have g: "g < length us"
        using lr_len[OF lr] i by (cases ysL) auto
      have idx: "g < length [jpsij..<jpsij']" and pos: "[jpsij..<jpsij'] ! g = jfrz0"
        using g us gap by (auto dest: list_all2_lengthD)
      have "qtable n (FV \<psi>1) (mem_restr R)
        (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz0), v, jfrz0\<rangle> \<Turnstile>\<^sub>M \<psi>1) (us ! g)"
        using list_all2_nthD[OF us idx] unfolding pos .
      then have "good jfrz0 (us ! g)"
        unfolding good_def fv_Frz[symmetric]
        by (intro qtable_Frz_window[where w = wL and i = jfrz0 and Q = "frz_cv \<sigma> V \<phi>1 NL wL jfrz0"]) (simp_all add: fv(1) frz_cv_ge winL)
      then show ?thesis
        using nth_ysL i lr i0 cond len_ysL unfolding jfrz1_def jfrzM_def by simp
    qed
  qed
  \<comment> \<open>the window moves forward\<close>
  define tq1 where "tq1 = (if d = \<infinity> then [] else tq @ ?ts)"
  have tq1_eq: "tq1 = (if d = \<infinity> then [] else map (\<tau> \<sigma>) [w..<j + \<delta>])"
    using tq_eq w_le by (simp add: tq1_def upt_add_eq_append'[of w j "j + \<delta>"])
  define a where "a = frz_adv d w jfrz1 (j + \<delta>) tq1"
  have a_facts: "w + a \<le> jfrz1 \<and> (\<forall>k<w + a. enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> jfrz1))"
  proof (cases "d \<noteq> \<infinity> \<and> w \<le> jfrz1 \<and> w < j + \<delta>")
    case True
    define c where "c = min jfrz1 (j + \<delta> - 1)"
    have c: "w \<le> c" "c \<le> jfrz1" "c < j + \<delta>"
      using True by (auto simp: c_def)
    then have tq1: "tq1 = map (\<tau> \<sigma>) [w..<j + \<delta>]" and nth: "tq1 ! (c - w) = \<tau> \<sigma> c"
      using True by (auto simp: tq1_eq)
    let ?P = "\<lambda>t. enat t + d < enat (\<tau> \<sigma> c)"
    have a_eq: "a = length (takeWhile ?P tq1)"
      using True unfolding a_def frz_adv_def c_def[symmetric] nth by simp
    have not_P: "\<not> ?P (\<tau> \<sigma> c)"
      by (simp add: not_less le_iff_add[symmetric])
    have le: "a \<le> c - w"
    proof (rule ccontr)
      assume "\<not> a \<le> c - w"
      then have "c - w < length (takeWhile ?P tq1)"
        by (simp add: a_eq)
      then have "?P (takeWhile ?P tq1 ! (c - w))"
        by (meson nth_mem set_takeWhileD)
      moreover have "takeWhile ?P tq1 ! (c - w) = \<tau> \<sigma> c"
        using \<open>c - w < length (takeWhile ?P tq1)\<close> nth by (simp add: takeWhile_nth)
      ultimately show False
        using not_P by simp
    qed
    have "enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> jfrz1)" if "k < w + a" for k
    proof (cases "k < w")
      case True
      with frz_win_mono[OF win_old] jfrz_le jfrz1_eq show ?thesis
        by auto
    next
      case False
      then have k: "k - w < length (takeWhile ?P tq1)"
        using that by (simp add: a_eq)
      then have "?P (takeWhile ?P tq1 ! (k - w))"
        by (meson nth_mem set_takeWhileD)
      moreover have "takeWhile ?P tq1 ! (k - w) = \<tau> \<sigma> k"
      proof -
        have "k - w < j + \<delta> - w"
          using that le c False by linarith
        then show ?thesis
          using k False unfolding tq1 by (simp add: takeWhile_nth)
      qed
      ultimately have "enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> c)"
        by simp
      also have "\<dots> \<le> enat (\<tau> \<sigma> jfrz1)"
        using c(2) by simp
      finally show ?thesis .
    qed
    with le c show ?thesis
      by auto
  next
    case False
    then have "a = 0"
      unfolding a_def frz_adv_def by auto
    with frz_win_mono[OF win_old] w_jfrz0 jfrz_le jfrz1_eq show ?thesis
      by auto
  qed
  have wa_le: "w + a \<le> jfrz1" and win_new: "\<forall>k<w + a. enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> jfrz1)"
    using a_facts by auto
  have wa_le': "w + a \<le> j + \<delta>"
    using wa_le jfrz1_eq jfrz'_le by simp
  \<comment> \<open>the time points that leave the window are absorbed with a frozen table, or the empty one\<close>
  have \<alpha>s_xs_qtab: "\<forall>\<alpha>\<in>set (\<alpha>s @ xs). \<exists>i. qtable m (FV \<phi>1) (mem_restr UNIV) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>1) \<alpha>"
    using old_queue new_queue
    by (fastforce simp: wf_frz_queue_def frz_qtable_def in_set_conv_nth list_all2_conv_all_nth)
  obtain fl where fl: "frz_fill ng (\<alpha>s @ xs) = map Some ` {v. length v = m \<and>
      (case fl of None \<Rightarrow> False | Some i \<Rightarrow> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>1)}"
    using frz_fill_val[OF \<alpha>s_xs_qtab fv(2)] by blast
  define N' where "N' = (\<lambda>k. if k < w then N k else fl)"
  obtain rs2 \<rho>2 where e\<rho>2: "meval (j + \<delta>) n [] (Mapping.update ?pn (replicate a (frz_fill ng (\<alpha>s @ xs))) ?dbe) \<rho>1 = (rs2, \<rho>2)"
    by (cases "meval (j + \<delta>) n [] (Mapping.update ?pn (replicate a (frz_fill ng (\<alpha>s @ xs))) ?dbe) \<rho>1")
  define pR2 where "pR2 = progress \<sigma> (P'(?pn \<mapsto> w + a)) \<psi>1 (j + \<delta>)"
  have IH\<rho>2: "wf_mformula \<sigma> (j + \<delta>) (P'(?pn \<mapsto> w + a))
      (V(?pn \<mapsto> frz_val \<sigma> V \<phi>1 (\<lambda>k. if k < w + a then N' k else M k))) n R \<rho>2 \<psi>1 \<and>
    list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R)
      (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_val \<sigma> V \<phi>1 (\<lambda>k. if k < w + a then N' k else M k)), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [pR1..<pR2] rs2"
    for M
  proof -
    have eq: "(\<lambda>k. if k < w then N k else if k < w + a then fl else M k) =
      (\<lambda>k. if k < w + a then N' k else M k)"
      by (auto simp: N'_def fun_eq_iff)
    have wf1: "wf_mformula \<sigma> (j + \<delta>) (P'(?pn \<mapsto> w))
      (V(?pn \<mapsto> frz_val \<sigma> V \<phi>1 (\<lambda>k. if k < w + a then N' k else M k))) n R \<rho>1 \<psi>1"
      using conjunct1[OF IH\<rho>[of "\<lambda>k. if k < w + a then fl else M k"]] unfolding eq .
    have envs: "wf_envs (S(?pn \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1))) \<sigma> (j + \<delta>) 0 (P'(?pn \<mapsto> w))
      (P'(?pn \<mapsto> w + a)) (V(?pn \<mapsto> frz_val \<sigma> V \<phi>1 (\<lambda>k. if k < w + a then N' k else M k)))
      (Mapping.update ?pn (replicate a (frz_fill ng (\<alpha>s @ xs))) ?dbe)"
    proof (rule wf_envs_update_frz[OF wf_envs_empty[OF MFrz.prems(2)] fv safe1 wty1])
      show "list_all2 (\<lambda>k Y. Y = map Some ` {v. length v = m \<and>
          frz_val \<sigma> V \<phi>1 (\<lambda>k. if k < w + a then N' k else M k) v k})
        [w..<w + a] (replicate a (frz_fill ng (\<alpha>s @ xs)))"
        by (auto simp: list_all2_conv_all_nth fl N'_def frz_val_def)
    qed (use w_le wa_le' frz_val_sat in auto)
    show ?thesis
      using MFrz(3)[OF size_\<rho>1 wf1 envs wty2] e\<rho>2
      by (simp add: pR1_def pR2_def fun_upd_def)
  qed
  have rs2_good: "list_all2 (\<lambda>k X. jfrz1 \<le> k \<longrightarrow> good k X) [pR1..<pR2] rs2"
  proof -
    have "list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R)
      (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 N' (w + a) i), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [pR1..<pR2] rs2" for i
      using IH\<rho>2[of "\<lambda>_. Some i"] by blast
    then have "list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R)
      (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 N' (w + a) k), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [pR1..<pR2] rs2"
      by (rule list_all2_diag)
    then show ?thesis
    proof (rule list.rel_mono_strong, intro impI)
      fix k X
      assume "qtable n (FV \<psi>1) (mem_restr R)
        (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 N' (w + a) k), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1) X" "jfrz1 \<le> k"
      then show "good k X"
        unfolding good_def fv_Frz[symmetric]
        by (intro qtable_Frz_window[where w = "w + a" and i = k and Q = "frz_cv \<sigma> V \<phi>1 N' (w + a) k"])
          (simp_all add: fv(1) frz_cv_ge frz_win_mono[OF win_new[unfolded d_eq]])
    qed
  qed
  have pR1_pR2: "pR1 \<le> pR2"
    unfolding pR1_def pR2_def by (rule mono_pn) (use wa_le' in simp_all)
  define rb2 where "rb2 = rb1 @ rs2"
  have rb2_good: "list_all2 (\<lambda>k X. jfrz1 \<le> k \<longrightarrow> good k X) [rb0..<pR2] rb2"
    unfolding rb2_def
    by (rule list_all2_upt_append[OF _ rs2_good])
      (use rb1_good rb0_le pR1_pR2 jfrz_le jfrz1_eq in \<open>auto elim!: list.rel_mono_strong\<close>)
  have rb_new: "list_all2 good [min jfrz1 pR2..<pR2] (drop (min jfrz1 pR2 - rb0) rb2)"
  proof -
    have "rb0 \<le> min jfrz1 pR2"
      using rb0_le jfrz_le jfrz1_eq pR1_pR2 by simp
    then have "drop (min jfrz1 pR2 - rb0) [rb0..<pR2] = [min jfrz1 pR2..<pR2]"
      by simp
    with list_all2_dropI[OF rb2_good, of "min jfrz1 pR2 - rb0"]
    have "list_all2 (\<lambda>k X. jfrz1 \<le> k \<longrightarrow> good k X) [min jfrz1 pR2..<pR2] (drop (min jfrz1 pR2 - rb0) rb2)"
      by simp
    then show ?thesis
      by (rule list.rel_mono_strong) auto
  qed
  \<comment> \<open>the step\<close>
  define jpsi0_val1 where "jpsi0_val1 = jpsi0_val + length zs0"
  define jphi1 where "jphi1 = jphi0 + length xs"
  have len_rs: "length rs = pR1 - pR" and len_rs2: "length rs2 = pR2 - pR1"
    using IH\<rho>[of "\<lambda>_. None"] IH\<rho>2[of "\<lambda>_. None"] by (auto dest: list_all2_lengthD)
  have pR_code: "pR + length rs + length rs2 = pR2"
    using pR_le pR1_pR2 len_rs len_rs2 by simp
  \<comment> \<open>the new live copy\<close>
  let ?lvp = "if po then None else lv1"
  have live_new: "\<not> po \<and> (\<exists>wL NL. (\<forall>k<wL. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz1)) \<and>
      jfrz1 = progress \<sigma> (P'(?pn \<mapsto> j + \<delta>)) \<psi>1 (j + \<delta>) + g' \<and>
      wf_mformula \<sigma> (j + \<delta>) (P'(?pn \<mapsto> j + \<delta>)) (V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz1)) n R
        (frz_keep_st ?lvp \<rho>L) \<psi>1)"
    if "frz_keep_lv ?lvp \<rho>L = Some g'" for g'
  proof -
    from that obtain st where npo: "\<not> po" and lv1: "lv1 = Some (g', st)"
      and st: "frz_keep_st ?lvp \<rho>L = st"
      by (auto simp: frz_keep_lv_def frz_keep_st_def split: if_splits option.splits)
    from lv1_cases[unfolded lv1] show ?thesis
    proof (elim disjE exE conjE)
      fix g us st'
      assume lr: "lr = Some (g, us, st')" and ysL: "ysL = []" and len: "length us \<le> g"
        and eq: "Some (g', st) = Some (g - length us, st')"
      from lr_facts[OF lr] obtain wL NL where
        winL: "\<forall>k<wL. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz0)" and
        gap: "jfrz0 = jpsij + g" and cond: "zs0_out = [] \<and> \<alpha>s1 \<noteq> []" and
        wfL: "wf_mformula \<sigma> (j + \<delta>) (P'(?pn \<mapsto> j + \<delta>)) (V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz0)) n R st' \<psi>1"
        and us: "list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R)
          (\<lambda>v. \<langle>\<sigma>, V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz0), v, k\<rangle> \<Turnstile>\<^sub>M \<psi>1)) [jpsij..<jpsij'] us"
        by blast
      have len_us: "length us = jpsij' - jpsij"
        using us by (auto dest: list_all2_lengthD)
      have j1: "jfrz1 = jfrz0"
        using ysL len_ysL cond unfolding jfrz1_def jfrzM_def by simp
      show ?thesis
        using npo winL gap wfL len_us len eq st jpsij_le unfolding j1
        by (intro conjI exI[of _ wL] exI[of _ NL]) (auto simp: jpsij'_def)
    next
      assume "Some (g', st) = (case \<alpha>s2 of [] \<Rightarrow> None
        | \<alpha> # _ \<Rightarrow> (case cp \<alpha> of (us, st) \<Rightarrow> Some (k0 + length ysL - length us, st)))"
      then obtain \<alpha> \<alpha>t where \<alpha>s2: "\<alpha>s2 = \<alpha> # \<alpha>t" and g': "g' = k0 + length ysL - length (fst (cp \<alpha>))"
        and st': "st = snd (cp \<alpha>)"
        by (cases \<alpha>s2) (auto split: prod.splits)
      have dr: "drop (length ys) \<alpha>s1 = \<alpha> # \<alpha>t"
        using freeze_meval0_drop[OF ef] \<alpha>s2 by simp
      then have i: "length ys < length \<alpha>s1"
        by (metis drop_all list.distinct(1) not_le)
      have \<alpha>: "\<alpha> = \<alpha>s1 ! length ys"
        using dr i by (metis hd_drop_conv_nth list.sel(1))
      have q\<alpha>: "qtable m (FV \<phi>1) (mem_restr UNIV) (\<lambda>v. \<langle>\<sigma>, V, v, jfrz1\<rangle> \<Turnstile>\<^sub>M \<phi>1) \<alpha>"
        using qtab_\<alpha>s1[OF i] unfolding \<alpha> jfrz1_def .
      have wc: "w + c = j + \<delta>"
        using npo w_le by (simp add: c_def frz_cut_def)
      have wf_st: "wf_mformula \<sigma> (j + \<delta>) (P'(?pn \<mapsto> j + \<delta>)) (V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 N w jfrz1))
        n R st \<psi>1"
        using conjunct1[OF cp_full[OF q\<alpha>]] unfolding st' cp_eq wc by simp
      have len_cp: "length (fst (cp \<alpha>)) = L"
        using replay[of \<alpha>] \<alpha> i by auto
      have j1: "jfrz1 = jpsij'"
        using i len_ys len_\<alpha>s1 jfrzM_jpsic jpsic_le unfolding jfrz1_def by linarith
      have g'0: "g' = 0"
        using g' len_cp len_ysL j1 nopo_jpsic[OF npo] rb0_le jfrz_le
        unfolding L_def k0_def jfrz1_def jfrzM_def by linarith
      show ?thesis
        using frz_win_mono[OF win_old[unfolded d_eq], of jfrz1] jfrz_le jfrz1_eq wf_st st j1 g'0 npo
        by (intro conjI exI[of _ w] exI[of _ N]) (auto simp: jpsij'_def)
    qed
  qed
  have meq: "meval (j + \<delta>) n ?ts db (MFrz p m \<phi> \<psi> jfrz0 jpsi0_val jphi0 \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
    (zs0_out @ ysL, MFrz p m \<phi>_new \<psi>_new jfrz1 jpsi0_val1 jphi1 \<alpha>s2 \<rho>2 (w + a) (pR + length rs + length rs2)
      (drop a tq1) (drop (min jfrz1 (pR + length rs + length rs2) - rb0) rb2) d po ng
      (frz_keep_lv ?lvp \<rho>L) (frz_keep_st ?lvp \<rho>L))"
    by (simp only: meval.simps Let_def e\<phi> e\<psi>0 e\<rho>1 prod.case zs0_out_def[symmetric] jfrzM_def[symmetric]
        \<alpha>s1_def[symmetric] rb0_def[symmetric] rb1_def[symmetric] c_def[symmetric] cp_def[symmetric]
        k0_def[symmetric] lr_def[symmetric] els len_ysL[symmetric]
        jfrz1_def[symmetric] tq1_def[symmetric] a_def[symmetric] e\<rho>2 rb2_def[symmetric]
        jpsi0_val1_def[symmetric] jphi1_def[symmetric])
  show ?case
    unfolding meq Frz_eq prod.case pR_code
  proof (intro conjI)
    show "wf_mformula \<sigma> (j + \<delta>) P' V n R (MFrz p m \<phi>_new \<psi>_new jfrz1 jpsi0_val1 jphi1 \<alpha>s2 \<rho>2 (w + a) pR2
      (drop a tq1) (drop (min jfrz1 pR2 - rb0) rb2) d po ng (frz_keep_lv ?lvp \<rho>L) (frz_keep_st ?lvp \<rho>L))
      (Formula.Frz p \<phi>1 \<psi>1)"
    proof (rule wf_mformula.Frz[OF wf_\<phi>_new])
      show "\<forall>g. frz_keep_lv ?lvp \<rho>L = Some g \<longrightarrow> \<not> po \<and> (\<exists>wL NL. (\<forall>k<wL. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz1)) \<and>
        jfrz1 = progress \<sigma> (P'(?pn \<mapsto> j + \<delta>)) \<psi>1 (j + \<delta>) + g \<and>
        wf_mformula \<sigma> (j + \<delta>) (P'(?pn \<mapsto> j + \<delta>)) (V(?pn \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz1)) n R
          (frz_keep_st ?lvp \<rho>L) \<psi>1)"
        using live_new by blast
      show "\<forall>i. wf_mformula \<sigma> (j + \<delta>) (P'(?pn \<mapsto> 0)) (V(?pn \<mapsto> \<lambda>w j. \<langle>\<sigma>, V, w, i\<rangle> \<Turnstile> \<phi>1)) n R \<psi>_new \<psi>1"
        using IH\<psi> by blast
      have frz_prog: "progress \<sigma> P' (Formula.Frz p \<phi>1 \<psi>1) (j + \<delta>) =
        progress \<sigma> P (Formula.Frz p \<phi>1 \<psi>1) j + length zs0_out + length ys"
        using jfrz1_eq unfolding jfrz1_def jfrzM_def jfrz'_def jfrz0_eq by simp
      show "wf_frz_state \<sigma> (j + \<delta>) P' V p m \<phi>1 \<psi>1 jphi1 \<alpha>s2"
        unfolding jphi1_def
        by (rule frz_step_post[OF wf_state phi_res[unfolded jphi_def jphi'_def] 
            progress_mono_gen[OF le_add1 pm pm' rm] _ \<alpha>s1_def ef frz_prog])
          (simp add: jfrz0_eq)
      show "jfrz1 = progress \<sigma> P' (Formula.Frz p \<phi>1 \<psi>1) (j + \<delta>)"
        by (simp add: jfrz1_eq jfrz'_def)
      show "jpsi0_val1 = progress \<sigma> (P'(?pn \<mapsto> 0)) \<psi>1 (j + \<delta>)"
        using len_zs0 jpsi0_le by (simp add: jpsi0_val1_def jpsi0_eq jpsi0_def jpsi0'_def)
      show "\<forall>M. wf_mformula \<sigma> (j + \<delta>) (P'(?pn \<mapsto> w + a))
        (V(?pn \<mapsto> frz_val \<sigma> V \<phi>1 (\<lambda>k. if k < w + a then N' k else M k))) n R \<rho>2 \<psi>1"
        using IH\<rho>2 by blast
      show "wf_frz_win \<sigma> (j + \<delta>) P' V n R p m \<phi>1 \<psi>1 jfrz1 (w + a) pR2 (drop a tq1)
        (drop (min jfrz1 pR2 - rb0) rb2) d"
        unfolding wf_frz_win_def
      proof (intro conjI)
        show "drop a tq1 = (if d = \<infinity> then [] else map (\<tau> \<sigma>) [w + a..<j + \<delta>])"
          using tq1_eq by (auto simp: a_def frz_adv_def drop_map)
        show "list_all2 (\<lambda>k. qtable n (FV \<psi>1) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, k\<rangle> \<Turnstile>\<^sub>M Formula.Frz p \<phi>1 \<psi>1))
          [min jfrz1 pR2..<pR2] (drop (min jfrz1 pR2 - rb0) rb2)"
          using rb_new unfolding good_def .
      qed (use wa_le' d_eq win_new in \<open>simp_all add: pR2_def\<close>)
    qed (use fv safe1 safe2 po in simp_all)
  next
    show "list_all2 (\<lambda>i. qtable n (FV (Formula.Frz p \<phi>1 \<psi>1)) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M Formula.Frz p \<phi>1 \<psi>1))
      [progress \<sigma> P (Formula.Frz p \<phi>1 \<psi>1) j..<progress \<sigma> P' (Formula.Frz p \<phi>1 \<psi>1) (j + \<delta>)] (zs0_out @ ysL)"
      unfolding jfrz0_eq[symmetric] jfrz'_def[symmetric] jfrz1_eq[symmetric] fv_Frz
      by (rule list_all2_upt_append[OF zs0_out_rows[unfolded good_def] ysL_rows[unfolded good_def]])
        (simp_all add: jfrzM_def jfrz1_def)
  qed
next
  case (MLetPast p m \<phi>1 \<phi>2 i buf)
  let ?pn = "(p, m)"
  from MLetPast.prems(1) obtain \<phi>1' \<phi>2' 
    where LetPast: "\<phi>' = Formula.LetPast p \<phi>1' \<phi>2'"
      and 1: "wf_mformula \<sigma> j (P(?pn\<mapsto>i)) 
        (V(?pn \<mapsto> letpast_sat (\<lambda>X v i. \<langle>\<sigma>, V(?pn \<mapsto> X), v, i\<rangle> \<Turnstile> \<phi>1'))) m UNIV \<phi>1 \<phi>1'"
      and buf: "case buf of
        None \<Rightarrow> i = letpast_progress \<sigma> P ?pn \<phi>1' j
      | Some Z \<Rightarrow> Suc i = letpast_progress \<sigma> P ?pn \<phi>1' j
          \<and> qtable m (Formula.fv \<phi>1') (mem_restr UNIV)
            (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>1') (map the v) i) Z"
      and fv: "m = Formula.nfv \<phi>1'" "{0..<m} \<subseteq> fv \<phi>1'"
      and 2:  "wf_mformula \<sigma> j (P(?pn \<mapsto> letpast_progress \<sigma> P ?pn \<phi>1' j))
      (V(?pn \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V(?pn \<mapsto> X)) v i \<phi>1'))) n R \<phi>2 \<phi>2'"
      and safe: "safe_letpast ?pn \<phi>1' \<le> PastRec"
      and safe1: "safe_formula \<phi>1'"
      and safe2: "safe_formula \<phi>2'"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MLetPast.prems(3) LetPast obtain E' 
    where wty1: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1')), E' \<turnstile> \<phi>1'" 
      and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1')), E \<turnstile> \<phi>2'"
    unfolding fv by (cases pred: wty_formula) simp_all
  from MLetPast(4) have pred: "pred_mapping (\<lambda> x. x\<le>j) P"
    by auto
  from MLetPast(3) pred LetPast
  have invar:"letpast_meval_invar n V \<sigma> P \<phi>1' m (j+\<delta>) i [] (list_of_option buf) p (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>1 (letpast_progress \<sigma> P ?pn \<phi>1' j)"
    by(auto intro!: letpast_meval_invar_init[where j="j+\<delta>" and ts="(map (\<tau> \<sigma>) [j ..< j + \<delta>])" and \<phi> = "\<phi>1" and \<phi>'= "\<phi>1'", simplified])

  obtain ys' i' buf' \<phi>f \<phi>f1 \<phi>f2 xs' where
    e1: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db (MLetPast p m \<phi>1 \<phi>2 i buf) = (xs', \<phi>f)" and
    e_letpast: "(ys', i', buf', \<phi>f1) = letpast_meval m (j+\<delta>) i [] (list_of_option buf) ?pn (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>1" and
    e2: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) (Mapping.update ?pn ys' db) \<phi>2 = (xs', \<phi>f2)" and
    \<phi>f: "\<phi>f = MLetPast p m \<phi>f1 \<phi>f2 i' buf'"
  proof -
    obtain ys' i' buf' \<phi>f1 where e_letpast: "(ys', i', buf', \<phi>f1) =
        letpast_meval m (j+\<delta>) i [] (list_of_option buf) ?pn (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>1"
      by (metis prod_cases4)
    obtain xs' \<phi>f2 where
      e2: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) (Mapping.update ?pn ys' db) \<phi>2 = (xs', \<phi>f2)"
      by (metis surj_pair)
    show thesis
    proof (rule that[OF _ e_letpast e2 refl])
      show "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db (MLetPast p m \<phi>1 \<phi>2 i buf) =
        (xs', MLetPast p m \<phi>f1 \<phi>f2 i' buf')"
        by (simp add: e_letpast[symmetric] e2)
    qed
  qed
  have pred_alt: "pred_mapping (\<lambda>x. x \<le> j + \<delta> - length (map (\<tau> \<sigma>) [j..<j + \<delta>])) P" 
    using pred by fastforce
  have pred_alt_2: "pred_mapping (\<lambda>x. x \<le> j + \<delta>) P'" 
    using MLetPast.prems(2) wf_envs_P_simps(2) by blast
  have rel_map:  "rel_mapping (\<le>) P P'" 
    using MLetPast.prems(2) by auto
  have wf_form: "wf_mformula \<sigma> (j + \<delta> - length (map (\<tau> \<sigma>) [j..<j + \<delta>])) (P((p, m) \<mapsto> i))
 (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>1'))) m UNIV \<phi>1 \<phi>1'" by (simp add: "1")
  have wf_envs: "wf_envs S \<sigma> (j + \<delta> - length (map (\<tau> \<sigma>) [j..<j + \<delta>])) (length (map (\<tau> \<sigma>) [j..<j + \<delta>])) P P' V db" 
    using MLetPast.prems(2) by force
  have post: "letpast_meval_post n V \<sigma> P' \<phi>1' m (j+\<delta>) i' ys' buf' p \<phi>f1 (letpast_progress \<sigma> P ?pn \<phi>1' j)"
  proof (rule letpast_meval_invar_post[OF safe pred_alt pred_alt_2 rel_map fv wf_form wf_envs _ _ wty1 safe1 invar e_letpast],
      goal_cases)
    case (1 xs db \<phi>_m us P P' V S E)
    \<comment> \<open>the evaluation of @{term \<phi>1} in each iteration is covered by the induction hypothesis,
      either for the new time-points (first iteration) or for no time-points (later iterations)\<close>
    from 1(5) show ?case
    proof
      assume us: "us = []"
      from 1(2,3) have wf: "wf_mformula \<sigma> (j + \<delta>) P V m UNIV \<phi>_m \<phi>1'"
        and envs: "wf_envs S \<sigma> (j + \<delta>) 0 P P' V (Mapping.update (p, m) xs db)"
        by (simp_all add: us)
      from MLetPast.IH(1)[OF 1(1) wf envs 1(4)] show ?case
        by (simp add: us mem_restr_UNIV[THEN eqTrueI, abs_def] split: prod.splits)
    next
      assume us: "us = map (\<tau> \<sigma>) [j..<j + \<delta>]"
      from 1(2,3) have wf: "wf_mformula \<sigma> j P V m UNIV \<phi>_m \<phi>1'"
        and envs: "wf_envs S \<sigma> j \<delta> P P' V (Mapping.update (p, m) xs db)"
        by (simp_all add: us)
      from MLetPast.IH(1)[OF 1(1) wf envs 1(4)] show ?case
        by (simp add: us mem_restr_UNIV[THEN eqTrueI, abs_def] split: prod.splits)
    qed
  qed simp

  from e1 e_letpast e2 have
    wf_letpast: "wf_mformula \<sigma> (j+\<delta>) (P'(?pn\<mapsto>i')) (V(?pn \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V(?pn \<mapsto> X)) v i \<phi>1'))) m UNIV \<phi>f1 \<phi>1'" and
    buf': "case buf' of
        None \<Rightarrow> i' = letpast_progress \<sigma> P' ?pn \<phi>1' (j+\<delta>)
      | Some Z \<Rightarrow> Suc i' = letpast_progress \<sigma> P' ?pn \<phi>1' (j+\<delta>) \<and>
          qtable m (Formula.fv \<phi>1') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>1') (map the v) i') Z" and
    list_letpast_full: "list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>1') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V(?pn \<mapsto> X)) v i \<phi>1') (map the v) i))
      [letpast_progress \<sigma> P ?pn \<phi>1' j..<letpast_progress \<sigma> P' ?pn \<phi>1' (j+\<delta>)] ys'"
    using post by (auto simp add: letpast_meval_post_def)
  from MLetPast(2)[OF 2 wf_envs_update_sup[OF MLetPast.prems(2) fv list_letpast_full safe1 wty1] wty2] e1 fv safe e_letpast \<phi>f buf' e2 wf_letpast safe1 safe2
  show ?case unfolding LetPast
    by (auto simp: fun_upd_def Let_def intro!: wf_mformula.LetPast simp del: fun_upd_apply)
next
  case (MAnd A_\<phi> \<phi> pos A_\<psi> \<psi> buf)
  from MAnd.prems(1) obtain \<phi>'' \<psi>'' where
    wf\<phi>: "wf_mformula \<sigma> j P V n R \<phi> \<phi>''" and wf\<psi>: "wf_mformula \<sigma> j P V n R \<psi> \<psi>''"
    and pos: "if pos then \<phi>' = Formula.And \<phi>'' \<psi>''
      else \<phi>' = Formula.And \<phi>'' (Formula.Neg \<psi>'') \<and> Formula.fv \<psi>'' \<subseteq> Formula.fv \<phi>''"
    and buf: "wf_mbuf2' \<sigma> P V j n R \<phi>'' \<psi>'' buf"
    and safe: "safe_formula \<phi>''" "safe_formula \<psi>''"
    and A: "A_\<phi> = Formula.fv \<phi>''" "A_\<psi> = Formula.fv \<psi>''"
    by (cases rule: wf_mformula.cases) auto
  from pos have \<phi>'_eq: "\<phi>' = (if pos then \<phi>'' \<and>\<^sub>F \<psi>'' else \<phi>'' \<and>\<^sub>F \<not>\<^sub>F \<psi>'')"
    and fv_sub: "\<not> pos \<Longrightarrow> Formula.fv \<psi>'' \<subseteq> Formula.fv \<phi>''"
    by (cases pos; simp)+
  have wty_And: "S, E \<turnstile> Formula.And \<phi>'' (if pos then \<psi>'' else Formula.Neg \<psi>'')"
    using MAnd.prems(3) unfolding \<phi>'_eq by (cases pos) simp_all
  from wty_And have wty\<phi>: "S, E \<turnstile> \<phi>''"
    by (rule wty_formula_AndD(1))
  from wty_formula_AndD(2)[OF wty_And] have wty\<psi>: "S, E \<turnstile> \<psi>''"
    by (cases pos) (auto dest: wty_formula_NegD)
  obtain xs \<phi>n where eq_\<phi>: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi> = (xs, \<phi>n)"
    by (elim prod.exhaust)
  obtain ys \<psi>n where eq_\<psi>: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<psi> = (ys, \<psi>n)"
    by (elim prod.exhaust)
  obtain zs buf' where eq_buf:
    "mbuf2_take (\<lambda>r1 r2. bin_join n A_\<phi> r1 pos A_\<psi> r2) (mbuf2_add xs ys buf) = (zs, buf')"
    by (elim prod.exhaust)
  note IH\<phi> = MAnd.IH(1)[OF wf\<phi> MAnd.prems(2) wty\<phi>, unfolded eq_\<phi> prod.case]
  note IH\<psi> = MAnd.IH(2)[OF wf\<psi> MAnd.prems(2) wty\<psi>, unfolded eq_\<psi> prod.case]
  note buf_new = mbuf2_take_add'[OF eq_buf buf wf_envs_P_simps(3)[OF MAnd.prems(2)]
      IH\<phi>[THEN conjunct2] IH\<psi>[THEN conjunct2] le_add1 wf_envs_P_simps(1,2)[OF MAnd.prems(2)]]
  have meval_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db (MAnd A_\<phi> \<phi> pos A_\<psi> \<psi> buf) =
      (zs, MAnd A_\<phi> \<phi>n pos A_\<psi> \<psi>n buf')"
    by (simp only: meval.simps Let_def eq_\<phi> eq_\<psi> eq_buf prod.case)
  have wf_new: "wf_mformula \<sigma> (j + \<delta>) P' V n R (MAnd A_\<phi> \<phi>n pos A_\<psi> \<psi>n buf') \<phi>'"
    unfolding A
    by (rule wf_mformula.And[OF IH\<phi>[THEN conjunct1] IH\<psi>[THEN conjunct1] pos buf_new(1) safe])
  have prog: "progress \<sigma> Q \<phi>' k = min (progress \<sigma> Q \<phi>'' k) (progress \<sigma> Q \<psi>'' k)" for Q k
    by (simp add: \<phi>'_eq)
  have step: "qtable n (Formula.fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')
      (bin_join n A_\<phi> X pos A_\<psi> Y)"
    if "qtable n (Formula.fv \<phi>'') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'') X"
      and "qtable n (Formula.fv \<psi>'') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>'') Y" for i X Y
    unfolding A by (rule qtable_bin_join[OF that fv_sub]) (auto simp: \<phi>'_eq sat_the_restrict)
  have out: "list_all2 (\<lambda>i. qtable n (Formula.fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'))
      [progress \<sigma> P \<phi>' j..<progress \<sigma> P' \<phi>' (j + \<delta>)] zs"
    unfolding prog
    by (rule list.rel_mono_strong[OF buf_new(2)]) (auto simp del: bin_join.simps intro: step)
  show ?case
    unfolding meval_eq prod.case using wf_new out by (rule conjI)
next
  case (MAndAssign \<phi> conf)
  from MAndAssign.prems obtain \<phi>'' x t \<psi>'' where
    wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db" and
    \<phi>'_eq: "\<phi>' = formula.And \<phi>'' \<psi>''" and
    wf_\<phi>: "wf_mformula \<sigma> j P V n R \<phi> \<phi>''" and
    "x < n" and
    "x \<notin> fv \<phi>''" and
    fv_t_subset: "fv_trm t \<subseteq> fv \<phi>''" and
    conf: "(x, t) = conf" and
    \<psi>''_eqs: "\<psi>'' = formula.Eq (trm.Var x) t \<or> \<psi>'' = formula.Eq t (trm.Var x)" and
    safe: "safe_formula \<phi>''"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MAndAssign.prems(3) obtain "S, E \<turnstile> \<phi>''" and "S, E \<turnstile> \<psi>''"
    by (cases rule: wty_formula.cases) (auto simp: \<phi>'_eq)
  with wf_\<phi> wf_envs obtain xs \<phi>\<^sub>n where
    meval_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi> = (xs, \<phi>\<^sub>n)" and
    wf_\<phi>\<^sub>n: "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<phi>''" and
    xs: "list_all2 (\<lambda>i. qtable n (fv \<phi>'') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>''))
        [progress \<sigma> P \<phi>'' j..<progress \<sigma> P' \<phi>'' (j + \<delta>)] xs"
    by (auto dest!: MAndAssign.IH)
  have progress_eqs:
      "progress \<sigma> P \<phi>' j = progress \<sigma> P \<phi>'' j"
      "progress \<sigma> P' \<phi>' (j + \<delta>) = progress \<sigma> P' \<phi>'' (j + \<delta>)"
    using \<psi>''_eqs wf_envs_progress_le[OF wf_envs, of \<phi>''] unfolding \<phi>'_eq by auto
  show ?case proof (simp add: meval_eq, intro conjI)
    show "wf_mformula \<sigma> (j + \<delta>) P' V n R (MAndAssign \<phi>\<^sub>n conf) \<phi>'"
      unfolding \<phi>'_eq
      by (rule wf_mformula.AndAssign) fact+
  next
    show "list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'))
        [progress \<sigma> P \<phi>' j..<progress \<sigma> P' \<phi>' (j + \<delta>)] (map ((`) (eval_assignment conf)) xs)"
      unfolding list.rel_map progress_eqs conf[symmetric] eval_assignment.simps
      using xs
    proof (rule list.rel_mono_strong)
      fix i X
      assume qtable: "qtable n (fv \<phi>'') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'') X"
      then show "qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')
          ((\<lambda>y. y[x := Some (meval_trm t y)]) ` X)"
      proof (rule qtable_assign)
        show "x < n" by fact
        show "insert x (fv \<phi>'') = fv \<phi>'"
          using \<psi>''_eqs fv_t_subset by (auto simp: \<phi>'_eq)
        show "x \<notin> fv \<phi>''" by fact
      next
        fix v
        assume wf_v: "wf_tuple n (fv \<phi>') v" and "mem_restr R v"
        then show "mem_restr R (restrict (fv \<phi>'') v)" by simp

        assume sat: "Formula.sat \<sigma> V (map the v) i \<phi>'"
        then have A: "Formula.sat \<sigma> V (map the (restrict (fv \<phi>'') v)) i \<phi>''" (is ?A)
          by (simp add: \<phi>'_eq sat_the_restrict)
        have "map the v ! x = Formula.eval_trm (map the v) t"
          using sat \<psi>''_eqs by (auto simp: \<phi>'_eq)
        also have "... = Formula.eval_trm (map the (restrict (fv \<phi>'') v)) t"
          using fv_t_subset by (auto simp: map_the_restrict intro!: eval_trm_fv_cong)
        finally have "map the v ! x = meval_trm t (restrict (fv \<phi>'') v)"
          using meval_trm_eval_trm[of n "fv \<phi>''" "restrict (fv \<phi>'') v" t]
            fv_t_subset wf_v wf_mformula_wf_set[unfolded wf_set_def, OF wf_\<phi>]
          by (fastforce simp: \<phi>'_eq intro!: wf_tuple_restrict)
        then have B: "v ! x = Some (meval_trm t (restrict (fv \<phi>'') v))" (is ?B)
          using \<psi>''_eqs wf_v \<open>x < n\<close> by (auto simp: wf_tuple_def \<phi>'_eq)
        from A B show "?A \<and> ?B" ..
      next
        fix v
        assume wf_v: "wf_tuple n (fv \<phi>'') v" and "mem_restr R v"
          and sat: "Formula.sat \<sigma> V (map the v) i \<phi>''"
        let ?v = "v[x := Some (meval_trm t v)]"
        from sat have A: "Formula.sat \<sigma> V (map the ?v) i \<phi>''"
          using \<open>x \<notin> fv \<phi>''\<close> by (simp add: sat_the_update)
        have "y \<in> fv_trm t \<Longrightarrow> x \<noteq> y" for y
          using fv_t_subset \<open>x \<notin> fv \<phi>''\<close> by auto
        then have B: "Formula.sat \<sigma> V (map the ?v) i \<psi>''"
          using \<psi>''_eqs meval_trm_eval_trm[of n "fv \<phi>''" v t] \<open>x < n\<close>
            fv_t_subset wf_v wf_mformula_wf_set[unfolded wf_set_def, OF wf_\<phi>]
          by (auto simp: wf_tuple_def map_update intro!: eval_trm_fv_cong)
        from A B show "Formula.sat \<sigma> V (map the ?v) i \<phi>'"
          by (simp add: \<phi>'_eq)
      qed
    qed
  qed
next
  case (MAndTrigger args X\<^sub>\<phi> \<phi>' \<gamma>' \<beta>' buf1 buf2 nts aux db P P' V n R z)
  from MAndTrigger.prems obtain \<phi> \<gamma> \<alpha> I \<beta>
    where z_eq: "z = formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
      and wf_phi: "wf_mformula \<sigma> j P V n R \<phi>' \<phi>"
      and wf_gamma: "wf_mformula \<sigma> j P V n R \<gamma>' \<gamma>"
      and wf_beta: "wf_mformula \<sigma> j P V n R \<beta>' \<beta>"
      and wf_buf1: "wf_mbuft2' \<sigma> P V j n R \<phi> \<alpha> I \<beta> buf1" 
      and wf_buf2: "wf_mbuf2' \<sigma> P V j n R \<gamma> \<beta> buf2"
      and pos: "if args_pos args then \<alpha> = \<gamma> else \<alpha> = Formula.Neg \<gamma>"
      and pos_eq: "safe_formula \<alpha> = args_pos args" 
      and fv_t_subset: "FV (\<alpha> \<^bold>T I \<beta>) \<subseteq> FV \<phi>" 
      and args_ivl: "args_ivl args = I" 
      and args_n: "args_n args = n" 
      and args_L: "args_L args = Formula.fv \<gamma>" 
      and args_R: "args_R args = Formula.fv \<beta>"
      and fv_l_n: "\<forall>x\<in>fv \<beta>. x < n" and fv_phi_eq: "X\<^sub>\<phi> = fv \<phi>"
      and nts: "wf_ts \<sigma> P j \<gamma> \<beta> nts" 
      and fvi_subset: "if mem I 0 then fv \<gamma> \<subseteq> fv \<beta> else fv \<gamma> = fv \<beta>" 
      and aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux (progress \<sigma> P (\<alpha> \<^bold>T I \<beta>) j)"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)    
  have "S, E \<turnstile> \<phi>" "S, E \<turnstile> \<alpha>" "S, E \<turnstile> \<beta>" "S, E \<turnstile> \<gamma>"
    using wty_formula_AndD[OF MAndTrigger.prems(3)[unfolded z_eq]]
      wty_formula_TriggerD[of S E \<alpha> I \<beta>] pos wty_formula_NegD[of S E \<gamma>]
    by (auto elim!: wty_formulaD split: if_splits)
  define z' where "z' \<equiv> MAndTrigger X\<^sub>\<phi> \<phi>' buf1 args \<gamma>' \<beta>' buf2 nts aux"
  then obtain zs and z''
    where zs_def: "zs = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db z')" 
      and z''_def: "z'' = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db z')"
      and ztuple_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db z' = (zs, z'')"
    by fastforce
  obtain xs and \<phi>''
    where xs_def: "xs = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>')" 
      and phi''_def: "\<phi>'' = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>')"
      and xtuple_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>' = (xs, \<phi>'')"
    by fastforce
  have IH_phi: "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>'' \<phi>"
    "list_all2 (\<lambda>i. qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>)) 
      [Progress.progress \<sigma> P \<phi> j..<Progress.progress \<sigma> P' \<phi> (j + \<delta>)] xs"
    using MAndTrigger.IH(1)[OF wf_phi MAndTrigger.prems(2) \<open>S, E \<turnstile> \<phi>\<close>] xtuple_eq
    by auto
  obtain as and \<gamma>''
    where as_def: "as = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<gamma>')"
      and gamma''_def: "\<gamma>'' = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<gamma>')"
      and atuple_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<gamma>' = (as, \<gamma>'')"
    by fastforce
  have IH_gamma: "wf_mformula \<sigma> (j + \<delta>) P' V n R \<gamma>'' \<gamma>"
    "list_all2 (\<lambda>i. qtable n (fv \<gamma>) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<gamma>)) 
      [Progress.progress \<sigma> P \<gamma> j..<Progress.progress \<sigma> P' \<gamma> (j + \<delta>)] as"
    using MAndTrigger.IH(2)[OF wf_gamma MAndTrigger.prems(2) \<open>S, E \<turnstile> \<gamma>\<close>] atuple_eq
    by auto
  obtain bs and \<beta>''
    where bs_def: "bs = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<beta>')"
      and beta''_def: "\<beta>'' = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<beta>')"
      and btuple_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<beta>' = (bs, \<beta>'')"
    by fastforce
  have IH_beta:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<beta>'' \<beta>"
    "list_all2 (\<lambda>i. qtable n (fv \<beta>) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<beta>)) 
      [Progress.progress \<sigma> P \<beta> j..<Progress.progress \<sigma> P' \<beta> (j + \<delta>)] bs"
    using MAndTrigger.IH(3)[OF wf_beta MAndTrigger.prems(2) \<open>S, E \<turnstile> \<beta>\<close>] btuple_eq
    by auto

  have args_props:
    "args_n args = n"
    "args_R args = fv \<alpha> \<union> fv \<beta>"
    "fv \<gamma> = fv \<alpha>"
    using pos args_n args_L args_R fvi_subset
    by (auto split: if_splits)

  define tuple where "tuple = mbuf2T_take (\<lambda>r1 r2 t (zs, aux). let
    aux = update_mtaux args t r1 r2 aux;
    (fv_z, z) = result_mtaux args aux
    in (zs @ [(fv_z, z)], aux)
  ) ([], aux) (mbuf2_add as bs buf2) (nts @ map (\<tau> \<sigma>) [j..<j + \<delta>])"
  
  define zs' where "zs' = fst (fst tuple)"
  define aux' where "aux' = snd (fst tuple)"
  define buf2' where "buf2' = fst (snd tuple)"
  define nts' where "nts' = snd (snd tuple)"

  have tuple_eq: "tuple = ((zs', aux'), buf2', nts')"
    unfolding zs'_def aux'_def buf2'_def nts'_def Let_def
    by auto

  have pred_mapping:
    "pred_mapping (\<lambda>i. i \<le> j) P"
    "pred_mapping (\<lambda>i. i \<le> j + \<delta>) P'"
    "rel_mapping (\<le>) P P'"
    using MAndTrigger.prems(2)
    by auto

  from MAndTrigger.prems(2) have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> P \<gamma> j) (progress \<sigma> P \<beta> j)..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts
    unfolding wf_ts_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_le[THEN min.coboundedI1] list.rel_map
      intro!: list_all2_appendI list.rel_refl)

  have wf_buf_ts_trigger:
    "wf_mbuf2' \<sigma> P' V (j + \<delta>) n R \<gamma> \<beta> buf2'"
    "wf_ts \<sigma> P' (j + \<delta>) \<gamma> \<beta> nts'"
    using mbuf2T_take_add'[OF tuple_eq[unfolded tuple_def] pred_mapping 
        wf_buf2 nts_snoc IH_gamma(2) IH_beta(2)] by auto
  have \<alpha>_\<gamma>_props: "Formula.fv \<alpha> = Formula.fv \<gamma>" "progress \<sigma> P \<alpha> j = progress \<sigma> P \<gamma> j"
  "progress \<sigma> P' \<alpha> j = progress \<sigma> P' \<gamma> j" for j
    using pos
    by (simp_all split: if_splits)

  have update_trigger:
    "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (snd (zs', aux')) (progress \<sigma> P' (\<alpha> \<^bold>T I \<beta>) (j + \<delta>))
  \<and> list_all2 (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (\<alpha> \<^bold>T I \<beta>) 
      \<and> qtable n dfvs (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<alpha> \<^bold>T I \<beta>) r)
    [progress \<sigma> P (\<alpha> \<^bold>T I \<beta>) j..<progress \<sigma> P' (\<alpha> \<^bold>T I \<beta>) (j + \<delta>)] (fst (zs', aux'))"
    unfolding progress_simps \<alpha>_\<gamma>_props
  proof (rule mbuf2T_take_add_induct'[where j=j and j'="j + \<delta>" and z'="(zs', aux')",
        OF tuple_eq[unfolded tuple_def] pred_mapping wf_buf2 nts_snoc IH_gamma(2) IH_beta(2)],
      goal_cases _ base step) (*  *)
  next
    case base
    then show ?case
      using aux \<alpha>_\<gamma>_props base
      unfolding progress_simps
      by auto
  next
    case (step k X Y acc)
    define zs where "zs = fst acc"
    define aux where "aux = snd acc"
    have z_eq: "acc = (zs, aux)"
      unfolding zs_def aux_def
      by auto

    have table:
      "table (args_n args) (args_L args) X"
      "table (args_n args) (args_R args) Y"
      using step(4,5) args_n args_L args_R
      unfolding qtable_def
      by auto

    have wf_trigger: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux k"
      using step(6)
      unfolding aux_def
      by auto
    then have fv_subset: "fv \<gamma> \<subseteq> fv \<beta> "
      unfolding wf_trigger_aux_def
      by auto

    have wf_trigger_aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (update_mtaux args (\<tau> \<sigma> k) X Y aux) (Suc k)"
      using update_trigger[OF wf_trigger step(4,5) args_n args_L args_R]
      by auto

    then obtain auxlist' where
      valid_mtaux: "valid_mtaux args (\<tau> \<sigma> k) (update_mtaux args (\<tau> \<sigma> k) X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')" and
      sorted_wrt: "sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist'" and
      auxlist_len: "length auxlist' = Suc k" and
      auxlist_props: "(\<forall>(i, t, l, r)\<in>set (zip [0..<length auxlist'] auxlist').
         Suc k \<noteq> 0 \<and>
         t = \<tau> \<sigma> i \<and>
         t \<le> \<tau> \<sigma> k \<and>
         qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l \<and>
         qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r
      )" and
      auxlist_mem: "(\<forall>i.
          Suc k \<noteq> 0 \<and>
          i \<le> k
          \<longrightarrow>
          (\<exists>X. (\<tau> \<sigma> i, X) = auxlist'!i)
      )"
      unfolding wf_trigger_aux_def
      by auto

    define zs' where "zs' = fst (let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [(fv_z, z)], aux))"
    define aux' where "aux' = snd (let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [(fv_z, z)], aux))"

    have "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (snd (case acc of (zs, aux) \<Rightarrow> let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [(fv_z, z)], aux))) (Suc k)"
      using wf_trigger_aux
      unfolding z_eq Let_def
      by (auto split: prod.splits)
    moreover have "list_all2 (\<lambda>i a. case a of (dfvs, r) \<Rightarrow> wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
     [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]
     (fst (case acc of (zs, aux) \<Rightarrow> let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [(fv_z, z)], aux)))"
    proof -
      have aux'_eq: "aux' = update_mtaux args (\<tau> \<sigma> k) X Y aux"
        unfolding aux'_def Let_def
        by (auto split: prod.splits)
      define fv_z where "fv_z = fst (result_mtaux args aux')"
      define z where "z = snd (result_mtaux args aux')"
      define auxlist'' where "auxlist'' = (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"

      have valid_mtaux': "valid_mtaux args (\<tau> \<sigma> k) aux' auxlist''"
        unfolding aux'_eq auxlist''_def
        using valid_mtaux
        by auto
      have z_eq: "z = snd (trigger_results args (\<tau> \<sigma> k) auxlist'')"
        unfolding z_def
        using valid_result_mtaux[OF valid_mtaux']
        by (auto)

      have fv_z_eq: "fv_z = fst (trigger_results args (\<tau> \<sigma> k) auxlist'')"
        unfolding fv_z_def
        using valid_result_mtaux[OF valid_mtaux']
        by (auto)

      have filter_inv: "(filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist'') = (filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist')"
        unfolding auxlist''_def filter_filter
        by (metis (mono_tags, lifting) case_prod_beta')

      show ?thesis
      proof (cases "0 < length (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')")
        case non_empty: True
        have equiv: "(x \<in> z) = Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)" if
          restr: "mem_restr R x" and
          wf_x: "wf_tuple (args_n args) (args_R args) x"
        for x
          unfolding z_eq auxlist''_def
          using trigger_sat_equiv[OF restr wf_x pos args_n args_ivl args_L args_R fvi_subset 
              fv_l_n(1) valid_mtaux sorted_wrt auxlist_len auxlist_props auxlist_mem non_empty]
          by auto

        have int_non_empty: "\<not>(\<forall>j\<le>k. \<not> mem I (\<tau> \<sigma> k - \<tau> \<sigma> j))"
        proof -
          define auxlist''' where "auxlist''' = (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
          have "auxlist''' \<noteq> []"
            unfolding auxlist'''_def
            using non_empty
            by auto
          then obtain t X where "(t, X) \<in> set auxlist'''"
            by (metis filter_True filter_empty_conv prod.exhaust)
          then have mem:
            "mem (args_ivl args) (\<tau> \<sigma> k - t)"
            "(t, X) \<in> set auxlist'"
            unfolding auxlist'''_def
            by auto
          then obtain i where i_props:
            "i \<in> {0..<length auxlist'}"
            "(t, X) = auxlist'!i"
            by (metis atLeastLessThan_iff in_set_conv_nth zero_le)
          then have "(i, t, X)\<in>set (zip [0..<length auxlist'] auxlist')"
            using mem
            using in_set_zip by fastforce
          then have t_eq: "t = \<tau> \<sigma> i"
            using auxlist_len auxlist_props
            by auto
          show ?thesis
            using mem(1)[unfolded t_eq] i_props(1)[unfolded auxlist_len] not_le_imp_less
            unfolding args_ivl
            by fastforce
        qed

        have "fv_z = args_R args"
          using non_empty filter_inv
          unfolding fv_z_eq auxlist''_def trigger_results.simps
          by auto
        then have fv_z_eq'': "fv_z = fv \<alpha> \<union> fv \<beta>"
          using args_props
          by auto
  
        have "result_mtaux args aux' = trigger_results args (\<tau> \<sigma> k) auxlist''"
          using valid_result_mtaux[OF valid_mtaux]
          unfolding aux'_def auxlist''_def
          by auto
        moreover have "(length (filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist'') > 0)"
          using filter_inv non_empty
          unfolding auxlist''_def
          by auto
        ultimately have z_eq': "z = {
          tuple. wf_tuple (args_n args) (args_R args) tuple \<and>
            (\<forall>i \<in> {0..<(length auxlist'')}.
              let (t, l, r) = auxlist''!i in
              mem (args_ivl args) ((\<tau> \<sigma> k) - t) \<longrightarrow> 
              (
                tuple \<in> r \<or>
                (\<exists>j \<in> {i<..<(length auxlist'')}.
                  join_cond (args_pos args) ((fst o snd) (auxlist''!j)) (proj_tuple (join_mask (args_n args) (args_L args)) tuple)
                )
              )
            )
          }"
          unfolding z_def
          by auto
  
        have args_R_simp: "args_R args = fv \<alpha> \<union> fv \<beta>"
          using args_L args_R pos fvi_subset
          by (auto split: if_splits)
        have table: "table n (fv \<alpha> \<union> fv \<beta>) z"
          using z_eq'
          unfolding table_def args_R_simp args_n
          by auto
  
        have correctness: "(\<And>x. x \<in> z \<Longrightarrow> wf_tuple n (fv \<alpha> \<union> fv \<beta>) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>))"
          using equiv args_props
          by auto
  
        have completeness: "\<And>x. wf_tuple n (fv \<alpha> \<union> fv \<beta>) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>) \<Longrightarrow> x \<in> z"
          using equiv args_props
          by auto
  
        have qtable_k: "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k (formula.Trigger \<alpha> I \<beta>)) z"
          using qtableI[OF table correctness completeness]
          by auto
  
        have zs'_eq: "zs' = zs @ [(fv_z, z)]"
          unfolding zs'_def fv_z_def z_def aux'_eq  Let_def
          by (auto split: prod.splits)
  
        have IH: "list_all2
          (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
          [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs"
          using step(6) zs_def args_props(3)
          by auto
        then have "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] = length zs"
          unfolding list_all2_iff
          by auto
        then have len: "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] = length zs'"
          unfolding zs'_eq length_append
          by (simp add: step(1))
  
        moreover have "(\<forall>(i, (dfvs, r)) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] zs').
        wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and>
        qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)"
        proof -
          {
            fix i dfvs r
            assume assm: "(i, (dfvs, r)) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] zs')"
            
            have "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] = length zs"
              using step(6) zs_def
              unfolding list_all2_iff
              by auto
            moreover have "[min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] @ [k] =
                           [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]"
              by (simp add: step(1))
            ultimately have zip_eq:
              "zip ([min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]) zs' =
               zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs @ zip [k] [(fv_z, z)]"
              unfolding zs'_eq
              using zip_append[of "[min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k]" "zs" "[k]" "[(fv_z, z)]"]
              by auto
            {
              assume "(i, (dfvs, r)) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs)"
              then have
                "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
                using step(6) args_props(3) zs_def
                unfolding list_all2_iff
                by auto
            }
            moreover {
              assume "(i, (dfvs, r)) \<notin> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs)"
              then have eqs: "(i, dfvs, r) = (k, fv_z, z)"
                using assm zip_eq
                by auto
              moreover have "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                using eqs int_non_empty
                unfolding fv_z_eq'' wf_dfvs_def
                by auto
              ultimately have
                "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
                using qtable_k fv_z_eq''
                by auto
            }
            ultimately have
              "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
              "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
              by auto
          }
          then show ?thesis by auto
        qed
  
        ultimately show ?thesis
          unfolding list_all2_iff zs'_def zs_def aux_def
          by (auto split: prod.splits)
        
      next
        case False
        then have empty: "length (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist') = 0"
          by auto

        have int_empty:"\<forall>j\<le>k. \<not> mem I (\<tau> \<sigma> k - \<tau> \<sigma> j)"
        proof -
          {
            assume "\<exists>j\<le>k. mem I (\<tau> \<sigma> k - \<tau> \<sigma> j)"
            then obtain j where j_props: "j \<le> k" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> j)"
              by blast
            then obtain X where "(\<tau> \<sigma> j, X) = auxlist' ! j"
              using auxlist_mem
              by auto
            then have  "(\<tau> \<sigma> j, X) \<in> set (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
              using auxlist_len j_props args_ivl
              by auto
            then have "False"
              using empty length_pos_if_in_set[of "(\<tau> \<sigma> j, X)"]
              by auto
          }
          then show ?thesis by blast
        qed

        have sat: "\<And>v. Formula.sat \<sigma> V v k (formula.Trigger \<alpha> I \<beta>)"
          using int_empty
          by auto

        have z_eq': "z = {replicate (args_n args) None}"
          using empty filter_inv
          unfolding z_eq auxlist''_def trigger_results.simps
          by auto

        have fv_z_eq': "fv_z = {}"
          using empty filter_inv
          unfolding fv_z_eq auxlist''_def trigger_results.simps
          by auto

        have table: "table n {} z"
          unfolding fv_z_eq' z_eq'
          by (simp add: args_n table_def wf_tuple_empty_iff)

        have correctness: "(\<And>x. x \<in> z \<Longrightarrow> wf_tuple n {} x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>))"
          using sat
          by auto
  
        have completeness: "\<And>x. wf_tuple n {} x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>) \<Longrightarrow> x \<in> z"
          using sat
          unfolding z_eq'
          by (simp add: args_n wf_tuple_empty_iff)
  
        have qtable_k: "qtable n {} (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k (formula.Trigger \<alpha> I \<beta>)) z"
          using qtableI[OF table correctness completeness]
          by auto
  
        have zs'_eq: "zs' = zs @ [(fv_z, z)]"
          unfolding zs'_def fv_z_def z_def aux'_eq  Let_def
          by (auto split: prod.splits)
  
        have IH: "list_all2
          (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
          [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs"
          using step(6) zs_def args_props(3)
          by auto
        then have "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] = length zs"
          unfolding list_all2_iff
          by auto
        then have len: "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] = length zs'"
          unfolding zs'_eq length_append
          by (simp add: step(1))
  
        moreover have "(\<forall>(i, (dfvs, r)) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] zs').
        wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and>
        qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)"
        proof -
          {
            fix i dfvs r
            assume assm: "(i, (dfvs, r)) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] zs')"
            
            have "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] = length zs"
              using step(6) zs_def
              unfolding list_all2_iff
              by auto
            moreover have "[min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] @ [k] =
                           [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]"
              by (simp add: step(1))
            ultimately have zip_eq:
              "zip ([min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]) zs' =
               zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs @ zip [k] [(fv_z, z)]"
              unfolding zs'_eq
              using zip_append[of "[min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k]" "zs" "[k]" "[(fv_z, z)]"]
              by auto
            {
              assume "(i, (dfvs, r)) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs)"
              then have
                "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
                using step(6) args_props(3) zs_def
                unfolding list_all2_iff
                by auto
            }
            moreover {
              assume "(i, (dfvs, r)) \<notin> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs)"
              then have eq: "(i, dfvs, r) = (k, fv_z, z)"
                using assm zip_eq
                by auto
              moreover have "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                using sat eq fv_z_eq' int_empty
                unfolding wf_dfvs_def
                by auto
              ultimately have
                "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
                using qtable_k fv_z_eq'
                by auto
            }
            ultimately have
              "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
              "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
              by auto
          }
          then show ?thesis by auto
        qed
  
        ultimately show ?thesis
          unfolding list_all2_iff zs'_def zs_def aux_def
          by (auto split: prod.splits)
      qed
    qed
    ultimately show ?case 
      using args_props(3) by auto
  qed auto
  (* same but this time without the conjunction *)
  then have update_trigger:
    "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux' (Progress.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>))"
    "list_all2 (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
     [Progress.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j..<Progress.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>)] zs'"
    by auto

  define tuple' where "tuple' = mbuf2_take (\<lambda>r1 (V_trigger, r2).
      bin_join n (fv \<phi>) r1 True V_trigger r2
  ) (mbuf2_add xs zs' buf1)"

  \<comment> \<open>the evaluation step of @{term z'} in terms of the intermediate results\<close>
  have meval_z': "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db z' =
      (fst tuple', MAndTrigger (fv \<phi>) \<phi>'' (snd tuple') args \<gamma>'' \<beta>'' buf2' nts' aux')"
    unfolding z'_def meval.simps Let_def \<open>X\<^sub>\<phi> = fv \<phi>\<close> xtuple_eq atuple_eq btuple_eq prod.case
      tuple_def[unfolded Let_def, symmetric] tuple_eq tuple'_def
    by (simp add: case_prod_beta')

  have zs_eq: "zs = fst tuple'"
    using meval_z' unfolding zs_def by simp
    
  define buf1' where "buf1' = snd tuple'"

  have tuple'_eq: "tuple' = (zs, buf1')"
    unfolding zs_eq buf1'_def
    by auto

  have z''_eq: "z'' = MAndTrigger (fv \<phi>) \<phi>'' buf1' args \<gamma>'' \<beta>'' buf2' nts' aux'"
    using meval_z' unfolding z''_def buf1'_def by simp

  have buf_and:
    "wf_mbuft2' \<sigma> P' V (j + \<delta>) n R \<phi> \<alpha> I \<beta> buf1'"
    "list_all2
     (\<lambda>i Z. \<exists>X V_Y Y.
                qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X \<and>
                wf_dfvs V_Y \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and>
                qtable n V_Y (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) Y \<and>
                Z = bin_join n (fv \<phi>) X True V_Y Y)
     [min (Progress.progress \<sigma> P \<phi> j) (Progress.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)..<
      min (Progress.progress \<sigma> P' \<phi> (j + \<delta>)) (Progress.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>))]
     zs"
    using mbuft2_take_add'[OF tuple'_eq[unfolded tuple'_def] 
        wf_buf1 pred_mapping(3,1,2) IH_phi(2) update_trigger(2)]
    by auto

  have "wf_mformula \<sigma> (j + \<delta>) P' V n R z'' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))"
    unfolding z''_eq
    using  wf_mformula.And_Trigger[OF IH_phi(1) buf_and(1) fv_t_subset 
        IH_beta(1) pos IH_gamma(1) pos_eq args_ivl args_n args_L args_R fv_l_n(1) fvi_subset 
        wf_buf_ts_trigger update_trigger(1)] .
  moreover have "list_all2
       (\<lambda>i. qtable n (fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))))
       [Progress.progress \<sigma> P (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) j..<Progress.progress \<sigma> P' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) (j + \<delta>)] zs" 
  proof -
    have "length [Progress.progress \<sigma> P (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) j..<Progress.progress \<sigma> P' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) (j + \<delta>)] = length zs"
      using buf_and(2)
      unfolding list_all2_iff
      by auto
    moreover have "\<And>i r. (i, r)\<in>set (zip [Progress.progress \<sigma> P (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) j..<Progress.progress \<sigma> P' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) (j + \<delta>)] zs) \<Longrightarrow>
        qtable n (fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) r"
    proof -
      fix i r
      assume "(i, r)\<in>set (zip [Progress.progress \<sigma> P (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) j..<Progress.progress \<sigma> P' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) (j + \<delta>)] zs)"
      then have "(i, r)\<in>set (zip [min (Progress.progress \<sigma> P \<phi> j) (Progress.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)..< min (Progress.progress \<sigma> P' \<phi> (j + \<delta>)) (Progress.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>))] zs)"
        by auto
      then have "\<exists>X V_Y Y.
           qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X \<and>
           wf_dfvs V_Y \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and>
           qtable n V_Y (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) Y \<and> r = bin_join n (fv \<phi>) X True V_Y Y"
        using buf_and(2)
        unfolding list_all2_iff
        by fast
      then obtain X V_Y Y where qtables:
        "qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X"
        "qtable n V_Y (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) Y"
        "wf_dfvs V_Y \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
        "r = bin_join n (fv \<phi>) X True V_Y Y"
        by blast

      have "V_Y \<subseteq> fv (formula.Trigger \<alpha> I \<beta>)"
        using qtables(3)
        unfolding wf_dfvs_def
        by (auto split: if_splits)
      then have fvs: "(fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) = fv \<phi> \<union> V_Y"
        using fv_t_subset
        by auto

      have "\<And>x. Formula.sat \<sigma> V (map the (restrict (fv \<phi>) x)) i \<phi> = Formula.sat \<sigma> V (map the x) i \<phi>"
        using sat_the_restrict
        by auto

      have qtable_pos: "(\<And>x.
          wf_tuple n (fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) x \<Longrightarrow>
          mem_restr R x \<Longrightarrow>
          Formula.sat \<sigma> V (map the x) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) =
          (Formula.sat \<sigma> V (map the (restrict (fv \<phi>) x)) i \<phi> \<and> Formula.sat \<sigma> V (map the (restrict V_Y x)) i (formula.Trigger \<alpha> I \<beta>)))"
      proof (cases "\<forall>j\<le>i. \<not> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)")
        case True
        fix x
        show "Formula.sat \<sigma> V (map the x) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) =
          (Formula.sat \<sigma> V (map the (restrict (fv \<phi>) x)) i \<phi> \<and> Formula.sat \<sigma> V (map the (restrict V_Y x)) i (formula.Trigger \<alpha> I \<beta>))"
          using sat_the_restrict True
          by auto
      next
        case False
        then have V_Y_eq: "V_Y = fv (formula.Trigger \<alpha> I \<beta>)"
          using qtables(3)
          unfolding wf_dfvs_def
          by auto

        fix x
        show "Formula.sat \<sigma> V (map the x) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) =
          (Formula.sat \<sigma> V (map the (restrict (fv \<phi>) x)) i \<phi> \<and> Formula.sat \<sigma> V (map the (restrict V_Y x)) i (formula.Trigger \<alpha> I \<beta>))"
          unfolding V_Y_eq
          using sat_the_restrict
          by auto
      qed

      then show "qtable n (fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) r"
        unfolding qtables(4)
        using qtable_bin_join[OF qtables(1-2) _ fvs _ qtable_pos, of True]
        by auto
    qed
    ultimately show ?thesis
      unfolding list_all2_iff
      by blast
  qed

  ultimately show ?case 
    using ztuple_eq  
    by (auto simp: z'_def fv_phi_eq z_eq)
next
  case (MAndRel \<phi> conf)
  from MAndRel.prems obtain \<phi>'' \<psi>'' where
  \<phi>'_eq: "\<phi>' = formula.And \<phi>'' \<psi>''"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MAndRel.prems(3) obtain "S, E \<turnstile> \<phi>''" and "S, E \<turnstile> \<psi>''"
    by (cases rule: wty_formula.cases) (auto simp: \<phi>'_eq)
  with MAndRel.prems show ?case
    by (cases rule: wf_mformula.cases)
      (auto simp: progress_constraint progress_le list.rel_map fv_formula_of_constraint \<phi>'_eq
        Un_absorb2 wf_mformula_wf_set[unfolded wf_set_def] simp del: Set.filter_eq split: prod.splits
        dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E
        dest!: MAndRel.IH eval_constraint_sat_eq[THEN iffD2]
        intro!: wf_mformula.AndRel
        elim!: list.rel_mono_strong qtable_filter eval_constraint_sat_eq[THEN iffD1])
next
  case (MAnds A_pos A_neg l buf)
  note mbufn_take.simps[simp del] mbufn_add.simps[simp del] mmulti_join.simps[simp del]

  from MAnds.prems obtain pos neg l' 
    where wf_l: "list_all2 (wf_mformula \<sigma> j P V n R) l (pos @ map remove_neg neg)" 
      and wf_buf: "wf_mbufn (progress \<sigma> P (\<And>\<^sub>F l') j) 
        (map (\<lambda>\<psi>. progress \<sigma> P \<psi> j) (pos @ map remove_neg neg))
        (map (\<lambda>\<psi> i. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<psi>)) (pos @ map remove_neg neg)) 
        buf" 
      and posneg: "(pos, neg) = partition safe_formula l'" 
      and "pos \<noteq> []"
      and safe_neg: "list_all safe_formula (map remove_neg neg)"
      and A_eq: "A_pos = map fv pos" "A_neg = map fv neg"
      and fv_subset: "\<Union> (set A_neg) \<subseteq> \<Union> (set A_pos)"
      and \<phi>'_eq: "\<phi>' = Formula.Ands l'"
    by (cases rule: wf_mformula.cases) 
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  have progress_eq: "progress \<sigma> P'  (\<And>\<^sub>F l') (j + \<delta>) =
      Mini (progress \<sigma> P (\<And>\<^sub>F l') j) (map (\<lambda>\<psi>. progress \<sigma> P' \<psi> (j + \<delta>)) (pos @ map remove_neg neg))"
    using \<open>pos \<noteq> []\<close> posneg
    by (auto simp: Mini_def image_Un[symmetric] Collect_disj_eq[symmetric] 
        intro!: arg_cong[where f=Min])

  have join_ok: "qtable n (\<Union> (fv ` set l')) (mem_restr R)
        (\<lambda>v. list_all (Formula.sat \<sigma> V (map the v) k) l')
        (mmulti_join n A_pos A_neg L)"
    if args_ok: "list_all2 (\<lambda>x. qtable n (fv x) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k x))
        (pos @ map remove_neg neg) L"
    for k L
  proof (rule qtable_mmulti_join)
    let ?ok = "\<lambda>A Qi X. qtable n A (mem_restr R) Qi X \<and> wf_set n A"
    let ?L_pos = "take (length A_pos) L"
    let ?L_neg = "drop (length A_pos) L"
    have 1: "length pos \<le> length L"
      using args_ok by (auto dest!: list_all2_lengthD)
    show "list_all3 ?ok A_pos (map (\<lambda>\<psi> v. Formula.sat \<sigma> V (map the v) k \<psi>) pos) ?L_pos"
      using args_ok wf_l unfolding A_eq
      by (auto simp add: list_all3_conv_all_nth list_all2_conv_all_nth nth_append
          split: if_splits intro!: wf_mformula_wf_set[of \<sigma> j P V n R]
          dest: order.strict_trans2[OF _ 1]) 
    have prems_neg: "list_all2 (\<lambda>\<psi>. qtable n (fv \<psi>) (mem_restr R) 
        (\<lambda>v. \<langle>\<sigma>, V, v, k\<rangle> \<Turnstile>\<^sub>M remove_neg \<psi>)) neg ?L_neg"
      using args_ok
      by (auto simp: A_eq list_all2_append1 list.rel_map)
    show "list_all3 ?ok A_neg (map (\<lambda>\<psi> v. Formula.sat \<sigma> V (map the v) k (remove_neg \<psi>)) neg) ?L_neg"
      using prems_neg wf_l unfolding A_eq
      by (auto simp add: list_all3_conv_all_nth list_all2_conv_all_nth list_all_length 
          nth_append less_diff_conv split: if_splits 
          intro!: wf_mformula_wf_set[of \<sigma> j P V n R _ "remove_neg _", simplified])
    show "\<Union>(fv ` set l') = \<Union>(set A_pos)"
      using fv_subset posneg unfolding A_eq by auto
    show "L = take (length A_pos) L @ drop (length A_pos) L" by simp
    show "A_pos \<noteq> []" using \<open>pos \<noteq> []\<close> A_eq by simp

    fix x :: "event_data tuple"
    assume "wf_tuple n (\<Union> (fv ` set l')) x" and "mem_restr R x"
    then show "list_all (\<lambda>A. mem_restr R (restrict A x)) A_pos"
      and "list_all (\<lambda>A. mem_restr R (restrict A x)) A_neg"
      by (simp_all add: list.pred_set)

    have "list_all Formula.is_Neg neg"
      using posneg safe_neg
      by (auto 0 3 simp add: list.pred_map elim!: list.pred_mono_strong
          intro: formula.exhaust[of \<psi> "Formula.is_Neg \<psi>" for \<psi>])
    then have "list_all (\<lambda>\<psi>. Formula.sat \<sigma> V (map the v) i (remove_neg \<psi>) \<longleftrightarrow>
      \<not> Formula.sat \<sigma> V (map the v) i \<psi>) neg" for v i
      by (fastforce simp: Formula.is_Neg_def elim!: list.pred_mono_strong)
    then show "list_all (Formula.sat \<sigma> V (map the x) k) l' =
       (list_all2 (\<lambda>A Qi. Qi (restrict A x)) A_pos
         (map (\<lambda>\<psi> v. Formula.sat \<sigma> V (map the v) k \<psi>) pos) \<and>
        list_all2 (\<lambda>A Qi. \<not> Qi (restrict A x)) A_neg
         (map (\<lambda>\<psi> v. Formula.sat \<sigma> V (map the v) k
                       (remove_neg \<psi>))
           neg))"
      using posneg
      by (auto simp add: A_eq list_all2_conv_all_nth list_all_length sat_the_restrict
          elim: nth_filter nth_partition[where P=safe_formula and Q="Formula.sat _ _ _ _"])
  qed fact
  have split: 
    "\<phi> \<in> set pos \<Longrightarrow> \<phi> \<in> set l'"
    "\<phi> \<in> set (map remove_neg neg) \<Longrightarrow> Formula.Neg \<phi> \<in> set l' \<or> \<phi> \<in> set l'" for \<phi> 
  proof -
    show "\<phi> \<in> set pos \<Longrightarrow> \<phi> \<in> set l'"
      using posneg by simp
  next
    assume "\<phi> \<in> set (map remove_neg neg)"
    then obtain \<psi> where \<psi>: "\<psi> \<in> set l'" "\<phi> = remove_neg \<psi>"
      using posneg by auto
    show "Formula.Neg \<phi> \<in> set l' \<or> \<phi> \<in> set l'"
      by (cases \<psi>) (use \<psi> in simp_all)
  qed
  from MAnds.prems(3) have all_wty: "\<forall>\<phi>\<in>set l'. S, E \<turnstile> \<phi>"
    unfolding \<phi>'_eq by (cases rule: wty_formula.cases) auto
  have "\<phi> \<in> set pos \<Longrightarrow> S, E \<turnstile> \<phi>" for \<phi> using split(1) all_wty by auto
  moreover have "\<phi> \<in> set (map remove_neg neg) \<Longrightarrow> S, E \<turnstile> \<phi>" for \<phi> 
  proof -
    assume asm: "\<phi> \<in> set (map remove_neg neg)"
    show "S, E \<turnstile> \<phi>" using split(2)[OF asm] all_wty
      by(auto elim:wty_formula.cases)
  qed
  ultimately have "\<forall>\<phi>\<in>set (pos @ map remove_neg neg). S, E \<turnstile> \<phi>"
    by auto
  with MAnds.prems(2) show ?case
    unfolding \<phi>'_eq
    by (auto 0 3 simp add: list.rel_map progress_eq map2_map_map list_all3_map
        list_all3_list_all2_conv list.pred_map
        simp del: set_append map_append progress_simps split: prod.splits
        intro!: wf_mformula.Ands[OF _ _ posneg \<open>pos \<noteq> []\<close> safe_neg A_eq fv_subset]
        list.rel_mono_strong[OF wf_l] wf_mbufn_add[OF wf_buf]
        list.rel_flip[THEN iffD1, OF list.rel_mono_strong, OF wf_l]
        list.rel_refl join_ok[unfolded list.pred_set]
        dest!: MAnds.IH[where E4=E, OF _ _ MAnds.prems(2), rotated]
        elim!: wf_mbufn_take list_all2_appendI
        elim: mbufn_take_induct[OF _ wf_mbufn_add[OF wf_buf]])
next
  case (MOr \<phi> \<psi> buf)
  from MOr.prems obtain \<phi>'' \<psi>'' \<alpha>' J where
    \<phi>'_eq: "\<phi>' = \<phi>'' \<or>\<^sub>F \<psi>'' \<or> \<phi>' = \<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'') \<or> \<phi>' = \<phi>'' \<^bold>R J \<psi>''"
    by (cases rule: wf_mformula.cases)
      auto
  have pred_mappings: "rel_mapping (\<le>) P P'"
    "pred_mapping (\<lambda>x. x \<le> j) P"
    "pred_mapping (\<lambda>x. x \<le> j + \<delta>) P'"
    using MOr.prems by auto
  have wty_phi: "S, E \<turnstile> \<phi>''" 
    and wty_psi: "S, E \<turnstile> \<psi>''"
    and wty_alpha: "\<phi>' = \<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'') \<Longrightarrow> S, E \<turnstile> \<alpha>'"
    \<comment> \<open>in all three shapes of @{term \<phi>'}, these are subformulas of the well-typed @{term \<phi>'}\<close>
    using \<phi>'_eq MOr.prems(3) by (auto dest: wty_formulaD)
  {assume phi'_eq: "\<phi>' = \<phi>'' \<or>\<^sub>F \<psi>''"
    from MOr.prems(3) and this
    obtain "S, E \<turnstile> \<phi>''" and "S, E \<turnstile> \<psi>''"
      by (cases rule: wty_formula.cases)
      (auto simp: \<phi>'_eq)
    with MOr.prems have ?case
      unfolding phi'_eq
      by (cases rule: wf_mformula.cases)
        (auto dest!: MOr.IH split: if_splits prod.splits intro!: wf_mformula.Or qtable_union
          elim: mbuf2_take_add'(1) list.rel_mono_strong[OF mbuf2_take_add'(2)])
  } moreover {
    let ?ff = "\<not>\<^sub>F Formula.eventually J Formula.TT" 
      and ?Rbdd = "release_safe_bounded \<phi>'' J \<psi>''"
      and ?AndRbdd = "and_release_safe_bounded \<alpha>' \<phi>'' J \<psi>''"
    assume phi'_eq: "\<phi>' = \<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'')"
    (* obtain hyps for inductive hypothesis *)
    hence wtys: "S, E \<turnstile> \<alpha>' \<and>\<^sub>F ?ff" "S, E \<turnstile> \<alpha>' \<and>\<^sub>F ?Rbdd"
      using wty_phi wty_psi wty_alpha[OF phi'_eq]
      by (auto simp: Formula.eventually_def release_safe_bounded_def 
          always_safe_bounded_def once_def intro!: wty_formula.intros)
    have progress_eq: "progress \<sigma> W ?AndRbdd i 
      = min (progress \<sigma> W (\<alpha>' \<and>\<^sub>F ?ff) i) (progress \<sigma> W (\<alpha>' \<and>\<^sub>F ?Rbdd) i)" for i W
      by (clarsimp simp: and_release_safe_bounded_def)
    from MOr.prems have "\<not> mem J 0" and "bounded J" 
      and fvs: "FV \<phi>'' = FV \<psi>''" "FV \<psi>'' \<subseteq> FV \<alpha>'" "FV \<alpha>' \<union> FV \<psi>'' = FV \<alpha>'"
      and safes: "safe_formula \<alpha>'" "safe_formula ?Rbdd" 
      and wf_buf: "wf_mbuf2' \<sigma> P V j n R (\<alpha>' \<and>\<^sub>F ?ff) (\<alpha>' \<and>\<^sub>F ?Rbdd) buf"
      by (cases rule: wf_mformula.cases; force simp: phi'_eq)+
    from MOr.prems have wf_MOr: "wf_mformula \<sigma> j P V n R (MOr \<phi> \<psi> buf) ?AndRbdd"
      by (cases rule: wf_mformula.cases; clarsimp simp: phi'_eq)
    hence wf_psi: "wf_mformula \<sigma> j P V n R \<psi> (\<alpha>' \<and>\<^sub>F ?Rbdd)"
      by (cases rule: wf_mformula.cases; clarsimp simp: and_release_safe_bounded_def)
    have wf_phi: "wf_mformula \<sigma> j P V n R \<phi> (\<alpha>' \<and>\<^sub>F ?ff)"
      using wf_MOr
      by (cases rule: wf_mformula.cases; clarsimp simp: 
          and_release_safe_bounded_def Formula.eventually_def)
    (* apply inductive hypothesis *)
    obtain \<phi>s \<phi>\<^sub>M and \<psi>s \<psi>\<^sub>M and \<phi>\<psi>s buf'
      where meval_defs: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> = (\<phi>s, \<phi>\<^sub>M)"
        "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi> = (\<psi>s, \<psi>\<^sub>M)"
        "mbuf2_take (\<union>) (mbuf2_add \<phi>s \<psi>s buf) = (\<phi>\<psi>s, buf')"
      by (meson eq_snd_iff)
    hence preIH: "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>M (\<alpha>' \<and>\<^sub>F ?ff)"
      "list_all2 (\<lambda>i. qtable n (FV (\<alpha>' \<and>\<^sub>F ?ff)) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<alpha>' \<and>\<^sub>F ?ff))
        [progress \<sigma> P (\<alpha>' \<and>\<^sub>F ?ff) j..< progress \<sigma> P' (\<alpha>' \<and>\<^sub>F ?ff) (j + \<delta>)] \<phi>s"
      "wf_mformula \<sigma> (j + \<delta>) P' V n R \<psi>\<^sub>M (\<alpha>' \<and>\<^sub>F ?Rbdd)"
      "list_all2 (\<lambda>i. qtable n (FV (\<alpha>' \<and>\<^sub>F ?Rbdd)) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<alpha>' \<and>\<^sub>F ?Rbdd))
       [Progress.progress \<sigma> P (\<alpha>' \<and>\<^sub>F ?Rbdd) j..<Progress.progress \<sigma> P' (\<alpha>' \<and>\<^sub>F ?Rbdd) (j + \<delta>)] \<psi>s"
      using MOr.IH(1)[OF wf_phi MOr.prems(2) wtys(1)] MOr.IH(2)[OF wf_psi MOr.prems(2) wtys(2)]
      by auto
    note mbuf'_obs = mbuf2_take_add'[OF meval_defs(3) wf_buf pred_mappings(1) 
        preIH(2,4) _ pred_mappings(2,3)]
    from wf_MOr have safes': "safe_formula (\<alpha>' \<and>\<^sub>F ?ff)" "safe_formula (\<alpha>' \<and>\<^sub>F ?Rbdd)"
      by (cases rule: wf_mformula.cases; simp add: and_release_safe_bounded_def)+
    have IH1: "wf_mformula \<sigma> (j + \<delta>) P' V n R (MOr \<phi>\<^sub>M \<psi>\<^sub>M buf') ?AndRbdd"
      unfolding and_release_safe_bounded_def
    proof (rule wf_mformula.Or[OF preIH(1,3)])
      show "FV (\<alpha>' \<and>\<^sub>F ?ff) = FV (\<alpha>' \<and>\<^sub>F ?Rbdd)"
        using fvs by auto
      show "wf_mbuf2' \<sigma> P' V (j + \<delta>) n R (\<alpha>' \<and>\<^sub>F ?ff) (\<alpha>' \<and>\<^sub>F ?Rbdd) buf'"
        by (rule mbuf'_obs(1)[OF le_add1])
      show "safe_formula (\<alpha>' \<and>\<^sub>F ?ff)" "safe_formula (\<alpha>' \<and>\<^sub>F ?Rbdd)"
        by (rule safes')+
    qed
    have fv_eqs: "FV ?AndRbdd = FV (\<alpha>' \<and>\<^sub>F ?ff)" "FV ?AndRbdd = FV (\<alpha>' \<and>\<^sub>F ?Rbdd)"
      using fvs by auto
    have step: "qtable n (FV ?AndRbdd) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i ?AndRbdd) (X \<union> Y)"
      if X: "qtable n (FV (\<alpha>' \<and>\<^sub>F ?ff)) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (\<alpha>' \<and>\<^sub>F ?ff)) X"
        and Y: "qtable n (FV (\<alpha>' \<and>\<^sub>F ?Rbdd)) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (\<alpha>' \<and>\<^sub>F ?Rbdd)) Y"
      for i X Y
    proof (rule qtable_union)
      show "qtable n (FV ?AndRbdd) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (\<alpha>' \<and>\<^sub>F ?ff)) X"
        using X unfolding fv_eqs(1) .
      show "qtable n (FV ?AndRbdd) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (\<alpha>' \<and>\<^sub>F ?Rbdd)) Y"
        using Y unfolding fv_eqs(2) .
      show "Formula.sat \<sigma> V (map the x) i ?AndRbdd \<longleftrightarrow>
          Formula.sat \<sigma> V (map the x) i (\<alpha>' \<and>\<^sub>F ?ff) \<or> Formula.sat \<sigma> V (map the x) i (\<alpha>' \<and>\<^sub>F ?Rbdd)" for x
        unfolding and_release_safe_bounded_def by (rule sat.simps)
    qed
    have IH2: 
      "list_all2 (\<lambda>i. qtable n (fv ?AndRbdd) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M ?AndRbdd))
        [progress \<sigma> P ?AndRbdd j..< progress \<sigma> P' ?AndRbdd (j + \<delta>)] \<phi>\<psi>s"
      unfolding progress_eq using mbuf'_obs(2)[OF le_add1]
      by (rule list_all2_mono) (elim exE conjE, hypsubst, rule step)
    (* translate encoding *)
    have key: "(\<lambda>i. qtable n (FV (\<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>''))) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'')))
      = (\<lambda>i. qtable n (FV ?AndRbdd) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M ?AndRbdd))"
    proof (intro ext qtable_cong_strong[THEN fun_cong])
      show "FV (\<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'')) = FV ?AndRbdd"
        using fvs by auto
      show "\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'') \<longleftrightarrow> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M ?AndRbdd" for i v
        using sat_and_release_rewrite[OF \<open>bounded J\<close> \<open>\<not> mem J 0\<close>] .
    qed
    have "wf_mformula \<sigma> (j + \<delta>) P' V n R (MOr \<phi>\<^sub>M \<psi>\<^sub>M buf') (\<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>''))"
      using wf_mformula.intros(10)[OF \<open>\<not> mem J 0\<close> \<open>bounded J\<close> fvs(1,2) safes mbuf'_obs(1) IH1] 
      by force
    moreover have "list_all2 (\<lambda>i. qtable n (FV (\<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>''))) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'')))
       [Progress.progress \<sigma> P (\<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'')) j..<Progress.progress \<sigma> P' (\<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'')) (j + \<delta>)] \<phi>\<psi>s"
      unfolding progress_and_release_rewrite_bounded[OF \<open>\<not> mem J 0\<close> \<open>bounded J\<close>, symmetric] key
      by (rule IH2)
    ultimately have ?case
      unfolding phi'_eq meval.simps Let_def meval_defs prod.case by (rule conjI)
  } moreover {
    let ?R0 = "release_safe_0 \<phi>'' J \<psi>''" and ?A0 = "always_safe_0 J \<psi>''"
    assume phi'_eq: "\<phi>' = \<phi>'' \<^bold>R J \<psi>''"
    (* obtain hyps for inductive hypothesis *)
    with MOr.prems have "wf_envs S \<sigma> j \<delta> P P' V db"
      and "S, E \<turnstile> \<phi>'' \<^bold>R J \<psi>''"
      and "mem J 0"
      and "bounded J"
      and "FV \<phi>'' \<subseteq> FV \<psi>''"
      and safes: "safe_formula \<psi>''" "safe_formula (?R0)"
      and wf_mOr: "wf_mformula \<sigma> j P V n R (MOr \<phi> \<psi> buf) (?R0)"
      and wf_buf: "wf_mbuf2' \<sigma> P V j n R (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'') (?A0) buf"
      unfolding phi'_eq
      by (cases rule: wf_mformula.cases, clarsimp)+
    hence fvs: "FV (\<phi>'' \<^bold>R J \<psi>'') = FV \<psi>''"
      "FV (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'') = FV \<psi>''"
      "FV (?A0) = FV \<psi>''"
      "FV (?R0) = FV \<psi>''"
      by auto
    have wtys: "S, E \<turnstile> \<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>''" "S, E \<turnstile> ?A0"
      using wty_phi wty_psi
      unfolding always_safe_0_def
      by (auto intro!: wty_formula.intros)
    have wf_phi: "wf_mformula \<sigma> j P V n R \<phi> (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'')"
      using wf_mOr
      by (cases rule: wf_mformula.cases; clarsimp simp: release_safe_0_def)
    have wf_psi: "wf_mformula \<sigma> j P V n R \<psi> ?A0"
      using wf_mOr
      by (cases rule: wf_mformula.cases; clarsimp simp: release_safe_0_def)
    (* apply inductive hypothesis *)
    obtain \<phi>s \<phi>\<^sub>M and \<psi>s \<psi>\<^sub>M and \<phi>\<psi>s buf'
      where meval_defs: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> = (\<phi>s, \<phi>\<^sub>M)"
        "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi> = (\<psi>s, \<psi>\<^sub>M)"
        "mbuf2_take (\<union>) (mbuf2_add \<phi>s \<psi>s buf) = (\<phi>\<psi>s, buf')"
      by (meson eq_snd_iff)
    hence preIH: "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>M (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'')"
      "list_all2 (\<lambda>i. qtable n (FV (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'')) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'')))
        [progress \<sigma> P (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'') j..< progress \<sigma> P' (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'') (j + \<delta>)] \<phi>s"
      "wf_mformula \<sigma> (j + \<delta>) P' V n R \<psi>\<^sub>M ?A0"
      "list_all2 (\<lambda>i. qtable n (FV ?A0) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M ?A0))
        [progress \<sigma> P ?A0 j..< progress \<sigma> P' ?A0 (j + \<delta>)] \<psi>s"
      using MOr.IH(1)[OF wf_phi MOr.prems(2) wtys(1)] MOr.IH(2)[OF wf_psi MOr.prems(2) wtys(2)]
      by auto
    note mbuf'_obs = mbuf2_take_add'[OF meval_defs(3) wf_buf pred_mappings(1) 
        preIH(2,4) _ pred_mappings(2,3)]
    have IH1: "wf_mformula \<sigma> (j + \<delta>) P' V n R (MOr \<phi>\<^sub>M \<psi>\<^sub>M buf') ?R0"
      unfolding release_safe_0_def
    proof (rule wf_mformula.Or[OF preIH(1,3)])
      show "FV (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'') = FV ?A0"
        by (simp only: fvs(2,3))
      show "wf_mbuf2' \<sigma> P' V (j + \<delta>) n R (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'') ?A0 buf'"
        by (rule mbuf'_obs(1)[OF le_add1])
      show "safe_formula (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'')" "safe_formula ?A0"
        using safes(2) by (simp_all add: release_safe_0_def)
    qed
    have prog_R0: "progress \<sigma> W ?R0 i = min (progress \<sigma> W (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'') i) (progress \<sigma> W ?A0 i)"
      for W i
      unfolding release_safe_0_def by (rule progress.simps(9))
    have step: "qtable n (FV ?R0) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i ?R0) (X \<union> Y)"
      if X: "qtable n (FV (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'')) (mem_restr R)
          (\<lambda>v. Formula.sat \<sigma> V (map the v) i (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'')) X"
        and Y: "qtable n (FV ?A0) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i ?A0) Y"
      for i X Y
    proof (rule qtable_union)
      show "qtable n (FV ?R0) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'')) X"
        using X unfolding fvs(2,4) .
      show "qtable n (FV ?R0) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i ?A0) Y"
        using Y unfolding fvs(3,4) .
      show "Formula.sat \<sigma> V (map the x) i ?R0 \<longleftrightarrow>
          Formula.sat \<sigma> V (map the x) i (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'') \<or> Formula.sat \<sigma> V (map the x) i ?A0" for x
        unfolding release_safe_0_def by (rule sat.simps)
    qed
    have IH2: "list_all2 (\<lambda>i. qtable n (FV ?R0) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M ?R0))
        [progress \<sigma> P ?R0 j..< progress \<sigma> P' ?R0 (j + \<delta>)] \<phi>\<psi>s"
      unfolding prog_R0 using mbuf'_obs(2)[OF le_add1]
      by (rule list_all2_mono) (elim exE conjE, hypsubst, rule step)
    have "list_all2 (\<lambda>i. qtable n (FV ?R0) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>'' \<^bold>R J \<psi>''))
      [progress \<sigma> P (\<phi>'' \<^bold>R J \<psi>'') j..< progress \<sigma> P' (\<phi>'' \<^bold>R J \<psi>'') (j + \<delta>)] \<phi>\<psi>s"
      using IH2 
      unfolding sat_release_rewrite_0[OF \<open>mem J 0\<close> \<open>bounded J\<close>] progress_release_rewrite_0[OF \<open>mem J 0\<close>]
      by auto
    moreover note wf_mformula.Release_0[OF \<open>mem J 0\<close> \<open>bounded J\<close> \<open>FV \<phi>'' \<subseteq> FV \<psi>''\<close> safes mbuf'_obs(1) IH1] 
    ultimately have ?case
      using meval_defs
      unfolding meval.simps phi'_eq fvs
      by auto
  }
  ultimately show ?case
    using \<phi>'_eq by metis
next
  case (MNeg \<phi>)
  have *: "qtable n {} (mem_restr R) (\<lambda>v. P v) X \<Longrightarrow>
    \<not> qtable n {} (mem_restr R) (\<lambda>v. \<not> P v) empty_table \<Longrightarrow> x \<in> X \<Longrightarrow> False" for P x X
    using nullary_qtable_cases qtable_unit_empty_table by fastforce
  from MNeg.prems obtain \<phi>'' where \<phi>'_eq: "\<phi>' = formula.Neg \<phi>''"
    by (cases rule: wf_mformula.cases) 
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MNeg.prems(3) have "S, E \<turnstile> \<phi>''"
    by (cases rule: wty_formula.cases) (auto simp: \<phi>'_eq)
  with MNeg.prems show ?case
    unfolding \<phi>'_eq
    by (cases rule: wf_mformula.cases)
      (auto 0 4 intro!: wf_mformula.Neg dest!: MNeg.IH
        simp add: list.rel_map
        dest: nullary_qtable_cases qtable_unit_empty_table intro!: qtable_empty_unit_table
        elim!: list.rel_mono_strong elim: *)
next
  case (MExists P V n R \<phi> \<phi>')
  from MExists.prems obtain \<phi>'' t where \<phi>'_eq: "\<phi>' = formula.Exists t \<phi>''"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MExists.prems(3) obtain t where "S, case_nat t E \<turnstile> \<phi>''"
    by (cases rule: wty_formula.cases) (auto simp: \<phi>'_eq)
  with MExists.prems show ?case
    unfolding \<phi>'_eq
    by (cases rule: wf_mformula.cases)
      (force simp: list.rel_map fvi_Suc sat_fv_cong nth_Cons'
        intro!: wf_mformula.Exists dest!: MExists.IH qtable_project_fv
        elim!: list.rel_mono_strong table_fvi_tl qtable_cong sat_fv_cong[THEN iffD1, rotated -1]
        split: if_splits)+
next
  case (MAgg args \<phi>)
  let ?tys = "aggargs_tys args"
  from MAgg.prems(1) obtain \<phi>'' where
    \<phi>'_eq: "\<phi>' = formula.Agg (aggargs_y args) (aggargs_\<omega> args) ?tys (aggargs_f args) \<phi>''"
    and wf\<phi>: "wf_mformula \<sigma> j P V (length ?tys + n) (lift_envs' (length ?tys) R) \<phi> \<phi>''"
    and y: "aggargs_y args < n" and fresh: "aggargs_y args + length ?tys \<notin> Formula.fv \<phi>''"
    and b_fv: "{0..<length ?tys} \<subseteq> Formula.fv \<phi>''"
    and f_fv: "Formula.fv_trm (aggargs_f args) \<subseteq> Formula.fv \<phi>''"
    and g0: "aggargs_g0 args = (Formula.fv \<phi>'' \<subseteq> {0..<length ?tys})"
    and cols: "aggargs_cols args = Formula.fv \<phi>''" and an: "aggargs_n args = n"
    and safe: "safe_formula \<phi>''"
    by (cases rule: wf_mformula.cases) auto
  from MAgg.prems(3) have wty: "S, agg_env E ?tys \<turnstile> \<phi>''"
    unfolding \<phi>'_eq by (cases rule: wty_formula.cases) auto
  obtain xs \<phi>n where eq_\<phi>: "meval (j + \<delta>) (length ?tys + n) (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi> = (xs, \<phi>n)"
    by (elim prod.exhaust)
  note IH = MAgg.IH[OF wf\<phi> MAgg.prems(2) wty, unfolded eq_\<phi> prod.case]
  have meval_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db (MAgg args \<phi>) =
      (map (eval_aggargs args) xs, MAgg args \<phi>n)"
    by (simp only: meval.simps Let_def eq_\<phi> prod.case)
  have wf_new: "wf_mformula \<sigma> (j + \<delta>) P' V n R (MAgg args \<phi>n) \<phi>'"
    unfolding \<phi>'_eq
    by (rule wf_mformula.Agg[OF IH[THEN conjunct1] y fresh b_fv f_fv g0 cols an refl refl refl refl safe])
  have fv_bound: "\<forall>x\<in>Formula.fv \<phi>'. x < n"
    using wf_mformula_wf_set[OF MAgg.prems(1), unfolded wf_set_def] .
  have prog: "progress \<sigma> Q \<phi>' k = progress \<sigma> Q \<phi>'' k" for Q k
    by (simp add: \<phi>'_eq)
  have step: "qtable n (Formula.fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')
      (eval_aggargs args X)"
    if "qtable (length ?tys + n) (Formula.fv \<phi>'') (mem_restr (lift_envs' (length ?tys) R))
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'') X" for i X
    unfolding \<phi>'_eq eval_aggargs_def an
    by (rule qtable_eval_agg[OF that fv_bound[unfolded \<phi>'_eq] fresh b_fv f_fv g0])
  have out: "list_all2 (\<lambda>i. qtable n (Formula.fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'))
      [progress \<sigma> P \<phi>' j..<progress \<sigma> P' \<phi>' (j + \<delta>)] (map (eval_aggargs args) xs)"
    unfolding prog list.rel_map using IH[THEN conjunct2] by (rule list_all2_mono) (rule step)
  show ?case
    unfolding meval_eq prod.case using wf_new out by (rule conjI)
next
  case (MPrev I \<phi> first buf nts)
  from MPrev.prems show ?case
  proof (cases rule: wf_mformula.cases)
    case (Prev \<psi>)
    from MPrev.prems(3) have wty: "S, E \<turnstile> \<psi>"
      unfolding Prev(1) by (rule wty_formula_PrevD)
    let ?ts = "map (\<tau> \<sigma>) [j ..< j + \<delta>]"
    let ?p = "progress \<sigma> P \<psi> j"
    let ?p' = "progress \<sigma> P' \<psi> (j + \<delta>)"
    let ?i = "min ?p (j - 1)"
    let ?Q = "\<lambda>i X. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) X"
    obtain xs \<phi>n where eq_\<phi>: "meval (j + \<delta>) n ?ts db \<phi> = (xs, \<phi>n)"
      by (elim prod.exhaust)
    note IH = MPrev.IH[OF Prev(2) MPrev.prems(2) wty, unfolded eq_\<phi> prod.case]
    note p_le = wf_envs_progress_le[OF MPrev.prems(2), of \<psi>]
    note p_p' = wf_envs_progress_mono[OF MPrev.prems(2), of \<psi>]
    show ?thesis
    proof (cases "first \<and> ?ts = []")
      case True
      then have j: "j = 0" and \<delta>: "\<delta> = 0"
        using Prev(4) by auto
      from p_le j \<delta> have p: "?p = 0" and p': "?p' = 0"
        by simp_all
      from IH[THEN conjunct2] p p' have xs: "xs = []"
        by simp
      from Prev(5) p have buf: "buf = []"
        by simp
      from Prev(6) j have nts: "nts = []"
        by simp
      have meval_eq: "meval (j + \<delta>) n ?ts db (MPrev I \<phi> first buf nts) =
          ([], MPrev I \<phi>n True (buf @ xs) (nts @ ?ts))"
        by (simp only: meval.simps Let_def eq_\<phi> prod.case if_P[OF True])
      have wf_new: "wf_mformula \<sigma> (j + \<delta>) P' V n R (MPrev I \<phi>n True (buf @ xs) (nts @ ?ts)) \<phi>'"
        unfolding Prev(1)
      proof (rule wf_mformula.Prev[OF IH[THEN conjunct1] Prev(3)])
        show "True \<longleftrightarrow> j + \<delta> = 0"
          using j \<delta> by simp
        show "list_all2 ?Q [min ?p' (j + \<delta> - 1)..<?p'] (buf @ xs)"
          using p' buf xs by simp
        show "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min ?p' (j + \<delta> - 1)..<j + \<delta>] (nts @ ?ts)"
          using j \<delta> nts by simp
      qed
      have out: "list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'))
          [progress \<sigma> P \<phi>' j..<progress \<sigma> P' \<phi>' (j + \<delta>)] []"
        using j \<delta> by (simp add: Prev(1))
      show ?thesis
        unfolding meval_eq prod.case using wf_new out by (rule conjI)
    next
      case False
      have jd: "0 < j + \<delta>"
      proof (rule ccontr)
        assume "\<not> 0 < j + \<delta>"
        then have "j = 0" "\<delta> = 0"
          by simp_all
        then show False
          using False Prev(4) by simp
      qed
      then obtain m where m: "j + \<delta> = Suc m"
        using gr0_implies_Suc by blast
      obtain zs buf' nts' where eq_mpn: "mprev_next I (buf @ xs) (nts @ ?ts) = (zs, buf', nts')"
        by (elim prod_cases3)
      have meval_eq: "meval (j + \<delta>) n ?ts db (MPrev I \<phi> first buf nts) =
          (if first then empty_table # zs else zs, MPrev I \<phi>n False buf' nts')"
        by (simp only: meval.simps Let_def eq_\<phi> eq_mpn prod.case if_not_P[OF False])
      have ts_rel: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [j..<j + \<delta>] ?ts"
        unfolding list.rel_map by (rule list.rel_refl) (rule refl)
      have buf_xs: "list_all2 ?Q [?i..<?p'] (buf @ xs)"
        by (rule list_all2_upt_append[OF Prev(5) IH[THEN conjunct2]]) (use p_p' in simp_all)
      have nts_ts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?i..<j + \<delta>] (nts @ ?ts)"
        by (rule list_all2_upt_append[OF Prev(6) ts_rel]) simp_all
      have i_le: "?i \<le> ?p'" and i_le': "?i \<le> j + \<delta>" and i_ne: "?i \<noteq> j + \<delta>"
        using p_p' p_le jd by linarith+
      note mprev_res = mprev[OF eq_mpn buf_xs nts_ts i_le i_le', unfolded if_not_P[OF i_ne]]
      have step: "qtable n (fv (Formula.Prev I \<psi>)) (mem_restr R)
          (\<lambda>v. Formula.sat \<sigma> V (map the v) (Suc l) (Formula.Prev I \<psi>)) X"
        if "if mem I (\<tau> \<sigma> (Suc l) - \<tau> \<sigma> l) then ?Q l X else X = empty_table" for l X
        using that by (cases "mem I (\<tau> \<sigma> (Suc l) - \<tau> \<sigma> l)") (auto simp: qtable_empty_iff)
      have zs: "list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'))
          [Suc ?i..<Suc (min ?p' (j + \<delta> - 1))] zs"
        unfolding Prev(1) map_Suc_upt[symmetric] list.rel_map
        using mprev_res[THEN conjunct1] by (rule list_all2_mono) (rule step)
      have prog': "progress \<sigma> P' \<phi>' (j + \<delta>) = Suc (min ?p' (j + \<delta> - 1))"
        by (simp add: Prev(1) m)
      have wf_new: "wf_mformula \<sigma> (j + \<delta>) P' V n R (MPrev I \<phi>n False buf' nts') \<phi>'"
        unfolding Prev(1)
      proof (rule wf_mformula.Prev[OF IH[THEN conjunct1] Prev(3)])
        show "False \<longleftrightarrow> j + \<delta> = 0"
          using jd by simp
        show "list_all2 ?Q [min ?p' (j + \<delta> - 1)..<?p'] buf'"
          by (rule mprev_res[THEN conjunct2, THEN conjunct1])
        show "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min ?p' (j + \<delta> - 1)..<j + \<delta>] nts'"
          by (rule mprev_res[THEN conjunct2, THEN conjunct2])
      qed
      have out: "list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'))
          [progress \<sigma> P \<phi>' j..<progress \<sigma> P' \<phi>' (j + \<delta>)] (if first then empty_table # zs else zs)"
      proof (cases first)
        case first_T: True
        with Prev(4) have j: "j = 0"
          by simp
        then have i0: "?i = 0" and prog: "progress \<sigma> P \<phi>' j = 0"
          by (simp_all add: Prev(1))
        have empty: "qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) 0 \<phi>') empty_table"
          by (simp add: Prev(1) qtable_empty_iff)
        show ?thesis
          unfolding prog prog' if_P[OF first_T] upt_conv_Cons[OF zero_less_Suc] list.rel_inject
          using empty zs[unfolded i0] by (rule conjI)
      next
        case first_F: False
        with Prev(4) obtain j0 where "j = Suc j0"
          using not0_implies_Suc by blast
        then have prog: "progress \<sigma> P \<phi>' j = Suc ?i"
          by (simp add: Prev(1))
        show ?thesis
          unfolding prog prog' if_not_P[OF first_F] by (rule zs)
      qed
      show ?thesis
        unfolding meval_eq prod.case using wf_new out by (rule conjI)
    qed
  qed
next
  case (MNext I \<phi> first nts)
  from MNext.prems show ?case
  proof (cases rule: wf_mformula.cases)
    case (Next \<psi>)
    from MNext.prems(3) have wty: "S, E \<turnstile> \<psi>"
      unfolding Next(1) by (rule wty_formula_NextD)
    let ?ts = "map (\<tau> \<sigma>) [j ..< j + \<delta>]"
    let ?p = "progress \<sigma> P \<psi> j"
    let ?p' = "progress \<sigma> P' \<psi> (j + \<delta>)"
    let ?Q = "\<lambda>i X. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) X"
    obtain xs \<phi>n where eq_\<phi>: "meval (j + \<delta>) n ?ts db \<phi> = (xs, \<phi>n)"
      by (elim prod.exhaust)
    note IH = MNext.IH[OF Next(2) MNext.prems(2) wty, unfolded eq_\<phi> prod.case]
    note p_le = wf_envs_progress_le[OF MNext.prems(2), of \<psi>]
    note p_p' = wf_envs_progress_mono[OF MNext.prems(2), of \<psi>]
    have prog: "progress \<sigma> Q (Formula.Next I \<psi>) k = progress \<sigma> Q \<psi> k - 1" for Q k
      by simp
    have ts_rel: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [j..<j + \<delta>] ?ts"
      unfolding list.rel_map by (rule list.rel_refl) (rule refl)
    have nts_ts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?p - 1..<j + \<delta>] (nts @ ?ts)"
      by (rule list_all2_upt_append[OF Next(5) ts_rel]) (use p_le in simp_all)
    show ?thesis
    proof (cases "?p < ?p'")
      case False
      with p_p' have pp': "?p' = ?p"
        by linarith
      from IH[THEN conjunct2] pp' have xs: "xs = []"
        by simp
      have meval_eq: "meval (j + \<delta>) n ?ts db (MNext I \<phi> first nts) = ([], MNext I \<phi>n first (nts @ ?ts))"
        by (simp add: eq_\<phi> xs Let_def)
      have wf_new: "wf_mformula \<sigma> (j + \<delta>) P' V n R (MNext I \<phi>n first (nts @ ?ts)) \<phi>'"
        unfolding Next(1)
      proof (rule wf_mformula.Next[OF IH[THEN conjunct1] Next(3)])
        show "first \<longleftrightarrow> ?p' = 0"
          using Next(4) pp' by simp
        show "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?p' - 1..<j + \<delta>] (nts @ ?ts)"
          unfolding pp' by (rule nts_ts)
      qed
      have out: "list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'))
          [progress \<sigma> P \<phi>' j..<progress \<sigma> P' \<phi>' (j + \<delta>)] []"
        unfolding Next(1) prog pp' by simp
      show ?thesis
        unfolding meval_eq prod.case using wf_new out by (rule conjI)
    next
      case True
      have "xs \<noteq> []"
        using True list_all2_lengthD[OF IH[THEN conjunct2]] by (cases xs) simp_all
      then obtain x xs0 where xs: "xs = x # xs0"
        by (meson neq_Nil_conv)
      note xs_rel = IH[THEN conjunct2, unfolded xs]
      define ys where "ys = (if first then xs0 else x # xs0)"
      have ys_rel: "list_all2 ?Q [Suc (?p - 1)..<?p'] ys"
      proof (cases first)
        case first_T: True
        with Next(4) have p0: "?p = 0"
          by simp
        show ?thesis
          unfolding ys_def using first_T p0 True xs_rel by (simp add: upt_conv_Cons)
      next
        case first_F: False
        with Next(4) have "0 < ?p"
          by simp
        then show ?thesis
          unfolding ys_def using first_F xs_rel by simp
      qed
      obtain zs buf' nts' where eq_mpn: "mprev_next I ys (nts @ ?ts) = (zs, buf', nts')"
        by (elim prod_cases3)
      have meval_eq: "meval (j + \<delta>) n ?ts db (MNext I \<phi> first nts) = (zs, MNext I \<phi>n False nts')"
        using eq_mpn unfolding ys_def by (cases first) (simp_all add: eq_\<phi> xs Let_def)
      have le1: "Suc (?p - 1) \<le> ?p'" and le2: "?p - 1 \<le> j + \<delta>"
        and ne: "?p - 1 \<noteq> j + \<delta>" and mn: "min (?p' - 1) (j + \<delta> - 1) = ?p' - 1"
        using True p_le by linarith+
      note mnext_res = mnext[OF eq_mpn ys_rel nts_ts le1 le2, unfolded if_not_P[OF ne] mn]
      have step: "qtable n (fv (Formula.Next I \<psi>)) (mem_restr R)
          (\<lambda>v. Formula.sat \<sigma> V (map the v) l (Formula.Next I \<psi>)) X"
        if "if mem I (\<tau> \<sigma> (Suc l) - \<tau> \<sigma> l) then ?Q (Suc l) X else X = empty_table" for l X
        using that by (cases "mem I (\<tau> \<sigma> (Suc l) - \<tau> \<sigma> l)") (auto simp: qtable_empty_iff)
      have wf_new: "wf_mformula \<sigma> (j + \<delta>) P' V n R (MNext I \<phi>n False nts') \<phi>'"
        unfolding Next(1)
      proof (rule wf_mformula.Next[OF IH[THEN conjunct1] Next(3)])
        show "False \<longleftrightarrow> ?p' = 0"
          using True by simp
        show "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?p' - 1..<j + \<delta>] nts'"
          by (rule mnext_res[THEN conjunct2, THEN conjunct2])
      qed
      have out: "list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'))
          [progress \<sigma> P \<phi>' j..<progress \<sigma> P' \<phi>' (j + \<delta>)] zs"
        unfolding Next(1) prog
        using mnext_res[THEN conjunct1] by (rule list_all2_mono) (rule step)
      show ?thesis
        unfolding meval_eq prod.case using wf_new out by (rule conjI)
    qed
  qed
next
  case (MSince args \<phi> \<psi> buf  aux db P P' V n' R' \<phi>')
  note sat.simps[simp del]
  from MSince.prems obtain \<phi>'' \<phi>''' \<psi>'' I n R pos where Since_eq: "\<phi>' = packagg args (Formula.Since \<phi>''' I \<psi>'')"
    and pos: "if args_pos args then \<phi>''' = \<phi>'' else \<phi>''' = Formula.Neg \<phi>''"
    and safe1: "safe_formula \<phi>''"
    and safe2: "safe_formula \<psi>''"
    and \<phi>: "wf_mformula \<sigma> j P V n R \<phi> \<phi>''"
    and \<psi>: "wf_mformula \<sigma> j P V n R \<psi> \<psi>''"
    and fvi_subset: "Formula.fv \<phi>'' \<subseteq> Formula.fv \<psi>''"
    and buf: "wf_mbuf2S \<sigma> P V j n R \<phi>'' I \<psi>'' buf (min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j))
      (progress \<sigma> P (Sincep (args_pos args) \<phi>'' I \<psi>'') j)"
    and aux: "wf_since_aux \<sigma> V R args \<phi>'' \<psi>'' aux (min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j))
      (progress \<sigma> P (Sincep (args_pos args) \<phi>'' I \<psi>'') j)"
    and args: "args_ivl args = I" "args_n args = n" "args_L args = Formula.fv \<phi>''"
    "args_R args = Formula.fv \<psi>''" "args_pos args = pos"
    "mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')" "agg_n args = n'"
    by (cases rule: wf_mformula.cases)
      (auto simp: Sincep_def 
        dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E split: if_splits)

  obtain E' where wty_Since: "S, E' \<turnstile> Formula.Since \<phi>''' I \<psi>''"
  proof (cases "args_agg args")
    case None
    with MSince.prems(3) have "S, E \<turnstile> Formula.Since \<phi>''' I \<psi>''"
      by (simp add: Since_eq packagg_def)
    then show ?thesis
      by (rule that)
  next
    case (Some aggargs)
    with MSince.prems(3) have "S, E \<turnstile> Formula.Agg (aggargs_y aggargs) (aggargs_\<omega> aggargs)
        (aggargs_tys aggargs) (aggargs_f aggargs) (Formula.Since \<phi>''' I \<psi>'')"
      by (simp add: Since_eq packagg_def)
    then have "S, agg_env E (aggargs_tys aggargs) \<turnstile> Formula.Since \<phi>''' I \<psi>''"
      by (cases rule: wty_formula.cases) auto
    then show ?thesis
      by (rule that)
  qed
  from wty_Since have wty\<psi>: "S, E' \<turnstile> \<psi>''"
    by (rule wty_formula_SinceD(2))
  from pos wty_formula_SinceD(1)[OF wty_Since] have wty\<phi>: "S, E' \<turnstile> \<phi>''"
    by (cases "args_pos args") (auto dest: wty_formula_NegD)
  have valid_aggargs: "valid_aggargs n (fv \<psi>'') (args_agg args)"
    using aux
    by (auto simp: wf_since_aux_def args)
  obtain xs \<phi>n where eq1: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi> = (xs, \<phi>n)"
    by (elim prod.exhaust)
  note meval1 = MSince.IH(1)[OF \<phi> MSince.prems(2) wty\<phi>, unfolded eq1 prod.case]
  obtain ys \<psi>n where eq2: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<psi> = (ys, \<psi>n)"
    by (elim prod.exhaust)
  note meval2 = MSince.IH(2)[OF \<psi> MSince.prems(2) wty\<psi>, unfolded eq2 prod.case]
  obtain zs buf' aux' where eval_eq: "(zs, buf', aux') 
    = eval_since args [] (mbuf2S_add xs ys (map (\<tau> \<sigma>) [j..<j + \<delta>]) buf) aux"
    by (metis surj_pair)
  have env: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j + \<delta>) P'" "rel_mapping (\<le>) P P'"
    using MSince.prems(2) unfolding wf_envs_def by auto
  have alt:
    "progress \<sigma> P (packagg args (Sincep (args_pos args) \<phi>'' I \<psi>'')) j = progress \<sigma> P \<phi>' j" for P j
    using pos fvi_subset by (simp add: Since_eq Sincep_def)
  then show ?case
    unfolding meval.simps args(2) eq1 eq2 Let_def prod.case eval_eq[symmetric]
    using meval1[THEN conjunct1] meval2[THEN conjunct1]
      eval_since[OF eval_eq buf aux meval1[THEN conjunct2] meval2[THEN conjunct2] env fvi_subset args(1-4) _ args(6-7)]
      pos fvi_subset args safe1 safe2
    by (auto simp add: Since_eq args(1) Sincep_def simp del: progress_simps 
        intro!: wf_mformula.Since split:option.splits)
next
  case (MUntil args \<phi> \<psi> buf nts t aux  db P P' V n' R' \<phi>')
  note sat.simps[simp del] progress_simps[simp del]
  from MUntil.prems obtain \<phi>'' \<phi>''' \<psi>'' I n R where Until_eq: "\<phi>' = packagg args (Formula.Until \<phi>''' I \<psi>'')"
    and pos: "if args_pos args then \<phi>''' = \<phi>'' else \<phi>''' = Formula.Neg \<phi>''"
    and safe1: "safe_formula \<phi>''"
    and safe2: "safe_formula \<psi>''"
    and \<phi>: "wf_mformula \<sigma> j P V n R \<phi> \<phi>''"
    and \<psi>: "wf_mformula \<sigma> j P V n R \<psi> \<psi>''"
    and fvi_subset: "Formula.fv \<phi>'' \<subseteq> Formula.fv \<psi>''"
    and buf: "wf_mbuf2' \<sigma> P V j n R \<phi>'' \<psi>'' buf"
    and nts: "wf_ts \<sigma> P j \<phi>'' \<psi>'' nts"
    and aux: "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux (progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j)"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_L: "args_L args = Formula.fv \<phi>''"
    and args_R: "args_R args = Formula.fv \<psi>''"
    and mr: "mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')"
    and agg_n: "agg_n args = n'"
    and t: "t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j))))"
    and length_aux: "progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j + length_muaux args aux =
      min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)"
    by (cases rule: wf_mformula.cases) 
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  obtain E' where wty_Until: "S, E' \<turnstile> Formula.Until \<phi>''' I \<psi>''"
  proof (cases "args_agg args")
    case None
    with MUntil.prems(3) have "S, E \<turnstile> Formula.Until \<phi>''' I \<psi>''"
      by (simp add: Until_eq packagg_def)
    then show ?thesis
      by (rule that)
  next
    case (Some aggargs)
    with MUntil.prems(3) have "S, E \<turnstile> Formula.Agg (aggargs_y aggargs) (aggargs_\<omega> aggargs)
        (aggargs_tys aggargs) (aggargs_f aggargs) (Formula.Until \<phi>''' I \<psi>'')"
      by (simp add: Until_eq packagg_def)
    then have "S, agg_env E (aggargs_tys aggargs) \<turnstile> Formula.Until \<phi>''' I \<psi>''"
      by (cases rule: wty_formula.cases) auto
    then show ?thesis
      by (rule that)
  qed
  from wty_Until have wty\<psi>: "S, E' \<turnstile> \<psi>''"
    by (rule wty_formula_UntilD(2))
  from pos wty_formula_UntilD(1)[OF wty_Until] have wty\<phi>: "S, E' \<turnstile> \<phi>''"
    by (cases "args_pos args") (auto dest: wty_formula_NegD)
  define pos where args_pos: "pos = args_pos args"
  have \<phi>''': "progress \<sigma> P \<phi>''' j = progress \<sigma> P \<phi>'' j"  "progress \<sigma> P' \<phi>''' j = progress \<sigma> P' \<phi>'' j" for j
    using pos by (simp_all add: progress.simps split: if_splits)
  have valid_aggargs: "valid_aggargs n (fv \<psi>'') (args_agg args)"
    using aux
    by (auto simp: wf_until_aux_def args_n)
  from MUntil.prems(2) have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts unfolding wf_ts_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_le[THEN min.coboundedI1] list.rel_map
      intro!: list_all2_appendI list.rel_refl)
  obtain xs \<phi>n where eq_\<phi>: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi> = (xs, \<phi>n)"
    by (elim prod.exhaust)
  obtain ys \<psi>n where eq_\<psi>: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<psi> = (ys, \<psi>n)"
    by (elim prod.exhaust)
  obtain aux' buf' nt nts' where eq1: "mbuf2t_take (add_new_muaux args) aux (mbuf2_add xs ys buf) t
      (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]) = (aux', buf', nt, nts')"
    by (elim prod_cases4)
  obtain zs aux'' where eq2: "eval_muaux args nt aux' = (zs, aux'')"
    by (elim prod.exhaust)
  note IH\<phi> = MUntil.IH(1)[OF \<phi> MUntil.prems(2) wty\<phi>, unfolded eq_\<phi> prod.case]
  note IH\<psi> = MUntil.IH(2)[OF \<psi> MUntil.prems(2) wty\<psi>, unfolded eq_\<psi> prod.case]
  have Untilp_eq: "Untilp pos \<phi>'' I \<psi>'' = Formula.Until \<phi>''' I \<psi>''"
    using pos by (cases "args_pos args") (simp_all add: Untilp_def args_pos)
  from update_until'[OF IH\<phi>[THEN conjunct2] IH\<psi>[THEN conjunct2] eq1 eq2 pos MUntil.prems(2)
      fvi_subset buf nts aux args_ivl args_n args_L args_R args_pos t refl length_aux nts_snoc
      mr valid_aggargs]
  obtain wf_aux'': "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux'' (progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>))"
    and len_zs: "progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j + length zs =
      progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)"
    and len_aux'': "progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j + length zs + length_muaux args aux'' =
      min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
    and zs: "list_all2 (\<lambda>i. qtable (agg_n args) (Formula.fv (packagg args (Formula.Until \<phi>''' I \<psi>'')))
        (mem_restr R') (\<lambda>v. Formula.sat \<sigma> V (map the v) i (packagg args (Formula.Until \<phi>''' I \<psi>''))))
      [progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j..<progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j + length zs] zs"
    and nt: "nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1)
      (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))))"
    unfolding Untilp_eq by blast
  note buf'_nts' = mbuf2t_take_add'[OF eq1 wf_envs_P_simps[OF MUntil.prems(2)] buf nts_snoc
      IH\<phi>[THEN conjunct2] IH\<psi>[THEN conjunct2] le_add1]
  have len: "progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>) + length_muaux args aux'' =
      min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
    using len_zs len_aux'' \<phi>'''(2)[of "j + \<delta>"] by linarith
  have wf_new: "wf_mformula \<sigma> (j + \<delta>) P' V n' R' (MUntil args \<phi>n \<psi>n buf' nts' nt aux'') \<phi>'"
    unfolding Until_eq agg_n[symmetric]
    by (rule wf_mformula.Until[OF IH\<phi>[THEN conjunct1] IH\<psi>[THEN conjunct1] pos safe1 safe2 args_ivl
        args_n args_L args_R mr fvi_subset buf'_nts' nt wf_aux'' len])
  have out: "list_all2 (\<lambda>i. qtable n' (Formula.fv \<phi>') (mem_restr R') (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'))
      [progress \<sigma> P \<phi>' j..<progress \<sigma> P' \<phi>' (j + \<delta>)] zs"
    using zs unfolding Until_eq progress_packagg agg_n len_zs .
  have meval_eq: "meval (j + \<delta>) n' (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MUntil args \<phi> \<psi> buf nts t aux) =
      (zs, MUntil args \<phi>n \<psi>n buf' nts' nt aux'')"
    by (simp add: args_n eq_\<phi> eq_\<psi> eq1 eq2 Let_def)
  show ?case
    unfolding meval_eq prod.case using wf_new out by (rule conjI)
next
  case (MTrigger args \<phi> \<psi> buf nts aux db P P' V)
  from MTrigger.prems obtain \<gamma> I \<alpha> \<beta>
    where phi'_eq: "\<phi>' = Formula.Trigger \<alpha> I \<beta>"
      and pos: "if args_pos args then \<alpha> = \<gamma> else \<alpha> = formula.Neg \<gamma>"
      and pos_eq: "safe_formula \<alpha> = args_pos args"
      and \<phi>: "wf_mformula \<sigma> j P V n R \<phi> \<gamma>"
      and \<psi>: "wf_mformula \<sigma> j P V n R \<psi> \<beta>"
      and fvi_subset: "if mem I 0 then fv \<gamma> \<subseteq> fv \<beta> else fv \<gamma> = fv \<beta>"
      and buf: "wf_mbuf2' \<sigma> P V j n R \<gamma> \<beta> buf"
      and nts: "wf_ts \<sigma> P j \<gamma> \<beta> nts"
      and aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux (Progress.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)"
      and args_ivl: "args_ivl args = I"
      and args_n: "args_n args = n"
      and args_L: "args_L args = fv \<gamma>"
      and args_R: "args_R args = fv \<beta>"
      and fv_l_n: "\<forall>x\<in>fv \<beta>. x < n"
      and mem0: "mem I 0"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)

  have "S, E \<turnstile> \<alpha>" "S, E \<turnstile> \<beta>" "S, E \<turnstile> \<gamma>"
    using wty_formula_TriggerD[OF MTrigger.prems(3)[unfolded phi'_eq]] 
      pos wty_formula_NegD[of S E \<gamma>]
    by (auto elim!: wty_formulaD split: if_splits)

  have args_props:
    "args_n args = n"
    "args_R args = fv \<alpha> \<union> fv \<beta>"
    "fv \<gamma> = fv \<alpha>"
    using pos args_n args_L args_R fvi_subset
    by (auto split: if_splits)

  note IH_\<phi> = MTrigger.IH(1)[OF \<phi> MTrigger.prems(2) \<open>S, E \<turnstile> \<gamma>\<close>]
  note IH_\<psi> = MTrigger.IH(2)[OF \<psi> MTrigger.prems(2) \<open>S, E \<turnstile> \<beta>\<close>]

  define zs where "zs = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MTrigger args \<phi> \<psi> buf nts aux))"
  define \<eta> where "\<eta> = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MTrigger args \<phi> \<psi> buf nts aux))"

  define xs where "xs = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)"
  define \<gamma>' where "\<gamma>' = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)"

  have \<phi>_pair_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> = (xs, \<gamma>')"
    unfolding xs_def \<gamma>'_def
    by auto

  have \<gamma>_props:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<gamma>' \<gamma>"
    "list_all2 (\<lambda>i. qtable n (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>)) [Progress.progress \<sigma> P \<gamma> j..<Progress.progress \<sigma> P' \<gamma> (j + \<delta>)] xs"
    using IH_\<phi>
    unfolding \<phi>_pair_eq
    by auto

  define ys where "ys = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi>)"
  define \<beta>' where "\<beta>' = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi>)"

  have \<psi>_pair_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi> = (ys, \<beta>')"
    unfolding ys_def \<beta>'_def
    by auto

  have \<beta>_props:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<beta>' \<beta>"
    "list_all2 (\<lambda>i. qtable n (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>)) [Progress.progress \<sigma> P \<beta> j..<Progress.progress \<sigma> P' \<beta> (j + \<delta>)] ys"
    using IH_\<psi>
    unfolding \<psi>_pair_eq
    by auto

  define tuple where "tuple = mbuf2T_take (\<lambda>r1 r2 t (zs, aux). let
    aux = update_mtaux args t r1 r2 aux;
    (fv_z, z) = result_mtaux args aux
    in
      (zs @ [z], aux)
  ) ([], aux) (mbuf2_add xs ys buf) (nts @ map (\<tau> \<sigma>) [j..<j + \<delta>])"

  have zs_eq: "zs = fst (fst tuple)"
    unfolding tuple_def zs_def meval.simps Let_def xs_def ys_def
    by (auto split: prod.splits)

  define aux' where "aux' = snd (fst tuple)"
  define buf' where "buf' = fst (snd tuple)"
  define nts' where "nts' = snd (snd tuple)"

  have tuple_eq: "tuple = ((zs, aux'), buf', nts')"
    unfolding zs_eq aux'_def buf'_def nts'_def Let_def
    by auto

  have \<eta>_eq: "\<eta> = MTrigger args \<gamma>' \<beta>' buf' nts' aux'"
    unfolding \<eta>_def meval.simps \<gamma>'_def \<beta>'_def aux'_def buf'_def nts'_def tuple_def xs_def ys_def Let_def
    by (auto split: prod.splits)

  have pred_mapping:
    "pred_mapping (\<lambda>i. i \<le> j) P"
    "pred_mapping (\<lambda>i. i \<le> j + \<delta>) P'"
    "rel_mapping (\<le>) P P'"
    using MTrigger.prems(2)
    by auto

  from MTrigger.prems(2) have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> P \<gamma> j) (progress \<sigma> P \<beta> j)..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts
    unfolding wf_ts_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_le[THEN min.coboundedI1] list.rel_map
      intro!: list_all2_appendI list.rel_refl)

  have wf_buf_ts:
    "wf_mbuf2' \<sigma> P' V (j + \<delta>) n R \<gamma> \<beta> buf'"
    "wf_ts \<sigma> P' (j + \<delta>) \<gamma> \<beta> nts'"
    using mbuf2T_take_add'[OF tuple_eq[unfolded tuple_def] pred_mapping buf nts_snoc \<gamma>_props(2) \<beta>_props(2)]
    by auto

  have \<alpha>_\<gamma>_props: "Formula.fv \<alpha> = Formula.fv \<gamma>" "progress \<sigma> P \<alpha> j = progress \<sigma> P \<gamma> j"
  "progress \<sigma> P' \<alpha> j = progress \<sigma> P' \<gamma> j" for j
    using pos
    by (simp_all split: if_splits)

  have update: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (snd (zs, aux')) (Progress.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>)) \<and>
  list_all2 (\<lambda>i. qtable n (Formula.fv \<alpha> \<union> Formula.fv \<beta>) (mem_restr R)
    (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)))
    [progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j..<progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>)] (fst (zs, aux'))"
  unfolding progress_simps \<alpha>_\<gamma>_props
  proof (rule mbuf2T_take_add_induct'[where j=j and j'="j + \<delta>" and z'="(zs, aux')",
      OF tuple_eq[unfolded tuple_def] wf_envs_P_simps[OF MTrigger.prems(2)] buf nts_snoc],
      goal_cases xs ys _ base step)
    case xs
    then show ?case using \<gamma>_props(2) by auto
  next
    case ys
    then show ?case using \<beta>_props(2) by auto
  next
    case base
    then show ?case
      using aux \<alpha>_\<gamma>_props
      unfolding progress_simps 
      by auto
  next
    case (step k X Y acc)
    define zs where "zs = fst acc"
    define aux where "aux = snd acc"
    have z_eq: "acc = (zs, aux)"
      unfolding zs_def aux_def
      by auto

    have table:
      "table (args_n args) (args_L args) X"
      "table (args_n args) (args_R args) Y"
      using step(4-5) args_n args_L args_R
      unfolding qtable_def
      by auto

    define zs' where "zs' = fst (let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [z], aux))"
    define aux' where "aux' = snd (let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [z], aux))"
    define cur' where "cur' = \<tau> \<sigma> k"

    have wf_trigger: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux k"
      using step(6)
      unfolding aux_def
      by auto
    then have fv_subset: "fv \<gamma> \<subseteq> fv \<beta> "
      unfolding wf_trigger_aux_def
      by auto

    have wf_trigger_aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (update_mtaux args (\<tau> \<sigma> k) X Y aux) (Suc k)"
      using update_trigger[OF wf_trigger step(4-5) args_n args_L args_R]
      by auto

    then obtain auxlist' where
      valid_mtaux: "valid_mtaux args (\<tau> \<sigma> k) (update_mtaux args (\<tau> \<sigma> k) X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')" and
      sorted_wrt: "sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist'" and
      auxlist_len: "length auxlist' = Suc k" and
      auxlist_props: "(\<forall>(i, t, l, r)\<in>set (zip [0..<length auxlist'] auxlist').
         Suc k \<noteq> 0 \<and>
         t = \<tau> \<sigma> i \<and>
         t \<le> \<tau> \<sigma> k \<and>
         qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l \<and>
         qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r
      )" and
      auxlist_mem: "(\<forall>i.
          Suc k \<noteq> 0 \<and>
          i \<le> k
          \<longrightarrow>
          (\<exists>X. (\<tau> \<sigma> i, X) = auxlist'!i)
      )"
      unfolding wf_trigger_aux_def
      by auto

    then have sorted: "sorted (map fst auxlist')"
      using sorted_wrt
      by (simp add: sorted_map)
    have "\<exists>X. (\<tau> \<sigma> k, X) \<in> set auxlist'"
      using auxlist_mem auxlist_len
      by (metis Zero_not_Suc less_Suc_eq_le nth_mem order_refl)
    then obtain X_tmp where "(\<tau> \<sigma> k, X_tmp) \<in> set (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
      using args_ivl mem0
      by auto
    then have non_empty: "(length (filter (\<lambda> (t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist') > 0)"
      using length_pos_if_in_set[of "(\<tau> \<sigma> k, X_tmp)"]
      by auto
    
    have "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (snd (case acc of (zs, aux) \<Rightarrow> let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [z], aux)))
 (Suc k)"
      using wf_trigger_aux
      unfolding z_eq Let_def
      by (auto split: prod.splits)
    moreover have "list_all2
    (\<lambda>i. qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)))
    [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]
    (fst (case acc of (zs, aux) \<Rightarrow> let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [z], aux)))"
    proof -
      have aux'_eq: "aux' = update_mtaux args (\<tau> \<sigma> k) X Y aux"
        unfolding aux'_def Let_def
        by (auto split: prod.splits)
      define fv_z where "fv_z = fst (result_mtaux args aux')"
      define z where "z = snd (result_mtaux args aux')"
      define auxlist'' where "auxlist'' = (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"

      have valid_mtaux': "valid_mtaux args (\<tau> \<sigma> k) aux' auxlist''"
        unfolding aux'_eq auxlist''_def
        using valid_mtaux
        by auto
      have z_eq: "z = snd (trigger_results args (\<tau> \<sigma> k) auxlist'')"
        unfolding z_def
        using valid_result_mtaux[OF valid_mtaux']
        by (auto)

      have equiv: "(x \<in> z) =
         Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)" if
          restr: "mem_restr R x" and
          wf_x: "wf_tuple (args_n args) (args_R args) x"
        for x
        unfolding z_eq auxlist''_def
        using trigger_sat_equiv[OF restr wf_x pos args_n args_ivl args_L args_R fvi_subset fv_l_n valid_mtaux sorted_wrt auxlist_len auxlist_props auxlist_mem non_empty]
        by auto

      have filter_inv: "(filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist'') = (filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist')"
        unfolding auxlist''_def filter_filter
        by (metis (mono_tags, lifting) case_prod_beta')

      have "result_mtaux args aux' = trigger_results args cur' auxlist''"
        using valid_result_mtaux[OF valid_mtaux]
        unfolding aux'_def cur'_def auxlist''_def
        by auto
      moreover have "(length (filter (\<lambda> (t, _). mem (args_ivl args) (cur' - t)) auxlist'') > 0)"
        using filter_inv non_empty
        unfolding cur'_def auxlist''_def
        by auto
      ultimately have z_eq': "z = {
        tuple. wf_tuple (args_n args) (args_R args) tuple \<and>
          (\<forall>i \<in> {0..<(length auxlist'')}.
            let (t, l, r) = auxlist''!i in
            mem (args_ivl args) (cur' - t) \<longrightarrow> 
            (
              tuple \<in> r \<or>
              (\<exists>j \<in> {i<..<(length auxlist'')}.
                join_cond (args_pos args) ((fst o snd) (auxlist''!j)) (proj_tuple (join_mask (args_n args) (args_L args)) tuple)
              )
            )
          )
        }"
        unfolding z_def
        by auto

      have args_R_simp: "args_R args = fv \<alpha> \<union> fv \<beta>"
        using args_L args_R pos fvi_subset
        by (auto split: if_splits)
      have table: "table n (fv \<alpha> \<union> fv \<beta>) z"
        using z_eq'
        unfolding table_def args_R_simp args_n
        by auto

      have correctness: "(\<And>x. x \<in> z \<Longrightarrow> wf_tuple n (fv \<alpha> \<union> fv \<beta>) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>))"
        using equiv args_props
        by auto

      have completeness: "\<And>x. wf_tuple n (fv \<alpha> \<union> fv \<beta>) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>) \<Longrightarrow> x \<in> z"
        using equiv args_props
        by auto

      have qtable_k: "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k (formula.Trigger \<alpha> I \<beta>)) z"
        using qtableI[OF table correctness completeness]
        by auto

      have zs'_eq: "zs' = zs @ [z]"
        unfolding zs'_def z_def aux'_eq  Let_def
        by (auto split: prod.splits)

      have IH: "list_all2
        (\<lambda>i. qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)))
        [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs"
        using step(6) zs_def args_props(3)
        by auto
      then have "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] = length zs"
        unfolding list_all2_iff
        by auto
      then have len: "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] = length zs'"
        unfolding zs'_eq length_append
        by (simp add: step(1))

      moreover have "(\<forall>(i, r) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] zs').
      qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)"
      proof -
        {
          fix i r
          assume assm: "(i, r) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] zs')"
          
          have "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] = length zs"
            using step(6) zs_def
            unfolding list_all2_iff
            by auto
          moreover have "[min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] @ [k] =
                         [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]"
            by (simp add: step(1))
          ultimately have zip_eq:
            "zip ([min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]) zs' =
             zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs @ zip [k] [z]"
            unfolding zs'_eq
            using zip_append[of "[min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k]" "zs" "[k]" "[z]"]
            by auto
          {
            assume "(i, r) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs)"
            then have "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
              using step(6) args_props(3) zs_def
              unfolding list_all2_iff
              by auto
          }
          moreover {
            assume "(i, r) \<notin> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs)"
            then have "(i, r) = (k, z)"
              using assm zip_eq
              by auto
            then have "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
              using qtable_k
              by auto
          }
          ultimately have "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
            by blast
        }
        then show ?thesis by auto
      qed

      ultimately show ?thesis
        unfolding list_all2_iff zs'_def zs_def aux_def
        by (auto split: prod.splits)
    qed

    ultimately show ?case using args_props(3) by auto
  qed (auto)

  have aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux' (progress \<sigma> P' (\<alpha> \<^bold>T I \<beta>) (j + \<delta>))"
    using update
    by auto

  have "wf_mformula \<sigma> (j + \<delta>) P' V n R \<eta> (formula.Trigger \<alpha> I \<beta>)"
    unfolding \<eta>_eq
    using wf_mformula.Trigger_0[OF \<beta>_props(1) pos \<gamma>_props(1) pos_eq args_ivl 
        args_n args_L args_R fv_l_n mem0 fvi_subset wf_buf_ts aux]
    by auto

  moreover have "list_all2 (\<lambda>i. qtable n (FV (\<alpha> \<^bold>T I \<beta>)) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<alpha> \<^bold>T I \<beta>))
    [progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j..<progress \<sigma> P' (\<alpha> \<^bold>T I \<beta>) (j + \<delta>)] zs"
    using update
    by auto

  ultimately show ?case
    unfolding zs_def \<eta>_def phi'_eq
    by auto
next
  case (MMatchP I mr mrs \<phi>s buf nts aux)
  note sat.simps[simp del] mbufnt_take.simps[simp del] mbufn_add.simps[simp del]
  from MMatchP.prems obtain r \<psi>s where eq: "\<phi>' = Formula.MatchP I r"
    and safe: "Regex.safe_regex fv rgx_safe_pred Past Strict r"
    and mr: "to_mregex r = (mr, \<psi>s)"
    and mrs: "mrs = sorted_list_of_set (RPDs mr)"
    and \<psi>s: "list_all2 (wf_mformula \<sigma> j P V n R) \<phi>s \<psi>s"
    and buf: "wf_mbufn' \<sigma> P V j n R r buf"
    and nts: "wf_ts_regex \<sigma> P j r nts"
    and aux: "wf_matchP_aux \<sigma> V n R I r aux (progress \<sigma> P (Formula.MatchP I r) j)"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  have wty: "\<forall>\<psi>\<in>set \<psi>s. S, E \<turnstile> \<psi>"
  proof
    fix \<psi>
    assume "\<psi> \<in> set \<psi>s"
    from MMatchP.prems(3) have "Regex.pred_regex (wty_formula S E) r"
      unfolding eq by (cases pred: wty_formula) simp_all
    moreover from \<open>\<psi> \<in> set \<psi>s\<close> mr have "\<psi> \<in> safe_atms r"
      by (rule to_mregex_safe_atms)
    ultimately show "S, E \<turnstile> \<psi>"
      by (rule pred_regex_wty_formula)
  qed
  have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> P r j..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts unfolding wf_ts_regex_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_regex_le[OF MMatchP.prems(2)] list.rel_map
      intro!: list_all2_appendI list.rel_refl)
  have update: "wf_matchP_aux \<sigma> V n R I r (snd (zs, aux')) (progress \<sigma> P' (Formula.MatchP I r) (j + \<delta>)) \<and>
    list_all2 (\<lambda>i. qtable n (Formula.fv_regex r) (mem_restr R)
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.MatchP I r)))
      [progress \<sigma> P (Formula.MatchP I r) j..<progress \<sigma> P' (Formula.MatchP I r) (j + \<delta>)] (fst (zs, aux'))"
    if eval: "map (fst o meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db) \<phi>s = xss"
      and eq: "mbufnt_take (\<lambda>rels t (zs, aux).
        case update_matchP n I mr mrs rels t aux of (z, x) \<Rightarrow> (zs @ [z], x))
        ([], aux) (mbufn_add xss buf) 0 (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]) = ((zs, aux'), buf', nt, nts')"
    for xss zs aux' buf' nt nts'
    unfolding progress_simps
  proof (rule mbufnt_take_add_induct'[where j'="j + \<delta>" and z'="(zs, aux')", OF eq wf_envs_P_simps[OF MMatchP.prems(2)] safe mr buf nts_snoc],
      goal_cases xss _ base step)
    case xss
    then show ?case
      using eval \<psi>s wty
      by (auto simp: list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map
          list.rel_flip[symmetric, of _ \<psi>s \<phi>s] dest!: MMatchP.IH(1)[OF _ _ MMatchP.prems(2)]
          elim!: list.rel_mono_strong split: prod.splits)
  next
    case base
    then show ?case
      using aux by auto
  next
    case (step k Xs z)
    then show ?case
      by (auto simp: Un_absorb1 mrs safe mr elim!: update_matchP(1) list_all2_appendI
          dest!: update_matchP(2) split: prod.split)
  qed simp
  then show ?case using \<psi>s wty
    by (auto simp: eq mr mrs safe map_split_alt list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
        list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map intro!: wf_mformula.intros
        elim!: list.rel_mono_strong mbufnt_take_add'(1)[OF _ wf_envs_P_simps[OF MMatchP.prems(2)] safe mr buf nts_snoc]
        mbufnt_take_add'(2)[OF _ wf_envs_P_simps[OF MMatchP.prems(2)] safe mr buf nts_snoc]
        dest!: MMatchP.IH[OF _ _ MMatchP.prems(2)] split: prod.splits)
next
  case (MMatchF I mr mrs \<phi>s buf nts t aux)
  note sat.simps[simp del] mbufnt_take.simps[simp del] mbufn_add.simps[simp del] progress_simps[simp del]
  from MMatchF.prems obtain r \<psi>s where eq: "\<phi>' = Formula.MatchF I r"
    and safe: "Regex.safe_regex fv rgx_safe_pred Futu Strict r"
    and mr: "to_mregex r = (mr, \<psi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and \<psi>s: "list_all2 (wf_mformula \<sigma> j P V n R) \<phi>s \<psi>s"
    and buf: "wf_mbufn' \<sigma> P V j n R r buf"
    and nts: "wf_ts_regex \<sigma> P j r nts"
    and aux: "wf_matchF_aux \<sigma> V n R I r aux (progress \<sigma> P (Formula.MatchF I r) j) 0"
    and t: "t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (progress_regex \<sigma> P r j)))"
    and length_aux: "progress \<sigma> P (Formula.MatchF I r) j + length aux = progress_regex \<sigma> P r j"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  have wty: "\<forall>\<psi>\<in>set \<psi>s. S, E \<turnstile> \<psi>"
  proof
    fix \<psi>
    assume "\<psi> \<in> set \<psi>s"
    from MMatchF.prems(3) have "Regex.pred_regex (wty_formula S E) r"
      unfolding eq by (cases pred: wty_formula) simp_all
    moreover from \<open>\<psi> \<in> set \<psi>s\<close> mr have "\<psi> \<in> safe_atms r"
      by (rule to_mregex_safe_atms)
    ultimately show "S, E \<turnstile> \<psi>"
      by (rule pred_regex_wty_formula)
  qed
  have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [progress_regex \<sigma> P r j..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts unfolding wf_ts_regex_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_regex_le[OF MMatchF.prems(2)] list.rel_map
      intro!: list_all2_appendI list.rel_refl)
  {
    fix xss zs aux' aux'' buf' nts' nt
    assume eval: "map (fst o meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db) \<phi>s = xss"
      and eq1: "mbufnt_take (update_matchF n I mr mrs) aux (mbufn_add xss buf) t (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]) =
        (aux', buf', nt, nts')"
      and eq2: "eval_matchF I mr nt aux' = (zs, aux'')"
    note nt_def = mbufnt_take_nt[OF eq1]
    have update1: "wf_matchF_aux \<sigma> V n R I r aux' (progress \<sigma> P (Formula.MatchF I r) j) 0 \<and>
      progress \<sigma> P (Formula.MatchF I r) j + length aux' = progress_regex \<sigma> P' r (j + \<delta>)"
      using eval nts_snoc nts_snoc length_aux aux \<psi>s wty
      by (elim mbufnt_take_add_induct'[where j'="j + \<delta>", OF eq1 wf_envs_P_simps[OF MMatchF.prems(2)] safe mr buf])
        (auto simp: length_update_matchF
          list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
          dest!: MMatchF.IH[OF _ _ MMatchF.prems(2)]
          elim: wf_update_matchF[OF _ safe mr mrs] elim!: list.rel_mono_strong)
    \<comment> \<open>the new results of the subformulas, by the induction hypothesis\<close>
    have xss: "list_all3 list_all2
        (map (\<lambda>\<psi> i r. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r) \<psi>s)
        (map2 upt (map (\<lambda>\<psi>. progress \<sigma> P \<psi> j) \<psi>s) (map (\<lambda>\<psi>. progress \<sigma> P' \<psi> (j + \<delta>)) \<psi>s)) xss"
      using eval \<psi>s wty
      by (auto simp: list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map
          list.rel_flip[symmetric, of _ \<psi>s \<phi>s] dest!: MMatchF.IH[OF _ _ MMatchF.prems(2)]
          elim!: list.rel_mono_strong split: prod.splits)
    have nts': "wf_ts_regex \<sigma> P' (j + \<delta>) r nts'"
      by (rule mbufnt_take_add'(2)[OF eq1 wf_envs_P_simps[OF MMatchF.prems(2)] safe mr buf nts_snoc xss])
        simp
    have nt: "nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (progress_regex \<sigma> P' r (j + \<delta>))))"
    proof -
      let ?m = "progress_regex \<sigma> P r j"
      let ?m' = "progress_regex \<sigma> P' r (j + \<delta>)"
      from nts have nts_rel: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?m..<j] nts"
        unfolding wf_ts_regex_def .
      from nts' have nts'_rel: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?m'..<j + \<delta>] nts'"
        unfolding wf_ts_regex_def .
      show ?thesis
      proof (cases "nts' = []")
        case False
        with nts'_rel have "hd nts' = \<tau> \<sigma> ?m'" "?m' < j + \<delta>"
          by (rule list_all2_hdD)+
        then have "j + \<delta> \<noteq> 0" "min (j + \<delta> - 1) ?m' = ?m'"
          by linarith+
        with \<open>hd nts' = \<tau> \<sigma> ?m'\<close> False show ?thesis
          unfolding nt_def by (simp only: hd_append if_False if_not_P)
      next
        case True
        with nts'_rel have "j + \<delta> \<le> ?m'"
          by auto
        show ?thesis
        proof (cases "\<delta> = 0")
          case False
          with \<open>j + \<delta> \<le> ?m'\<close> have "j + \<delta> \<noteq> 0" "min (j + \<delta> - 1) ?m' = j + \<delta> - 1"
            by linarith+
          with False show ?thesis
            unfolding nt_def \<open>nts' = []\<close>
            by (simp only: if_not_P) (simp add: hd_append hd_rev last_map)
        next
          case True
          show ?thesis
          proof (cases "nts = []")
            case False
            with nts_rel have "last nts = \<tau> \<sigma> (j - 1)" "?m < j"
              by (rule list_all2_lastD list_all2_hdD(2))+
            with \<open>j + \<delta> \<le> ?m'\<close> \<open>\<delta> = 0\<close> have "j + \<delta> \<noteq> 0" "min (j + \<delta> - 1) ?m' = j - 1"
              by linarith+
            with False \<open>last nts = \<tau> \<sigma> (j - 1)\<close> \<open>\<delta> = 0\<close> show ?thesis
              unfolding nt_def \<open>nts' = []\<close>
              by (simp only: if_not_P) (simp add: hd_append hd_rev)
          next
            case True
            with nts_rel have "j \<le> ?m"
              by auto
            with \<open>j + \<delta> \<le> ?m'\<close> \<open>\<delta> = 0\<close> have "min (j - 1) ?m = j - 1" "min (j + \<delta> - 1) ?m' = j - 1"
              by linarith+
            with True \<open>\<delta> = 0\<close> show ?thesis
              unfolding nt_def \<open>nts' = []\<close> t
              by (simp only: add_0_right upt_conv_Nil[OF order.refl] list.map(1) rev.simps(1)
                  append_Nil list.sel(1))
          qed
        qed
      qed
    qed
    have "i \<le> progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>) \<Longrightarrow>
      wf_matchF_aux \<sigma> V n R I r aux' i 0 \<Longrightarrow>
      i + length aux' = progress_regex \<sigma> P' r (j + \<delta>) \<Longrightarrow>
      wf_matchF_aux \<sigma> V n R I r aux'' (progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>)) 0 \<and>
        i + length zs = progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>) \<and>
        i + length zs + length aux'' = progress_regex \<sigma> P' r (j + \<delta>) \<and>
        list_all2 (\<lambda>i. qtable n (Formula.fv_regex r) (mem_restr R)
          (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.MatchF I r)))
          [i..<i + length zs] zs" for i
      using eq2
    proof (induction aux' arbitrary: zs aux'' i)
      case Nil
      then show ?case by (auto dest!: antisym[OF progress_MatchF_le])
    next
      case (Cons a aux')
      obtain t rels rel where "a = (t, rels, rel)" by (cases a)
      from Cons.prems(2) have aux': "wf_matchF_aux \<sigma> V n R I r aux' (Suc i) 0"
        by (rule wf_matchF_aux_Cons)
      from Cons.prems(2) have 1: "t = \<tau> \<sigma> i"
        unfolding \<open>a = (t, rels, rel)\<close> by (rule wf_matchF_aux_Cons1)
      from Cons.prems(2) have 3: "qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v.
        (\<exists>j\<ge>i. j < Suc (i + length aux') \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and> Regex.match (Formula.sat \<sigma> V (map the v)) r i j)) rel"
        unfolding \<open>a = (t, rels, rel)\<close> using wf_matchF_aux_Cons3 by force
      from Cons.prems(3) have Suc_i_aux': "Suc i + length aux' = progress_regex \<sigma> P' r (j + \<delta>)"
        by simp
      have "i \<ge> progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>)"
        if "memR I (nt - t)"
        using that nts' unfolding wf_ts_regex_def progress_simps nt
        by (auto simp add: 1 list_all2_Cons2 upt_eq_Cons_conv
          intro!: cInf_lower \<tau>_mono diff_le_mono simp del: upt_Suc split: if_splits list.splits)
      moreover
      have "Suc i \<le> progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>)"
        if "\<not> memR I (nt - t)"
      proof -
        have \<tau>_min:  "\<tau> \<sigma> (min (j + \<delta> - 1) k) = min (\<tau> \<sigma> (j + \<delta> - 1) ) (\<tau> \<sigma> k)" for k
          by (simp add: min_of_mono monoI)
        have le_progress_iff[simp]: "j + \<delta> \<le> progress \<sigma> P' \<phi> (j + \<delta>) \<longleftrightarrow> progress \<sigma> P' \<phi> (j + \<delta>) = (j + \<delta>)" for \<phi> :: "'t Formula.formula"
          using wf_envs_progress_le[OF MMatchF.prems(2), of \<phi>] by auto
        have min_Suc[simp]: "min j (j + \<delta>) = j" by auto
        let ?X = "{i. \<forall>k. k < j + \<delta> \<and> k \<le> progress_regex \<sigma> P' r (j + \<delta>) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
        let ?min = "min (j + \<delta> - 1) (progress_regex \<sigma> P' r (j + \<delta>))"
        have "\<tau> \<sigma> ?min \<le> \<tau> \<sigma> (j + \<delta>)"
          by (rule \<tau>_mono) auto
        from that have "?X \<noteq> {}"
          by (auto intro!: exI[of _ "progress_regex \<sigma> P' r (j + \<delta>)"])
        show ?thesis
          using that nts' wf_envs_progress_regex_le[OF MMatchF.prems(2), of r]
          unfolding wf_ts_regex_def progress_simps nt
          by (intro cInf_greatest[OF \<open>?X \<noteq> {}\<close>])
            (auto 0 3 simp: 1 list_all2_Cons2 upt_eq_Cons_conv
              simp del: upt_Suc split: list.splits if_splits
              dest!: spec[of _ "?min"]
              intro!: diff_le_mono diff_le_mono2 order_trans[OF diff_le_mono diff_le_mono2] \<tau>_mono
              elim!: contrapos_np[of _ "Suc i \<le> _"])
      qed
      moreover have *: "k < progress_regex \<sigma> P' r (j + \<delta>)" if
        "\<not> memR I (nt - \<tau> \<sigma> i)"
        "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
        using that nts' unfolding wf_ts_regex_def nt
        by (auto simp: list_all2_Cons2 upt_eq_Cons_conv
          simp del: upt_Suc split: list.splits if_splits
          elim!: contrapos_np[of _ "k < _"] intro!: diff_le_mono diff_le_mono2)
      ultimately show ?case using Cons.prems Suc_i_aux'[simplified]
        unfolding \<open>a = (t, rels, rel)\<close>
        by (auto simp: 1 sat.simps upt_conv_Cons dest!: Cons.IH[OF _ aux' Suc_i_aux']
            simp del: upt_Suc split: if_splits prod.splits intro!: iff_exI qtable_cong[OF 3 refl])

    qed
    note conjI[OF nt this[OF progress_mono_gen[OF le_add1] conjunct1[OF update1] conjunct2[OF update1]]]
  }
  note update = this[OF refl, rotated]
  from MMatchF.prems(2) show ?case using \<psi>s wty
    by (auto simp: eq mr mrs safe map_split_alt list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
        list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map Let_def
        intro!: wf_mformula.intros
        elim!: list.rel_mono_strong mbufnt_take_add'(1)[OF _ wf_envs_P_simps[OF MMatchF.prems(2)] safe mr buf nts_snoc]
        mbufnt_take_add'(2)[OF _ wf_envs_P_simps[OF MMatchF.prems(2)] safe mr buf nts_snoc]
        dest!: MMatchF.IH[OF _ _ MMatchF.prems(2)] update split: prod.splits)

next
  case (MTP mt i)
  then obtain t where "\<forall>x\<in>fv_trm t. x < n" "Formula.is_Var t \<or> Formula.is_Const t"
    "mt = mtrm_of_trm t" "\<phi>' = Formula.TP t" "i = j"
    by (cases rule: wf_mformula.cases) 
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  then show ?case
    by (auto simp add: list.rel_map intro!: wf_mformula.MTP list.rel_refl qtable_eval_mtrm)
next
  case (MTS mt)
  then obtain t where "\<forall>x\<in>fv_trm t. x < n" "Formula.is_Var t \<or> Formula.is_Const t"
    "mt = mtrm_of_trm t" "\<phi>' = Formula.TS t"
    by (cases rule: wf_mformula.cases) 
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  then show ?case
    by (auto simp add: list.rel_map intro!: wf_mformula.MTS list.rel_refl qtable_eval_mtrm)
qed

unbundle MFODL_no_notation


subsection \<open> Correct step \<close>

lemma wty_db_empty: "wty_db S {}"
  by (simp add: wty_db_def)

lemma prefix_of_wty_trace:
  assumes "wty_trace S \<sigma>" and "prefix_of \<pi> \<sigma>"
  shows "wty_prefix S \<pi>"
proof -
  from assms(1) have "\<forall>i. wty_db S (\<Gamma> \<sigma> i)"
    by (simp add: wty_envs_def wty_db_def)
  with assms(2) show ?thesis
    by (transfer fixing: S) (metis in_set_conv_nth stake_nth)
qed

lemma ex_prefix_of_wty:
  assumes "wty_prefix S p"
  shows "\<exists>s. prefix_of p s \<and> wty_trace S s"
proof -
  from assms have "\<exists>s. prefix_of p s \<and> (\<forall>i. wty_db S (\<Gamma> s i))"
    proof (transfer fixing: S, intro bexI CollectI conjI)
    fix p :: "((string8 \<times> event_data list) set \<times> nat) list"
    assume *: "sorted (map snd p)"
    let ?\<sigma> = "p @- smap (Pair {}) (fromN (snd (last p)))"
    show "stake (length p) ?\<sigma> = p" by (simp add: stake_shift)
    assume "\<forall>x\<in>set p. wty_db S (fst x)"
    then show "\<forall>i. wty_db S (fst (snth ?\<sigma> i))"
      by (simp add: shift_snth wty_db_empty)
    have le_last: "snd (p ! i) \<le> snd (last p)" if "i < length p" for i
      using sorted_nth_mono[OF *, of i "length p - 1"] that
      by (cases p) (auto simp: last_conv_nth nth_Cons')
    with * show "ssorted (smap snd ?\<sigma>)"
      by (force simp: ssorted_iff_mono sorted_iff_nth_mono shift_snth)
    show "sincreasing (smap snd ?\<sigma>)"
    proof (rule sincreasingI)
      fix x
      have "x < snth (smap snd ?\<sigma>) (Suc (length p + x))"
        by simp (metis Suc_pred add.commute diff_Suc_Suc length_greater_0_conv less_add_Suc1 less_diff_conv)
      then show "\<exists>i. x < snth (smap snd ?\<sigma>) i" ..
    qed
  qed
  then show ?thesis by (auto simp: wty_envs_def wty_db_def)
qed

lemma (in maux) wf_mstate_mstep:
  assumes "wf_mstate S E \<phi> \<pi> R st" and "wty_db S (fst tdb)" and  "last_ts \<pi> \<le> snd tdb"
  shows "wf_mstate S E \<phi> (psnoc \<pi> tdb) R (snd (mstep (apfst mk_db tdb) st))"
proof -
  from assms(1) have "mstate_i st \<le> plen \<pi>"
    using ex_prefix_of_wty
    unfolding wf_mstate_def
    by (metis progress_le)
  with assms show ?thesis
    unfolding wf_mstate_def mstep_def
    by (force simp: progress_mono le_imp_diff_is_add pts_psnoc length_pts_eq_plen add.commute
        split: prod.splits intro!:wty_psnoc  
        elim!: prefix_of_psnocE dest: meval_correct[OF _ wf_envs_mk_db] list_all2_lengthD)
qed

definition "flatten_verdicts Vs = (\<Union> (set (map (\<lambda>(i, t, X). (\<lambda>v. (i, t, v)) ` X) Vs)))"

lemma flatten_verdicts_append[simp]:
  "flatten_verdicts (Vs @ Us) = flatten_verdicts Vs \<union> flatten_verdicts Us"
  unfolding flatten_verdicts_def by simp

lemma (in maux) mstep_output_iff:
  assumes "wf_mstate S E \<phi> \<pi> R st" "last_ts \<pi> \<le> snd tdb" "prefix_of (psnoc \<pi> tdb) \<sigma>" "wty_trace S \<sigma>" "mem_restr R v"
  shows "(i, t, v) \<in> flatten_verdicts (fst (mstep (apfst mk_db tdb) st)) \<longleftrightarrow>
    progress \<sigma> Map.empty \<phi> (plen \<pi>) \<le> i \<and> i < progress \<sigma> Map.empty \<phi> (Suc (plen \<pi>)) \<and> t = \<tau> \<sigma> i \<and>
    wf_tuple (Formula.nfv \<phi>) (Formula.fv \<phi>) v \<and> Formula.sat \<sigma> Map.empty (map the v) i \<phi>"
  (is "?L \<longleftrightarrow> ?R")
proof -
  let ?p = "progress \<sigma> Map.empty \<phi> (plen \<pi>)"
  let ?p' = "progress \<sigma> Map.empty \<phi> (Suc (plen \<pi>))"
  from prefix_of_psnocE[OF assms(3,2)] have "prefix_of \<pi> \<sigma>"
    and tdb_eqs: "\<Gamma> \<sigma> (plen \<pi>) = fst tdb" "\<tau> \<sigma> (plen \<pi>) = snd tdb" by auto
  from assms(1, 4) \<open>prefix_of \<pi> \<sigma>\<close> have
    state_eqs:
    "mstate_n st = Formula.nfv \<phi>" "mstate_j st = plen \<pi>"
    "mstate_i st = ?p" "mstate_t st = drop ?p (pts \<pi>)"
    and wf_m: "wf_mformula \<sigma> (plen \<pi>) Map.empty Map.empty (Formula.nfv \<phi>) R (mstate_m st) \<phi>" and
    wty: "S, E \<turnstile> \<phi>"
    unfolding wf_mstate_def by auto
  from meval_correct[OF wf_m wf_envs_mk_db[OF assms(4)] wty]
  obtain Vs st' where
    meval_eq: "meval (Suc (plen \<pi>)) (Formula.nfv \<phi>) [snd tdb] (mk_db (fst tdb)) (mstate_m st) = (Vs, st')"
    and wf_m': "wf_mformula \<sigma> (Suc (plen \<pi>)) Map.empty Map.empty (Formula.nfv \<phi>) R st' \<phi>"
    and "list_all2 (\<lambda>i. qtable (Formula.nfv \<phi>) (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> Map.empty (map the v) i \<phi>))
      [progress \<sigma> Map.empty \<phi> (plen \<pi>)..<progress \<sigma> Map.empty \<phi> (Suc (plen \<pi>))] Vs"
    by (auto simp add: tdb_eqs state_eqs)
  then have
    length_Vs: "length Vs = ?p' - ?p"
    and set_Vs: "\<forall>i < ?p'-?p. v \<in> Vs ! i \<longleftrightarrow>
      wf_tuple (Formula.nfv \<phi>) (Formula.fv \<phi>) v \<and> Formula.sat \<sigma> Map.empty (map the v) (?p + i) \<phi>"
    using assms(5)
    by (auto simp add: list_all2_conv_all_nth in_set_conv_nth elim!: in_qtableE in_qtableI)
  have \<tau>_eq: "(drop ?p (pts \<pi>) @ [snd tdb]) ! (i - ?p) = \<tau> \<sigma> i" if "?p \<le> i" "i < ?p'"
  proof (cases "i = plen \<pi>")
    case True
    then show ?thesis
      by (auto simp add: nth_append length_pts_eq_plen tdb_eqs)
  next
    case False
    with that(2) have "i < plen \<pi>"
      by (metis less_trans_Suc linorder_not_less nat_neq_iff progress_le)
    with that(1) show ?thesis
      by (auto simp add: nth_append length_pts_eq_plen nth_pts_eq_\<tau>[OF \<open>prefix_of \<pi> \<sigma>\<close>])
  qed
  show ?thesis
  proof
    assume ?L
    then show ?R
      unfolding flatten_verdicts_def mstep_def using set_Vs \<tau>_eq
      by (auto simp add: in_set_enumerate_eq state_eqs meval_eq length_pts_eq_plen length_Vs
          split: prod.splits)
  next
    assume ?R
    then have "i \<le> plen \<pi>"
      by (metis Suc_leI Suc_le_mono le_trans progress_le)
    with \<open>?R\<close> show ?L
      unfolding flatten_verdicts_def mstep_def using set_Vs \<tau>_eq
      by (auto simp add: in_set_enumerate_eq state_eqs meval_eq length_pts_eq_plen length_Vs
          min_add_distrib_left split: prod.splits 
          intro!: bexI[where x="(i, \<tau> \<sigma> i, Vs ! (i - ?p))"])
  qed
qed


section \<open> Specification \<close>

definition pprogress :: "'t Formula.formula \<Rightarrow> Formula.prefix \<Rightarrow> nat" where
  "pprogress \<phi> \<pi> = (THE n. \<forall>\<sigma>. prefix_of \<pi> \<sigma> \<longrightarrow> progress \<sigma> Map.empty \<phi> (plen \<pi>) = n)"

lemma pprogress_eq: "prefix_of \<pi> \<sigma> \<Longrightarrow> pprogress \<phi> \<pi> = progress \<sigma> Map.empty \<phi> (plen \<pi>)"
  unfolding pprogress_def using progress_prefix_conv
  by blast

locale wty_mfodl =
  fixes \<phi> :: "ty Formula.formula" and SIG :: sig and ENV :: tyenv
  assumes well_typed: "SIG, ENV \<turnstile> \<phi>"
begin

definition "traces = {\<sigma>. wty_trace SIG \<sigma>}"

sublocale traces_downward_closed traces
  by unfold_locales (auto simp add: traces_def wty_envs_def)

end

locale future_bounded_mfodl = wty_mfodl +
   assumes future_bounded: "Safety.future_bounded \<phi>"

sublocale future_bounded_mfodl \<subseteq> sliceable_timed_progress "Formula.nfv \<phi>" "Formula.fv \<phi>" traces "relevant_events \<phi>"
  "\<lambda>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<phi>" "pprogress \<phi>"
proof (unfold_locales, goal_cases)
  case (1 \<pi>' \<pi>)
  moreover obtain \<sigma> where "prefix_of \<pi>' \<sigma>"
    using ex_prefix_of ..
  moreover have "prefix_of \<pi> \<sigma>"
    using prefix_of_antimono[OF \<open>\<pi> \<le> \<pi>'\<close> \<open>prefix_of \<pi>' \<sigma>\<close>] .
  ultimately show ?case
    by (simp add: pprogress_eq plen_mono progress_mono)
next
  case (2 \<sigma> x)
  obtain j where "x \<le> progress \<sigma> Map.empty \<phi> j"
    using future_bounded progress_ge by blast
  then have "x \<le> pprogress \<phi> (take_prefix j \<sigma>)"
    by (simp add: pprogress_eq[of _ \<sigma>])
  then show ?case by force
next
  case (3 \<sigma> \<pi> \<sigma>' i v)
  then have "i < progress \<sigma> Map.empty \<phi> (plen \<pi>)"
    by (simp add: pprogress_eq)
  with 3 show ?case
    using sat_prefix_conv by blast
next
  case (4 \<pi> \<pi>')
  then have "plen \<pi> = plen \<pi>'"
    unfolding length_pts_eq_plen[symmetric] by auto
  moreover obtain \<sigma> \<sigma>' where "prefix_of \<pi> \<sigma>" "prefix_of \<pi>' \<sigma>'"
    using ex_prefix_of by blast+
  moreover have "\<forall>i < plen \<pi>. \<tau> \<sigma> i = \<tau> \<sigma>' i"
    using 4 calculation nth_pts_eq_\<tau>[OF calculation(3)] nth_pts_eq_\<tau>[OF calculation(2)]
    by auto
  ultimately show ?case
    by (simp add: pprogress_eq progress_time_conv)
qed

lemma (in future_bounded_mfodl) prefixes_alt: "formula_slicer.prefixes = {\<pi>. wty_prefix SIG \<pi>}"
  unfolding formula_slicer.prefixes_def
  using ex_prefix_of_wty prefix_of_wty_trace
  by (fastforce simp: traces_def)

locale verimon_spec = wty_mfodl +
   assumes monitorable: "mmonitorable \<phi>"

sublocale verimon_spec \<subseteq> future_bounded_mfodl
  using monitorable by unfold_locales (simp add: mmonitorable_def)

context maux
begin

lemma minit_safe_minit: "mmonitorable \<phi> \<Longrightarrow> minit_safe \<phi> = minit \<phi>"
  unfolding minit_safe_def monitorable_formula_code by simp

lemma wf_mstate_minit_safe: "S, E \<turnstile> \<phi> \<Longrightarrow> mmonitorable \<phi> \<Longrightarrow> wf_mstate S E \<phi> pnil R (minit_safe \<phi>)"
  using wf_mstate_minit minit_safe_minit mmonitorable_def by metis

end

locale verimon = verimon_spec + maux

lemma (in verimon) Mt_pnil: "Mt pnil = {}"
  by (simp add: Mt_def M_def pprogress_eq)

lemma (in verimon) fst_M_less_plen: 
  assumes "(i, v) \<in> M \<pi>" 
  shows "i < plen \<pi>"
proof -
  obtain \<sigma> where "prefix_of \<pi> \<sigma>"
    using ex_prefix_of by blast
  then have "pprogress \<phi> \<pi> \<le> plen \<pi>"
    by (simp add: pprogress_eq)
  with assms show ?thesis
    unfolding M_def by simp
qed

lemma (in verimon) mono_monitor': "\<pi>' \<in> formula_slicer.prefixes \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> Mt \<pi> \<subseteq> Mt \<pi>'"
  unfolding Mt_def using mono_monitor[of \<pi>' \<pi>] fst_M_less_plen[of _ _ \<pi>]
  by (auto simp add: nth_pts_prefix_cong dest!: subsetD)

lemma (in verimon) mstep_mverdicts:
  assumes wf: "wf_mstate SIG ENV \<phi> \<pi> R st"
    and wty: "wty_db SIG (fst tdb)"
    and le[simp]: "last_ts \<pi> \<le> snd tdb"
    and restrict: "mem_restr R v"
  shows "(i, t, v) \<in> flatten_verdicts (fst (mstep (apfst mk_db tdb) st)) \<longleftrightarrow>
    (i, t, v) \<in> Mt (psnoc \<pi> tdb) - Mt \<pi>"
proof -
  have "wty_prefix SIG (psnoc \<pi> tdb)"
    using wf wty by (auto simp: wf_mstate_def intro!: wty_psnoc)
  then obtain \<sigma> where p2: "prefix_of (psnoc \<pi> tdb) \<sigma>" and wty_\<sigma>: "wty_trace SIG \<sigma>"
    using ex_prefix_of_wty by blast
  with le have p1: "prefix_of \<pi> \<sigma>" by (blast elim!: prefix_of_psnocE)
  have "i < progress \<sigma> Map.empty \<phi> (Suc (plen \<pi>)) \<Longrightarrow> i < Suc (plen \<pi>)"
    by (metis order.strict_trans2 progress_le)
  then show ?thesis 
    unfolding Mt_def M_def using wty_\<sigma>
    by (auto 0 3 simp: p2 progress_prefix_conv[OF _ p1] sat_prefix_conv[OF _ p1] not_less
        pprogress_eq[OF p1] pprogress_eq[OF p2] nth_pts_eq_\<tau>[OF p1] nth_pts_eq_\<tau>[OF p2]
        image_iff less_Suc_eq traces_def cong: conj_cong
        dest: mstep_output_iff[OF wf le p2 _ restrict, THEN iffD1] spec[of _ \<sigma>]
        mstep_output_iff[OF wf le _ _ restrict, THEN iffD1] progress_sat_cong[OF _ p1]
        intro: mstep_output_iff[OF wf le p2 _ restrict, THEN iffD2] p1)
qed

lemma (in verimon) wf_mstate_msteps: 
  "wf_mstate SIG ENV \<phi> \<pi> R st \<Longrightarrow> mem_restr R v \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> wty_prefix SIG \<pi>' \<Longrightarrow>
  X = msteps (pdrop (plen \<pi>) \<pi>') st \<Longrightarrow> wf_mstate SIG ENV \<phi> \<pi>' R (snd X) \<and>
  ((i, t, v) \<in> flatten_verdicts (fst X)) = ((i, t, v) \<in> Mt \<pi>' - Mt \<pi>)"
proof (induct "plen \<pi>' - plen \<pi>" arbitrary: X st \<pi> \<pi>')
  case 0
  from 0(1,4,5,6) have "\<pi> = \<pi>'"  "X = ([], st)"
    by (transfer; auto)+
  with 0(2) show ?case unfolding flatten_verdicts_def by simp
next
  case (Suc x)
  from Suc(2,5,6) obtain \<pi>'' tdb where "x = plen \<pi>'' - plen \<pi>"  "\<pi> \<le> \<pi>''" "wty_prefix SIG \<pi>''" "wty_db SIG (fst tdb)"
    "\<pi>' = psnoc \<pi>'' tdb" "pdrop (plen \<pi>) (psnoc \<pi>'' tdb) = psnoc (pdrop (plen \<pi>) \<pi>'') tdb"
    "last_ts (pdrop (plen \<pi>) \<pi>'') \<le> snd tdb" "last_ts \<pi>'' \<le> snd tdb"
    "\<pi>'' \<le> psnoc \<pi>'' tdb"
  proof (atomize_elim, transfer, elim exE, goal_cases prefix)
    case (prefix _ _ \<pi>' _ \<pi>_tdb)
    then show ?case
    proof (cases \<pi>_tdb rule: rev_cases)
      case (snoc \<pi> tdb)
      with prefix show ?thesis
        by (intro bexI[of _ "\<pi>' @ \<pi>"] exI[of _ tdb])
          (force simp: sorted_append append_eq_Cons_conv split: list.splits if_splits)+
    qed simp
  qed
  with Suc(1)[OF this(1) Suc.prems(1,2) this(2,3) refl] Suc.prems show ?case
    by (auto simp: msteps_psnoc split_beta mstep_mverdicts
        dest: mono_monitor'[THEN set_mp, rotated, unfolded prefixes_alt] intro!: wf_mstate_mstep)
qed

lemma (in verimon) wf_mstate_msteps_stateless:
  assumes "wf_mstate SIG ENV \<phi> \<pi> R st" "mem_restr R v" "\<pi> \<le> \<pi>'" "wty_prefix SIG \<pi>'"
  shows "(i, t, v) \<in> flatten_verdicts (msteps_stateless (pdrop (plen \<pi>) \<pi>') st) \<longleftrightarrow>
    (i, t, v) \<in> Mt \<pi>' - Mt \<pi>"
  using wf_mstate_msteps[OF assms refl] unfolding msteps_msteps_stateless by simp

lemma (in verimon) wf_mstate_msteps_stateless_UNIV: 
  "wf_mstate SIG ENV \<phi> \<pi> UNIV st \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> wty_prefix SIG \<pi>' 
  \<Longrightarrow> flatten_verdicts (msteps_stateless (pdrop (plen \<pi>) \<pi>') st) = Mt \<pi>' - Mt \<pi>"
  by (auto dest: wf_mstate_msteps_stateless[OF _ mem_restr_UNIV])

lemma (in verimon) monitor_mverdicts: 
  "wty_prefix SIG \<pi> \<Longrightarrow> flatten_verdicts (monitor \<phi> \<pi>) = Mt \<pi>"
  unfolding monitor_def using monitorable
  by (subst wf_mstate_msteps_stateless_UNIV[OF wf_mstate_minit_safe, simplified])
    (auto simp: mmonitorable_def Mt_pnil well_typed)


section \<open>Collected correctness results\<close>

context verimon
begin

text \<open>We summarize the main results proved above.
\begin{enumerate}
\item The term @{term M} describes semantically the monitor's expected behaviour:
\begin{itemize}
\item @{thm[source] mono_monitor}: @{thm mono_monitor[no_vars]}
\item @{thm[source] sound_monitor}: @{thm sound_monitor[no_vars]}
\item @{thm[source] complete_monitor}: @{thm complete_monitor[no_vars]}
\item @{thm[source] sliceable_M}: @{thm sliceable_M[no_vars]}
\end{itemize}
\item The executable monitor's online interface @{term minit_safe} and @{term mstep}
  preserves the invariant @{term wf_mstate} and produces the the verdicts according
  to @{term M}:
\begin{itemize}
\item @{thm[source] wf_mstate_minit_safe}: @{thm wf_mstate_minit_safe[no_vars]}
\item @{thm[source] wf_mstate_mstep}: @{thm wf_mstate_mstep[no_vars]}
\item @{thm[source] mstep_mverdicts}: @{thm mstep_mverdicts[no_vars]}
\end{itemize}
\item The executable monitor's offline interface @{term monitor} implements @{term M}:
\begin{itemize}
\item @{thm[source] monitor_mverdicts}: @{thm monitor_mverdicts[no_vars]}
\end{itemize}
\end{enumerate}
\<close>

end

(*<*)
end
(*>*)

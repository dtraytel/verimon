(*<*)
theory Dense_Unbox_Exec
  imports Dense_Descend
begin
(*>*)

section \<open>The executable dense evaluator\<close>

text \<open>
  @{const deval} keeps its buffers in lists and its fused aggregation windows in the structures
  of @{theory MFODL_Monitor_Dense.Dense_Evt_Agg} and @{theory MFODL_Monitor_Dense.Dense_Evt_UAgg}.
  This theory states the same evaluator, @{text udeval}, with its buffers in queues
  (@{typ "'a mbuf_t"}), the fused windows of @{theory MFODL_Monitor_Dense.Dense_Unbox_Eval},
  @{theory MFODL_Monitor_Dense.Dense_Unbox_UAgg} and @{theory MFODL_Monitor_Dense.Dense_Agg_Cache},
  and the constraint over a fused aggregating Since node carried by the node as its guard.  The
  theorem @{text udeval_Rep} at the end says that the two evaluators agree exactly: running
  @{const deval} on the represented state is running @{text udeval} and representing its
  results.  No invariant is needed, because every operation commutes with the representation on
  every input.  So the simulation of the kernel by @{const deval}
  (@{theory MFODL_Monitor_Dense.Dense_Eval}) is a simulation by @{text udeval}, and the generated
  code runs the latter.
\<close>

subsection \<open>The formula\<close>

datatype udformula =
    UDFail
  | UDRel utable
  | UDPredS Formula.name nat
  | UDPredM Formula.name nat "Formula.trm list" cols
  | UDAndRel udformula "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | UDNeg udformula
  | UDExists udformula bool
  | UDAgg bool "ty Formula.agg_op" Formula.trm nat nat udformula
  | UDOr udformula udformula uebuf2
  | UDAnd djoin_plan udformula bool udformula uebuf2
  | UDPrev \<I> udformula bool "utable mbuf_t" "ts mbuf_t"
  | UDNext \<I> udformula bool "ts mbuf_t"
  | UDAnds "djoin_plan list" "djoin_plan list" "udformula list" uebufn
  | UDSince args udformula udformula uebuf2S udsaux_x
  | UDUntil args "bool list" udformula udformula uebuf2 "ts mbuf_t" ts uduaux_x
  | UDAndAssign nat Formula.trm udformula
  | UDTP mtrm nat
  | UDTS mtrm
  | UDLet Formula.name nat udformula udformula
  | UDFrz Formula.name nat udformula udformula nat nat nat "utable list"
      udformula nat nat "ts list" "utable list" enat bool bool "nat option" udformula
  | UDLetPast Formula.name nat udformula udformula nat "utable option"
  | UDTrigger args "nat option list" udformula udformula uebuf2 "ts mbuf_t"
      "event_data gmmtaux"
  | UDAndTrigger djoin_plan udformula "utable mbuf_t \<times> utable option mbuf_t" args
      udformula udformula uebuf2 "ts mbuf_t" "event_data gmmtaux"
  | UDMatchP nat \<I> mregex "mregex list" "nat option list list" "udformula list"
      uebufn "ts mbuf_t" "event_data mr\<delta>aux"
  | UDMatchF nat \<I> mregex "mregex list" "nat option list list" "udformula list"
      uebufn "ts mbuf_t" ts "event_data ml\<delta>aux"

text \<open>A guarded Since node stands for the dense node read through the constraint: the guard is
  the executable evaluator's alone, and the two agree because filtering the whole result is
  filtering the groups as they are read.\<close>

definition dandrel :: "uconstr option \<Rightarrow> dformula \<Rightarrow> dformula" where
  "dandrel q e = (case q of None \<Rightarrow> e | Some c \<Rightarrow> DAndRel e c)"

lemma dandrel_None[simp]: "dandrel None e = e"
  by (simp add: dandrel_def)

lemma deval_dandrel:
  "deval j ts db (dandrel q e)
   = (case deval j ts db e of (zs, e') \<Rightarrow> (map (ufilt q) zs, dandrel q e'))"
  by (simp add: dandrel_def ufilt_Some split: option.splits prod.splits)

lemma vdfail_nodes_dandrel[simp]: "vdfail_nodes (dandrel q e) = vdfail_nodes e"
  by (simp add: dandrel_def split: option.splits)

fun Rep_udformula :: "udformula \<Rightarrow> dformula" where
  "Rep_udformula UDFail = DFail"
| "Rep_udformula (UDRel rel) = DRel rel"
| "Rep_udformula (UDPredS e ar) = DPredS e ar"
| "Rep_udformula (UDPredM e ar tms cs) = DPredM e ar tms cs"
| "Rep_udformula (UDAndRel \<phi> conf) = DAndRel (Rep_udformula \<phi>) conf"
| "Rep_udformula (UDNeg \<phi>) = DNeg (Rep_udformula \<phi>)"
| "Rep_udformula (UDExists \<phi> b) = DExists (Rep_udformula \<phi>) b"
| "Rep_udformula (UDAgg g0 \<omega> f k pos \<phi>) = DAgg g0 \<omega> f k pos (Rep_udformula \<phi>)"
| "Rep_udformula (UDOr \<phi> \<psi> buf) = DOr (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 buf)"
| "Rep_udformula (UDAnd pl \<phi> pos \<psi> buf) =
     DAnd pl (Rep_udformula \<phi>) pos (Rep_udformula \<psi>) (rbuf2 buf)"
| "Rep_udformula (UDPrev I \<phi> first buf nts) =
     DPrev I (Rep_udformula \<phi>) first (Rep_mbuf_t buf) (Rep_mbuf_t nts)"
| "Rep_udformula (UDNext I \<phi> first nts) = DNext I (Rep_udformula \<phi>) first (Rep_mbuf_t nts)"
| "Rep_udformula (UDAnds ps ns L buf) =
     DAnds ps ns (map Rep_udformula L) (map Rep_mbuf_t buf)"
| "Rep_udformula (UDSince args \<phi> \<psi> buf aux) =
     dandrel (usx_q aux)
       (DSince args (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbufS buf) (rdsx aux))"
| "Rep_udformula (UDUntil args msk \<phi> \<psi> buf nts t aux) =
     DUntil args msk (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 buf) (Rep_mbuf_t nts) t (rdux aux)"
| "Rep_udformula (UDAndAssign p t \<phi>) = DAndAssign p t (Rep_udformula \<phi>)"
| "Rep_udformula (UDTP mt i) = DTP mt i"
| "Rep_udformula (UDTS mt) = DTS mt"
| "Rep_udformula (UDLet p m \<phi> \<psi>) = DLet p m (Rep_udformula \<phi>) (Rep_udformula \<psi>)"
| "Rep_udformula (UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
     DFrz p m (Rep_udformula \<phi>) (Rep_udformula \<psi>) jfrz jpsi0 jphi \<alpha>s
       (Rep_udformula \<rho>) w pR tq rb d po ng lv (Rep_udformula \<rho>L)"
| "Rep_udformula (UDLetPast p m \<phi> \<psi> i buf) =
     DLetPast p m (Rep_udformula \<phi>) (Rep_udformula \<psi>) i buf"
| "Rep_udformula (UDTrigger dags pl \<phi> \<psi> dbuf nts daux) =
     DTrigger dags pl (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 dbuf) (Rep_mbuf_t nts) daux"
| "Rep_udformula (UDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) =
     DAndTrigger pl (Rep_udformula \<alpha>) (rbufo dbf1) dags
       (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 dbf2) (Rep_mbuf_t nts) daux"
| "Rep_udformula (UDMatchP m I mr mrs pls Ld dbuf nts daux) =
     DMatchP m I mr mrs pls (map Rep_udformula Ld) (map Rep_mbuf_t dbuf) (Rep_mbuf_t nts) daux"
| "Rep_udformula (UDMatchF m I mr mrs pls Ld dbuf nts t daux) =
     DMatchF m I mr mrs pls (map Rep_udformula Ld) (map Rep_mbuf_t dbuf) (Rep_mbuf_t nts) t daux"

fun uvdfail_nodes :: "udformula \<Rightarrow> nat" where
  "uvdfail_nodes UDFail = 1"
| "uvdfail_nodes (UDAndRel \<phi> conf) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDNeg \<phi>) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDExists \<phi> b) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDAgg g0 \<omega> f k pos \<phi>) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDOr \<phi> \<psi> buf) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDAnd pl \<phi> pos \<psi> buf) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDPrev I \<phi> f buf nts) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDNext I \<phi> f nts) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDAnds ps ns L buf) = sum_list (map uvdfail_nodes L)"
| "uvdfail_nodes (UDSince args \<phi> \<psi> buf aux) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDUntil args msk \<phi> \<psi> buf nts t aux) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDAndAssign p t \<phi>) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDLet p m \<phi> \<psi>) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
    uvdfail_nodes \<phi> + uvdfail_nodes \<psi> + uvdfail_nodes \<rho>"
| "uvdfail_nodes (UDLetPast p m \<phi> \<psi> i buf) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDTrigger dags pl \<phi> \<psi> dbuf nts daux) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) =
     uvdfail_nodes \<alpha> + uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDMatchP m I mr mrs pls L dbuf nts daux) = sum_list (map uvdfail_nodes L)"
| "uvdfail_nodes (UDMatchF m I mr mrs pls L dbuf nts t daux) = sum_list (map uvdfail_nodes L)"
| "uvdfail_nodes \<phi> = 0"

lemma vdfail_nodes_Rep: "vdfail_nodes (Rep_udformula \<phi>) = uvdfail_nodes \<phi>"
  by (induct \<phi>) (auto simp: comp_def intro: arg_cong[of _ _ sum_list])

subsection \<open>The size of the represented formula\<close>

text \<open>The guarded Since node stands for two dense nodes, so the executable formula's own size is
  not that of the dense one it stands for.  The two guards of the evaluator that compare formulas,
  the one keeping the freeze's live copy and the one of the recursive let, compare the size of the
  represented formula instead, computed on the executable one; so they take the dense evaluator's
  branches on every formula, and the evaluator terminates by the same measure.\<close>

fun ursize :: "udformula \<Rightarrow> nat" where
  "ursize (UDAndRel \<phi> conf) = ursize \<phi> + 1"
| "ursize (UDNeg \<phi>) = ursize \<phi> + 1"
| "ursize (UDExists \<phi> b) = ursize \<phi> + 1"
| "ursize (UDAgg g0 \<omega> f k pos \<phi>) = ursize \<phi> + 1"
| "ursize (UDOr \<phi> \<psi> buf) = ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDAnd pl \<phi> pos \<psi> buf) = ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDPrev I \<phi> first buf nts) = ursize \<phi> + 1"
| "ursize (UDNext I \<phi> first nts) = ursize \<phi> + 1"
| "ursize (UDAnds ps ns L buf) = sum_list (map ursize L) + length L + 1"
| "ursize (UDSince args \<phi> \<psi> buf aux) =
     ursize \<phi> + ursize \<psi> + (case usx_q aux of None \<Rightarrow> 1 | Some _ \<Rightarrow> 2)"
| "ursize (UDUntil args msk \<phi> \<psi> buf nts t aux) = ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDAndAssign p t \<phi>) = ursize \<phi> + 1"
| "ursize (UDLet p m \<phi> \<psi>) = ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
     ursize \<phi> + ursize \<psi> + ursize \<rho> + ursize \<rho>L + 1"
| "ursize (UDLetPast p m \<phi> \<psi> i buf) = ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDTrigger dags pl \<phi> \<psi> dbuf nts daux) = ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) = ursize \<alpha> + ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDMatchP m I mr mrs pls Ld dbuf nts daux) = sum_list (map ursize Ld) + length Ld + 1"
| "ursize (UDMatchF m I mr mrs pls Ld dbuf nts t daux) = sum_list (map ursize Ld) + length Ld + 1"
| "ursize _ = 0"

lemma size_list_sum_list: "size_list f xs = sum_list (map f xs) + length xs"
  by (induction xs) auto

lemma ursize_Rep: "ursize \<phi> = size (Rep_udformula \<phi>)"
  by (induction \<phi> rule: ursize.induct)
    (auto simp: dandrel_def size_list_sum_list comp_def split: option.splits intro!: arg_cong[of _ _ sum_list])

lemma ursize_in_set: "x \<in> set L \<Longrightarrow> ursize x < Suc (sum_list (map ursize L) + length L)"
  by (induction L) auto

definition ufrz_keep_lv :: "(nat \<times> udformula) option \<Rightarrow> udformula \<Rightarrow> nat option" where
  "ufrz_keep_lv lv \<rho>L = (case lv of Some (g, st) \<Rightarrow> if ursize st = ursize \<rho>L then Some g else None
     | None \<Rightarrow> None)"

definition ufrz_keep_st :: "(nat \<times> udformula) option \<Rightarrow> udformula \<Rightarrow> udformula" where
  "ufrz_keep_st lv \<rho>L = (case lv of Some (g, st) \<Rightarrow> if ursize st = ursize \<rho>L then st else \<rho>L
     | None \<Rightarrow> \<rho>L)"

lemma ursize_ufrz_keep_st[simp]: "ursize (ufrz_keep_st lv \<rho>L) = ursize \<rho>L"
  by (auto simp: ufrz_keep_st_def split: option.splits)

lemma frz_keep_Rep:
  "frz_keep_lv (map_option (apsnd Rep_udformula) lv) (Rep_udformula \<rho>L) = ufrz_keep_lv lv \<rho>L"
  "frz_keep_st (map_option (apsnd Rep_udformula) lv) (Rep_udformula \<rho>L) = Rep_udformula (ufrz_keep_st lv \<rho>L)"
  by (auto simp: frz_keep_lv_def frz_keep_st_def ufrz_keep_lv_def ufrz_keep_st_def ursize_Rep
      split: option.splits)

function uletpast_meval0 where
  "uletpast_meval0 eval j i ys xs p ts db \<phi> =
     (let (ys', \<phi>') = eval ts (Mapping.update p xs db) \<phi>
     in if ursize \<phi>' \<noteq> ursize \<phi> then ([], 0, None, \<phi>)
     else (case ys' of
       [] \<Rightarrow> (ys @ ys', i + length xs, None, \<phi>')
     | y # _ \<Rightarrow> (if Suc (i + length xs) \<ge> j then (ys @ ys', i + length xs, Some y, \<phi>')
         else uletpast_meval0 eval j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>')))"
  by auto
termination
  by (relation "measure (\<lambda>(_, j, i, _, xs, _). j - (i + length xs))")
    (auto simp: not_le min_def diff_less_mono2)

declare uletpast_meval0.simps[simp del]

lemma uletpast_meval0_cong[fundef_cong]:
  assumes "(\<And>ts db \<psi>. ursize \<psi> = ursize \<phi> \<Longrightarrow> eval ts db \<psi> = eval' ts db \<psi>)"
  shows "uletpast_meval0 eval j i ys xs p ts db \<phi> = uletpast_meval0 eval' j i ys xs p ts db \<phi>"
  using assms
proof (induct eval j i ys xs p ts db \<phi> rule: uletpast_meval0.induct)
  case (1 eval j i ys xs p ts db \<phi>)
  obtain ys' \<phi>' where eval: "eval ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    by fastforce
  have eval': "eval' ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    using 1(2)[of \<phi>] eval by simp
  show ?case
  proof (cases ys')
    case Nil
    then show ?thesis
      using eval eval' by (subst (1 2) uletpast_meval0.simps) simp
  next
    case (Cons y ys'')
    have "uletpast_meval0 eval j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>' =
      uletpast_meval0 eval' j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>'"
      if "ursize \<phi>' = ursize \<phi>" "\<not> j \<le> Suc (i + length xs)"
      using 1(1)[OF eval[symmetric] refl _ Cons] 1(2) that by simp
    then show ?thesis
      using eval eval' Cons by (subst (1 2) uletpast_meval0.simps) (simp add: Let_def)
  qed
qed

lemma ursize_uletpast_meval:
  "ursize (snd (snd (snd (uletpast_meval0 eval j i ys xs p ts db \<phi>)))) = ursize \<phi>"
proof (induct eval j i ys xs p ts db \<phi> rule: uletpast_meval0.induct)
  case (1 eval j i ys xs p ts db \<phi>)
  obtain ys' \<phi>' where eval: "eval ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    by fastforce
  show ?case
  proof (cases ys')
    case Nil
    then show ?thesis
      using eval by (subst uletpast_meval0.simps) simp
  next
    case (Cons y ys'')
    have "ursize (snd (snd (snd (uletpast_meval0 eval j (i + length xs) (ys @ ys') ys' p []
      (Mapping.map_values (\<lambda>_ _. []) db) \<phi>')))) = ursize \<phi>'"
      if "ursize \<phi>' = ursize \<phi>" "\<not> j \<le> Suc (i + length xs)"
      using 1(1)[OF eval[symmetric] refl _ Cons] that by simp
    then show ?thesis
      using eval Cons by (subst uletpast_meval0.simps) (simp add: Let_def)
  qed
qed

subsection \<open>The evaluator\<close>

function (sequential) udeval :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> udformula \<Rightarrow>
    utable list \<times> udformula" where
  "udeval j ts db UDFail = ([], UDFail)"
| "udeval j ts db (UDRel rel) = (replicate (length ts) rel, UDRel rel)"
| "udeval j ts db (UDPredS e ar) =
     ((case Mapping.lookup db (e, ar) of
         None \<Rightarrow> replicate (length ts) {}
       | Some xs \<Rightarrow> xs), UDPredS e ar)"
| "udeval j ts db (UDPredM e ar tms cs) =
     ((case Mapping.lookup db (e, ar) of
         None \<Rightarrow> replicate (length ts) {}
       | Some xs \<Rightarrow> map (umatch_table tms cs) xs), UDPredM e ar tms cs)"
| "udeval j ts db (UDAndRel \<phi> conf) =
     (let (xs, \<phi>') = udeval j ts db \<phi>
      in (map (Set.filter (ueval_constraint conf)) xs, UDAndRel \<phi>' conf))"
| "udeval j ts db (UDNeg \<phi>) =
     (let (xs, \<phi>') = udeval j ts db \<phi>
      in (map (\<lambda>r. if r = {} then {[]} else {}) xs, UDNeg \<phi>'))"
| "udeval j ts db (UDExists \<phi> drop0) =
     (let (xs, \<phi>') = udeval j ts db \<phi>
      in (if drop0 then map (\<lambda>r. tl ` r) xs else xs, UDExists \<phi>' drop0))"
| "udeval j ts db (UDAgg g0 \<omega> f k pos \<phi>) =
     (let (xs, \<phi>') = udeval j ts db \<phi> in (map (uagg g0 \<omega> f k pos) xs, UDAgg g0 \<omega> f k pos \<phi>'))"
| "udeval j ts db (UDOr \<phi> \<psi> buf) =
     (let (xs, \<phi>') = udeval j ts db \<phi>; (ys, \<psi>') = udeval j ts db \<psi>;
          (zs, buf') = mebuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mebuf2_add xs ys buf)
      in (zs, UDOr \<phi>' \<psi>' buf'))"
| "udeval j ts db (UDAnd pl \<phi> pos \<psi> buf) =
     (let (xs, \<phi>') = udeval j ts db \<phi>; (ys, \<psi>') = udeval j ts db \<psi>;
          (zs, buf') = mebuf2_take (\<lambda>r1 r2. gbin_join pl r1 pos r2) (mebuf2_add xs ys buf)
      in (zs, UDAnd pl \<phi>' pos \<psi>' buf'))"
| "udeval j ts db (UDPrev I \<phi> first buf nts) =
     (let (xs, \<phi>') = udeval j ts db \<phi>
      in if first \<and> ts = [] then ([], UDPrev I \<phi>' True (buf @@ xs) (nts @@ ts))
      else let (zs, buf', nts') = meprev_next I (buf @@ xs) (nts @@ ts)
        in (if first then {} # zs else zs, UDPrev I \<phi>' False buf' nts'))"
| "udeval j ts db (UDNext I \<phi> first nts) =
     (let (xs, \<phi>') = udeval j ts db \<phi>;
          (xs, first') = (case (xs, first) of (_ # xs', True) \<Rightarrow> (xs', False) | a \<Rightarrow> a);
          (zs, _, nts') = meprev_next I (mbuf_t_empty @@ xs) (nts @@ ts)
      in (zs, UDNext I \<phi>' first' nts'))"
| "udeval j ts db (UDAnds ps ns Ld dbuf) =
     (let R = map (udeval j ts db) Ld;
          (zs, dbuf') = mebufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty
            (mebufn_add (map fst R) dbuf)
      in (Rep_mbuf_t zs, UDAnds ps ns (map snd R) dbuf'))"
| "udeval j ts db (UDSince dags \<phi> \<psi> buf aux) =
     (let (xs, \<phi>') = udeval j ts db \<phi>; (ys, \<psi>') = udeval j ts db \<psi>;
          (zs, buf', aux') = uedsx_eval_since dags [] (mebuf2S_add xs ys ts buf) aux
      in (zs, UDSince dags \<phi>' \<psi>' buf' aux'))"
| "udeval j ts db (UDUntil dags msk \<phi> \<psi> buf nts t aux) =
     (let (xs, \<phi>') = udeval j ts db \<phi>; (ys, \<psi>') = udeval j ts db \<psi>;
          (aux', buf', nt, nts') = mebuf2t_take (udux_add_new dags msk) aux
            (mebuf2_add xs ys buf) t (nts @@ ts);
          (zs, aux'') = udux_eval dags nt aux'
      in (zs, UDUntil dags msk \<phi>' \<psi>' buf' nts' nt aux''))"
| "udeval j ts db (UDAndAssign p t \<phi>) =
     (let (xs, \<phi>') = udeval j ts db \<phi> in (map (uassign p t) xs, UDAndAssign p t \<phi>'))"
| "udeval j ts db (UDTP mt i) =
     (map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) [i..<j], UDTP mt j)"
| "udeval j ts db (UDTS mt) = (map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) ts, UDTS mt)"
| "udeval j ts db (UDLet p m \<phi> \<psi>) =
     (let (xs, \<phi>') = udeval j ts db \<phi>;
          (ys, \<psi>') = udeval j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, UDLet p m \<phi>' \<psi>'))"
| "udeval j ts db (UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
     (let (xs, \<phi>) = udeval j ts db \<phi>;
          db0 = Mapping.update (p, m) [] db;
          (zs0, \<psi>) = udeval j ts db0 \<psi>;
          (rs, \<rho>) = udeval j ts db0 \<rho>;
          (zs0_out, jfrz, fl, \<alpha>s, lr) =
            (let zs0_out = drop (jfrz - jpsi0) zs0;
                 \<alpha>s1 = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs)
             in (zs0_out, jfrz + length zs0_out, frz_fill ng (\<alpha>s @ xs), \<alpha>s1,
               case lv of None \<Rightarrow> None | Some g \<Rightarrow>
                 if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
                 then Some (g, udeval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
                 else None));
          (ys, \<alpha>s', lv, \<rho>, w, pR, tq, rb) = frz_live_loop ursize (udeval j) (p, m) (Mapping.map_values (\<lambda>_ _. []) db)
            fl d po j jfrz \<alpha>s lr (\<rho>, w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
              drop (min jfrz (pR + length rs) - (pR - length rb)) (rb @ rs))
      in (zs0_out @ ys, UDFrz p m \<phi> \<psi> (jfrz + length ys) (jpsi0 + length zs0) (jphi + length xs) \<alpha>s' \<rho> w pR tq rb d po ng
        (ufrz_keep_lv (if po then None else lv) \<rho>L) (ufrz_keep_st (if po then None else lv) \<rho>L)))"
| "udeval j ts db (UDLetPast p m \<phi> \<psi> i buf) =
     (let (xs, i, buf, \<phi>) =
            uletpast_meval0 (udeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>;
          (ys, \<psi>) = udeval j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, UDLetPast p m \<phi> \<psi> i buf))"
| "udeval j ts db (UDTrigger dags pl \<phi> \<psi> dbuf nts daux) =
     (let (xs, \<phi>') = udeval j ts db \<phi>; (ys, \<psi>') = udeval j ts db \<psi>;
          ((zs, daux'), dbuf', nts') = mebuf2T_take (\<lambda>r1 r2 t (zs, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux)
            (mebuf2_add xs ys dbuf) (nts @@ ts)
      in (zs, UDTrigger dags pl \<phi>' \<psi>' dbuf' nts' daux'))"
| "udeval j ts db (UDMatchP m I mr mrs pls Ld dbuf nts daux) =
     (let R = map (udeval j ts db) Ld;
          ((zs, daux'), dbuf', _, nts') = mebufnt_take (\<lambda>rels t (zs, ax).
             let (z, ax) = gupdate_matchP (map emb_msk pls) I mr mrs rels t ax
             in (zs @@ [z], ax)) (mbuf_t_empty, daux)
             (mebufn_add (map fst R) dbuf) 0 (nts @@ ts)
      in (Rep_mbuf_t zs,
          UDMatchP m I mr mrs pls (map snd R) dbuf' nts' daux'))"
| "udeval j ts db (UDMatchF m I mr mrs pls Ld dbuf nts t daux) =
     (let R = map (udeval j ts db) Ld;
          (daux', dbuf', nt, nts') = mebufnt_take
             (\<lambda>rels. gupdate_matchF (map emb_msk pls) I mr mrs rels)
             daux (mebufn_add (map fst R) dbuf) t (nts @@ ts);
          (zs, daux'') = geval_matchF I mr nt daux'
      in (zs,
          UDMatchF m I mr mrs pls (map snd R) dbuf' nts' nt daux''))"
| "udeval j ts db (UDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) =
     (let (as, \<alpha>') = udeval j ts db \<alpha>; (xs, \<phi>') = udeval j ts db \<phi>;
          (ys, \<psi>') = udeval j ts db \<psi>;
          ((ws, daux'), dbf2', nts') = mebuf2T_take (\<lambda>r1 r2 t (ws, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (ws @ [if gmmtaux_empty ax then None
                      else Some (gresult_mmtaux dags ax)], ax)) ([], daux)
            (mebuf2_add xs ys dbf2) (nts @@ ts);
          (zs, dbf1') = mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
            | Some z \<Rightarrow> gbin_join pl r1 True z) (mebuf2_add as ws dbf1)
      in (zs, UDAndTrigger pl \<alpha>' dbf1' dags \<phi>' \<psi>' dbf2' nts' daux'))"
  by pat_completeness (simp_all only: prod.inject udformula.inject udformula.distinct simp_thms)

lemma psize_snd_udeval:
  "udeval_dom (j, ts, db, \<phi>) \<Longrightarrow> ursize (snd (udeval j ts db \<phi>)) = ursize \<phi>"
proof (induct rule: udeval.pinduct)
  case (11 j ts db I \<phi> first buf nts) \<comment> \<open>\<^const>\<open>UDPrev\<close>\<close>
  obtain xs \<phi>' where \<phi>': "udeval j ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs buf' nts' where mp: "meprev_next I (buf @@ xs) (nts @@ ts) = (zs, buf', nts')"
    by (metis prod_cases3)
  have "ursize \<phi>' = ursize \<phi>"
    using 11(2) \<phi>' by simp
  then show ?case
    by (simp add: udeval.psimps(11)[OF 11(1)] \<phi>' mp del: meprev_next.simps)
next
  case (14 j ts db dags \<phi> \<psi> buf aux) \<comment> \<open>\<^const>\<open>UDSince\<close>\<close>
  obtain xs \<phi>' where \<phi>': "udeval j ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain ys \<psi>' where \<psi>': "udeval j ts db \<psi> = (ys, \<psi>')"
    by fastforce
  obtain zs buf' aux' where e: "uedsx_eval_since dags [] (mebuf2S_add xs ys ts buf) aux = (zs, buf', aux')"
    by (metis prod_cases3)
  have "ursize \<phi>' = ursize \<phi>" "ursize \<psi>' = ursize \<psi>"
    using 14(2) 14(3)[OF refl \<phi>'[symmetric]] \<phi>' \<psi>' by simp_all
  then show ?case
    using usx_q_uedsx_eval_since'[OF e] by (simp add: udeval.psimps(14)[OF 14(1)] \<phi>' \<psi>' e)
next
  case (20 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) \<comment> \<open>\<^const>\<open>UDFrz\<close>\<close>
  let ?db0 = "Mapping.update (p, m) [] db"
  obtain xs \<phi>' where \<phi>': "udeval j ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs0 \<psi>' where \<psi>': "udeval j ts ?db0 \<psi> = (zs0, \<psi>')"
    by fastforce
  obtain rs \<rho>' where \<rho>': "udeval j ts ?db0 \<rho> = (rs, \<rho>')"
    by fastforce
  have s\<phi>: "ursize \<phi>' = ursize \<phi>"
    using 20(2) \<phi>' by simp
  have s\<psi>: "ursize \<psi>' = ursize \<psi>"
    using 20(3)[OF \<phi>'[symmetric] refl refl] \<psi>' by simp
  have s\<rho>: "ursize \<rho>' = ursize \<rho>"
    using 20(4)[OF \<phi>'[symmetric] refl refl \<psi>'[symmetric] refl] \<rho>' by simp
  obtain zo jf fl as lr where st: "(let zs0_out = drop (jfrz - jpsi0) zs0;
       \<alpha>s1 = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs)
     in (zs0_out, jfrz + length zs0_out, frz_fill ng (\<alpha>s @ xs), \<alpha>s1,
       case lv of None \<Rightarrow> None | Some g \<Rightarrow>
         if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
         then Some (g, udeval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
         else None)) = (zo, jf, fl, as, lr)"
    by (rule prod_cases5)
  obtain ys as' lv' s' where lp0: "frz_live_loop ursize (udeval j) (p, m) (Mapping.map_values (\<lambda>_ _. []) db)
      fl d po j jf as lr (\<rho>', w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
        drop (min jf (pR + length rs) - (pR - length rb)) (rb @ rs)) = (ys, as', lv', s')"
    by (metis prod_cases4)
  obtain \<rho>'' w' pR' tq' rb' where s': "s' = (\<rho>'', w', pR', tq', rb')"
    by (metis prod_cases5)
  have s\<rho>'': "ursize \<rho>'' = ursize \<rho>"
    using frz_live_loop_size[OF lp0] s\<rho> s' by simp
  have "snd (udeval j ts db (UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L)) =
    UDFrz p m \<phi>' \<psi>' (jf + length ys) (jpsi0 + length zs0) (jphi + length xs) as' \<rho>'' w' pR' tq' rb' d po ng
      (ufrz_keep_lv (if po then None else lv') \<rho>L) (ufrz_keep_st (if po then None else lv') \<rho>L)"
    by (simp only: udeval.psimps(20)[OF 20(1)] \<phi>' \<psi>' \<rho>' st lp0[unfolded s'] Let_def[where s = ?db0]
        Let_def[where s = "(xs, \<phi>')"] Let_def[where s = "(zs0, \<psi>')"] Let_def[where s = "(rs, \<rho>')"]
        Let_def[where s = "(zo, jf, fl, as, lr)"] Let_def[where s = "(ys, as', lv', \<rho>'', w', pR', tq', rb')"]
        prod.case snd_conv)
  then show ?case
    using s\<phi> s\<psi> s\<rho>'' by simp
next
  case (21 j ts db p m \<phi> \<psi> i buf) \<comment> \<open>\<^const>\<open>UDLetPast\<close>\<close>
  obtain xs i' buf' \<phi>' where lp:
    "uletpast_meval0 (udeval j) j i [] (list_of_option buf) (p, m) ts db \<phi> = (xs, i', buf', \<phi>')"
    by (metis prod_cases4)
  have ursize_\<phi>': "ursize \<phi>' = ursize \<phi>"
    using ursize_uletpast_meval[of "udeval j" j i "[]" "list_of_option buf" "(p, m)" ts db \<phi>]
    by (simp add: lp)
  obtain ys \<psi>' where \<psi>': "udeval j ts (Mapping.update (p, m) xs db) \<psi> = (ys, \<psi>')"
    by fastforce
  have ursize_\<psi>': "ursize \<psi>' = ursize \<psi>"
    using 21(3)[OF lp[symmetric] refl refl refl] \<psi>' by simp
  show ?case
    using ursize_\<phi>' ursize_\<psi>' by (simp add: udeval.psimps(21)[OF 21(1)] lp \<psi>')
  \<comment> \<open>in all other cases, the claim follows directly from the IHs for the subformulas,
    since evaluation keeps the node's constructor and its non-formula arguments do not count\<close>
qed (auto simp only: prod.inject udeval.psimps Let_def snd_conv fst_conv
    ursize.simps list.map map_map o_apply length_map ursize_ufrz_keep_st cong: map_cong
    split: prod.splits)

lemma total_udeval: "All udeval_dom"
proof (relation "measure (\<lambda>(j, ts, db, \<phi>). ursize \<phi>)", goal_cases)
  text \<open>The live copy and the replays of @{const UDFrz}, as for @{const meval}.\<close>
  case 23 \<comment> \<open>the live copy, a subterm\<close>
  then show ?case
    by simp
next
  case (24 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L x xa y xb xc xd ya xe xf yb xg xh
    yc xi yd xj yca xk ycb tsa dba \<psi>')
  have "ursize yb = ursize \<rho>"
    using psize_snd_udeval[of j ts xb \<rho>] 24 by (metis snd_conv)
  then show ?case
    using 24 by simp
qed (auto simp: ursize_in_set dest!: psize_snd_udeval dest: sym split: option.splits)

termination udeval by (rule total_udeval)

lemma ursize_snd_udeval[simp]: "ursize (snd (udeval j ts db \<phi>)) = ursize \<phi>"
  by (rule psize_snd_udeval[OF total_udeval[THEN spec]])

subsection \<open>The two evaluators agree\<close>

lemma mebuf2t_take_nat:
  assumes "\<And>x y t z. f x y t (h z) = h (g x y t z)"
  shows "mebuf2t_take f (h z) buf t ts
    = (case mebuf2t_take g z buf t ts of (z', b) \<Rightarrow> (h z', b))"
  using assms
proof (induct g z buf t ts rule: mebuf2t_take.induct)
  case (1 g z xs ys t0 ts)
  obtain ot ts' where t: "mbuf_t_cases ts = (ot, ts')" by fastforce
  obtain ox xs' where x: "mbuf_t_cases xs = (ox, xs')" by fastforce
  obtain oy ys' where y: "mbuf_t_cases ys = (oy, ys')" by fastforce
  show ?case
  proof (cases "ot = None \<or> ox = None \<or> oy = None")
    case True
    then show ?thesis
      using t x y by (subst (1 2) mebuf2t_take.simps) (auto simp del: mebuf2t_take.simps split: option.splits)
  next
    case False
    then obtain t1 x1 y1 where s: "ot = Some t1" "ox = Some x1" "oy = Some y1"
      by auto
    have IH: "mebuf2t_take f (h (g x1 y1 t1 z)) (xs', ys') t1 ts' =
        (case mebuf2t_take g (g x1 y1 t1 z) (xs', ys') t1 ts' of (z', b) \<Rightarrow> (h z', b))"
      by (rule 1(1)[OF t[symmetric] s(1) x[symmetric] s(2) y[symmetric] s(3) 1(2)])
    show ?thesis
      by (subst (1 2) mebuf2t_take.simps) (simp only: t x y s prod.case option.case 1(2) IH)
  qed
qed

lemma mbuf2t_take_until:
  "mbuf2t_take (dux_add_new dags msk) (rdux aux) (rbuf2 buf) t (Rep_mbuf_t nts @ ts)
   = (case mebuf2t_take (udux_add_new dags msk) aux buf t (nts @@ ts) of
        (aux', buf', t', nts') \<Rightarrow> (rdux aux', rbuf2 buf', t', Rep_mbuf_t nts'))"
  using mbuf2t_take_rbuf2[of "dux_add_new dags msk" "rdux aux" buf t nts ts]
    mebuf2t_take_nat[of "dux_add_new dags msk" rdux "udux_add_new dags msk" aux buf t "nts @@ ts"]
  by (simp add: dux_add_new_rdux split: prod.splits)

lemma mbuf2_add_rbufo: "mbuf2_add xs ys (rbufo buf) = rbufo (mebuf2_add xs ys buf)"
  by (rule mbuf2_add)

lemma mbuf2_take_rbufo:
  "mbuf2_take f (rbufo buf) = (case mebuf2_take f buf of (zs, buf') \<Rightarrow> (zs, rbufo buf'))"
  by (cases "mebuf2_take f buf") (simp add: mebuf2_take)

lemma uletpast_meval0_Rep:
  "(\<And>ts db \<psi>. ursize \<psi> = n \<Longrightarrow>
      eval ts db (Rep_udformula \<psi>) = (case eval' ts db \<psi> of (ys, \<psi>') \<Rightarrow> (ys, Rep_udformula \<psi>'))) \<Longrightarrow>
    ursize \<phi> = n \<Longrightarrow>
    letpast_meval0 eval j i ys xs p ts db (Rep_udformula \<phi>)
    = (case uletpast_meval0 eval' j i ys xs p ts db \<phi> of
        (ys', i', b, \<phi>') \<Rightarrow> (ys', i', b, Rep_udformula \<phi>'))"
proof (induct eval' j i ys xs p ts db \<phi> rule: uletpast_meval0.induct)
  case (1 eval' j i ys xs p ts db \<phi>)
  obtain ys' \<phi>' where e: "eval' ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    by (cases "eval' ts (Mapping.update p xs db) \<phi>")
  have L: "eval ts (Mapping.update p xs db) (Rep_udformula \<phi>) = (ys', Rep_udformula \<phi>')"
    using "1.prems"(1)[OF "1.prems"(2), of ts "Mapping.update p xs db"] by (simp add: e)
  have g: "(size (Rep_udformula \<phi>') \<noteq> size (Rep_udformula \<phi>)) = (ursize \<phi>' \<noteq> ursize \<phi>)"
    by (simp add: ursize_Rep)
  show ?case
  proof (cases "ursize \<phi>' = ursize \<phi>")
    case False
    then show ?thesis
      by (subst letpast_meval0.simps, subst uletpast_meval0.simps) (simp add: Let_def L e g)
  next
    case True
    show ?thesis
    proof (cases ys')
      case Nil
      then show ?thesis
        using True by (subst letpast_meval0.simps, subst uletpast_meval0.simps) (simp add: Let_def L e g)
    next
      case (Cons y ys'')
      show ?thesis
      proof (cases "j \<le> Suc (i + length xs)")
        case le: True
        then show ?thesis
          using True Cons
          by (subst letpast_meval0.simps, subst uletpast_meval0.simps) (simp add: Let_def L e g)
      next
        case False
        have n: "ursize \<phi>' = n"
          using True "1.prems"(2) by simp
        have rec: "letpast_meval0 eval j (i + length xs) (ys @ ys')
            ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) (Rep_udformula \<phi>') =
          (case uletpast_meval0 eval' j (i + length xs) (ys @ ys') ys' p []
              (Mapping.map_values (\<lambda>_ _. []) db) \<phi>' of
            (ys', i', b, \<phi>') \<Rightarrow> (ys', i', b, Rep_udformula \<phi>'))"
          using "1.hyps"[OF e[symmetric] refl _ Cons False "1.prems"(1) n] True by simp
        show ?thesis
          using True False Cons rec
          by (subst letpast_meval0.simps, subst uletpast_meval0.simps) (simp add: Let_def L e g)
      qed
    qed
  qed
qed

lemma gbin_join_eq': "(gbin_join :: _ \<Rightarrow> event_data table \<Rightarrow> _) = dbin_join"
  by (intro ext) (rule gbin_join_eq)

theorem udeval_Rep:
  "deval j ts db (Rep_udformula \<phi>)
   = (case udeval j ts db \<phi> of (zs, \<phi>') \<Rightarrow> (zs, Rep_udformula \<phi>'))"
proof (induction j ts db \<phi> rule: udeval.induct)
  case (13 j ts db ps ns L buf)
  have "map fst (map (deval j ts db) (map Rep_udformula L)) = map fst (map (udeval j ts db) L)"
    "map snd (map (deval j ts db) (map Rep_udformula L))
      = map Rep_udformula (map snd (map (udeval j ts db) L))"
    by (auto simp: 13 split: prod.splits)
  then show ?case
    by (auto simp only: Let_def deval.simps udeval.simps Rep_udformula.simps
        mbufn_add_rbl mbufn_take_ands split: prod.splits)
next
  case (20 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L)
  let ?db0 = "Mapping.update (p, m) [] db"
  let ?dbe = "Mapping.map_values (\<lambda>_ _. []) db"
  obtain xs \<phi>' where \<phi>: "udeval j ts db \<phi> = (xs, \<phi>')"
    by (cases "udeval j ts db \<phi>")
  obtain zs0 \<psi>' where \<psi>: "udeval j ts ?db0 \<psi> = (zs0, \<psi>')"
    by (cases "udeval j ts ?db0 \<psi>")
  obtain rs \<rho>' where \<rho>: "udeval j ts ?db0 \<rho> = (rs, \<rho>')"
    by (cases "udeval j ts ?db0 \<rho>")
  have IH1: "deval j ts db (Rep_udformula \<phi>) = (xs, Rep_udformula \<phi>')"
    using 20(1) \<phi> by simp
  have IH2: "deval j ts ?db0 (Rep_udformula \<psi>) = (zs0, Rep_udformula \<psi>')"
    using 20(2)[OF refl \<phi>[symmetric] refl] \<psi> by simp
  have IH3: "deval j ts ?db0 (Rep_udformula \<rho>) = (rs, Rep_udformula \<rho>')"
    using 20(3)[OF refl \<phi>[symmetric] refl refl \<psi>[symmetric]] \<rho> by simp
  let ?z = "drop (jfrz - jpsi0) zs0"
  let ?as = "drop (jfrz - jphi + length ?z) (\<alpha>s @ xs)"
  let ?dbL = "Mapping.update (p, m) (replicate (length ts) (hd ?as)) db"
  define lru where "lru = (case lv of None \<Rightarrow> None | Some g \<Rightarrow>
    if ?z = [] \<and> ?as \<noteq> [] then Some (g, udeval j ts ?dbL \<rho>L) else None)"
  define lre where "lre = (case lv of None \<Rightarrow> None | Some g \<Rightarrow>
    if ?z = [] \<and> ?as \<noteq> [] then Some (g, deval j ts ?dbL (Rep_udformula \<rho>L)) else None)"
  have st: "(let zs0_out = drop (jfrz - jpsi0) zs0;
       \<alpha>s1 = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs)
     in (zs0_out, jfrz + length zs0_out, frz_fill ng (\<alpha>s @ xs), \<alpha>s1,
       case lv of None \<Rightarrow> None | Some g \<Rightarrow>
         if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
         then Some (g, udeval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
         else None)) = (?z, jfrz + length ?z, frz_fill ng (\<alpha>s @ xs), ?as, lru)"
    by (simp only: Let_def lru_def)
  have IHL: "lre = map_option (\<lambda>(k, us, \<sigma>). (k, us, Rep_udformula \<sigma>)) lru"
  proof (cases lv)
    case (Some g)
    show ?thesis
    proof (cases "?z = [] \<and> ?as \<noteq> []")
      case True
      have "deval j ts ?dbL (Rep_udformula \<rho>L) =
          (case udeval j ts ?dbL \<rho>L of (zs, \<phi>') \<Rightarrow> (zs, Rep_udformula \<phi>'))"
        by (rule 20(4)[OF refl \<phi>[symmetric] refl refl \<psi>[symmetric] refl \<rho>[symmetric] refl refl Some True])
      then show ?thesis
        using Some True by (simp add: lru_def lre_def split: prod.splits)
    qed (use Some in \<open>auto simp: lru_def lre_def\<close>)
  qed (simp add: lru_def lre_def)
  have IHloop: "deval j ts' db' (Rep_udformula \<chi>) = apsnd Rep_udformula (udeval j ts' db' \<chi>)"
    if "ursize \<chi> = ursize \<rho>'" for ts' db' \<chi>
    using 20(5)[OF refl \<phi>[symmetric] refl refl \<psi>[symmetric] refl \<rho>[symmetric] refl st[symmetric]
        refl refl refl, of \<chi> ts' db'] that
    by (simp split: prod.splits)
  let ?k = "min (jfrz + length ?z) (pR + length rs) - (pR - length rb)"
  let ?tq = "if d = \<infinity> then [] else tq @ ts"
  obtain ys as' lvu \<rho>2 w2 pR2 tq2 rb2 where fr0: "frz_live_loop ursize (udeval j) (p, m) ?dbe
      (frz_fill ng (\<alpha>s @ xs)) d po j (jfrz + length ?z) ?as lru (\<rho>', w, pR + length rs, ?tq, drop ?k (rb @ rs))
      = (ys, as', lvu, \<rho>2, w2, pR2, tq2, rb2)"
    by (metis prod_cases4 prod_cases5)
  have fre: "frz_live_loop size (deval j) (p, m) ?dbe
      (frz_fill ng (\<alpha>s @ xs)) d po j (jfrz + length ?z) ?as lre
      (Rep_udformula \<rho>', w, pR + length rs, ?tq, drop ?k (rb @ rs))
      = (ys, as', map_option (apsnd Rep_udformula) lvu, Rep_udformula \<rho>2, w2, pR2, tq2, rb2)"
  proof -
    have ev: "deval j ts' db' (Rep_udformula \<chi>) = apsnd Rep_udformula (udeval j ts' db' \<chi>)"
      if "ursize \<chi> = ursize (fst (\<rho>', w, pR + length rs, ?tq, drop ?k (rb @ rs)))" for ts' db' \<chi>
      by (rule IHloop) (use that in \<open>simp only: fst_conv\<close>)
    show ?thesis
      using frz_live_loop_map[where sz' = size and ev' = "deval j" and f = Rep_udformula,
          OF ev ursize_Rep[symmetric] fr0]
      by (simp only: IHL[symmetric] apfst_conv)
  qed
  have keep: "frz_keep_lv (if po then None else map_option (apsnd Rep_udformula) lvu) (Rep_udformula \<rho>L) =
      ufrz_keep_lv (if po then None else lvu) \<rho>L"
    "frz_keep_st (if po then None else map_option (apsnd Rep_udformula) lvu) (Rep_udformula \<rho>L) =
      Rep_udformula (ufrz_keep_st (if po then None else lvu) \<rho>L)"
  proof -
    have ifm: "(if po then None else map_option (apsnd Rep_udformula) lvu) =
      map_option (apsnd Rep_udformula) (if po then None else lvu)"
      by simp
    show "frz_keep_lv (if po then None else map_option (apsnd Rep_udformula) lvu) (Rep_udformula \<rho>L) =
      ufrz_keep_lv (if po then None else lvu) \<rho>L"
      "frz_keep_st (if po then None else map_option (apsnd Rep_udformula) lvu) (Rep_udformula \<rho>L) =
      Rep_udformula (ufrz_keep_st (if po then None else lvu) \<rho>L)"
      by (simp_all only: ifm frz_keep_Rep)
  qed
  show ?case
    by (simp only: Rep_udformula.simps deval.simps udeval.simps Let_def IH1 IH2 IH3 \<phi> \<psi> \<rho>
        lre_def[symmetric] lru_def[symmetric] fr0 fre keep prod.case)
next
  case (21 j ts db p m \<phi> \<psi> i buf)
  have IH: "ursize \<psi> = ursize \<phi> \<Longrightarrow> deval j ts db (Rep_udformula \<psi>) =
    (case udeval j ts db \<psi> of (zs, \<psi>') \<Rightarrow> (zs, Rep_udformula \<psi>'))" for ts db \<psi>
    using 21 by auto
  have lp: "letpast_meval0 (deval j) j i [] (list_of_option buf) (p, m) ts db (Rep_udformula \<phi>)
    = (case uletpast_meval0 (udeval j) j i [] (list_of_option buf) (p, m) ts db \<phi> of
        (ys', i', b, \<phi>') \<Rightarrow> (ys', i', b, Rep_udformula \<phi>'))"
    by (rule uletpast_meval0_Rep[where n = "ursize \<phi>" and eval = "deval j" and eval' = "udeval j",
          OF IH refl])
  show ?case
    using 21(2)[OF refl _ refl refl]
    by (cases "uletpast_meval0 (udeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>")
      (auto simp: lp split: prod.splits)
next
  case (11 j ts db I \<phi> first buf nts)
  then show ?case
    by (simp add: mprev_next_prev mbuf_t_append.rep_eq
        del: mprev_next.simps meprev_next.simps split: prod.splits)
next
  case (12 j ts db I \<phi> first nts)
  then show ?case
    by (simp add: mprev_next_next del: mprev_next.simps meprev_next.simps split: prod.splits list.splits bool.splits)
next
  case (14 j ts db dags \<phi> \<psi> buf aux)
  obtain xs \<phi>' where e1: "udeval j ts db \<phi> = (xs, \<phi>')" by (cases "udeval j ts db \<phi>")
  obtain ys \<psi>' where e2: "udeval j ts db \<psi> = (ys, \<psi>')" by (cases "udeval j ts db \<psi>")
  obtain zs buf' aux' where e3: "uedsx_eval_since dags [] (mebuf2S_add xs ys ts buf) aux
      = (zs, buf', aux')"
    by (cases "uedsx_eval_since dags [] (mebuf2S_add xs ys ts buf) aux")
  obtain Zs Bf Ax where E3: "dsx_eval_since dags [] (rbufS (mebuf2S_add xs ys ts buf)) (rdsx aux)
      = (Zs, Bf, Ax)"
    by (cases "dsx_eval_since dags [] (rbufS (mebuf2S_add xs ys ts buf)) (rdsx aux)")
  have Z: "map (ufilt (usx_q aux)) Zs = zs" and B: "Bf = rbufS buf'" and A: "Ax = rdsx aux'"
    using dsx_eval_since_rdsx0[where args = dags and buf = "mebuf2S_add xs ys ts buf" and aux = aux]
    by (simp_all add: e3 E3)
  have q: "usx_q aux' = usx_q aux" by (rule usx_q_uedsx_eval_since'[OF e3])
  show ?case
    using 14
    by (simp add: e1 e2 e3 E3 Z B A q mbuf2S_add_rbufS deval_dandrel
        del: dsx_eval_since.simps uedsx_eval_since.simps split: prod.splits)
next
  case (15 j ts db dags msk \<phi> \<psi> buf nts t aux)
  then show ?case
    by (simp add: mbuf2_add_rbuf2 mbuf2t_take_until dux_eval_rdux split: prod.splits)
next
  case (22 j ts db dags pl \<phi> \<psi> dbuf nts daux)
  then show ?case
    by (simp add: mbuf2_add_rbuf2 mbuf2T_take_rbuf2
        del: mbuf2T_take.simps mebuf2T_take.simps split: prod.splits)
next
  case (23 j ts db m I mr mrs pls Ld dbuf nts daux)
  have R: "map fst (map (deval j ts db) (map Rep_udformula Ld)) = map fst (map (udeval j ts db) Ld)"
    "map snd (map (deval j ts db) (map Rep_udformula Ld))
      = map Rep_udformula (map snd (map (udeval j ts db) Ld))"
    by (auto simp: 23 split: prod.splits)
  show ?case
    by (simp only: Let_def deval.simps udeval.simps R mbufn_add_rbl mbufnt_take_matchP
        Rep_udformula.simps) (simp split: prod.splits)
next
  case (24 j ts db m I mr mrs pls Ld dbuf nts t daux)
  have R: "map fst (map (deval j ts db) (map Rep_udformula Ld)) = map fst (map (udeval j ts db) Ld)"
    "map snd (map (deval j ts db) (map Rep_udformula Ld))
      = map Rep_udformula (map snd (map (udeval j ts db) Ld))"
    by (auto simp: 24 split: prod.splits)
  show ?case
    by (simp only: Let_def deval.simps udeval.simps R mbufn_add_rbl mbufnt_take_rbl
        Rep_udformula.simps) (simp split: prod.splits)
next
  case (25 j ts db pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux)
  then show ?case
    by (simp add: mbuf2_add_rbuf2 mbuf2T_take_rbuf2 mbuf2_add_rbufo mbuf2_take_rbufo gbin_join_eq'
        del: mbuf2T_take.simps mebuf2T_take.simps mbuf2_take.simps mebuf2_take.simps split: prod.splits)
qed (simp_all add: mbuf2_add_rbuf2 mbuf2_take_rbuf2 gbin_join_eq'
    del: mbuf2_take.simps mebuf2_take.simps split: prod.splits option.splits)

subsection \<open>The compiler\<close>

text \<open>
  A constraint over a node whose result is an aggregate becomes the node's guard rather than a
  filter above it, when the node is a fused aggregating Since: the constraint is on the node's
  own columns, which are exactly the aggregation's, so the groups that fail it never have to be
  built.  Nothing else is fused -- every other node keeps the filter above it -- and the dense
  compiler @{const dof} keeps it above this one too, which is what @{const dandrel} in
  @{const Rep_udformula} says.
\<close>

fun uset_q :: "uconstr \<Rightarrow> udformula \<Rightarrow> udformula option" where
  "uset_q c (UDSince args \<phi> \<psi> buf aux) =
     (case aux of UDSX_wagg p None a \<Rightarrow> Some (UDSince args \<phi> \<psi> buf (UDSX_wagg p (Some c) a))
      | _ \<Rightarrow> None)"
| "uset_q c \<phi> = None"

lemma Rep_uset_q:
  "uset_q c d = Some d' \<Longrightarrow> Rep_udformula d' = DAndRel (Rep_udformula d) c"
  by (cases d) (auto simp: dandrel_def split: udsaux_x.splits option.splits)

text \<open>
  The initial state of the executable formula, compiled from the input formula: @{text udinit}
  places each node the way @{const dof} places the kernel's initial state @{const minit0},
  descending the formula the way @{const minit0} does and reading each operand's column list
  off the formula, as @{const minit0} stores it in the node.  The temporal nodes are built by
  the functions below, one for each case of @{const dof}, from their compiled operands.
\<close>

definition usince_init :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> udformula \<Rightarrow> udformula \<Rightarrow> udformula" where
  "usince_init n ks cs args \<phi>d \<psi>d =
     (let kL = args_L args; kR = args_R args; cL = dcols kL; cR = dcols kR in
      case args_agg args of
        None \<Rightarrow>
          (if args_n args = n \<and> ks = kR \<and> cs = cR \<and> set kL \<subseteq> set kR
           then UDSince (dargs cR cL args) \<phi>d \<psi>d init_mebuf2S
                  (udsx_init (dargs cR cL args) (dmsk cR cL))
           else UDFail)
      | Some ag \<Rightarrow>
          (let m = length (aggargs_tys ag); g = dagg_gcols ag; y = aggargs_y ag in
           if aggargs_cols ag = kR \<and> set kL \<subseteq> set kR \<and>
              agg_cols m g = cR \<and> ks = y # shift_cols m kR \<and> cs = merge_cols g [y] \<and>
              y \<notin> set g \<and> (aggargs_g0 ag \<longrightarrow> g = []) \<and> Formula.fv_trm (aggargs_f ag) \<subseteq> set kR
           then (if cpos cR (set cL) = {}
                 then UDSince (dargs cR cL args) \<phi>d \<psi>d init_mebuf2S
                        (udsx_init_agg (dargs cR cL args)
                          (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
                           m, ins_pos g y) None)
                 else UDAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
                        m (ins_pos g y)
                        (UDSince (dargs cR cL args) \<phi>d \<psi>d init_mebuf2S
                          (udsx_init (dargs cR cL args) (dmsk cR cL))))
           else UDFail))"

definition uuntil_init :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> udformula \<Rightarrow> udformula \<Rightarrow> udformula" where
  "uuntil_init n ks cs args \<phi>d \<psi>d =
     (let kL = args_L args; kR = args_R args; cL = dcols kL; cR = dcols kR in
      case args_agg args of
        None \<Rightarrow>
          (if args_n args = n \<and> ks = kR \<and> cs = cR \<and> set kL \<subseteq> set kR
           then UDUntil (dargs cR cL args) (dmsk cR cL) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty)
                  mbuf_t_empty 0 (udux_init (dargs cR cL args))
           else UDFail)
      | Some ag \<Rightarrow>
          (let m = length (aggargs_tys ag); g = dagg_gcols ag; y = aggargs_y ag in
           if aggargs_cols ag = kR \<and> set kL \<subseteq> set kR \<and>
              agg_cols m g = cR \<and> ks = y # shift_cols m kR \<and> cs = merge_cols g [y] \<and>
              y \<notin> set g \<and> (aggargs_g0 ag \<longrightarrow> g = []) \<and> Formula.fv_trm (aggargs_f ag) \<subseteq> set kR
           then (if cpos cR (set cL) = {} \<and> memL (args_ivl args) 0
                 then UDUntil (dargs cR cL args) (dmsk cR cL) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty)
                        mbuf_t_empty 0
                        (udux_init_agg (dargs cR cL args)
                          (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
                           m, ins_pos g y))
                 else UDAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
                        m (ins_pos g y)
                        (UDUntil (dargs cR cL args) (dmsk cR cL) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty)
                          mbuf_t_empty 0 (udux_init (dargs cR cL args))))
           else UDFail))"

definition utrigger_init :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> udformula \<Rightarrow> udformula \<Rightarrow> udformula" where
  "utrigger_init ks cs args \<phi>d \<psi>d =
     (let kL = args_L args; kR = args_R args; cL = dcols kL in
      if ks = kR \<and> cs = dcols kR \<and> set kL \<subseteq> set kR \<and> mem (args_ivl args) 0
      then UDTrigger (dargs cs cL args) (emb_plan cs cL) \<phi>d \<psi>d
             (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty (ginit_mmtaux (dargs cs cL args) (dmsk cs cL))
      else UDFail)"

definition uandtrigger_init :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> udformula \<Rightarrow> udformula \<Rightarrow> udformula \<Rightarrow>
    udformula" where
  "uandtrigger_init k ks cs args \<alpha>d \<phi>d \<psi>d =
     (let kL = args_L args; kR = args_R args; cR = dcols kR; cL = dcols kL in
      if k = ks \<and> set kR \<subseteq> set ks \<and> set kL \<subseteq> set kR \<and> tok cR cL args
      then UDAndTrigger (mk_djoin cs cR) \<alpha>d (mbuf_t_empty, mbuf_t_empty) (dargs cR cL args)
             \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty
             (ginit_mmtaux (dargs cR cL args) (dmsk cR cL))
      else UDFail)"

definition uagg_init :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> aggargs \<Rightarrow> (cols \<Rightarrow> udformula) \<Rightarrow> udformula" where
  "uagg_init n ks cs args \<phi>d =
     (let m = length (aggargs_tys args); k0 = aggargs_cols args; g = dagg_gcols args;
          y = aggargs_y args in
      if ks = y # shift_cols m k0 \<and> cs = merge_cols g [y] \<and> dcols k0 = agg_cols m g \<and>
         y \<notin> set g \<and> (aggargs_g0 args \<longrightarrow> g = []) \<and> Formula.fv_trm (aggargs_f args) \<subseteq> set k0
      then UDAgg (aggargs_g0 args) (aggargs_\<omega> args)
             (reindex_trm (agg_cols m g) (aggargs_f args)) m (ins_pos g y) (\<phi>d (agg_cols m g))
      else UDFail)"

abbreviation (input) fvc :: "ty Formula.formula \<Rightarrow> cols" where
  "fvc \<phi> \<equiv> dcols (Formula.fv_list \<phi>)"

function (sequential) udinit :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> ty Formula.formula \<Rightarrow> udformula" where
  "udinit n ks cs (Formula.Neg \<phi>) = (if fv \<phi> = {}
     then (if ks = [] \<and> cs = [] then UDNeg (udinit n [] [] \<phi>) else UDFail)
     else UDRel (dtabc ks cs empty_table))"
| "udinit n ks cs (Formula.Eq t1 t2) = UDRel (dtabc ks cs (eq_rel t1 t2))"
| "udinit n ks cs (Formula.Pred e tms) = (let mode = pred_mode_of n tms in
     if mode = Match then (if ks = pred_cols tms then UDPredM e (length tms) tms cs else UDFail)
     else if (mode = Copy \<and> tms = map Formula.Var [0..<length tms] \<and> ks = [0..<length tms] \<and> cs = ks)
          \<or> (mode = Simple \<and> is_simple_pattern tms 0 \<and> cs = smp_cols tms \<and> ks = cs)
     then UDPredS e (length tms)
     else UDFail)"
| "udinit n ks cs (Formula.Let p \<phi> \<psi>) =
     (let m = Formula.nfv \<phi>; kks = Formula.fv_list \<phi> in
      if dcols kks = [0..<m] then UDLet p m (udinit m kks [0..<m] \<phi>) (udinit n ks cs \<psi>) else UDFail)"
| "udinit n ks cs (Formula.Frz p \<phi> \<psi>) =
     (let m = Formula.nfv \<phi>; kks = Formula.fv_list \<phi>; d = udinit n ks cs \<psi> in
      if dcols kks = [0..<m]
      then UDFrz p m (udinit m kks [0..<m] \<phi>) d 0 0 0 [] d 0 0 [] [] (past_reach \<psi>)
        (safe_letpast (p, m) \<psi> \<le> NonFutuRec) (neg_pred (p, m) \<psi>) None d
      else UDFail)"
| "udinit n ks cs (Formula.LetPast p \<phi> \<psi>) =
     (let m = Formula.nfv \<phi>; kks = Formula.fv_list \<phi> in
      if dcols kks = [0..<m] then UDLetPast p m (udinit m kks [0..<m] \<phi>) (udinit n ks cs \<psi>) 0 None
      else UDFail)"
| "udinit n ks cs (Formula.Or \<phi> \<psi>) =
     (let k2 = Formula.fv_list \<psi> in
      if Formula.fv_list \<phi> = ks \<and> set k2 = set ks
      then UDOr (udinit n ks cs \<phi>) (udinit n k2 cs \<psi>) (mbuf_t_empty, mbuf_t_empty) else UDFail)"
| "udinit n ks cs (Formula.And \<phi> \<psi>) =
    (if safe_assignment (fv \<phi>) \<psi> then
       (let k0 = Formula.fv_list \<phi>; conf = split_assignment (fv \<phi>) \<psi>; y = fst conf; t = snd conf;
            c0 = dcols k0 in
        if ks = k0 @ [y] \<and> y \<notin> set k0 \<and> Formula.fv_trm t \<subseteq> set c0 \<and> cs = merge_cols c0 [y]
        then UDAndAssign (ins_pos c0 y) (reindex_trm c0 t) (udinit n k0 c0 \<phi>)
        else UDFail)
     else if safe_formula \<psi> then
       (let k1 = Formula.fv_list \<phi>; k2 = Formula.fv_list \<psi>; c1 = dcols k1; c2 = dcols k2 in
        if ks = cols_union k1 k2 \<and> cs = merge_cols c1 c2
        then UDAnd (mk_djoin c1 c2) (udinit n k1 c1 \<phi>) True (udinit n k2 c2 \<psi>)
               (mbuf_t_empty, mbuf_t_empty)
        else UDFail)
     else if is_constraint \<psi> then
       (let conf = split_constraint \<psi> in
        if Formula.fv_list \<phi> = ks \<and> Formula.fv_trm (fst conf) \<subseteq> set cs \<and>
           Formula.fv_trm (snd (snd (snd conf))) \<subseteq> set cs
        then (let d = udinit n ks cs \<phi>; c = reindex_constraint cs conf
              in case uset_q c d of Some d' \<Rightarrow> d' | None \<Rightarrow> UDAndRel d c)
        else UDFail)
     else (case \<psi> of
       Formula.Neg \<psi>' \<Rightarrow>
         (let k1 = Formula.fv_list \<phi>; k2 = Formula.fv_list \<psi>'; c1 = dcols k1; c2 = dcols k2 in
          if ks = cols_union k1 k2 \<and> cs = merge_cols c1 c2 \<and> set k2 \<subseteq> set k1
          then UDAnd (mk_djoin c1 c2) (udinit n k1 c1 \<phi>) False (udinit n k2 c2 \<psi>')
                 (mbuf_t_empty, mbuf_t_empty)
          else UDFail)
     | Formula.Trigger \<phi>' I \<psi>' \<Rightarrow>
         (let \<alpha>d = udinit n ks cs \<phi>; \<psi>d = udinit n (Formula.fv_list \<psi>') (fvc \<psi>') \<psi>';
              tr = (\<lambda>b \<alpha> \<phi>d. uandtrigger_init (Formula.fv_list \<phi>) ks cs
                (init_args I n (Formula.fv_list \<alpha>) (Formula.fv_list \<psi>') b None) \<alpha>d \<phi>d \<psi>d) in
          if safe_formula \<phi>' then tr True \<phi>' (udinit n (Formula.fv_list \<phi>') (fvc \<phi>') \<phi>')
          else case \<phi>' of Formula.Neg \<alpha> \<Rightarrow> tr False \<alpha> (udinit n (Formula.fv_list \<alpha>) (fvc \<alpha>) \<alpha>)
            | _ \<Rightarrow> UDRel (dtabc ks cs empty_table))
     | Formula.Release \<phi>' I \<psi>' \<Rightarrow> udinit n ks cs (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
     | _ \<Rightarrow> UDRel (dtabc ks cs empty_table)))"
| "udinit n ks cs (Formula.Ands l) =
    (let (pos, neg) = partition safe_formula l in
     case pos of [] \<Rightarrow> UDFail
     | p # ps \<Rightarrow>
       (let k0 = Formula.fv_list p; kss = map Formula.fv_list ps; kneg = map Formula.fv_list neg;
            c0 = dcols k0; css = map dcols kss; nss = map dcols kneg in
        if Formula.fv_list (Formula.Ands l) = ks \<and> cs = dands_cols c0 css \<and>
           (\<forall>c \<in> set nss. set c \<subseteq> set (dands_cols c0 css))
        then UDAnds (dands_plans c0 css) (dands_plans (dands_cols c0 css) nss)
               (map2 (\<lambda>k \<phi>. udinit n k (dcols k) \<phi>) (k0 # kss @ kneg) (pos @ map remove_neg neg))
               (map (\<lambda>_. mbuf_t_empty) (pos @ neg))
        else UDFail))"
| "udinit n ks cs (Formula.Exists T \<phi>) =
     (let kks = Formula.fv_list \<phi>; ccs = dcols kks in
      if ks = ex_cols kks \<and> cs = dex_cols ccs
      then UDExists (udinit (Suc n) kks ccs \<phi>) (ex_drop0 ccs) else UDFail)"
| "udinit n ks cs (Formula.Agg y \<omega> tys f \<phi>) =
    (let m = length tys; ag = init_aggargs (Formula.fv_list \<phi>) n (fv \<phi> \<subseteq> {0..<m}) y \<omega> tys f in
     case \<phi> of
       Formula.Since \<phi>' I \<psi>' \<Rightarrow>
         (let \<psi>d = udinit (m + n) (Formula.fv_list \<psi>') (fvc \<psi>') \<psi>';
              sn = (\<lambda>b \<alpha> \<phi>d. usince_init n ks cs
                (init_args I (m + n) (Formula.fv_list \<alpha>) (Formula.fv_list \<psi>') b (Some ag)) \<phi>d \<psi>d) in
          if safe_formula \<phi>' then sn True \<phi>' (udinit (m + n) (Formula.fv_list \<phi>') (fvc \<phi>') \<phi>')
          else case \<phi>' of Formula.Neg \<alpha> \<Rightarrow> sn False \<alpha> (udinit (m + n) (Formula.fv_list \<alpha>) (fvc \<alpha>) \<alpha>)
            | _ \<Rightarrow> UDRel (dtabc ks cs empty_table))
     | Formula.Until \<phi>' I \<psi>' \<Rightarrow>
         (let \<psi>d = udinit (m + n) (Formula.fv_list \<psi>') (fvc \<psi>') \<psi>';
              un = (\<lambda>b \<alpha> \<phi>d. uuntil_init n ks cs
                (init_args I (m + n) (Formula.fv_list \<alpha>) (Formula.fv_list \<psi>') b (Some ag)) \<phi>d \<psi>d) in
          if safe_formula \<phi>' then un True \<phi>' (udinit (m + n) (Formula.fv_list \<phi>') (fvc \<phi>') \<phi>')
          else case \<phi>' of Formula.Neg \<alpha> \<Rightarrow> un False \<alpha> (udinit (m + n) (Formula.fv_list \<alpha>) (fvc \<alpha>) \<alpha>)
            | _ \<Rightarrow> UDRel (dtabc ks cs empty_table))
     | _ \<Rightarrow> uagg_init n ks cs ag (\<lambda>c. udinit (m + n) (Formula.fv_list \<phi>) c \<phi>))"
| "udinit n ks cs (Formula.Prev I \<phi>) = UDPrev I (udinit n ks cs \<phi>) True mbuf_t_empty mbuf_t_empty"
| "udinit n ks cs (Formula.Next I \<phi>) = UDNext I (udinit n ks cs \<phi>) True mbuf_t_empty"
| "udinit n ks cs (Formula.Since \<phi> I \<psi>) =
    (let \<psi>d = udinit n (Formula.fv_list \<psi>) (fvc \<psi>) \<psi>;
         sn = (\<lambda>b \<alpha> \<phi>d. usince_init n ks cs
           (init_args I n (Formula.fv_list \<alpha>) (Formula.fv_list \<psi>) b None) \<phi>d \<psi>d) in
     if safe_formula \<phi> then sn True \<phi> (udinit n (Formula.fv_list \<phi>) (fvc \<phi>) \<phi>)
     else case \<phi> of Formula.Neg \<alpha> \<Rightarrow> sn False \<alpha> (udinit n (Formula.fv_list \<alpha>) (fvc \<alpha>) \<alpha>)
       | _ \<Rightarrow> UDRel (dtabc ks cs empty_table))"
| "udinit n ks cs (Formula.Until \<phi> I \<psi>) =
    (let \<psi>d = udinit n (Formula.fv_list \<psi>) (fvc \<psi>) \<psi>;
         un = (\<lambda>b \<alpha> \<phi>d. uuntil_init n ks cs
           (init_args I n (Formula.fv_list \<alpha>) (Formula.fv_list \<psi>) b None) \<phi>d \<psi>d) in
     if safe_formula \<phi> then un True \<phi> (udinit n (Formula.fv_list \<phi>) (fvc \<phi>) \<phi>)
     else case \<phi> of Formula.Neg \<alpha> \<Rightarrow> un False \<alpha> (udinit n (Formula.fv_list \<alpha>) (fvc \<alpha>) \<alpha>)
       | _ \<Rightarrow> UDRel (dtabc ks cs empty_table))"
| "udinit n ks cs (Formula.Trigger \<phi> I \<psi>) =
    (let \<psi>d = udinit n (Formula.fv_list \<psi>) cs \<psi>;
         tr = (\<lambda>b \<alpha> \<phi>d. utrigger_init ks cs
           (init_args I n (Formula.fv_list \<alpha>) (Formula.fv_list \<psi>) b None) \<phi>d \<psi>d) in
     if safe_formula \<phi> then tr True \<phi> (udinit n (Formula.fv_list \<phi>) (fvc \<phi>) \<phi>)
     else case \<phi> of Formula.Neg \<alpha> \<Rightarrow> tr False \<alpha> (udinit n (Formula.fv_list \<alpha>) (fvc \<alpha>) \<alpha>)
       | _ \<Rightarrow> UDRel (dtabc ks cs empty_table))"
| "udinit n ks cs (Formula.Release \<phi> I \<psi>) = (if mem I 0
     then udinit n ks cs (release_safe_0 \<phi> I \<psi>)
     else udinit n ks cs (release_safe_bounded \<phi> I \<psi>))"
| "udinit n ks cs (Formula.MatchP I r) =
    (let (mr, \<phi>s) = to_mregex r; dss = map Formula.fv_list \<phi>s; css = map dcols dss in
     if Formula.fv_list (Formula.MatchP I r) = ks \<and> (\<forall>c \<in> set css. set c \<subseteq> set cs)
     then UDMatchP (length cs) I mr (sorted_list_of_set (RPDs mr)) (map (emb_plan cs) css)
            (map2 (\<lambda>k \<phi>. udinit n k (dcols k) \<phi>) dss \<phi>s) (map (\<lambda>_. mbuf_t_empty) \<phi>s) mbuf_t_empty []
     else UDFail)"
| "udinit n ks cs (Formula.MatchF I r) =
    (let (mr, \<phi>s) = to_mregex r; dss = map Formula.fv_list \<phi>s; css = map dcols dss in
     if Formula.fv_list (Formula.MatchF I r) = ks \<and> (\<forall>c \<in> set css. set c \<subseteq> set cs)
     then UDMatchF (length cs) I mr (sorted_list_of_set (LPDs mr)) (map (emb_plan cs) css)
            (map2 (\<lambda>k \<phi>. udinit n k (dcols k) \<phi>) dss \<phi>s) (map (\<lambda>_. mbuf_t_empty) \<phi>s) mbuf_t_empty 0 []
     else UDFail)"
| "udinit n ks cs (Formula.TP t) =
     (let mt = mtrm_of_trm t in if ks = mtrm_dcols mt \<and> cs = ks then UDTP mt 0 else UDFail)"
| "udinit n ks cs (Formula.TS t) =
     (let mt = mtrm_of_trm t in if ks = mtrm_dcols mt \<and> cs = ks then UDTS mt else UDFail)"
| "udinit n ks cs _ = UDRel (dtabc ks cs empty_table)"
  by pat_completeness auto

termination
proof ((relation "measure (\<lambda>(_, _, _, \<phi>). size' \<phi>)"; clarsimp), goal_cases)
  case (5 \<phi> \<phi>' I \<psi>')
  then show ?case
    using size'_and_release[of \<phi> \<phi>' I \<psi>'] by simp
next
  case (6 l x xs c \<psi>)
  then have "\<psi> \<in> set (filter safe_formula l @ map remove_neg (filter (Not \<circ> safe_formula) l))"
    by (auto dest: set_zip_rightD)
  then obtain x where "x \<in> set l" "size' \<psi> \<le> size' x"
    using size'_remove_neg by fastforce
  then show ?case
    using sum_list_mem_leq[of x l size'] by linarith
next
  case (7 \<phi> I \<psi>)
  then show ?case
    using size'_release_aux(4)[of \<phi> I \<psi>] by simp
next
  case (8 \<phi> I \<psi>)
  then show ?case
    using size'_release_aux(3)[of \<phi> I \<psi>] by simp
next
  case 9
  then show ?case
    by (clarsimp dest!: to_mregex_ok[OF sym] atms_size' set_zip_rightD)
next
  case 10
  then show ?case
    by (clarsimp dest!: to_mregex_ok[OF sym] atms_size' set_zip_rightD)
qed (case_tac \<psi>; clarsimp)+

lemma usince_init_dof:
  assumes "Rep_udformula \<phi>d = dof (args_n args) (args_L args) (dcols (args_L args)) \<phi>"
    and "Rep_udformula \<psi>d = dof (args_n args) (args_R args) (dcols (args_R args)) \<psi>"
  shows "Rep_udformula (usince_init n ks cs args \<phi>d \<psi>d) = dof n ks cs (MSince args \<phi> \<psi> init_mbuf2S aux)"
  using assms by (cases "args_agg args")
    (simp_all only: usince_init_def dof.simps Let_def option.case Rep_udformula.simps dandrel_None
      usx_q.simps usx_q_init usx_q_init_agg dsx_init_rdsx[symmetric] dsx_init_agg_rdsx rbufS.simps mbuf_t_empty.rep_eq
      if_distrib[of Rep_udformula] simp_thms)

lemma uuntil_init_dof:
  assumes "Rep_udformula \<phi>d = dof (args_n args) (args_L args) (dcols (args_L args)) \<phi>"
    and "Rep_udformula \<psi>d = dof (args_n args) (args_R args) (dcols (args_R args)) \<psi>"
  shows "Rep_udformula (uuntil_init n ks cs args \<phi>d \<psi>d) = dof n ks cs (MUntil args \<phi> \<psi> ([], []) [] 0 aux)"
  using assms by (cases "args_agg args")
    (simp_all only: uuntil_init_def dof.simps Let_def option.case Rep_udformula.simps
      dux_init_rdux[symmetric] dux_init_agg_rdux[symmetric] map_prod_simp mbuf_t_empty.rep_eq
      if_distrib[of Rep_udformula] simp_thms)

lemma utrigger_init_dof:
  assumes "Rep_udformula \<phi>d = dof n (args_L args) (dcols (args_L args)) \<phi>"
    and "Rep_udformula \<psi>d = dof n (args_R args) cs \<psi>"
  shows "Rep_udformula (utrigger_init ks cs args \<phi>d \<psi>d) = dof n ks cs (MTrigger args \<phi> \<psi> ([], []) [] aux)"
  using assms by (simp add: utrigger_init_def Let_def mbuf_t_empty.rep_eq)

lemma uandtrigger_init_dof:
  assumes "Rep_udformula \<alpha>d = dof n ks cs \<alpha>"
    and "Rep_udformula \<phi>d = dof n (args_L args) (dcols (args_L args)) \<phi>"
    and "Rep_udformula \<psi>d = dof n (args_R args) (dcols (args_R args)) \<psi>"
  shows "Rep_udformula (uandtrigger_init k ks cs args \<alpha>d \<phi>d \<psi>d) =
    dof n ks cs (MAndTrigger k \<alpha> ([], []) args \<phi> \<psi> ([], []) [] aux)"
  using assms by (simp add: uandtrigger_init_def Let_def mbuf_t_empty.rep_eq)

lemma uagg_init_dof:
  assumes "\<And>c. Rep_udformula (\<phi>d c) = dof (length (aggargs_tys args) + n) (aggargs_cols args) c \<phi>"
  shows "Rep_udformula (uagg_init n ks cs args \<phi>d) = dof n ks cs (MAgg args \<phi>)"
  using assms by (simp add: uagg_init_def Let_def)

lemma case_formula_Neg_other:
  assumes "\<And>\<alpha>. \<phi> \<noteq> Formula.Neg \<alpha>"
  shows "(case \<phi> of Formula.Neg \<alpha> \<Rightarrow> Nf \<alpha> | _ \<Rightarrow> D) = D"
  using assms by (cases \<phi>) auto

lemma case_formula_NTR_other:
  assumes "\<And>a. \<psi> \<noteq> Formula.Neg a" "\<And>a I b. \<psi> \<noteq> Formula.Trigger a I b"
    "\<And>a I b. \<psi> \<noteq> Formula.Release a I b"
  shows "(case \<psi> of Formula.Neg a \<Rightarrow> Nf a | Formula.Trigger a I b \<Rightarrow> T a I b
    | Formula.Release a I b \<Rightarrow> R a I b | _ \<Rightarrow> D) = D"
  using assms by (cases \<psi>) auto

lemma case_formula_Since_Until_other:
  assumes "\<And>a I b. \<phi> \<noteq> Formula.Since a I b" and "\<And>a I b. \<phi> \<noteq> Formula.Until a I b"
  shows "(case \<phi> of Formula.Since a I b \<Rightarrow> S a I b | Formula.Until a I b \<Rightarrow> U a I b | _ \<Rightarrow> D) = D"
  using assms by (cases \<phi>) auto

lemma udinit_dof: "Rep_udformula (udinit n ks cs \<phi>) = dof n ks cs (minit0 n \<phi>)"
proof (induct n ks cs \<phi> rule: udinit.induct)
  case (8 n ks cs \<phi> \<psi>)
  show ?case
  proof (cases "safe_assignment (fv \<phi>) \<psi>")
    case A: True
    let ?k0 = "Formula.fv_list \<phi>" and ?y = "fst (split_assignment (fv \<phi>) \<psi>)"
      and ?t = "snd (split_assignment (fv \<phi>) \<psi>)"
    show ?thesis
    proof (cases "ks = ?k0 @ [?y] \<and> ?y \<notin> set ?k0 \<and> Formula.fv_trm ?t \<subseteq> set (dcols ?k0) \<and>
        cs = merge_cols (dcols ?k0) [?y]")
      case True
      then show ?thesis
        using A 8(1)[OF A refl refl refl refl refl True] by (simp add: Let_def)
    next
      case False
      then show ?thesis
        using A by (auto simp: Let_def)
    qed
  next
    case nA: False
    show ?thesis
    proof (cases "safe_formula \<psi>")
      case S: True
      show ?thesis
      proof (cases "ks = cols_union (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) \<and> cs = merge_cols (fvc \<phi>) (fvc \<psi>)")
        case True
        then show ?thesis
          using nA S 8(2)[OF nA S refl refl refl refl True] 8(3)[OF nA S refl refl refl refl True]
          by (simp add: Let_def mbuf_t_empty.rep_eq)
      next
        case False
        then show ?thesis
          using nA S by (auto simp: Let_def)
      qed
    next
      case nS: False
      show ?thesis
      proof (cases "is_constraint \<psi>")
        case C: True
        let ?conf = "split_constraint \<psi>"
        show ?thesis
        proof (cases "Formula.fv_list \<phi> = ks \<and> Formula.fv_trm (fst ?conf) \<subseteq> set cs \<and>
            Formula.fv_trm (snd (snd (snd ?conf))) \<subseteq> set cs")
          case True
          then show ?thesis
            using nA nS C 8(4)[OF nA nS C refl True]
            by (auto simp: Let_def dest: Rep_uset_q split: option.splits)
        next
          case False
          then show ?thesis
            using nA nS C by (auto simp: Let_def)
        qed
      next
        case nC: False
        show ?thesis
        proof (cases "\<exists>\<psi>'. \<psi> = Formula.Neg \<psi>'")
          case True
          then obtain \<psi>' where N: "\<psi> = Formula.Neg \<psi>'"
            by blast
          show ?thesis
          proof (cases "ks = cols_union (Formula.fv_list \<phi>) (Formula.fv_list \<psi>') \<and>
              cs = merge_cols (fvc \<phi>) (fvc \<psi>') \<and> set (Formula.fv_list \<psi>') \<subseteq> set (Formula.fv_list \<phi>)")
            case True
            then show ?thesis
              using nA nS nC N 8(5)[OF nA nS nC N refl refl refl refl True]
                8(6)[OF nA nS nC N refl refl refl refl True]
              by (auto simp: Let_def mbuf_t_empty.rep_eq)
          next
            case False
            then show ?thesis
              using nA nS nC N by (auto simp: Let_def)
          qed
        next
          case nN: False
          show ?thesis
          proof (cases "\<exists>\<phi>' I \<psi>'. \<psi> = Formula.Trigger \<phi>' I \<psi>'")
            case True
            then obtain \<phi>' I \<psi>' where Trigger: "\<psi> = Formula.Trigger \<phi>' I \<psi>'"
              by blast
            note f = nA[unfolded Trigger] nS[unfolded Trigger] nC[unfolded Trigger]
            have IH7: "Rep_udformula (udinit n ks cs \<phi>) = dof n ks cs (minit0 n \<phi>)"
              by (rule 8(7)[OF nA nS nC Trigger])
            have IH8: "Rep_udformula (udinit n (Formula.fv_list \<psi>') (fvc \<psi>') \<psi>') =
                dof n (Formula.fv_list \<psi>') (fvc \<psi>') (minit0 n \<psi>')"
              by (rule 8(8)[OF nA nS nC Trigger refl])
            show ?thesis
              unfolding Trigger
            proof (cases "safe_formula \<phi>'")
              case True
              have IH9: "Rep_udformula (udinit n (Formula.fv_list \<phi>') (fvc \<phi>') \<phi>') =
                  dof n (Formula.fv_list \<phi>') (fvc \<phi>') (minit0 n \<phi>')"
                by (rule 8(9)[OF nA nS nC Trigger refl refl refl True])
              show "Rep_udformula (udinit n ks cs (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>'))) =
                dof n ks cs (minit0 n (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')))"
                using True
                by (simp only: udinit.simps default_maux.minit0.simps Let_def
                    verimon_maux.init_and_trigger_def f if_True if_False formula.case)
                  (rule uandtrigger_init_dof; use IH7 IH8 IH9 in \<open>simp add: init_args_def\<close>)
            next
              case False
              show "Rep_udformula (udinit n ks cs (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>'))) =
                dof n ks cs (minit0 n (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')))"
              proof (cases "\<exists>\<alpha>. \<phi>' = Formula.Neg \<alpha>")
                case True
                then obtain \<alpha> where Neg: "\<phi>' = Formula.Neg \<alpha>"
                  by blast
                have IH10: "Rep_udformula (udinit n (Formula.fv_list \<alpha>) (fvc \<alpha>) \<alpha>) =
                    dof n (Formula.fv_list \<alpha>) (fvc \<alpha>) (minit0 n \<alpha>)"
                  by (rule 8(10)[OF nA nS nC Trigger refl refl refl False Neg])
                note f' = f[unfolded Neg] False[unfolded Neg]
                show ?thesis
                  unfolding Neg
                  by (simp only: udinit.simps default_maux.minit0.simps Let_def
                      verimon_maux.init_and_trigger_def f' if_True if_False formula.case
                      Formula.fvi_list.simps)
                    (rule uandtrigger_init_dof; use IH7 IH8 IH10 in \<open>simp add: init_args_def\<close>)
              next
                case nN': False
                then have nn: "\<And>\<alpha>. \<phi>' \<noteq> Formula.Neg \<alpha>"
                  by auto
                show ?thesis
                  by (simp only: udinit.simps default_maux.minit0.simps Let_def
                      verimon_maux.init_and_trigger_def f False if_True if_False formula.case
                      case_formula_Neg_other[OF nn] dof.simps(1) Rep_udformula.simps)
              qed
            qed
          next
            case nT: False
            show ?thesis
            proof (cases "\<exists>\<phi>' I \<psi>'. \<psi> = Formula.Release \<phi>' I \<psi>'")
              case True
              then obtain \<phi>' I \<psi>' where R: "\<psi> = Formula.Release \<phi>' I \<psi>'"
                by blast
              note f = nA[unfolded R] nS[unfolded R] nC[unfolded R]
              show ?thesis
                unfolding R
                by (simp only: udinit.simps default_maux.minit0.simps f if_False formula.case)
                  (rule 8(11)[OF nA nS nC R])
            next
              case nR: False
              have nn: "\<And>a. \<psi> \<noteq> Formula.Neg a" "\<And>a I b. \<psi> \<noteq> Formula.Trigger a I b"
                "\<And>a I b. \<psi> \<noteq> Formula.Release a I b"
                using nN nT nR by auto
              show ?thesis
                by (simp only: udinit.simps default_maux.minit0.simps nA nS nC if_False
                    case_formula_NTR_other[OF nn] dof.simps(1) Rep_udformula.simps)
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (9 n ks cs l)
  obtain pos neg where p: "partition safe_formula l = (pos, neg)"
    by fastforce
  show ?case
  proof (cases pos)
    case Nil
    then show ?thesis
      using p by (simp add: Let_def)
  next
    case (Cons p0 ps)
    let ?K = "Formula.fv_list p0 # map Formula.fv_list ps @ map Formula.fv_list neg"
    let ?F = "pos @ map remove_neg neg"
    show ?thesis
    proof (cases "Formula.fv_list (Formula.Ands l) = ks \<and>
        cs = dands_cols (dcols (Formula.fv_list p0)) (map dcols (map Formula.fv_list ps)) \<and>
        (\<forall>c \<in> set (map dcols (map Formula.fv_list neg)).
          set c \<subseteq> set (dands_cols (dcols (Formula.fv_list p0)) (map dcols (map Formula.fv_list ps))))")
      case True
      have IH: "Rep_udformula (udinit n k (dcols k) \<psi>) = dof n k (dcols k) (minit0 n \<psi>)"
        if "(k, \<psi>) \<in> set (zip ?K ?F)" for k \<psi>
        by (rule 9[OF refl p[symmetric] Cons refl refl refl refl refl refl True that refl])
      have M: "map Rep_udformula (map2 (\<lambda>k \<phi>. udinit n k (dcols k) \<phi>) ?K ?F) =
          map (\<lambda>(k, \<phi>). dof n k (dcols k) \<phi>) (zip ?K (map (minit0 n) ?F))"
        unfolding zip_map2 map_map by (rule map_cong[OF refl]) (auto simp: IH)
      have len: "length l = length pos + length neg"
        using p sum_length_filter_compl[of safe_formula l] by (auto simp: comp_def)
      show ?thesis
        using True M p Cons len by (simp add: Let_def mbuf_t_empty.rep_eq comp_def)
    next
      case False
      then show ?thesis
        using p Cons by (auto simp: Let_def)
    qed
  qed
next
  case (11 n ks cs y \<omega> tys f \<phi>)
  let ?ag = "init_aggargs (Formula.fv_list \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f"
  show ?case
  proof (cases "(\<exists>a I b. \<phi> = Formula.Since a I b) \<or> (\<exists>a I b. \<phi> = Formula.Until a I b)")
    case True
    then show ?thesis
    proof (elim disjE exE)
      fix \<phi>' I \<psi>'
      assume S: "\<phi> = Formula.Since \<phi>' I \<psi>'"
      have IH\<psi>: "Rep_udformula (udinit (length tys + n) (Formula.fv_list \<psi>') (fvc \<psi>') \<psi>') =
          dof (length tys + n) (Formula.fv_list \<psi>') (fvc \<psi>') (minit0 (length tys + n) \<psi>')"
        by (rule 11(16)[OF refl refl S])
      show ?thesis
        unfolding S
      proof (cases "safe_formula \<phi>'")
        case True
        have IH\<phi>: "Rep_udformula (udinit (length tys + n) (Formula.fv_list \<phi>') (fvc \<phi>') \<phi>') =
            dof (length tys + n) (Formula.fv_list \<phi>') (fvc \<phi>') (minit0 (length tys + n) \<phi>')"
          by (rule 11(17)[OF refl refl S refl refl True])
        show "Rep_udformula (udinit n ks cs (Formula.Agg y \<omega> tys f (Formula.Since \<phi>' I \<psi>'))) =
          dof n ks cs (minit0 n (Formula.Agg y \<omega> tys f (Formula.Since \<phi>' I \<psi>')))"
          using True
          by (simp only: udinit.simps default_maux.minit0.simps Let_def default_mmasaux.init_since_def
              if_True formula.case)
            (rule usince_init_dof; use IH\<phi> IH\<psi> in \<open>simp add: init_args_def\<close>)
      next
        case False
        show "Rep_udformula (udinit n ks cs (Formula.Agg y \<omega> tys f (Formula.Since \<phi>' I \<psi>'))) =
          dof n ks cs (minit0 n (Formula.Agg y \<omega> tys f (Formula.Since \<phi>' I \<psi>')))"
        proof (cases "\<exists>\<alpha>. \<phi>' = Formula.Neg \<alpha>")
          case True
          then obtain \<alpha> where Neg: "\<phi>' = Formula.Neg \<alpha>"
            by blast
          have IH\<alpha>: "Rep_udformula (udinit (length tys + n) (Formula.fv_list \<alpha>) (fvc \<alpha>) \<alpha>) =
              dof (length tys + n) (Formula.fv_list \<alpha>) (fvc \<alpha>) (minit0 (length tys + n) \<alpha>)"
            by (rule 11(18)[OF refl refl S refl refl False Neg])
          show ?thesis
            unfolding Neg using False[unfolded Neg]
            by (simp only: udinit.simps default_maux.minit0.simps Let_def default_mmasaux.init_since_def
                if_False formula.case Formula.fvi_list.simps)
              (rule usince_init_dof; use IH\<alpha> IH\<psi> in \<open>simp add: init_args_def\<close>)
        next
          case False': False
          then have nn: "\<And>\<alpha>. \<phi>' \<noteq> Formula.Neg \<alpha>"
            by auto
          show ?thesis
            using False
            by (simp only: udinit.simps default_maux.minit0.simps Let_def default_mmasaux.init_since_def
                if_False formula.case case_formula_Neg_other[OF nn] dof.simps(1) Rep_udformula.simps)
        qed
      qed
    next
      fix \<phi>' I \<psi>'
      assume U: "\<phi> = Formula.Until \<phi>' I \<psi>'"
      have IH\<psi>: "Rep_udformula (udinit (length tys + n) (Formula.fv_list \<psi>') (fvc \<psi>') \<psi>') =
          dof (length tys + n) (Formula.fv_list \<psi>') (fvc \<psi>') (minit0 (length tys + n) \<psi>')"
        by (rule 11(19)[OF refl refl U])
      show ?thesis
        unfolding U
      proof (cases "safe_formula \<phi>'")
        case True
        have IH\<phi>: "Rep_udformula (udinit (length tys + n) (Formula.fv_list \<phi>') (fvc \<phi>') \<phi>') =
            dof (length tys + n) (Formula.fv_list \<phi>') (fvc \<phi>') (minit0 (length tys + n) \<phi>')"
          by (rule 11(20)[OF refl refl U refl refl True])
        show "Rep_udformula (udinit n ks cs (Formula.Agg y \<omega> tys f (Formula.Until \<phi>' I \<psi>'))) =
          dof n ks cs (minit0 n (Formula.Agg y \<omega> tys f (Formula.Until \<phi>' I \<psi>')))"
          using True
          by (simp only: udinit.simps default_maux.minit0.simps Let_def dq_muaux.init_until_def
              if_True formula.case)
            (rule uuntil_init_dof; use IH\<phi> IH\<psi> in \<open>simp add: init_args_def\<close>)
      next
        case False
        show "Rep_udformula (udinit n ks cs (Formula.Agg y \<omega> tys f (Formula.Until \<phi>' I \<psi>'))) =
          dof n ks cs (minit0 n (Formula.Agg y \<omega> tys f (Formula.Until \<phi>' I \<psi>')))"
        proof (cases "\<exists>\<alpha>. \<phi>' = Formula.Neg \<alpha>")
          case True
          then obtain \<alpha> where Neg: "\<phi>' = Formula.Neg \<alpha>"
            by blast
          have IH\<alpha>: "Rep_udformula (udinit (length tys + n) (Formula.fv_list \<alpha>) (fvc \<alpha>) \<alpha>) =
              dof (length tys + n) (Formula.fv_list \<alpha>) (fvc \<alpha>) (minit0 (length tys + n) \<alpha>)"
            by (rule 11(21)[OF refl refl U refl refl False Neg])
          show ?thesis
            unfolding Neg using False[unfolded Neg]
            by (simp only: udinit.simps default_maux.minit0.simps Let_def dq_muaux.init_until_def
                if_False formula.case Formula.fvi_list.simps)
              (rule uuntil_init_dof; use IH\<alpha> IH\<psi> in \<open>simp add: init_args_def\<close>)
        next
          case False': False
          then have nn: "\<And>\<alpha>. \<phi>' \<noteq> Formula.Neg \<alpha>"
            by auto
          show ?thesis
            using False
            by (simp only: udinit.simps default_maux.minit0.simps Let_def dq_muaux.init_until_def
                if_False formula.case case_formula_Neg_other[OF nn] dof.simps(1) Rep_udformula.simps)
        qed
      qed
    qed
  next
    case False
    then have nS: "\<And>a I b. \<phi> \<noteq> Formula.Since a I b" and nU: "\<And>a I b. \<phi> \<noteq> Formula.Until a I b"
      by auto
    have IH: "Rep_udformula (udinit (length tys + n) (Formula.fv_list \<phi>) c \<phi>) =
        dof (length tys + n) (Formula.fv_list \<phi>) c (minit0 (length tys + n) \<phi>)" for c
      using nS nU
      by (cases \<phi>) ((rule 11(1-15,22-27)[OF refl refl], assumption) | blast)+
    have u: "udinit n ks cs (Formula.Agg y \<omega> tys f \<phi>) =
        uagg_init n ks cs ?ag (\<lambda>c. udinit (length tys + n) (Formula.fv_list \<phi>) c \<phi>)"
      by (subst udinit.simps) (simp only: Let_def case_formula_Since_Until_other[OF nS nU])
    have m: "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = MAgg ?ag (minit0 (length tys + n) \<phi>)"
      by (subst default_maux.minit0.simps) (simp only: Let_def case_formula_Since_Until_other[OF nS nU])
    show ?thesis
      unfolding u m
      by (rule uagg_init_dof) (simp add: init_aggargs_def IH)
  qed
next
  case (14 n ks cs \<phi> I \<psi>)
  show ?case
  proof (cases "safe_formula \<phi>")
    case True
    then show ?thesis
      by (simp only: udinit.simps default_maux.minit0.simps Let_def default_mmasaux.init_since_def if_True)
        (rule usince_init_dof; use 14 True in \<open>simp add: init_args_def\<close>)
  next
    case False
    then show ?thesis
    proof (cases \<phi>)
      case (Neg \<alpha>)
      then show ?thesis
        using False
        by (simp only: udinit.simps default_maux.minit0.simps Let_def default_mmasaux.init_since_def if_False
            formula.case Formula.fvi_list.simps)
          (rule usince_init_dof; use 14 False Neg in \<open>simp add: init_args_def\<close>)
    qed (subst udinit.simps, subst default_maux.minit0.simps,
        simp only: Let_def default_mmasaux.init_since_def False if_False formula.case dof.simps(1)
          Rep_udformula.simps)+
  qed
next
  case (15 n ks cs \<phi> I \<psi>)
  show ?case
  proof (cases "safe_formula \<phi>")
    case True
    then show ?thesis
      by (simp only: udinit.simps default_maux.minit0.simps Let_def dq_muaux.init_until_def if_True)
        (rule uuntil_init_dof; use 15 True in \<open>simp add: init_args_def\<close>)
  next
    case False
    then show ?thesis
    proof (cases \<phi>)
      case (Neg \<alpha>)
      then show ?thesis
        using False
        by (simp only: udinit.simps default_maux.minit0.simps Let_def dq_muaux.init_until_def if_False
            formula.case Formula.fvi_list.simps)
          (rule uuntil_init_dof; use 15 False Neg in \<open>simp add: init_args_def\<close>)
    qed (subst udinit.simps, subst default_maux.minit0.simps,
        simp only: Let_def dq_muaux.init_until_def False if_False formula.case dof.simps(1)
          Rep_udformula.simps)+
  qed
next
  case (16 n ks cs \<phi> I \<psi>)
  show ?case
  proof (cases "safe_formula \<phi>")
    case True
    then show ?thesis
      by (simp only: udinit.simps default_maux.minit0.simps Let_def verimon_maux.init_trigger_def if_True)
        (rule utrigger_init_dof; use 16 True in \<open>simp add: init_args_def\<close>)
  next
    case False
    then show ?thesis
    proof (cases \<phi>)
      case (Neg \<alpha>)
      then show ?thesis
        using False
        by (simp only: udinit.simps default_maux.minit0.simps Let_def verimon_maux.init_trigger_def
            if_False formula.case Formula.fvi_list.simps)
          (rule utrigger_init_dof; use 16 False Neg in \<open>simp add: init_args_def\<close>)
    qed (subst udinit.simps, subst default_maux.minit0.simps,
        simp only: Let_def verimon_maux.init_trigger_def False if_False formula.case dof.simps(1)
          Rep_udformula.simps)+
  qed
next
  case (18 n ks cs I r)
  obtain mr \<phi>s where r: "to_mregex r = (mr, \<phi>s)"
    by fastforce
  show ?case
  proof (cases "Formula.fv_list (Formula.MatchP I r) = ks \<and>
      (\<forall>c \<in> set (map dcols (map Formula.fv_list \<phi>s)). set c \<subseteq> set cs)")
    case True
    have IH: "Rep_udformula (udinit n k (dcols k) \<psi>) = dof n k (dcols k) (minit0 n \<psi>)"
      if "(k, \<psi>) \<in> set (zip (map Formula.fv_list \<phi>s) \<phi>s)" for k \<psi>
      by (rule 18[OF refl r[symmetric] refl refl True that refl])
    have M: "map Rep_udformula (map2 (\<lambda>k \<phi>. udinit n k (dcols k) \<phi>) (map Formula.fv_list \<phi>s) \<phi>s) =
        map (\<lambda>(k, \<phi>). dof n k (dcols k) \<phi>) (zip (map Formula.fv_list \<phi>s) (map (minit0 n) \<phi>s))"
      unfolding zip_map2 map_map by (rule map_cong[OF refl]) (auto simp: IH)
    show ?thesis
      using True M by (simp add: r Let_def mbuf_t_empty.rep_eq comp_def)
  next
    case False
    then show ?thesis
      by (auto simp: r Let_def)
  qed
next
  case (19 n ks cs I r)
  obtain mr \<phi>s where r: "to_mregex r = (mr, \<phi>s)"
    by fastforce
  show ?case
  proof (cases "Formula.fv_list (Formula.MatchF I r) = ks \<and>
      (\<forall>c \<in> set (map dcols (map Formula.fv_list \<phi>s)). set c \<subseteq> set cs)")
    case True
    have IH: "Rep_udformula (udinit n k (dcols k) \<psi>) = dof n k (dcols k) (minit0 n \<psi>)"
      if "(k, \<psi>) \<in> set (zip (map Formula.fv_list \<phi>s) \<phi>s)" for k \<psi>
      by (rule 19[OF refl r[symmetric] refl refl True that refl])
    have M: "map Rep_udformula (map2 (\<lambda>k \<phi>. udinit n k (dcols k) \<phi>) (map Formula.fv_list \<phi>s) \<phi>s) =
        map (\<lambda>(k, \<phi>). dof n k (dcols k) \<phi>) (zip (map Formula.fv_list \<phi>s) (map (minit0 n) \<phi>s))"
      unfolding zip_map2 map_map by (rule map_cong[OF refl]) (auto simp: IH)
    show ?thesis
      using True M by (simp add: r Let_def mbuf_t_empty.rep_eq comp_def)
  next
    case False
    then show ?thesis
      by (auto simp: r Let_def)
  qed
qed (simp_all add: Let_def mbuf_t_empty.rep_eq)

subsection \<open>The state and the step\<close>

record udmstate =
  udmstate_i :: nat
  udmstate_j :: nat
  udmstate_m :: udformula
  udmstate_n :: nat
  udmstate_cs :: cols
  udmstate_t :: "ts mbuf_t"

definition Rep_udmstate :: "udmstate \<Rightarrow> dmstate" where
  "Rep_udmstate st =
     \<lparr> dmstate_i = udmstate_i st, dmstate_j = udmstate_j st,
       dmstate_m = Rep_udformula (udmstate_m st),
       dmstate_n = udmstate_n st, dmstate_cs = udmstate_cs st, dmstate_t = udmstate_t st \<rparr>"

definition udminit_safe :: "ty Formula.formula \<Rightarrow> udmstate" where
  "udminit_safe \<phi> = (if mmonitorable_exec \<phi>
     then (let n = Formula.nfv \<phi>; ks = Formula.fv_list \<phi>; cs = dcols ks in
       \<lparr>udmstate_i = 0, udmstate_j = 0, udmstate_m = udinit n ks cs \<phi>, udmstate_n = n,
        udmstate_cs = cs, udmstate_t = mbuf_t_empty\<rparr>)
     else undefined)"

lemma mbuf_t_empty_append_Nil[simp]: "mbuf_t_empty @@ [] = mbuf_t_empty"
  by transfer simp

lemma Rep_udminit_safe:
  assumes "mmonitorable \<phi>"
  shows "Rep_udmstate (udminit_safe \<phi>) = dof_state (Formula.nfv \<phi>) (Formula.fv_list \<phi>)
    (dcols (Formula.fv_list \<phi>)) (minit_safe \<phi>)"
  using assms
  by (simp add: udminit_safe_def Rep_udmstate_def dof_state_def default_maux.minit_safe_def
      default_maux.minit_def udinit_dof monitorable_formula_code Let_def)

lemma vdfail_nodes_Rep_udmstate:
  "vdfail_nodes (dmstate_m (Rep_udmstate st)) = uvdfail_nodes (udmstate_m st)"
  by (simp add: Rep_udmstate_def vdfail_nodes_Rep)

definition udmstep :: "database \<times> ts \<Rightarrow> udmstate \<Rightarrow> (nat \<times> ts \<times> utable) list \<times> udmstate" where
  "udmstep tdb st =
    (case udeval (udmstate_j st + 1) [snd tdb] (fst tdb) (udmstate_m st) of
      (xs, m) \<Rightarrow>
      (case dannotate (udmstate_i st) (udmstate_t st @@ [snd tdb]) xs [] of
        (i', tq, vs) \<Rightarrow> (vs,
        \<lparr> udmstate_i = i',
          udmstate_j = udmstate_j st + 1,
          udmstate_m = m,
          udmstate_n = udmstate_n st,
          udmstate_cs = udmstate_cs st,
          udmstate_t = tq \<rparr>)))"

theorem udmstep_Rep:
  "dmstep (db, t) (Rep_udmstate st)
   = (case udmstep (db, t) st of (vs, st') \<Rightarrow> (vs, Rep_udmstate st'))"
proof -
  obtain xs m where e: "udeval (Suc (udmstate_j st)) [t] db (udmstate_m st) = (xs, m)"
    by (cases "udeval (Suc (udmstate_j st)) [t] db (udmstate_m st)")
  obtain i' tq vs where d: "dannotate (udmstate_i st) (udmstate_t st @@ [t]) xs [] = (i', tq, vs)"
    by (metis prod_cases3)
  show ?thesis
    unfolding dmstep_def udmstep_def Rep_udmstate_def
    by (simp add: udeval_Rep e d)
qed

end

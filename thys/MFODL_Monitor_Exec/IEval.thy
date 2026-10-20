(*<*)
theory IEval
  imports Eval IWindow
begin
(*>*)

section \<open>The executable evaluator over indexed tables\<close>

text \<open>
  The evaluator below is @{const eeval} with the tables of the unions' and joins' buffers
  indexed (@{typ "event_data itab"}): a join probes the index an operand carries at the plan's
  mask instead of building one (@{const ijoin}), and a union keeps its left operand's indices.
  The other nodes see plain tables, and the freeze and the recursive let run @{const eeval} on
  their subtree.  Forgetting the indices (@{text eabs}) maps a run of this evaluator to a run of
  @{const eeval} (@{text ieval_eeval}), so the simulation of the kernel and its correctness carry
  over unchanged.
\<close>

type_synonym itable = "event_data itab"
type_synonym iebuf2 = "itable mbuf_t \<times> itable mbuf_t"
type_synonym ieformula =
  "(iebuf2, uebufn, event_data table mbuf_t \<times> event_data table option mbuf_t, iudsaux_x) geformula"

lift_definition mbuf_t_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mbuf_t \<Rightarrow> 'b mbuf_t" is map .

lemma Rep_mbuf_t_map[simp]: "Rep_mbuf_t (mbuf_t_map f b) = map f (Rep_mbuf_t b)"
  by transfer simp

lemma mbuf_t_map_comp[simp]: "mbuf_t_map f (mbuf_t_map g b) = mbuf_t_map (f \<circ> g) b"
  by transfer simp

lemma mbuf_t_map_id[simp]: "mbuf_t_map (\<lambda>x. x) b = b" "mbuf_t_map id b = b"
  by (transfer, simp)+

definition ib2 :: "iebuf2 \<Rightarrow> uebuf2" where
  "ib2 = map_prod (mbuf_t_map iset) (mbuf_t_map iset)"

definition eb2 :: "uebuf2 \<Rightarrow> iebuf2" where
  "eb2 = map_prod (mbuf_t_map itab) (mbuf_t_map itab)"

lemma ib2_eb2[simp]: "ib2 (eb2 b) = b"
  by (cases b) (simp add: ib2_def eb2_def comp_def)

definition eabs :: "ieformula \<Rightarrow> eformula" where
  "eabs = map_geformula ib2 id id riu"

definition eemb :: "eformula \<Rightarrow> ieformula" where
  "eemb = map_geformula eb2 id id iudsx_emb"

lemma eabs_eemb[simp]: "eabs (eemb \<phi>) = \<phi>"
  by (simp add: eabs_def eemb_def geformula.map_comp comp_def geformula.map_ident)

subsection \<open>The evaluator\<close>

text \<open>
  The evaluator takes, besides the formula, the masks at which its caller would like the result
  indexed.  A join asks each operand for the index its plan probes, and the Since window of a
  closed left operand keeps the indices it is asked for from then on.  Every other node ignores
  the request.
\<close>

fun jreq_l :: "ejoin_plan \<Rightarrow> bool \<Rightarrow> bool list list" where
  "jreq_l (EJGen p lk rk) True = [lk]"
| "jreq_l (EJSub msk) True = [msk]"
| "jreq_l _ _ = []"

fun jreq_r :: "ejoin_plan \<Rightarrow> bool \<Rightarrow> bool list list" where
  "jreq_r (EJGen p lk rk) True = [rk]"
| "jreq_r (EJSup msk) True = [msk]"
| "jreq_r _ _ = []"

text \<open>
  The database the evaluator reads holds indexed tables, so a predicate hands on the indices of
  the table it reads.  A predicate bound by a let reads the table of the let's definition: the
  let asks its definition for the indices that its body's joins ask of the predicate.  Which
  ones these are depends only on the formula.
\<close>

type_synonym idatabase = "(Formula.name \<times> nat, itable list) mapping"

definition dabs :: "idatabase \<Rightarrow> database" where
  "dabs db = Mapping.map_values (\<lambda>_. map iset) db"

definition demb :: "database \<Rightarrow> idatabase" where
  "demb db = Mapping.map_values (\<lambda>_. map itab) db"

lemma lookup_dabs: "Mapping.lookup (dabs db) k = map_option (map iset) (Mapping.lookup db k)"
  by (simp add: dabs_def Mapping.lookup_map_values)

lemma dabs_update[simp]: "dabs (Mapping.update k xs db) = Mapping.update k (map iset xs) (dabs db)"
  by (rule mapping_eqI) (simp add: lookup_dabs Mapping.lookup_update')

lemma dabs_demb[simp]: "dabs (demb db) = db"
  by (rule mapping_eqI) (simp add: lookup_dabs demb_def Mapping.lookup_map_values option.map_comp
      comp_def option.map_ident)

fun is_pred :: "Formula.name \<times> nat \<Rightarrow> ('b2, 'bn, 'ba, 'bs) geformula \<Rightarrow> bool" where
  "is_pred pm (EPredS e ar) = ((e, ar) = pm)"
| "is_pred pm _ = False"

function (sequential) preq :: "Formula.name \<times> nat \<Rightarrow> ('b2, 'bn, 'ba, 'bs) geformula \<Rightarrow> bool list list" where
  "preq pm (EAnd pl \<phi> pos \<psi> buf) =
     (if is_pred pm \<phi> then jreq_l pl pos else preq pm \<phi>) @
     (if is_pred pm \<psi> then jreq_r pl pos else preq pm \<psi>)"
| "preq pm (EAndRel \<phi> conf) = preq pm \<phi>"
| "preq pm (ENeg \<phi>) = preq pm \<phi>"
| "preq pm (EExists \<phi> drop0) = preq pm \<phi>"
| "preq pm (EAgg g0 \<omega> f k pos \<phi>) = preq pm \<phi>"
| "preq pm (EAndAssign p t \<phi>) = preq pm \<phi>"
| "preq pm (EPrev I \<phi> first buf nts) = preq pm \<phi>"
| "preq pm (ENext I \<phi> first nts) = preq pm \<phi>"
| "preq pm (EOr \<phi> \<psi> buf) = preq pm \<phi> @ preq pm \<psi>"
| "preq pm (ESince dags \<phi> \<psi> buf aux) = preq pm \<phi> @ preq pm \<psi>"
| "preq pm (EUntil dags msk \<phi> \<psi> buf nts t aux) = preq pm \<phi> @ preq pm \<psi>"
| "preq pm (ELet p m \<phi> \<psi>) = preq pm \<phi> @ (if (p, m) = pm then [] else preq pm \<psi>)"
| "preq pm _ = []"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(_, \<phi>). size \<phi>)") auto

function (sequential) ieval :: "bool list list \<Rightarrow> nat \<Rightarrow> ts list \<Rightarrow> idatabase \<Rightarrow> ieformula \<Rightarrow> itable list \<times> ieformula" where
  "ieval rq j ts db EFail = ([], EFail)"
| "ieval rq j ts db (ERel rel) = (replicate (length ts) (itab rel), ERel rel)"
| "ieval rq j ts db (EPredS e ar) =
     (case Mapping.lookup db (e, ar) of
         None \<Rightarrow> replicate (length ts) (itab {})
       | Some xs \<Rightarrow> xs, EPredS e ar)"
| "ieval rq j ts db (EPredM e ar tms cs) =
     (map itab (case Mapping.lookup db (e, ar) of
         None \<Rightarrow> replicate (length ts) {}
       | Some xs \<Rightarrow> map (umatch_table tms cs \<circ> iset) xs), EPredM e ar tms cs)"
| "ieval rq j ts db (EAndRel \<phi> conf) =
     (let (xs, \<phi>') = ieval [] j ts db \<phi>
      in (map (\<lambda>x. itab (Set.filter (ueval_constraint conf) (iset x))) xs, EAndRel \<phi>' conf))"
| "ieval rq j ts db (ENeg \<phi>) =
     (let (xs, \<phi>') = ieval [] j ts db \<phi>
      in (map (\<lambda>r. itab (if iset r = {} then {[]} else {})) xs, ENeg \<phi>'))"
| "ieval rq j ts db (EExists \<phi> drop0) =
     (let (xs, \<phi>') = ieval [] j ts db \<phi>
      in (map (\<lambda>r. itab (if drop0 then tl ` iset r else iset r)) xs, EExists \<phi>' drop0))"
| "ieval rq j ts db (EAgg g0 \<omega> f k pos \<phi>) =
     (let (xs, \<phi>') = ieval [] j ts db \<phi>
      in (map (\<lambda>r. itab (uagg g0 \<omega> f k pos (iset r))) xs, EAgg g0 \<omega> f k pos \<phi>'))"
| "ieval rq j ts db (EOr \<phi> \<psi> buf) =
     (let (xs, \<phi>') = ieval [] j ts db \<phi>; (ys, \<psi>') = ieval [] j ts db \<psi>;
          (zs, buf') = mebuf2_take iunion (mebuf2_add xs ys buf)
      in (zs, EOr \<phi>' \<psi>' buf'))"
| "ieval rq j ts db (EAnd pl \<phi> pos \<psi> buf) =
     (let (xs, \<phi>') = ieval (jreq_l pl pos) j ts db \<phi>; (ys, \<psi>') = ieval (jreq_r pl pos) j ts db \<psi>;
          (zs, buf') = mebuf2_take (\<lambda>r1 r2. itab (ijoin pl r1 pos r2)) (mebuf2_add xs ys buf)
      in (zs, EAnd pl \<phi>' pos \<psi>' buf'))"
| "ieval rq j ts db (EPrev I \<phi> first buf nts) =
     (let (xs, \<phi>') = ieval [] j ts db \<phi>; xs = map iset xs
      in if first \<and> ts = [] then ([], EPrev I \<phi>' True (buf @@ xs) (nts @@ ts))
      else let (zs, buf', nts') = meprev_next I (buf @@ xs) (nts @@ ts)
        in (map itab (if first then {} # zs else zs), EPrev I \<phi>' False buf' nts'))"
| "ieval rq j ts db (ENext I \<phi> first nts) =
     (let (xs, \<phi>') = ieval [] j ts db \<phi>; xs = map iset xs;
          (xs, first') = (case (xs, first) of (_ # xs', True) \<Rightarrow> (xs', False) | a \<Rightarrow> a);
          (zs, _, nts') = meprev_next I (mbuf_t_empty @@ xs) (nts @@ ts)
      in (map itab zs, ENext I \<phi>' first' nts'))"
| "ieval rq j ts db (EAnds ps ns Ld dbuf) =
     (let R = map (ieval [] j ts db) Ld;
          (zs, dbuf') = mebufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty
            (mebufn_add (map (map iset \<circ> fst) R) dbuf)
      in (map itab (Rep_mbuf_t zs), EAnds ps ns (map snd R) dbuf'))"
| "ieval rq j ts db (ESince dags \<phi> \<psi> buf aux) =
     (let (xs, \<phi>') = ieval [] j ts db \<phi>; (ys, \<psi>') = ieval [] j ts db \<psi>;
          (zs, buf', aux') = iuedsx_eval_since dags [] (mebuf2S_add (map iset xs) (map iset ys) ts buf)
            (iudsx_ensure rq aux)
      in (zs, ESince dags \<phi>' \<psi>' buf' aux'))"
| "ieval rq j ts db (EUntil dags msk \<phi> \<psi> buf nts t aux) =
     (let (xs, \<phi>') = ieval [] j ts db \<phi>; (ys, \<psi>') = ieval [] j ts db \<psi>;
          (aux', buf', nt, nts') = mebuf2t_take (udux_add_new dags msk) aux
            (mebuf2_add (map iset xs) (map iset ys) buf) t (nts @@ ts);
          (zs, aux'') = udux_eval dags nt aux'
      in (map itab zs, EUntil dags msk \<phi>' \<psi>' buf' nts' nt aux''))"
| "ieval rq j ts db (EAndAssign p t \<phi>) =
     (let (xs, \<phi>') = ieval [] j ts db \<phi> in (map (\<lambda>r. itab (uassign p t (iset r))) xs, EAndAssign p t \<phi>'))"
| "ieval rq j ts db (ETP mt i) =
     (map (\<lambda>x. itab (umtrm mt (EInt (integer_of_nat x)))) [i..<j], ETP mt j)"
| "ieval rq j ts db (ETS mt) = (map (\<lambda>x. itab (umtrm mt (EInt (integer_of_nat x)))) ts, ETS mt)"
| "ieval rq j ts db (ELet p m \<phi> \<psi>) =
     (let (xs, \<phi>') = ieval (preq (p, m) \<psi>) j ts db \<phi>;
          (ys, \<psi>') = ieval [] j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, ELet p m \<phi>' \<psi>'))"
| "ieval rq j ts db (EFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E) =
     map_prod (map itab) eemb
       (eeval j ts (dabs db) (eabs (EFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E)))"
| "ieval rq j ts db (ELetPast p m \<phi> \<psi> i buf) =
     map_prod (map itab) eemb (eeval j ts (dabs db) (eabs (ELetPast p m \<phi> \<psi> i buf)))"
| "ieval rq j ts db (ETrigger dags pl \<phi> \<psi> dbuf nts daux) =
     (let (xs, \<phi>') = ieval [] j ts db \<phi>; (ys, \<psi>') = ieval [] j ts db \<psi>;
          ((zs, daux'), dbuf', nts') = mebuf2T_take (\<lambda>r1 r2 t (zs, ax).
            let ax = tw_update dags t r1 r2 ax
            in (zs @ [tw_result ax], ax)) ([], daux)
            (mebuf2_add (map iset xs) (map iset ys) dbuf) (nts @@ ts)
      in (map itab zs, ETrigger dags pl \<phi>' \<psi>' dbuf' nts' daux'))"
| "ieval rq j ts db (EAndTrigger pl \<alpha> dbuf1 dags \<phi> \<psi> xbuf2 nts daux) =
     (let (as, \<alpha>') = ieval [] j ts db \<alpha>; (xs, \<phi>') = ieval [] j ts db \<phi>;
          (ys, \<psi>') = ieval [] j ts db \<psi>;
          ((ws, daux'), dbuf2', nts') = mebuf2T_take (\<lambda>r1 r2 t (ws, ax).
            let ax = tw_update dags t r1 r2 ax
            in (ws @ [if tw_empty ax then None
                      else Some (tw_result ax)], ax)) ([], daux)
            (mebuf2_add (map iset xs) (map iset ys) xbuf2) (nts @@ ts);
          (zs, dbuf1') = mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
            | Some z \<Rightarrow> gbin_join pl r1 True z) (mebuf2_add (map iset as) ws dbuf1)
      in (map itab zs, EAndTrigger pl \<alpha>' dbuf1' dags \<phi>' \<psi>' dbuf2' nts' daux'))"
| "ieval rq j ts db (EMatchP m I mr mrs pls Ld dbuf nts daux) =
     (let R = map (ieval [] j ts db) Ld;
          ((zs, daux'), dbuf', _, nts') = mebufnt_take (\<lambda>rels t (zs, ax).
             let (z, ax) = gupdate_matchP (map emb_msk pls) I mr mrs rels t ax
             in (zs @@ [z], ax)) (mbuf_t_empty, daux)
             (mebufn_add (map (map iset \<circ> fst) R) dbuf) 0 (nts @@ ts)
      in (map itab (Rep_mbuf_t zs), EMatchP m I mr mrs pls (map snd R) dbuf' nts' daux'))"
| "ieval rq j ts db (EMatchF m I mr mrs pls Ld dbuf nts t daux) =
     (let R = map (ieval [] j ts db) Ld;
          (daux', dbuf', nt, nts') = mebufnt_take
             (\<lambda>rels. gupdate_matchF (map emb_msk pls) I mr mrs rels)
             daux (mebufn_add (map (map iset \<circ> fst) R) dbuf) t (nts @@ ts);
          (zs, daux'') = geval_matchF I mr nt daux'
      in (map itab zs, EMatchF m I mr mrs pls (map snd R) dbuf' nts' nt daux''))"
| "ieval rq j ts db (ERelease dags msk \<phi> \<psi> buf nts t aux) =
     (let (xs, \<phi>') = ieval [] j ts db \<phi>; (ys, \<psi>') = ieval [] j ts db \<psi>;
          (aux', buf', nt, nts') = mebuf2t_take (eraux_update dags msk) aux
            (mebuf2_add (map iset xs) (map iset ys) buf) t (nts @@ ts);
          (zs, aux'') = eraux_eval (args_ivl dags) nt aux'
      in (map itab zs, ERelease dags msk \<phi>' \<psi>' buf' nts' nt aux''))"
  by pat_completeness (simp_all only: prod.inject geformula.inject geformula.distinct simp_thms)
termination
  by (relation "measure (\<lambda>(_, _, _, _, \<phi>). size \<phi>)") (auto simp: less_Suc_eq_le intro: size_list_estimation')

subsection \<open>Forgetting the indices\<close>

lemma mbuf_t_map_code[code]: "mbuf_t_map f (MBuf2_t q) = mbuf_t_empty @@ map f (linearize q)"
  by transfer simp

lemma mbuf_t_map_append[simp]: "mbuf_t_map f (b @@ xs) = mbuf_t_map f b @@ map f xs"
  by transfer simp

lemma mbuf_t_map_Cons[simp]: "mbuf_t_map f (mbuf_t_Cons x b) = mbuf_t_Cons (f x) (mbuf_t_map f b)"
  by transfer simp

lemma mbuf_t_map_empty[simp]: "mbuf_t_map f mbuf_t_empty = mbuf_t_empty"
  by transfer simp

lemma mbuf_t_cases_map: "mbuf_t_cases (mbuf_t_map f b) = map_prod (map_option f) (mbuf_t_map f) (mbuf_t_cases b)"
  by transfer (auto split: list.splits)

lemma ib2_add[simp]: "ib2 (mebuf2_add xs ys b) = mebuf2_add (map iset xs) (map iset ys) (ib2 b)"
  by (cases b) (simp add: ib2_def)

lemma mebuf2_take_ib2:
  "mebuf2_take g b = (zs, b') \<Longrightarrow> (\<forall>x y. iset (g x y) = f (iset x) (iset y)) \<Longrightarrow>
   mebuf2_take f (ib2 b) = (map iset zs, ib2 b')"
proof (induction g b arbitrary: zs b' rule: mebuf2_take.induct)
  case (1 g xs ys)
  show ?case
  proof (cases "mbuf_t_cases xs")
    case (Pair xo xs')
    show ?thesis
    proof (cases xo)
      case None
      then show ?thesis using 1(2) Pair by (auto simp: ib2_def mbuf_t_cases_map)
    next
      case (Some x)
      show ?thesis
      proof (cases "mbuf_t_cases ys")
        case (Pair yo ys')
        then show ?thesis
          using 1 \<open>mbuf_t_cases xs = (xo, xs')\<close> Some
          by (cases yo) (auto simp: ib2_def mbuf_t_cases_map split: prod.splits)
      qed
    qed
  qed
qed

lemma eabs_simps[simp]:
  "eabs EFail = EFail"
  "eabs (ERel rel) = ERel rel"
  "eabs (EPredS e1 a1) = EPredS e1 a1"
  "eabs (EPredM e2 a2 tms cs) = EPredM e2 a2 tms cs"
  "eabs (EAndRel \<phi> conf) = EAndRel (eabs \<phi>) conf"
  "eabs (ENeg \<phi>) = ENeg (eabs \<phi>)"
  "eabs (EExists \<phi> b) = EExists (eabs \<phi>) b"
  "eabs (EAgg g0 \<omega> f k n \<phi>) = EAgg g0 \<omega> f k n (eabs \<phi>)"
  "eabs (EOr \<phi> \<psi> buf) = EOr (eabs \<phi>) (eabs \<psi>) (ib2 buf)"
  "eabs (EAnd pl \<phi> pos \<psi> buf) = EAnd pl (eabs \<phi>) pos (eabs \<psi>) (ib2 buf)"
  "eabs (EPrev I1 \<phi> fst1 pbuf nts1) = EPrev I1 (eabs \<phi>) fst1 pbuf nts1"
  "eabs (ENext I2 \<phi> fst2 nts2) = ENext I2 (eabs \<phi>) fst2 nts2"
  "eabs (EAnds ps ns Ld dbuf) = EAnds ps ns (map eabs Ld) dbuf"
  "eabs (ESince dags1 \<phi> \<psi> sbuf aux1) = ESince dags1 (eabs \<phi>) (eabs \<psi>) sbuf (riu aux1)"
  "eabs (EUntil dags2 msk2 \<phi> \<psi> ubuf nts3 t3 aux3) =
     EUntil dags2 msk2 (eabs \<phi>) (eabs \<psi>) ubuf nts3 t3 aux3"
  "eabs (EAndAssign p4 trm \<phi>) = EAndAssign p4 trm (eabs \<phi>)"
  "eabs (ETP mt5 i5) = ETP mt5 i5"
  "eabs (ETS mt6) = ETS mt6"
  "eabs (ELet p7 m7 \<phi> \<psi>) = ELet p7 m7 (eabs \<phi>) (eabs \<psi>)"
  "eabs (EFrz p13 m13 \<phi> \<psi> a13 b13 c13 d13 \<chi>1 e13 f13 g13 h13 i13 j13 k13 l13 \<chi>2 n13 o13 \<chi>3 \<chi>4) =
     EFrz p13 m13 (eabs \<phi>) (eabs \<psi>) a13 b13 c13 d13 (eabs \<chi>1) e13 f13 g13 h13 i13 j13 k13 l13
       (eabs \<chi>2) n13 o13 (eabs \<chi>3) (eabs \<chi>4)"
  "eabs (ELetPast p14 m14 \<phi> \<psi> i14 buf14) = ELetPast p14 m14 (eabs \<phi>) (eabs \<psi>) i14 buf14"
  "eabs (ETrigger dags8 pls8 \<phi> \<psi> tbuf8 nts8 aux8) =
     ETrigger dags8 pls8 (eabs \<phi>) (eabs \<psi>) tbuf8 nts8 aux8"
  "eabs (ERelease dags9 msk9 \<phi> \<psi> rbuf nts9 t9 aux9) =
     ERelease dags9 msk9 (eabs \<phi>) (eabs \<psi>) rbuf nts9 t9 aux9"
  "eabs (EAndTrigger pl10 \<alpha> abuf dags10 \<phi> \<psi> tbuf10 nts10 aux10) =
     EAndTrigger pl10 (eabs \<alpha>) abuf dags10 (eabs \<phi>) (eabs \<psi>) tbuf10 nts10 aux10"
  "eabs (EMatchP m11 I11 mr11 mrs11 pls11 Ld11 nbuf11 nts11 aux11) =
     EMatchP m11 I11 mr11 mrs11 pls11 (map eabs Ld11) nbuf11 nts11 aux11"
  "eabs (EMatchF m12 I12 mr12 mrs12 pls12 Ld12 nbuf12 nts12 t12 aux12) =
     EMatchF m12 I12 mr12 mrs12 pls12 (map eabs Ld12) nbuf12 nts12 t12 aux12"
  by (simp_all add: eabs_def)

lemma map_eabs[simp]: "map eabs (map snd R) = map (eabs \<circ> snd) R"
  by simp

lemma map_iset_itab[simp]: "map (iset \<circ> itab) X = X" "map (\<lambda>x. iset (itab x)) X = X"
  by (simp_all add: map_idI)

lemma map_eeval_eabs:
  assumes "\<And>x xs \<phi>'. x \<in> set Ld \<Longrightarrow> ieval [] j ts db x = (xs, \<phi>') \<Longrightarrow>
    eeval j ts (dabs db) (eabs x) = (map iset xs, eabs \<phi>')"
  shows "map (\<lambda>x. eeval j ts (dabs db) (eabs x)) Ld = map (\<lambda>x. map_prod (map iset) eabs (ieval [] j ts db x)) Ld"
proof (rule map_cong[OF refl])
  fix x
  assume x: "x \<in> set Ld"
  obtain xs \<phi>' where "ieval [] j ts db x = (xs, \<phi>')"
    by (cases "ieval [] j ts db x")
  then show "eeval j ts (dabs db) (eabs x) = map_prod (map iset) eabs (ieval [] j ts db x)"
    using assms[OF x] by simp
qed

lemma ieval_fallback: "map_prod (map itab) eemb E = (xs, \<phi>') \<Longrightarrow> E = (map iset xs, eabs \<phi>')"
  by (cases E) (auto simp: comp_def)

theorem ieval_eeval:
  "ieval rq j ts db \<phi> = (xs, \<phi>') \<Longrightarrow> eeval j ts (dabs db) (eabs \<phi>) = (map iset xs, eabs \<phi>')"
proof (induction rq j ts db \<phi> arbitrary: xs \<phi>' rule: ieval.induct)
  case (9 rq j ts db \<phi> \<psi> buf)
  obtain xs1 \<phi>1 where 1: "ieval [] j ts db \<phi> = (xs1, \<phi>1)" by fastforce
  obtain ys1 \<psi>1 where 2: "ieval [] j ts db \<psi> = (ys1, \<psi>1)" by fastforce
  obtain zs buf' where 3: "mebuf2_take iunion (mebuf2_add xs1 ys1 buf) = (zs, buf')"
    by (cases "mebuf2_take iunion (mebuf2_add xs1 ys1 buf)") auto
  have t: "mebuf2_take (\<union>) (ib2 (mebuf2_add xs1 ys1 buf)) = (map iset zs, ib2 buf')"
    by (rule mebuf2_take_ib2[OF 3]) simp
  show ?case
    using 9(3) 9(1)[OF 1] 9(2)[OF refl 1[symmetric] 2] t by (auto simp: 1 2 3)
next
  case (10 rq j ts db pl \<phi> pos \<psi> buf)
  obtain xs1 \<phi>1 where 1: "ieval (jreq_l pl pos) j ts db \<phi> = (xs1, \<phi>1)" by fastforce
  obtain ys1 \<psi>1 where 2: "ieval (jreq_r pl pos) j ts db \<psi> = (ys1, \<psi>1)" by fastforce
  obtain zs buf' where 3: "mebuf2_take (\<lambda>r1 r2. itab (ijoin pl r1 pos r2)) (mebuf2_add xs1 ys1 buf) = (zs, buf')"
    by (cases "mebuf2_take (\<lambda>r1 r2. itab (ijoin pl r1 pos r2)) (mebuf2_add xs1 ys1 buf)") auto
  have t: "mebuf2_take (\<lambda>r1 r2. gbin_join pl r1 pos r2) (ib2 (mebuf2_add xs1 ys1 buf)) = (map iset zs, ib2 buf')"
    by (rule mebuf2_take_ib2[OF 3]) (simp add: ijoin_eq)
  show ?case
    using 10(3) 10(1)[OF 1] 10(2)[OF refl 1[symmetric] 2] t by (auto simp: 1 2 3)
next
  case (14 rq j ts db dags \<phi> \<psi> buf aux)
  obtain xs1 \<phi>1 where 1: "ieval [] j ts db \<phi> = (xs1, \<phi>1)" by fastforce
  obtain ys1 \<psi>1 where 2: "ieval [] j ts db \<psi> = (ys1, \<psi>1)" by fastforce
  obtain zs buf' aux' where 3: "iuedsx_eval_since dags [] (mebuf2S_add (map iset xs1) (map iset ys1) ts buf)
      (iudsx_ensure rq aux) = (zs, buf', aux')"
    by (metis prod_cases3)
  have t: "uedsx_eval_since dags [] (mebuf2S_add (map iset xs1) (map iset ys1) ts buf) (riu aux)
      = (map iset zs, buf', riu aux')"
    using iuedsx_eval_since_abs[of dags "[]" "mebuf2S_add (map iset xs1) (map iset ys1) ts buf"
      "iudsx_ensure rq aux"] 3 by simp
  show ?case
    using 14(3) 14(1)[OF 1] 14(2)[OF refl 1[symmetric] 2] t by (auto simp: 1 2 3)
next
  case (13 rq j ts db ps ns Ld dbuf)
  have R: "map (\<lambda>x. eeval j ts (dabs db) (eabs x)) Ld = map (\<lambda>x. map_prod (map iset) eabs (ieval [] j ts db x)) Ld"
    by (rule map_eeval_eabs) (rule 13(1))
  show ?case
    using 13(2) by (auto simp add: Let_def comp_def R case_prod_beta simp del: mebufn_take.simps)
next
  case 20
  then show ?case by (intro ieval_fallback) (simp only: ieval.simps)
next
  case 21
  then show ?case by (intro ieval_fallback) (simp only: ieval.simps)
next
  case (24 rq j ts db m I mr mrs pls Ld dbuf nts daux)
  have R: "map (\<lambda>x. eeval j ts (dabs db) (eabs x)) Ld = map (\<lambda>x. map_prod (map iset) eabs (ieval [] j ts db x)) Ld"
    by (rule map_eeval_eabs) (rule 24(1))
  show ?case
    using 24(2) by (auto simp add: Let_def comp_def R case_prod_beta simp del: mebufnt_take.simps)
next
  case (25 rq j ts db m I mr mrs pls Ld dbuf nts t daux)
  have R: "map (\<lambda>x. eeval j ts (dabs db) (eabs x)) Ld = map (\<lambda>x. map_prod (map iset) eabs (ieval [] j ts db x)) Ld"
    by (rule map_eeval_eabs) (rule 25(1))
  show ?case
    using 25(2) by (auto simp add: Let_def comp_def R case_prod_beta simp del: mebufnt_take.simps)
qed (auto simp: Let_def lookup_dabs split: prod.splits option.splits
  simp del: mebuf2_take.simps mebuf2t_take.simps mebuf2T_take.simps mebufn_take.simps
    mebufnt_take.simps meprev_next.simps mebuf2S_add.simps)
end

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
type_synonym iebufn = "itable mbuf_t list"
type_synonym ieformula =
  "(iebuf2, iebufn, event_data table mbuf_t \<times> event_data table option mbuf_t, iudsaux_x, eformula) geformula"

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

definition ibn :: "iebufn \<Rightarrow> uebufn" where
  "ibn = map (mbuf_t_map iset)"

definition ebn :: "uebufn \<Rightarrow> iebufn" where
  "ebn = map (mbuf_t_map itab)"

lemma ibn_ebn[simp]: "ibn (ebn b) = b"
  by (simp add: ibn_def ebn_def comp_def map_idI)

text \<open>Forgetting the indices, and adding none.  A subformula the indexed evaluator does not
  run itself is kept in the plain form (@{text EPlain}): the freeze and the recursive let.\<close>

fun eabs :: "ieformula \<Rightarrow> eformula" where
  "eabs EFail = EFail"
| "eabs (ERel rel) = ERel rel"
| "eabs (EPredS e1 a1) = EPredS e1 a1"
| "eabs (EPredM e2 a2 tms cs) = EPredM e2 a2 tms cs"
| "eabs (EAndRel \<phi> conf) = EAndRel (eabs \<phi>) conf"
| "eabs (ENeg \<phi>) = ENeg (eabs \<phi>)"
| "eabs (EExists \<phi> b) = EExists (eabs \<phi>) b"
| "eabs (EAgg g0 \<omega> f k n \<phi>) = EAgg g0 \<omega> f k n (eabs \<phi>)"
| "eabs (EOr \<phi> \<psi> buf) = EOr (eabs \<phi>) (eabs \<psi>) (ib2 buf)"
| "eabs (EAnd pl \<phi> pos \<psi> buf) = EAnd pl (eabs \<phi>) pos (eabs \<psi>) (ib2 buf)"
| "eabs (EPrev I1 \<phi> fst1 pbuf nts1) = EPrev I1 (eabs \<phi>) fst1 pbuf nts1"
| "eabs (ENext I2 \<phi> fst2 nts2) = ENext I2 (eabs \<phi>) fst2 nts2"
| "eabs (EAnds ps ns Ld dbuf) = EAnds ps ns (map eabs Ld) (ibn dbuf)"
| "eabs (ESince dags1 \<phi> \<psi> sbuf aux1) = ESince dags1 (eabs \<phi>) (eabs \<psi>) sbuf (riu aux1)"
| "eabs (EUntil dags2 msk2 \<phi> \<psi> ubuf nts3 t3 aux3) = EUntil dags2 msk2 (eabs \<phi>) (eabs \<psi>) ubuf nts3 t3 aux3"
| "eabs (EAndAssign p4 trm \<phi>) = EAndAssign p4 trm (eabs \<phi>)"
| "eabs (ETP mt5 i5) = ETP mt5 i5"
| "eabs (ETS mt6) = ETS mt6"
| "eabs (ELet p7 m7 \<phi> \<psi>) = ELet p7 m7 (eabs \<phi>) (eabs \<psi>)"
| "eabs (EFrz p13 m13 \<phi> \<psi> a13 b13 c13 d13 \<chi>1 e13 f13 g13 h13 i13 j13 k13 l13 \<chi>2 n13 o13 \<chi>3 \<chi>4) = EFrz p13 m13 (eabs \<phi>) (eabs \<psi>) a13 b13 c13 d13 (eabs \<chi>1) e13 f13 g13 h13 i13 j13 k13 l13 (eabs \<chi>2) n13 o13 (eabs \<chi>3) (eabs \<chi>4)"
| "eabs (ELetPast p14 m14 \<phi> \<psi> i14 buf14) = ELetPast p14 m14 (eabs \<phi>) (eabs \<psi>) i14 buf14"
| "eabs (ETrigger dags8 pls8 \<phi> \<psi> tbuf8 nts8 aux8) = ETrigger dags8 pls8 (eabs \<phi>) (eabs \<psi>) tbuf8 nts8 aux8"
| "eabs (ERelease dags9 msk9 \<phi> \<psi> rbuf nts9 t9 aux9) = ERelease dags9 msk9 (eabs \<phi>) (eabs \<psi>) rbuf nts9 t9 aux9"
| "eabs (EAndTrigger pl10 \<alpha> abuf dags10 \<phi> \<psi> tbuf10 nts10 aux10) = EAndTrigger pl10 (eabs \<alpha>) abuf dags10 (eabs \<phi>) (eabs \<psi>) tbuf10 nts10 aux10"
| "eabs (EMatchP m11 I11 mr11 mrs11 pls11 Ld11 nbuf11 nts11 aux11) = EMatchP m11 I11 mr11 mrs11 pls11 (map eabs Ld11) nbuf11 nts11 aux11"
| "eabs (EMatchF m12 I12 mr12 mrs12 pls12 Ld12 nbuf12 nts12 t12 aux12) = EMatchF m12 I12 mr12 mrs12 pls12 (map eabs Ld12) nbuf12 nts12 t12 aux12"
| "eabs (EPlain x) = x"

fun eemb :: "eformula \<Rightarrow> ieformula" where
  "eemb EFail = EFail"
| "eemb (ERel rel) = ERel rel"
| "eemb (EPredS e1 a1) = EPredS e1 a1"
| "eemb (EPredM e2 a2 tms cs) = EPredM e2 a2 tms cs"
| "eemb (EAndRel \<phi> conf) = EAndRel (eemb \<phi>) conf"
| "eemb (ENeg \<phi>) = ENeg (eemb \<phi>)"
| "eemb (EExists \<phi> b) = EExists (eemb \<phi>) b"
| "eemb (EAgg g0 \<omega> f k n \<phi>) = EAgg g0 \<omega> f k n (eemb \<phi>)"
| "eemb (EOr \<phi> \<psi> buf) = EOr (eemb \<phi>) (eemb \<psi>) (eb2 buf)"
| "eemb (EAnd pl \<phi> pos \<psi> buf) = EAnd pl (eemb \<phi>) pos (eemb \<psi>) (eb2 buf)"
| "eemb (EPrev I1 \<phi> fst1 pbuf nts1) = EPrev I1 (eemb \<phi>) fst1 pbuf nts1"
| "eemb (ENext I2 \<phi> fst2 nts2) = ENext I2 (eemb \<phi>) fst2 nts2"
| "eemb (EAnds ps ns Ld dbuf) = EAnds ps ns (map eemb Ld) (ebn dbuf)"
| "eemb (ESince dags1 \<phi> \<psi> sbuf aux1) = ESince dags1 (eemb \<phi>) (eemb \<psi>) sbuf (iudsx_emb aux1)"
| "eemb (EUntil dags2 msk2 \<phi> \<psi> ubuf nts3 t3 aux3) = EUntil dags2 msk2 (eemb \<phi>) (eemb \<psi>) ubuf nts3 t3 aux3"
| "eemb (EAndAssign p4 trm \<phi>) = EAndAssign p4 trm (eemb \<phi>)"
| "eemb (ETP mt5 i5) = ETP mt5 i5"
| "eemb (ETS mt6) = ETS mt6"
| "eemb (ELet p7 m7 \<phi> \<psi>) = ELet p7 m7 (eemb \<phi>) (eemb \<psi>)"
| "eemb (EFrz p13 m13 \<phi> \<psi> a13 b13 c13 d13 \<chi>1 e13 f13 g13 h13 i13 j13 k13 l13 \<chi>2 n13 o13 \<chi>3 \<chi>4) = EPlain (EFrz p13 m13 \<phi> \<psi> a13 b13 c13 d13 \<chi>1 e13 f13 g13 h13 i13 j13 k13 l13 \<chi>2 n13 o13 \<chi>3 \<chi>4)"
| "eemb (ELetPast p14 m14 \<phi> \<psi> i14 buf14) = EPlain (ELetPast p14 m14 \<phi> \<psi> i14 buf14)"
| "eemb (ETrigger dags8 pls8 \<phi> \<psi> tbuf8 nts8 aux8) = ETrigger dags8 pls8 (eemb \<phi>) (eemb \<psi>) tbuf8 nts8 aux8"
| "eemb (ERelease dags9 msk9 \<phi> \<psi> rbuf nts9 t9 aux9) = ERelease dags9 msk9 (eemb \<phi>) (eemb \<psi>) rbuf nts9 t9 aux9"
| "eemb (EAndTrigger pl10 \<alpha> abuf dags10 \<phi> \<psi> tbuf10 nts10 aux10) = EAndTrigger pl10 (eemb \<alpha>) abuf dags10 (eemb \<phi>) (eemb \<psi>) tbuf10 nts10 aux10"
| "eemb (EMatchP m11 I11 mr11 mrs11 pls11 Ld11 nbuf11 nts11 aux11) = EMatchP m11 I11 mr11 mrs11 pls11 (map eemb Ld11) nbuf11 nts11 aux11"
| "eemb (EMatchF m12 I12 mr12 mrs12 pls12 Ld12 nbuf12 nts12 t12 aux12) = EMatchF m12 I12 mr12 mrs12 pls12 (map eemb Ld12) nbuf12 nts12 t12 aux12"
| "eemb (EPlain u) = EPlain (EPlain u)"

lemma eabs_eemb[simp]: "eabs (eemb \<phi>) = \<phi>"
  by (induct \<phi> rule: eemb.induct) (auto simp: comp_def intro!: map_idI)

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

text \<open>The multiway join joins its first operand with the other positive ones in turn, by the plans
  @{term ps}; each operand is asked for the index its plan probes, and the operands' tables stay
  indexed in the join's buffer.\<close>

definition eands_req :: "ejoin_plan list \<Rightarrow> nat \<Rightarrow> bool list list list" where
  "eands_req ps n = take n ((case ps of [] \<Rightarrow> [[]] | p # _ \<Rightarrow> [jreq_l p True]) @
     map (\<lambda>p. jreq_r p True) ps @ replicate n [])"

lemma length_eands_req[simp]: "length (eands_req ps n) = n"
  by (cases ps) (simp_all add: eands_req_def)

fun igands_pos :: "ejoin_plan list \<Rightarrow> itable \<Rightarrow> itable list \<Rightarrow> itable" where
  "igands_pos [] t us = t"
| "igands_pos (p # ps) t [] = t"
| "igands_pos (p # ps) t (u # us) = igands_pos ps (itab (ijoin p t True u)) us"

lemma iset_igands_pos: "iset (igands_pos ps t us) = gands_pos ps (iset t) (map iset us)"
  by (induct ps t us rule: igands_pos.induct) (simp_all add: ijoin_eq)

definition igmulti_join :: "ejoin_plan list \<Rightarrow> ejoin_plan list \<Rightarrow> itable list \<Rightarrow> event_data table" where
  "igmulti_join ps ns us = (case us of [] \<Rightarrow> {}
     | t # r \<Rightarrow> gands_neg ns (iset (igands_pos ps t (take (length ps) r))) (map iset (drop (length ps) r)))"

lemma igmulti_join_eq: "igmulti_join ps ns us = gmulti_join ps ns (map iset us)"
  by (cases us) (simp_all add: igmulti_join_def gmulti_join_def iset_igands_pos take_map drop_map)

function imebufn_take :: "(itable list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> iebufn \<Rightarrow> 'b \<times> iebufn" where
  "imebufn_take f z buf = (if buf = [] \<or> (\<exists>x \<in> set buf. mbuf_t_is_empty x) then (z, buf)
    else imebufn_take f (f (map (the \<circ> fst \<circ> mbuf_t_cases) buf) z) (map (snd \<circ> mbuf_t_cases) buf))"
  by pat_completeness auto
termination
  using size_list_snd_mbuf_t_cases
  by (relation "measure (\<lambda>(_, _, buf). size_list size buf)") (auto simp: comp_def Suc_le_eq size_list_length_diff1)

declare imebufn_take.simps[simp del]

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

fun is_pred :: "Formula.name \<times> nat \<Rightarrow> ('b2, 'bn, 'ba, 'bs, 'p) geformula \<Rightarrow> bool" where
  "is_pred pm (EPredS e ar) = ((e, ar) = pm)"
| "is_pred pm _ = False"

function (sequential) preq :: "Formula.name \<times> nat \<Rightarrow> ('b2, 'bn, 'ba, 'bs, 'p) geformula \<Rightarrow> bool list list" where
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
| "preq pm (EAnds ps ns Ld b) =
     concat (map (\<lambda>(q, \<phi>). if is_pred pm \<phi> then q else preq pm \<phi>) (zip (eands_req ps (length Ld)) Ld))"
| "preq pm (ELet p m \<phi> \<psi>) = preq pm \<phi> @ (if (p, m) = pm then [] else preq pm \<psi>)"
| "preq pm _ = []"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(_, \<phi>). size \<phi>)")
    (auto dest!: set_zip_rightD intro: size_list_estimation' simp: less_Suc_eq_le)

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
     (let R = map (\<lambda>(q, \<phi>). ieval q j ts db \<phi>) (zip (eands_req ps (length Ld)) Ld);
          (zs, dbuf') = imebufn_take (\<lambda>as zs. zs @@ [igmulti_join ps ns as]) mbuf_t_empty
            (List.map2 (@@) dbuf (map fst R))
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
| "ieval rq j ts db (EPlain x) = map_prod (map itab) EPlain (eeval j ts (dabs db) x)"
  by pat_completeness (simp_all only: prod.inject geformula.inject geformula.distinct simp_thms)
termination
  by (relation "measure (\<lambda>(_, _, _, _, \<phi>). size \<phi>)")
    (auto simp: less_Suc_eq_le intro: size_list_estimation' dest!: set_zip_rightD)

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

lemma mbuf_t_is_empty_map[simp]: "mbuf_t_is_empty (mbuf_t_map f b) = mbuf_t_is_empty b"
  by transfer simp

lemma imebufn_take_ibn:
  "imebufn_take g z buf = (z', buf') \<Longrightarrow> (\<forall>xs z. g xs z = f (map iset xs) z) \<Longrightarrow>
     mebufn_take f z (ibn buf) = (z', ibn buf')"
proof (induction g z buf arbitrary: z' buf' rule: imebufn_take.induct)
  case (1 g z buf)
  have e: "ibn buf = [] \<longleftrightarrow> buf = []" "(\<exists>x \<in> set (ibn buf). mbuf_t_is_empty x) \<longleftrightarrow> (\<exists>x \<in> set buf. mbuf_t_is_empty x)"
    by (auto simp: ibn_def)
  have ne: "\<And>x. \<not> mbuf_t_is_empty x \<Longrightarrow> fst (mbuf_t_cases x) \<noteq> None"
    by transfer (auto split: list.splits)
  show ?case
  proof (cases "buf = [] \<or> (\<exists>x \<in> set buf. mbuf_t_is_empty x)")
    case True
    then show ?thesis using 1(2) e
      by (subst mebufn_take.simps) (simp add: imebufn_take.simps[of g z buf] del: mebufn_take.simps)
  next
    case False
    have h: "map (the \<circ> fst \<circ> mbuf_t_cases) (ibn buf) = map iset (map (the \<circ> fst \<circ> mbuf_t_cases) buf)"
      unfolding ibn_def map_map
    proof (rule map_cong[OF refl])
      fix x
      assume "x \<in> set buf"
      then have "fst (mbuf_t_cases x) \<noteq> None" using False ne by blast
      then show "(the \<circ> fst \<circ> mbuf_t_cases \<circ> mbuf_t_map iset) x = (iset \<circ> (the \<circ> fst \<circ> mbuf_t_cases)) x"
        by (simp add: mbuf_t_cases_map option.map_sel)
    qed
    have t: "map (snd \<circ> mbuf_t_cases) (ibn buf) = ibn (map (snd \<circ> mbuf_t_cases) buf)"
      by (auto simp: ibn_def mbuf_t_cases_map split: prod.splits)
    have u: "imebufn_take g (g (map (the \<circ> fst \<circ> mbuf_t_cases) buf) z) (map (snd \<circ> mbuf_t_cases) buf)
        = (z', buf')"
      using 1(2) False by (simp add: imebufn_take.simps[of g z buf])
    have g: "g (map (the \<circ> fst \<circ> mbuf_t_cases) buf) z = f (map iset (map (the \<circ> fst \<circ> mbuf_t_cases) buf)) z"
      using 1(3) by blast
    have IH: "mebufn_take f (f (map iset (map (the \<circ> fst \<circ> mbuf_t_cases) buf)) z)
        (ibn (map (snd \<circ> mbuf_t_cases) buf)) = (z', ibn buf')"
      using 1(1)[OF False u 1(3)] unfolding g .
    have ne2: "\<not> (ibn buf = [] \<or> (\<exists>x \<in> set (ibn buf). mbuf_t_is_empty x))"
      using False e by blast
    show ?thesis
      by (subst mebufn_take.simps) (simp only: if_not_P[OF ne2] h t IH)
  qed
qed

lemma ibn_add: "ibn (List.map2 (@@) dbuf xss) = mebufn_add (map (map iset) xss) (ibn dbuf)"
  unfolding ibn_def mebufn_add.simps
  by (induct dbuf xss rule: list_induct2') simp_all

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

lemma map_eeval_eabs_zip:
  assumes "length Q = length Ld"
    and "\<And>q x xs \<phi>'. (q, x) \<in> set (zip Q Ld) \<Longrightarrow> ieval q j ts db x = (xs, \<phi>') \<Longrightarrow>
    eeval j ts (dabs db) (eabs x) = (map iset xs, eabs \<phi>')"
  shows "map (\<lambda>x. eeval j ts (dabs db) (eabs x)) Ld =
    map (\<lambda>(q, x). map_prod (map iset) eabs (ieval q j ts db x)) (zip Q Ld)"
proof -
  have L: "Ld = map snd (zip Q Ld)" using assms(1) by simp
  have "map (\<lambda>x. eeval j ts (dabs db) (eabs x)) Ld =
      map (\<lambda>(q, x). eeval j ts (dabs db) (eabs x)) (zip Q Ld)"
    by (subst (1) L) (simp add: case_prod_beta)
  also have "\<dots> = map (\<lambda>(q, x). map_prod (map iset) eabs (ieval q j ts db x)) (zip Q Ld)"
  proof (rule map_cong[OF refl])
    fix e
    assume e: "e \<in> set (zip Q Ld)"
    obtain q x where qx: "e = (q, x)" by (cases e)
    obtain xs \<phi>' where "ieval q j ts db x = (xs, \<phi>')" by (cases "ieval q j ts db x")
    then show "(\<lambda>(q, x). eeval j ts (dabs db) (eabs x)) e = (\<lambda>(q, x). map_prod (map iset) eabs (ieval q j ts db x)) e"
      using assms(2)[of q x] e qx by simp
  qed
  finally show ?thesis .
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
  let ?Q = "eands_req ps (length Ld)"
  let ?R = "map (\<lambda>(q, \<phi>). ieval q j ts db \<phi>) (zip ?Q Ld)"
  let ?F = "\<lambda>as zs. zs @@ [gmulti_join ps ns as]"
  let ?G = "\<lambda>as zs. zs @@ [igmulti_join ps ns as]"
  have R: "map (\<lambda>x. eeval j ts (dabs db) (eabs x)) Ld =
      map (\<lambda>(q, x). map_prod (map iset) eabs (ieval q j ts db x)) (zip ?Q Ld)"
    by (rule map_eeval_eabs_zip) (auto intro: 13(1))
  obtain zs dbuf' where 3: "imebufn_take ?G mbuf_t_empty (List.map2 (@@) dbuf (map fst ?R)) = (zs, dbuf')"
    by fastforce
  have t: "mebufn_take ?F mbuf_t_empty (mebufn_add (map (map iset \<circ> fst) ?R) (ibn dbuf)) = (zs, ibn dbuf')"
    using imebufn_take_ibn[OF 3, of ?F] by (simp add: igmulti_join_eq ibn_add comp_def)
  have i: "ieval rq j ts db (EAnds ps ns Ld dbuf) = (map itab (Rep_mbuf_t zs), EAnds ps ns (map snd ?R) dbuf')"
    using 3 by (simp add: Let_def)
  have e: "eeval j ts (dabs db) (eabs (EAnds ps ns Ld dbuf)) =
      (Rep_mbuf_t zs, EAnds ps ns (map (eabs \<circ> snd) ?R) (ibn dbuf'))"
    using t by (simp add: Let_def R comp_def case_prod_beta del: mebufn_take.simps mebufn_add.simps)
  from 13(2) i have xs: "xs = map itab (Rep_mbuf_t zs)" and \<phi>': "\<phi>' = EAnds ps ns (map snd ?R) dbuf'"
    by simp_all
  show ?case
    unfolding e xs \<phi>' by (simp add: comp_def)
next
  case (27 rq j ts db x)
  then show ?case by (cases "eeval j ts (dabs db) x") (auto simp: comp_def)
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

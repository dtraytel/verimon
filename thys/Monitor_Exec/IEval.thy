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
  "(iebuf2, iebufn, event_data table mbuf_t \<times> event_data table option mbuf_t, iudsaux_x, iuduaux_x, eformula) geformula"

lift_definition mbuf_t_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mbuf_t \<Rightarrow> 'b mbuf_t" is map .

definition ib2 :: "iebuf2 \<Rightarrow> uebuf2" where
  "ib2 = map_prod (mbuf_t_map iset) (mbuf_t_map iset)"

definition eb2 :: "uebuf2 \<Rightarrow> iebuf2" where
  "eb2 = map_prod (mbuf_t_map itab) (mbuf_t_map itab)"

definition ibn :: "iebufn \<Rightarrow> uebufn" where
  "ibn = map (mbuf_t_map iset)"

definition ebn :: "uebufn \<Rightarrow> iebufn" where
  "ebn = map (mbuf_t_map itab)"

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
| "eabs (EUntil dags2 msk2 \<phi> \<psi> ubuf nts3 t3 aux3) = EUntil dags2 msk2 (eabs \<phi>) (eabs \<psi>) ubuf nts3 t3 (riud aux3)"
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

subsection \<open>The evaluator\<close>

text \<open>
  The evaluator takes, besides the formula, the masks at which its caller would like the result
  indexed.  A join asks each operand for the index its plan probes; a Since or Until structure
  embedded indexed keeps them, every other node ignores the request.
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

definition igmulti_join :: "ejoin_plan list \<Rightarrow> ejoin_plan list \<Rightarrow> itable list \<Rightarrow> event_data table" where
  "igmulti_join ps ns us = (case us of [] \<Rightarrow> {}
     | t # r \<Rightarrow> gands_neg ns (iset (igands_pos ps t (take (length ps) r))) (map iset (drop (length ps) r)))"

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

lemma dabs_demb[simp]: "dabs (demb db) = db"
  by (rule mapping_eqI) (simp add: lookup_dabs demb_def Mapping.lookup_map_values option.map_comp
      comp_def option.map_ident)

fun is_pred :: "Formula.name \<times> nat \<Rightarrow> ('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula \<Rightarrow> bool" where
  "is_pred pm (EPredS e ar) = ((e, ar) = pm)"
| "is_pred pm _ = False"

function (sequential) preq :: "Formula.name \<times> nat \<Rightarrow> ('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula \<Rightarrow> bool list list" where
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

subsection \<open>Embedding, with the indices decided once\<close>

text \<open>
  Which nodes keep indexed tables is decided once, when the executable state is embedded, not
  while the monitor runs.  The embedding passes down the masks each node's consumer will ask for,
  exactly as the evaluator does (a join's plan, the multi-way join, the predicates of a LET), and
  a Since or Until structure is embedded indexed at those masks when the policy lets it
  (@{text ireq}).  Keeping an index costs at every insertion and deletion, which pays off only for
  a table that lives long compared to the rate at which it changes; the default policy
  (@{text IxUnbounded}) indexes the window of a past operator whose interval is unbounded.  The
  policy affects only the speed: the embedding forgets to the same formula whatever it decides
  (@{text eabs_eemb}).
\<close>

datatype ipolicy = IxNone | IxUnbounded | IxAll

fun ireq :: "ipolicy \<Rightarrow> args \<Rightarrow> bool list list \<Rightarrow> bool list list" where
  "ireq IxNone args rq = []"
| "ireq IxUnbounded args rq = (if bounded (args_ivl args) then [] else rq)"
| "ireq IxAll args rq = rq"
function (sequential) eemb :: "ipolicy \<Rightarrow> bool list list \<Rightarrow> eformula \<Rightarrow> ieformula" where
  "eemb ix rq EFail = EFail"
| "eemb ix rq (ERel rel) = ERel rel"
| "eemb ix rq (EPredS e1 a1) = EPredS e1 a1"
| "eemb ix rq (EPredM e2 a2 tms cs) = EPredM e2 a2 tms cs"
| "eemb ix rq (EAndRel \<phi> conf) = EAndRel (eemb ix [] \<phi>) conf"
| "eemb ix rq (ENeg \<phi>) = ENeg (eemb ix [] \<phi>)"
| "eemb ix rq (EExists \<phi> b) = EExists (eemb ix [] \<phi>) b"
| "eemb ix rq (EAgg g0 \<omega> f k n \<phi>) = EAgg g0 \<omega> f k n (eemb ix [] \<phi>)"
| "eemb ix rq (EOr \<phi> \<psi> buf) = EOr (eemb ix [] \<phi>) (eemb ix [] \<psi>) (eb2 buf)"
| "eemb ix rq (EAnd pl \<phi> pos \<psi> buf) = EAnd pl (eemb ix (jreq_l pl pos) \<phi>) pos (eemb ix (jreq_r pl pos) \<psi>) (eb2 buf)"
| "eemb ix rq (EPrev I1 \<phi> fst1 pbuf nts1) = EPrev I1 (eemb ix [] \<phi>) fst1 pbuf nts1"
| "eemb ix rq (ENext I2 \<phi> fst2 nts2) = ENext I2 (eemb ix [] \<phi>) fst2 nts2"
| "eemb ix rq (EAnds ps ns Ld dbuf) = EAnds ps ns (map (\<lambda>(q, \<phi>). eemb ix q \<phi>) (zip (eands_req ps (length Ld)) Ld)) (ebn dbuf)"
| "eemb ix rq (ESince dags1 \<phi> \<psi> sbuf aux1) = ESince dags1 (eemb ix [] \<phi>) (eemb ix [] \<psi>) sbuf (iudsx_emb (ireq ix dags1 rq) aux1)"
| "eemb ix rq (EUntil dags2 msk2 \<phi> \<psi> ubuf nts3 t3 aux3) = EUntil dags2 msk2 (eemb ix [] \<phi>) (eemb ix [] \<psi>) ubuf nts3 t3 (iudux_emb (ireq ix dags2 rq) aux3)"
| "eemb ix rq (EAndAssign p4 trm \<phi>) = EAndAssign p4 trm (eemb ix [] \<phi>)"
| "eemb ix rq (ETP mt5 i5) = ETP mt5 i5"
| "eemb ix rq (ETS mt6) = ETS mt6"
| "eemb ix rq (ELet p7 m7 \<phi> \<psi>) = ELet p7 m7 (eemb ix (preq (p7, m7) \<psi>) \<phi>) (eemb ix [] \<psi>)"
| "eemb ix rq (EFrz p13 m13 \<phi> \<psi> a13 b13 c13 d13 \<chi>1 e13 f13 g13 h13 i13 j13 k13 l13 \<chi>2 n13 o13 \<chi>3 \<chi>4) = EPlain (EFrz p13 m13 \<phi> \<psi> a13 b13 c13 d13 \<chi>1 e13 f13 g13 h13 i13 j13 k13 l13 \<chi>2 n13 o13 \<chi>3 \<chi>4)"
| "eemb ix rq (ELetPast p14 m14 \<phi> \<psi> i14 buf14) = EPlain (ELetPast p14 m14 \<phi> \<psi> i14 buf14)"
| "eemb ix rq (ETrigger dags8 pls8 \<phi> \<psi> tbuf8 nts8 aux8) = ETrigger dags8 pls8 (eemb ix [] \<phi>) (eemb ix [] \<psi>) tbuf8 nts8 aux8"
| "eemb ix rq (ERelease dags9 msk9 \<phi> \<psi> rbuf nts9 t9 aux9) = ERelease dags9 msk9 (eemb ix [] \<phi>) (eemb ix [] \<psi>) rbuf nts9 t9 aux9"
| "eemb ix rq (EAndTrigger pl10 \<alpha> abuf dags10 \<phi> \<psi> tbuf10 nts10 aux10) = EAndTrigger pl10 (eemb ix [] \<alpha>) abuf dags10 (eemb ix [] \<phi>) (eemb ix [] \<psi>) tbuf10 nts10 aux10"
| "eemb ix rq (EMatchP m11 I11 mr11 mrs11 pls11 Ld11 nbuf11 nts11 aux11) = EMatchP m11 I11 mr11 mrs11 pls11 (map (eemb ix []) Ld11) nbuf11 nts11 aux11"
| "eemb ix rq (EMatchF m12 I12 mr12 mrs12 pls12 Ld12 nbuf12 nts12 t12 aux12) = EMatchF m12 I12 mr12 mrs12 pls12 (map (eemb ix []) Ld12) nbuf12 nts12 t12 aux12"
| "eemb ix rq (EPlain u) = EPlain (EPlain u)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(_, _, \<phi>). size \<phi>)")
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
          (aux', buf', nt, nts') = mebuf2t_take (iudux_add_new dags msk) (iudux_ensure rq aux)
            (mebuf2_add (map iset xs) (map iset ys) buf) t (nts @@ ts);
          (zs, aux'') = iudux_eval dags nt aux'
      in (zs, EUntil dags msk \<phi>' \<psi>' buf' nts' nt aux''))"
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
     map_prod (map itab) (eemb IxNone [])
       (eeval j ts (dabs db) (eabs (EFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E)))"
| "ieval rq j ts db (ELetPast p m \<phi> \<psi> i buf) =
     map_prod (map itab) (eemb IxNone []) (eeval j ts (dabs db) (eabs (ELetPast p m \<phi> \<psi> i buf)))"
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

end

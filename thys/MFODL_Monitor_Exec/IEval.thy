(*<*)
theory IEval
  imports Eval ITable
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
  "(iebuf2, uebufn, event_data table mbuf_t \<times> event_data table option mbuf_t) geformula"

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
  "eabs = map_geformula ib2 id id"

definition eemb :: "eformula \<Rightarrow> ieformula" where
  "eemb = map_geformula eb2 id id"

lemma eabs_eemb[simp]: "eabs (eemb \<phi>) = \<phi>"
  by (simp add: eabs_def eemb_def geformula.map_comp comp_def geformula.map_ident)

subsection \<open>The evaluator\<close>

function (sequential) ieval :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> ieformula \<Rightarrow> itable list \<times> ieformula" where
  "ieval j ts db EFail = ([], EFail)"
| "ieval j ts db (ERel rel) = (replicate (length ts) (itab rel), ERel rel)"
| "ieval j ts db (EPredS e ar) = apfst (map itab) (eeval j ts db (EPredS e ar))"
| "ieval j ts db (EPredM e ar tms cs) = apfst (map itab) (eeval j ts db (EPredM e ar tms cs))"
| "ieval j ts db (EAndRel \<phi> conf) =
     (let (xs, \<phi>') = ieval j ts db \<phi>
      in (map (\<lambda>x. itab (Set.filter (ueval_constraint conf) (iset x))) xs, EAndRel \<phi>' conf))"
| "ieval j ts db (ENeg \<phi>) =
     (let (xs, \<phi>') = ieval j ts db \<phi>
      in (map (\<lambda>r. itab (if iset r = {} then {[]} else {})) xs, ENeg \<phi>'))"
| "ieval j ts db (EExists \<phi> drop0) =
     (let (xs, \<phi>') = ieval j ts db \<phi>
      in (map (\<lambda>r. itab (if drop0 then tl ` iset r else iset r)) xs, EExists \<phi>' drop0))"
| "ieval j ts db (EAgg g0 \<omega> f k pos \<phi>) =
     (let (xs, \<phi>') = ieval j ts db \<phi>
      in (map (\<lambda>r. itab (uagg g0 \<omega> f k pos (iset r))) xs, EAgg g0 \<omega> f k pos \<phi>'))"
| "ieval j ts db (EOr \<phi> \<psi> buf) =
     (let (xs, \<phi>') = ieval j ts db \<phi>; (ys, \<psi>') = ieval j ts db \<psi>;
          (zs, buf') = mebuf2_take iunion (mebuf2_add xs ys buf)
      in (zs, EOr \<phi>' \<psi>' buf'))"
| "ieval j ts db (EAnd pl \<phi> pos \<psi> buf) =
     (let (xs, \<phi>') = ieval j ts db \<phi>; (ys, \<psi>') = ieval j ts db \<psi>;
          (zs, buf') = mebuf2_take (\<lambda>r1 r2. itab (ijoin pl r1 pos r2)) (mebuf2_add xs ys buf)
      in (zs, EAnd pl \<phi>' pos \<psi>' buf'))"
| "ieval j ts db (EPrev I \<phi> first buf nts) =
     (let (xs, \<phi>') = ieval j ts db \<phi>; xs = map iset xs
      in if first \<and> ts = [] then ([], EPrev I \<phi>' True (buf @@ xs) (nts @@ ts))
      else let (zs, buf', nts') = meprev_next I (buf @@ xs) (nts @@ ts)
        in (map itab (if first then {} # zs else zs), EPrev I \<phi>' False buf' nts'))"
| "ieval j ts db (ENext I \<phi> first nts) =
     (let (xs, \<phi>') = ieval j ts db \<phi>; xs = map iset xs;
          (xs, first') = (case (xs, first) of (_ # xs', True) \<Rightarrow> (xs', False) | a \<Rightarrow> a);
          (zs, _, nts') = meprev_next I (mbuf_t_empty @@ xs) (nts @@ ts)
      in (map itab zs, ENext I \<phi>' first' nts'))"
| "ieval j ts db (EAnds ps ns Ld dbuf) =
     (let R = map (ieval j ts db) Ld;
          (zs, dbuf') = mebufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty
            (mebufn_add (map (map iset \<circ> fst) R) dbuf)
      in (map itab (Rep_mbuf_t zs), EAnds ps ns (map snd R) dbuf'))"
| "ieval j ts db (ESince dags \<phi> \<psi> buf aux) =
     (let (xs, \<phi>') = ieval j ts db \<phi>; (ys, \<psi>') = ieval j ts db \<psi>;
          (zs, buf', aux') = uedsx_eval_since dags [] (mebuf2S_add (map iset xs) (map iset ys) ts buf) aux
      in (map itab zs, ESince dags \<phi>' \<psi>' buf' aux'))"
| "ieval j ts db (EUntil dags msk \<phi> \<psi> buf nts t aux) =
     (let (xs, \<phi>') = ieval j ts db \<phi>; (ys, \<psi>') = ieval j ts db \<psi>;
          (aux', buf', nt, nts') = mebuf2t_take (udux_add_new dags msk) aux
            (mebuf2_add (map iset xs) (map iset ys) buf) t (nts @@ ts);
          (zs, aux'') = udux_eval dags nt aux'
      in (map itab zs, EUntil dags msk \<phi>' \<psi>' buf' nts' nt aux''))"
| "ieval j ts db (EAndAssign p t \<phi>) =
     (let (xs, \<phi>') = ieval j ts db \<phi> in (map (\<lambda>r. itab (uassign p t (iset r))) xs, EAndAssign p t \<phi>'))"
| "ieval j ts db (ETP mt i) = apfst (map itab) (eeval j ts db (ETP mt i))"
| "ieval j ts db (ETS mt) = apfst (map itab) (eeval j ts db (ETS mt))"
| "ieval j ts db (ELet p m \<phi> \<psi>) =
     (let (xs, \<phi>') = ieval j ts db \<phi>;
          (ys, \<psi>') = ieval j ts (Mapping.update (p, m) (map iset xs) db) \<psi>
      in (ys, ELet p m \<phi>' \<psi>'))"
| "ieval j ts db (EFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E) =
     map_prod (map itab) eemb
       (eeval j ts db (eabs (EFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E)))"
| "ieval j ts db (ELetPast p m \<phi> \<psi> i buf) =
     map_prod (map itab) eemb (eeval j ts db (eabs (ELetPast p m \<phi> \<psi> i buf)))"
| "ieval j ts db (ETrigger dags pl \<phi> \<psi> dbuf nts daux) =
     (let (xs, \<phi>') = ieval j ts db \<phi>; (ys, \<psi>') = ieval j ts db \<psi>;
          ((zs, daux'), dbuf', nts') = mebuf2T_take (\<lambda>r1 r2 t (zs, ax).
            let ax = tw_update dags t r1 r2 ax
            in (zs @ [tw_result ax], ax)) ([], daux)
            (mebuf2_add (map iset xs) (map iset ys) dbuf) (nts @@ ts)
      in (map itab zs, ETrigger dags pl \<phi>' \<psi>' dbuf' nts' daux'))"
| "ieval j ts db (EAndTrigger pl \<alpha> dbuf1 dags \<phi> \<psi> ebuf2 nts daux) =
     (let (as, \<alpha>') = ieval j ts db \<alpha>; (xs, \<phi>') = ieval j ts db \<phi>;
          (ys, \<psi>') = ieval j ts db \<psi>;
          ((ws, daux'), dbuf2', nts') = mebuf2T_take (\<lambda>r1 r2 t (ws, ax).
            let ax = tw_update dags t r1 r2 ax
            in (ws @ [if tw_empty ax then None
                      else Some (tw_result ax)], ax)) ([], daux)
            (mebuf2_add (map iset xs) (map iset ys) ebuf2) (nts @@ ts);
          (zs, dbuf1') = mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
            | Some z \<Rightarrow> gbin_join pl r1 True z) (mebuf2_add (map iset as) ws dbuf1)
      in (map itab zs, EAndTrigger pl \<alpha>' dbuf1' dags \<phi>' \<psi>' dbuf2' nts' daux'))"
| "ieval j ts db (EMatchP m I mr mrs pls Ld dbuf nts daux) =
     (let R = map (ieval j ts db) Ld;
          ((zs, daux'), dbuf', _, nts') = mebufnt_take (\<lambda>rels t (zs, ax).
             let (z, ax) = gupdate_matchP (map emb_msk pls) I mr mrs rels t ax
             in (zs @@ [z], ax)) (mbuf_t_empty, daux)
             (mebufn_add (map (map iset \<circ> fst) R) dbuf) 0 (nts @@ ts)
      in (map itab (Rep_mbuf_t zs), EMatchP m I mr mrs pls (map snd R) dbuf' nts' daux'))"
| "ieval j ts db (EMatchF m I mr mrs pls Ld dbuf nts t daux) =
     (let R = map (ieval j ts db) Ld;
          (daux', dbuf', nt, nts') = mebufnt_take
             (\<lambda>rels. gupdate_matchF (map emb_msk pls) I mr mrs rels)
             daux (mebufn_add (map (map iset \<circ> fst) R) dbuf) t (nts @@ ts);
          (zs, daux'') = geval_matchF I mr nt daux'
      in (map itab zs, EMatchF m I mr mrs pls (map snd R) dbuf' nts' nt daux''))"
| "ieval j ts db (ERelease dags msk \<phi> \<psi> buf nts t aux) =
     (let (xs, \<phi>') = ieval j ts db \<phi>; (ys, \<psi>') = ieval j ts db \<psi>;
          (aux', buf', nt, nts') = mebuf2t_take (eraux_update dags msk) aux
            (mebuf2_add (map iset xs) (map iset ys) buf) t (nts @@ ts);
          (zs, aux'') = eraux_eval (args_ivl dags) nt aux'
      in (map itab zs, ERelease dags msk \<phi>' \<psi>' buf' nts' nt aux''))"
  by pat_completeness (simp_all only: prod.inject geformula.inject geformula.distinct simp_thms)
termination
  by (relation "measure (\<lambda>(_, _, _, \<phi>). size \<phi>)") (auto simp: size_list_estimation')

end

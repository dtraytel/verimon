(*<*)
theory Generic_Ops
  imports Until_Gen
begin
(*>*)

section \<open>The executable operations over a bare element type\<close>

text \<open>
  The executable operations of @{theory MFODL_Monitor_Exec.Frame} and
  @{theory MFODL_Monitor_Exec.Frame_Aux} are stated at the kernel's tuples, @{typ "event_data
  list"}.  The executable evaluator runs the same operations restated over a bare element type
  \<open>'b\<close>; each generic operation is proved equal to the one it generalises at
  @{typ event_data}, so every theorem of @{theory MFODL_Monitor_Exec.Frame} and
  @{theory MFODL_Monitor_Exec.Frame_Aux} continues to say what it said about the code that
  runs.

  The operations that read a field rather than move it -- the assignment, the time-point and
  time-stamp terms, the match, the constraint and the aggregation -- are not generalised: they
  go through the evaluation of terms, and their versions over the short tuples are those of
  @{theory MFODL_Monitor_Exec.Tuple_Fields}.
\<close>

text \<open>The executable monitor runs at @{typ event_data}, and a table of it is this.\<close>

type_synonym utable = "event_data list set"

lemma ID_ccompare_ed: "ID CCOMPARE(event_data list) \<noteq> None"
  by (simp add: ccompare_list_def ccompare_event_data_def ID_def split: option.splits)

lemma set_csorted_list_of_set_ed:
  "finite (X :: event_data list set) \<Longrightarrow> set (csorted_list_of_set X) = X"
  using ID_ccompare_ed by (subst csorted_list_of_set_split) auto

lemma set_csl_ed: "finite (X :: event_data list set) \<Longrightarrow> set (csl X) = X"
  by (simp add: csl_finite set_csorted_list_of_set_ed)

subsection \<open>The trigger structure over short tuples\<close>

text \<open>
  The kernel's trigger structure of @{theory MFODL_Monitor_Devel.Optimized_Trigger} keeps its
  tuples over the node's kernel columns.  Its queues, its two mappings and the shift it performs
  on them only ever test membership and look keys up, so they carry over unchanged to the
  ascending columns.  Two things do not.

  The first is the semi-join that decides which of the right operand's tuples the left one
  admits.  The kernel restricts to the left operand's columns; over the ascending columns the
  projection is @{const eproj} through a mask.  Where the left operand has the node's columns
  the projection is the identity, where it has none the whole table is taken or dropped on one
  test of the empty tuple, and otherwise each tuple is projected.

  The second is the result at an empty window, which is every valuation of the node's columns.
  A table of tuples cannot say that, so the result is split in two: @{term gresult_mmtaux}
  returns the union of the three sets, which is the kernel's answer on a non-empty window, and
  @{term gmmtaux_empty} says whether the window is empty, so that a node which can face an empty
  one recognises the case rather than reading a wrong table.  The standalone trigger cannot face
  it -- its interval contains zero, so the update always appends to the window -- and reads the
  result directly; the conjunction with a trigger can, and treats the empty window as the
  identity on its other operand.
\<close>

type_synonym 'b gmmtaux = "
  ts \<times> nat \<times> nat \<times> nat \<times>
  bool list \<times>
  (ts \<times> 'b list set \<times> 'b list set) queue \<times>
  (ts \<times> 'b list set) queue \<times>
  (('b list, ts) mapping) \<times>
  'b list set \<times>
  (('b list, nat) mapping) \<times>
  'b list set \<times>
  'b list set"

definition gsemi_join :: "bool list \<Rightarrow> bool \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "gsemi_join msk pos r l =
     (if \<forall>i \<in> set msk. i then (if pos then r \<inter> l else r - l)
      else if \<forall>i \<in> set msk. \<not> i then (if pos = ([] \<in> l) then r else {})
      else esemi msk pos r l)"

definition ginit_mmtaux :: "args \<Rightarrow> bool list \<Rightarrow> 'b gmmtaux" where
  "ginit_mmtaux args msk = (0, 0, 0, 0, msk, empty_queue, empty_queue,
     Mapping.empty, {}, Mapping.empty, {}, {})"

definition gupdate_mmtaux' :: "args \<Rightarrow> ts \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow>
    (ts \<times> 'b list set \<times> 'b list set) queue \<Rightarrow> (ts \<times> 'b list set) queue \<Rightarrow>
    (('b list, ts) mapping) \<Rightarrow> 'b list set \<Rightarrow> (('b list, nat) mapping) \<Rightarrow> 'b list set \<Rightarrow>
    'b list set \<Rightarrow>
    (nat \<times> nat \<times> (ts \<times> 'b list set \<times> 'b list set) queue \<times> (ts \<times> 'b list set) queue \<times>
     (('b list, ts) mapping) \<times> 'b list set \<times> (('b list, nat) mapping) \<times> 'b list set \<times>
     'b list set)" where
  "gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tuple_in_once
     tuple_in_once_keys tuple_since_hist hist_sat since_sat = (
    let (_, data_prev', move, tuple_in_once', tuple_in_once_keys') = shift_end'
      (flip_int_less_lower (args_ivl args)) nt fst
      (empty_queue :: (ts \<times> 'b list set \<times> 'b list set) queue,
       data_prev, tuple_in_once, tuple_in_once_keys);
    move_len = length move;
    idx_mid' = idx_mid + move_len;
    (data_in', drop) = takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in;
    move' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move;
    drop_prev_len = move_len - length move';
    idx_oldest' = idx_oldest + length drop + drop_prev_len;
    data_in'' = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move' data_in';
    (tuple_since_hist', hist_sat', idx_move, since_sat') =
      fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
        let tuple_since_hist = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist;
            hist_sat = hist_sat \<inter> r;
            since_sat = since_sat \<inter> r
        in (upd_set tuple_since_hist (\<lambda>_. idx_move) (r - Mapping.keys tuple_since_hist),
            hist_sat, idx_move + 1,
            since_sat \<union> gsemi_join msk (args_pos args) r l))
      move (tuple_since_hist, hist_sat, idx_mid, since_sat);
    tuple_since_hist'' = (if idx_mid' = idx_oldest' then Mapping.empty else tuple_since_hist');
    since_sat'' = (if idx_mid' = idx_oldest' then {} else since_sat');
    hist_sat'' = (case fst (safe_hd data_in'') of None \<Rightarrow> {}
      | Some db \<Rightarrow> hist_sat' \<union> {tuple \<in> snd db.
          case Mapping.lookup tuple_since_hist'' tuple of
            Some idx \<Rightarrow> idx \<le> idx_oldest' | None \<Rightarrow> False})
    in
    (idx_mid', idx_oldest', data_prev', data_in'', tuple_in_once', tuple_in_once_keys',
     tuple_since_hist'', hist_sat'', since_sat''))"

definition gupdate_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> 'b gmmtaux \<Rightarrow>
    'b gmmtaux" where
  "gupdate_mmtaux args nt l r = (\<lambda>(cur, idx_next, idx_mid, idx_oldest, msk, data_prev, data_in,
      tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat).
    (let (idx_mid', idx_oldest', data_prev', data_in', tuple_in_once', tuple_in_once_keys',
          tuple_since_hist', hist_sat', since_sat') =
       gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tuple_in_once
         tuple_in_once_keys tuple_since_hist hist_sat since_sat
     in (if mem (args_ivl args) 0
       then (let tuple_since_hist'' = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist' in
         (nt, idx_next + 1, idx_mid' + 1, idx_oldest', msk, data_prev',
          append_queue (nt, r) data_in', tuple_in_once', tuple_in_once_keys',
          upd_set tuple_since_hist'' (\<lambda>_. idx_mid') (r - Mapping.keys tuple_since_hist''),
          (if Queue.is_empty data_in' then r else hist_sat' \<inter> r),
          (since_sat' \<inter> r) \<union> gsemi_join msk (args_pos args) r l))
       else
         (nt, idx_next + 1, idx_mid', idx_oldest', msk,
          append_queue (nt, l, r) data_prev', data_in',
          upd_set tuple_in_once' (\<lambda>_. nt) l, tuple_in_once_keys' \<union> l,
          tuple_since_hist', hist_sat', since_sat'))))"

definition gresult_mmtaux :: "args \<Rightarrow> 'b gmmtaux \<Rightarrow> 'b list set" where
  "gresult_mmtaux args = (\<lambda>(cur, idx_next, idx_mid, idx_oldest, msk, data_prev, data_in,
      tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat).
    tuple_in_once_keys \<union> hist_sat \<union> since_sat)"

definition gmmtaux_empty :: "'b gmmtaux \<Rightarrow> bool" where
  "gmmtaux_empty = (\<lambda>(cur, idx_next, idx_mid, idx_oldest, msk, data_prev, data_in,
      tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat).
    Queue.is_empty data_in)"

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

lemma gnth_nth[simp]: "i < length xs \<Longrightarrow> gnth xs i = xs ! i"
  by (simp add: gnth_def)

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

(*<*)
end
(*>*)
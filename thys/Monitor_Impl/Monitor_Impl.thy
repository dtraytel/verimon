(*<*)
theory Monitor_Impl
  imports
    Optimized_Trigger
    Optimized_Agg_Temporal
    Optimized_Agg_Valid
    Optimized_Until_Deque
    "HOL-Library.Code_Target_Nat"
    Containers.Containers
    "Generic_Join_Devel.Proj_Code"
begin
(*>*)

declare Let_def[simp del]

section \<open>Data refinement\<close>

typedef 'a mbuf_t = "UNIV :: 'a list set" ..

setup_lifting type_definition_mbuf_t

instantiation mbuf_t :: (type) size
begin

lift_definition size_mbuf_t :: "'a mbuf_t \<Rightarrow> nat" is "length" .

instance ..

end

lift_definition mbuf_t_empty :: "'a mbuf_t" is "[]" .

lift_definition mbuf_t_is_empty :: "'a mbuf_t \<Rightarrow> bool" is "\<lambda>xs. xs = []" .

lift_definition mbuf_t_Cons :: "'a \<Rightarrow> 'a mbuf_t \<Rightarrow> 'a mbuf_t" is Cons .

no_notation SCons (infixr "##" 65)
notation mbuf_t_Cons (infixr "##" 65)

lift_definition mbuf_t_append :: "'a mbuf_t \<Rightarrow> 'a list \<Rightarrow> 'a mbuf_t" is append .

notation mbuf_t_append (infixr "@@" 65)

lift_definition mbuf_t_cases :: "'a mbuf_t \<Rightarrow> 'a option \<times> 'a mbuf_t" is
  "\<lambda>xs. case xs of [] \<Rightarrow> (None, xs) | y # ys \<Rightarrow> (Some y, ys)" .

lemma mbuf_t_cases_size[termination_simp]: "(Some x, xs') = mbuf_t_cases xs \<Longrightarrow> size xs' < size xs"
  by transfer (auto split: list.splits)

lift_definition MBuf2_t :: "'a queue \<Rightarrow> 'a mbuf_t" is "linearize" .

code_datatype MBuf2_t

declare MBuf2_t.rep_eq[code]

lemma mbuf_t_empty_code[code]: "mbuf_t_empty = MBuf2_t empty_queue"
  by transfer' (auto simp: empty_queue_rep)

lemma mbuf_t_is_empty_code[code]: "mbuf_t_is_empty (MBuf2_t xs) = Queue.is_empty xs"
  by transfer' (auto simp: is_empty_alt)

lemma mbuf_t_Cons_code[code]: "mbuf_t_Cons x (MBuf2_t xs) = MBuf2_t (prepend_queue x xs)"
  by transfer' (auto simp: prepend_queue_rep)

lemma mbuf_t_append_code[code]: "mbuf_t_append (MBuf2_t xs) ys = MBuf2_t (fold append_queue ys xs)"
proof transfer'
  fix xs :: "'a queue" and ys :: "'a list"
  show "linearize xs @ ys = linearize (fold append_queue ys xs)"
  proof (induction ys arbitrary: xs)
    case (Cons y ys)
    have "linearize xs @ y # ys = linearize (append_queue y xs) @ ys"
      by (simp add: append_queue_rep)
    also have "\<dots> = linearize (fold append_queue ys (append_queue y xs))"
      by (rule Cons)
    finally show ?case
      by simp
  qed simp
qed

lemma mbuf_t_cases_code[code]: "mbuf_t_cases (MBuf2_t xs) = (case safe_hd xs of (None, xs') \<Rightarrow> (None, MBuf2_t xs')
  | (Some x, xs') \<Rightarrow> (Some x, MBuf2_t (tl_queue xs')))"
  by transfer' (auto simp: tl_queue_rep split: list.splits prod.splits option.splits dest: safe_hd_rep)

text \<open>
  The two code equations above take the buffer apart and put it back together more often than
  they need to: @{const mbuf_t_cases} asks @{const safe_hd} for a pair it immediately splits,
  and then calls @{const tl_queue} on a queue @{const safe_hd} has just rebuilt, while
  @{const mbuf_t_append} wraps and unwraps the queue once per appended element.  Asking for the
  head and the tail separately -- and appending in one pass -- allocates the pair once and the
  queue once.  In the empty case the buffer is returned unchanged, so nothing is allocated
  at all.
\<close>

lift_definition mbuf_t_hd :: "'a mbuf_t \<Rightarrow> 'a option" is
  "\<lambda>xs. case xs of [] \<Rightarrow> None | y # _ \<Rightarrow> Some y" .

lift_definition mbuf_t_tl :: "'a mbuf_t \<Rightarrow> 'a mbuf_t" is tl .

declare [[code drop: mbuf_t_cases mbuf_t_append]]

lemma mbuf_t_cases_alt[code]:
  "mbuf_t_cases b = (let a = mbuf_t_hd b in
     (a, case a of None \<Rightarrow> b | Some _ \<Rightarrow> mbuf_t_tl b))"
  by transfer (auto split: list.splits)

lemma mbuf_t_hd_code[code]: "mbuf_t_hd (MBuf2_t xs) = hd_queue xs"
  by transfer' (simp add: hd_queue_rep)

lemma mbuf_t_tl_code[code]: "mbuf_t_tl (MBuf2_t xs) = MBuf2_t (pop_queue xs)"
  by transfer' (simp add: pop_queue_rep)

lemma mbuf_t_append_code'[code]:
  "mbuf_t_append (MBuf2_t xs) ys = MBuf2_t (append_queue_list ys xs)"
  by transfer' (simp add: append_queue_list_rep)

type_synonym 'a mebuf2 = "'a table mbuf_t \<times> 'a table mbuf_t"
type_synonym 'a mebuft2 = "('a table) mbuf_t \<times> (nat set \<times> 'a table) mbuf_t"
type_synonym 'a mebufn = "'a table mbuf_t list"
type_synonym 'a mebuf2S = "'a table mbuf_t \<times> 'a table mbuf_t \<times> ts mbuf_t \<times> bool"

abbreviation (input) "init_mebuf2S \<equiv> (mbuf_t_empty, mbuf_t_empty, mbuf_t_empty, False)"

fun meprev_next :: "\<I> \<Rightarrow> event_data table mbuf_t \<Rightarrow> ts mbuf_t 
  \<Rightarrow> event_data table list \<times> event_data table mbuf_t \<times> ts mbuf_t" 
  where "meprev_next I xs ts = (case mbuf_t_cases xs of (None, xs') \<Rightarrow> ([], mbuf_t_empty, ts)
  | (Some x, xs') \<Rightarrow> (case mbuf_t_cases ts of (None, ts') \<Rightarrow> ([], x ## xs', mbuf_t_empty)
  | (Some t, ts') \<Rightarrow> (case mbuf_t_cases ts' of (None, ts'') \<Rightarrow> ([], x ## xs', t ## mbuf_t_empty)
  | (Some t', ts'') \<Rightarrow> (let (ys, zs) = meprev_next I xs' (t' ## ts'')
    in ((if mem I ((t' - t)) then x else empty_table) # ys, zs)))))"

fun mebuf2_add where
  "mebuf2_add xs' ys' (xs, ys) = (xs @@ xs', ys @@ ys')"

fun mebuf2S_add :: "event_data table list \<Rightarrow> event_data table list \<Rightarrow> ts list 
  \<Rightarrow> event_data mebuf2S \<Rightarrow> event_data mebuf2S" 
  where "mebuf2S_add xs' ys' ts' (xs, ys, ts, skew) = (xs @@ xs', ys @@ ys', ts @@ ts', skew)"

fun mebuf2_take where
  "mebuf2_take f (xs, ys) = (case mbuf_t_cases xs of (None, xs') \<Rightarrow> ([], (xs', ys)) | (Some x, xs') \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow> ([], (x ## xs', ys')) | (Some y, ys') \<Rightarrow>
    let (zs, buf) = mebuf2_take f (xs', ys') in (f x y # zs, buf)))"

fun mebuf2t_take :: "(event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow>
    event_data mebuf2 \<Rightarrow> ts \<Rightarrow> ts mbuf_t \<Rightarrow> 'b \<times> event_data mebuf2 \<times> ts \<times> ts mbuf_t" where
  "mebuf2t_take f z (xs, ys) t0 ts =
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> (z, (xs, ys), t0, ts') | (Some t, ts') \<Rightarrow>
    (case mbuf_t_cases xs of (None, xs') \<Rightarrow> (z, (xs', ys), t, t ## ts') | (Some x, xs') \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow> (z, (x ## xs', ys'), t, t ## ts') | (Some y, ys') \<Rightarrow>
    mebuf2t_take f (f x y t z) (xs', ys') t ts')))"

fun mebuf2T_take :: "(event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow>
    event_data mebuf2 \<Rightarrow> ts mbuf_t \<Rightarrow> 'b \<times> event_data mebuf2 \<times> ts mbuf_t" where
  "mebuf2T_take f z (xs, ys) ts =
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> (z, (xs, ys), ts') | (Some t, ts') \<Rightarrow>
    (case mbuf_t_cases xs of (None, xs') \<Rightarrow> (z, (xs', ys), t ## ts') | (Some x, xs') \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow> (z, (x ## xs', ys'), t ## ts') | (Some y, ys') \<Rightarrow>
    mebuf2T_take f (f x y t z) (xs', ys') ts')))" (* TODO: replace with mebuf2t_take *)

fun mebufn_add :: "event_data table list list \<Rightarrow> event_data mebufn \<Rightarrow> event_data mebufn" 
  where "mebufn_add xs' xs = List.map2 (@@) xs xs'"

lemma size_snd_mbuf_t_cases: "\<not> mbuf_t_is_empty a \<Longrightarrow> size (snd (mbuf_t_cases a)) < size a"
  by transfer (auto split: list.splits)

lemma size_list_snd_mbuf_t_cases: assumes "buf \<noteq> []" "\<And>x. x \<in> set buf \<Longrightarrow> \<not> mbuf_t_is_empty x"
  shows "size_list (\<lambda>x. size (snd (mbuf_t_cases x))) buf < size_list size buf"
  using assms
proof (induction buf)
  case IH: (Cons a buf)
  show ?case
  proof (cases buf)
    case Nil
    show ?thesis
      using IH(3) size_snd_mbuf_t_cases
      by (auto simp: Nil)
  next
    case (Cons a' buf')
    have "size_list (\<lambda>x. size (snd (mbuf_t_cases x))) buf < size_list size buf"
      using IH(1,3)
      by (auto simp: Cons)
    then show ?thesis
      using IH(3) size_snd_mbuf_t_cases
      by force
  qed
qed auto

function mebufn_take :: "(event_data table list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> event_data mebufn \<Rightarrow> 'b \<times> event_data mebufn" where
  "mebufn_take f z buf = (if buf = [] \<or> (\<exists>x \<in> set buf. mbuf_t_is_empty x) then (z, buf)
    else mebufn_take f (f (map (the \<circ> fst \<circ> mbuf_t_cases) buf) z) (map (snd \<circ> mbuf_t_cases) buf))"
  by pat_completeness auto
termination
  using size_list_snd_mbuf_t_cases
  by (relation "measure (\<lambda>(_, _, buf). size_list size buf)") (auto simp: comp_def Suc_le_eq size_list_length_diff1)

fun mebufnt_take :: "(event_data table list \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
    'b \<Rightarrow> event_data mebufn \<Rightarrow> ts \<Rightarrow> ts mbuf_t \<Rightarrow> 'b \<times> event_data mebufn \<times> ts \<times> ts mbuf_t" where
  "mebufnt_take f z buf t0 ts =
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> (z, buf, t0, ts) | (Some t, ts') \<Rightarrow>
    (if (\<exists>x \<in> set buf. mbuf_t_is_empty x) then (z, buf, t, t ## ts')
    else mebufnt_take f (f (map (the \<circ> fst \<circ> mbuf_t_cases) buf) t z) (map (snd \<circ> mbuf_t_cases) buf) t ts'))"

section \<open>Instantiation of the generic algorithm and code setup\<close>

(*
  The following snippet (context \<dots> end) is taken from HOL-Library.Code_Cardinality.
  We do not include the entire theory because the remaining code setup is superseded
  by Containers.
*)
context
begin

qualified definition card_UNIV' :: "'a card_UNIV"
where [code drop]: "card_UNIV' = Phantom('a) CARD('a)"

lemma CARD_code [code_unfold]:
  "CARD('a) = of_phantom (card_UNIV' :: 'a card_UNIV)"
by(simp add: card_UNIV'_def)

lemma card_UNIV'_code [code]:
  "card_UNIV' = card_UNIV"
by(simp add: card_UNIV card_UNIV'_def)

end

instantiation enat :: set_impl begin
definition set_impl_enat :: "(enat, set_impl) phantom" where
  "set_impl_enat = phantom set_RBT"

instance ..
end

derive ccompare Formula.trm
derive (eq) ceq Formula.trm
derive (rbt) set_impl Formula.trm
derive (eq) ceq Monitor.mregex
derive ccompare Monitor.mregex
derive (rbt) set_impl Monitor.mregex
derive (rbt) mapping_impl Monitor.mregex
derive (no) cenum Monitor.mregex
derive (rbt) set_impl string8
derive (rbt) mapping_impl string8
derive (rbt) set_impl event_data
derive (rbt) mapping_impl event_data

type_synonym 'a vmsaux = "nat \<times> (nat \<times> 'a table) list"

definition valid_vmsaux :: "args \<Rightarrow> nat \<Rightarrow> event_data vmsaux \<Rightarrow>
  (nat \<times> event_data table) list \<Rightarrow> bool" where
  "valid_vmsaux = (\<lambda>_ cur (t, aux) auxlist. t = cur \<and> aux = auxlist)"

definition init_vmsaux :: "args \<Rightarrow> event_data vmsaux" where
  "init_vmsaux = (\<lambda>_. (0, []))"

definition add_new_ts_vmsaux :: "args \<Rightarrow> nat \<Rightarrow> event_data vmsaux \<Rightarrow> event_data vmsaux" where
  "add_new_ts_vmsaux = (\<lambda>args nt (t, auxlist). (nt, filter (\<lambda>(t, rel).
    memR (args_ivl args) (nt - t)) auxlist))"

definition join_vmsaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data vmsaux \<Rightarrow> event_data vmsaux" where
  "join_vmsaux = (\<lambda>args rel1 (t, auxlist). (t, map (\<lambda>(t, rel).
    (t, join (args_R args) rel (args_pos args) (args_L args) rel1)) auxlist))"

definition add_new_table_vmsaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data vmsaux \<Rightarrow>
  event_data vmsaux" where
  "add_new_table_vmsaux = (\<lambda>args rel2 (cur, auxlist). (cur, (case auxlist of
    [] => [(cur, rel2)]
  | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)))"

definition result_vmsaux :: "args \<Rightarrow> event_data vmsaux \<Rightarrow> event_data table" where
  "result_vmsaux = (\<lambda>args (cur, auxlist). eval_args_agg args
    (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}))"

type_synonym 'a vmuaux = "nat \<times> (nat \<times> 'a table \<times> 'a table) list"

definition valid_vmuaux :: "args \<Rightarrow> nat \<Rightarrow> event_data vmuaux \<Rightarrow>
  (nat \<times> event_data table \<times> event_data table) list \<Rightarrow> bool" where
  "valid_vmuaux = (\<lambda>_ cur (t, aux) auxlist. t = cur \<and> aux = auxlist)"

definition init_vmuaux :: "args \<Rightarrow> event_data vmuaux" where
  "init_vmuaux = (\<lambda>_. (0, []))"

definition add_new_vmuaux ::  "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> nat \<Rightarrow>
  event_data vmuaux \<Rightarrow> event_data vmuaux" where
  "add_new_vmuaux = (\<lambda>args rel1 rel2 nt (t, auxlist). (nt, update_until args rel1 rel2 nt auxlist))"

definition length_vmuaux :: "args \<Rightarrow> event_data vmuaux \<Rightarrow> nat" where
  "length_vmuaux = (\<lambda>_ (_, auxlist). length auxlist)"

definition eval_vmuaux :: "args \<Rightarrow> nat \<Rightarrow> event_data vmuaux \<Rightarrow>
  event_data table list \<times> event_data vmuaux" where
  "eval_vmuaux = (\<lambda>args nt (t, auxlist).
    (let (res, auxlist') = eval_until (args_ivl args) nt auxlist in (map (eval_args_agg args)res, (t, auxlist'))))"

global_interpretation verimon_maux: maux_ops init_vmsaux add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux result_vmsaux init_vmuaux add_new_vmuaux length_vmuaux eval_vmuaux init_mmtaux update_mmtaux result_mmtaux bin_join mmulti_join
  defines vminit0 = "maux_ops.minit0 (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: _ \<Rightarrow> ty Formula.formula \<Rightarrow> _"
  and vminit = "maux_ops.minit (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: ty Formula.formula \<Rightarrow> _"
  and vminit_safe = "maux_ops.minit_safe (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: ty Formula.formula \<Rightarrow> _"
  and vmeval_since = "maux_ops.eval_since add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> event_data table)"
  and vmeval = "maux_ops.meval add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _) update_mmtaux result_mmtaux bin_join mmulti_join"
  and letpast_vmeval = "maux_ops.letpast_meval add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _) update_mmtaux result_mmtaux bin_join mmulti_join"
  and vmstep = "maux_ops.mstep add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _) update_mmtaux result_mmtaux bin_join mmulti_join"
  and vmsteps0_stateless = "maux_ops.msteps0_stateless add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _) update_mmtaux result_mmtaux bin_join mmulti_join"
  and vmsteps_stateless = "maux_ops.msteps_stateless add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _) update_mmtaux result_mmtaux bin_join mmulti_join"
  and vmonitor = "maux_ops.monitor init_vmsaux add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) init_vmuaux add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _) init_mmtaux update_mmtaux result_mmtaux bin_join mmulti_join"
  .

global_interpretation default_maux: maux_ops "init_mmasaux :: _ \<Rightarrow> mmasaux" add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux result_mmasaux "init_muaux_dq :: _ \<Rightarrow> muaux_dq" add_new_muaux_dq length_muaux_dq eval_muaux_dq init_mmtaux update_mmtaux result_mmtaux bin_join mmulti_join
  defines minit0 = "maux_ops.minit0 (init_mmasaux :: _ \<Rightarrow> mmasaux) (init_muaux_dq :: _ \<Rightarrow> muaux_dq) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: _ \<Rightarrow> ty Formula.formula \<Rightarrow> _"
  and minit = "maux_ops.minit (init_mmasaux :: _ \<Rightarrow> mmasaux) (init_muaux_dq :: _ \<Rightarrow> muaux_dq) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: ty Formula.formula \<Rightarrow> _"
  and minit_safe = "maux_ops.minit_safe (init_mmasaux :: _ \<Rightarrow> mmasaux) (init_muaux_dq :: _ \<Rightarrow> muaux_dq) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: ty Formula.formula \<Rightarrow> _"
  and meval_since = "maux_ops.eval_since add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> event_data table)"
  and meval = "maux_ops.meval add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux bin_join mmulti_join"
  and letpast_meval = "maux_ops.letpast_meval add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux bin_join mmulti_join"
  and mstep = "maux_ops.mstep add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux bin_join mmulti_join"
  and msteps0_stateless = "maux_ops.msteps0_stateless add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux bin_join mmulti_join"
  and msteps_stateless = "maux_ops.msteps_stateless add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux bin_join mmulti_join"
  and monitor = "maux_ops.monitor init_mmasaux add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) init_muaux_dq add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) init_mmtaux update_mmtaux result_mmtaux bin_join mmulti_join"
  .

definition "RPDs_aux = saturate (\<lambda>S. S \<union> \<Union> (RPD ` S))"

lemma RPDs_aux_code[code]:
  "RPDs_aux S = (let S' = S \<union> Set.bind S RPD in if S' \<subseteq> S then S else RPDs_aux S')"
  unfolding RPDs_aux_def bind_UNION
  by (subst saturate_code) auto

declare RPDs_code[code drop]
lemma RPDs_code[code]: "RPDs r = RPDs_aux {r}"
  unfolding RPDs_aux_def RPDs_code
  by (rule saturate_commute[where C="RPDs r"])
     (auto 0 3 simp: mono_def subset_singleton_iff RPDs_refl RPDs_trans finite_RPDs)

definition "LPDs_aux = saturate (\<lambda>S. S \<union> \<Union> (LPD ` S))"

lemma LPDs_aux_code[code]:
  "LPDs_aux S = (let S' = S \<union> Set.bind S LPD in if S' \<subseteq> S then S else LPDs_aux S')"
  unfolding LPDs_aux_def bind_UNION
  by (subst saturate_code) auto

declare LPDs_code[code drop]
lemma LPDs_code[code]: "LPDs r = LPDs_aux {r}"
  unfolding LPDs_aux_def LPDs_code
  by (rule saturate_commute[where C="LPDs r"])
     (auto 0 3 simp: mono_def subset_singleton_iff LPDs_refl LPDs_trans finite_LPDs)

lemma is_empty_table_unfold [code_unfold]:
  "X = empty_table \<longleftrightarrow> Set.is_empty X"
  "empty_table = X \<longleftrightarrow> Set.is_empty X"
  "set_eq X empty_table \<longleftrightarrow> Set.is_empty X"
  "set_eq empty_table X \<longleftrightarrow> Set.is_empty X"
  "X = (set_empty impl) \<longleftrightarrow> Set.is_empty X"
  "(set_empty impl) = X \<longleftrightarrow> Set.is_empty X"
  "set_eq (set_empty impl) X \<longleftrightarrow> Set.is_empty X"
  "set_eq X (set_empty impl) \<longleftrightarrow> Set.is_empty X"
  unfolding set_eq_def set_empty_def empty_table_def
  by auto

lemma tabulate_rbt_code[code]: "Monitor.mrtabulate (xs :: mregex list) f =
  (case ID CCOMPARE(mregex) of None \<Rightarrow> Code.abort (STR ''mrtabulate RBT_Mapping: ccompare = None'') (\<lambda>_. Monitor.mrtabulate (xs :: mregex list) f)
  | _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.bulkload (List.map_filter (\<lambda>k. let fk = f k in if fk = empty_table then None else Some (k, fk)) xs)))"
  unfolding mrtabulate.abs_eq RBT_Mapping_def
  by (auto split: option.splits)

declare [[code drop: lexordp_eq]]

lemma lexordp_eq_code[code]: "lexordp_eq xs ys \<longleftrightarrow> (case xs of [] \<Rightarrow> True
  | x # xs \<Rightarrow> (case ys of [] \<Rightarrow> False
    | y # ys \<Rightarrow> if x < y then True else if x > y then False else lexordp_eq xs ys))"
  by (subst lexordp_eq.simps) (auto split: list.split)

declare [[code drop: shift_end]]
declare shift_end.simps[folded filter_mapping_def filter_set'_def, code]

definition upd_nested_max_tstp where
  "upd_nested_max_tstp m d X = upd_nested m d (max_tstp d) X"

lemma upd_nested_max_tstp_fold:
  assumes "finite X"
  shows "upd_nested_max_tstp m d X = Finite_Set.fold (upd_nested_step d (max_tstp d)) m X"
proof -
  interpret comp_fun_idem "upd_nested_step d (max_tstp d)"
    by (unfold_locales; rule ext)
      (auto simp add: comp_def upd_nested_step_def Mapping.lookup_update'
       update_update max_tstp_d_d max_tstp_idem' split: option.splits)
  note upd_nested_insert' = upd_nested_insert[of d "max_tstp d",
    OF max_tstp_d_d[symmetric] max_tstp_idem']
  show ?thesis
    using assms
    by (induct X arbitrary: m rule: finite.induct)
      (auto simp add: upd_nested_max_tstp_def upd_nested_insert')
qed

lift_definition upd_nested_max_tstp_cfi ::
  "ts + tp \<Rightarrow> ('a \<times> 'b, ('a, ('b, ts + tp) mapping) mapping) comp_fun_idem"
  is "\<lambda>d. upd_nested_step d (max_tstp d)"
  by (unfold_locales; rule ext)
    (auto simp add: comp_def upd_nested_step_def Mapping.lookup_update'
      update_update max_tstp_d_d max_tstp_idem' split: option.splits)

lemma upd_nested_max_tstp_code[code]:
  "upd_nested_max_tstp m d X = (if finite X then set_fold_cfi (upd_nested_max_tstp_cfi d) m X
    else Code.abort (STR ''upd_nested_max_tstp: infinite'') (\<lambda>_. upd_nested_max_tstp m d X))"
  by transfer (auto simp add: upd_nested_max_tstp_fold)

definition "filter_join pos X m = Mapping.filter (join_filter_cond pos X) m"

declare [[code drop: join_mmsaux]]
declare join_mmsaux.simps[folded filter_join_def, code]

declare [[code drop: New_max_getIJ_genericJoin New_max_getIJ_wrapperGenericJoin]]
declare New_max.genericJoin_code[folded remove_Union_def, code]
declare New_max.wrapperGenericJoin.simps[folded remove_Union_def, code]

lemma group_images: "(\<lambda>k. let group = Set.filter (\<lambda>x. f x = k) rel in g k group) ` f ` rel =
    (\<lambda>(k, group). g k group) ` images ((\<lambda>t. (f t, t)) ` rel)"
proof (rule set_eqI, rule iffI)
  fix x
  assume "x \<in> (\<lambda>k. Let (Set.filter (\<lambda>x. f x = k) rel) (g k)) ` f ` rel"
  then obtain t where t_def: "t \<in> rel" "x = g (f t) {x \<in> rel. f x = f t}"
    by auto
  have "(f t, {b. (f t, b) \<in> (\<lambda>t. (f t, t)) ` rel}) \<in>
    (\<lambda>a. (a, {b. (a, b) \<in> (\<lambda>t. (f t, t)) ` rel})) ` fst ` (\<lambda>t. (f t, t)) ` rel"
    using t_def(1)
    by force
  moreover have "{b. (f t, b) \<in> (\<lambda>t. (f t, t)) ` rel} = {x \<in> rel. f x = f t}"
    by (auto simp add: image_def)
  ultimately show "x \<in> (\<lambda>(k, group). g k group) ` images ((\<lambda>t. (f t, t)) ` rel)"
    unfolding t_def(2) images_def
    by auto
next
  fix x
  assume "x \<in> (\<lambda>(k, group). g k group) ` images ((\<lambda>t. (f t, t)) ` rel)"
  then obtain t where t_def: "t \<in> rel" "x = g (f t) {b. (f t, b) \<in> (\<lambda>t. (f t, t)) ` rel}"
    by (auto simp: images_def)
  have "{b. (f t, b) \<in> (\<lambda>t. (f t, t)) ` rel} = {x \<in> rel. f x = f t}"
    by (auto simp add: image_def)
  then show "x \<in> (\<lambda>k. Let (Set.filter (\<lambda>x. f x = k) rel) (g k)) ` f ` rel"
    using t_def(1)
    by (auto simp: t_def(2))
qed

lemma eval_agg_code[code]: "eval_agg cs g0 \<omega> tys f rel = (if g0 \<and> rel = empty_table
  then singleton_table (eval_agg_op \<omega> {})
  else (\<lambda>(k, group). let M = (\<lambda>(e, ts). (e, ecard ts)) ` images ((\<lambda>t. (meval_trm cs f t, t)) ` group) in
    eval_agg_op \<omega> M # k) ` images ((\<lambda>t. (agg_key (length tys) cs t, t)) ` rel))"
proof -
  have "(\<lambda>k. let group = Set.filter (\<lambda>x. agg_key (length tys) cs x = k) rel;
      M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group in
      eval_agg_op \<omega> M # k) ` agg_key (length tys) cs ` rel =
    (\<lambda>(k, group). let M = (\<lambda>(e, ts). (e, ecard ts)) ` images ((\<lambda>t. (meval_trm cs f t, t)) ` group) in
      eval_agg_op \<omega> M # k) ` images ((\<lambda>t. (agg_key (length tys) cs t, t)) ` rel)"
    unfolding Let_def group_images[of "agg_key (length tys) cs" rel
      "(\<lambda>k g. eval_agg_op \<omega> ((\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) g))) ` meval_trm cs f ` g) # k)", unfolded Let_def]
    unfolding group_images[of "meval_trm cs f" _ "(\<lambda>y g. (y, ecard g))", unfolded Let_def]
    by simp
  then show ?thesis
    by (auto simp: eval_agg_def)
qed


declare regex.pred_inject[code]

declare regex.pred_set[THEN fun_cong, symmetric, code_unfold]

lemma Bex_pred_regex[code_unfold]: "Bex (regex.atms x) P \<longleftrightarrow> \<not> regex.pred_regex (Not o P) x"
  by (induct x) auto


derive (eq) ceq rec_safety
derive ccompare rec_safety
derive (dlist) set_impl rec_safety

declare [[code drop: safe_letpast]]
lemma safe_letpast_code[code]:
  "safe_letpast p (Formula.Eq t1 t2) = Unused"
  "safe_letpast p (Formula.Less t1 t2) = Unused"
  "safe_letpast p (Formula.LessEq t1 t2) = Unused"
  "safe_letpast p (Formula.Pred e ts) = (if p = (e, length ts) then NonFutuRec else Unused)"
  "safe_letpast p (Formula.Let e \<phi> \<psi>) =
      (safe_letpast (e, Formula.nfv \<phi>) \<psi> * safe_letpast p \<phi>) \<squnion>
      (if p = (e, Formula.nfv \<phi>) then Unused else safe_letpast p \<psi>)"
  "safe_letpast p (Formula.Frz e \<phi> \<psi>) =
      (frz_dep (safe_letpast (e, Formula.nfv \<phi>) \<psi>) (safe_letpast p \<phi>)) \<squnion>
      (if p = (e, Formula.nfv \<phi>) then Unused else safe_letpast p \<psi>)"
  "safe_letpast p (Formula.LetPast e \<phi> \<psi>) =
      (if p = (e, Formula.nfv \<phi>) then Unused else
        (safe_letpast (e, Formula.nfv \<phi>) \<psi> * safe_letpast p \<phi>) \<squnion> safe_letpast p \<psi>)"
  "safe_letpast p (Formula.Neg \<phi>) = safe_letpast p \<phi>"
  "safe_letpast p (Formula.Or \<phi> \<psi>) = (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  "safe_letpast p (Formula.And \<phi> \<psi>) = (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  "safe_letpast p (Formula.Ands l) = \<Squnion> set (map (safe_letpast p) l)"
  "safe_letpast p (Formula.Exists ty \<phi>) = safe_letpast p \<phi>"
  "safe_letpast p (Formula.Agg y \<omega> b' f \<phi>) = safe_letpast p \<phi>"
  "safe_letpast p (Formula.Prev I \<phi>) = PastRec * safe_letpast p \<phi>"
  "safe_letpast p (Formula.Next I \<phi>) = AnyRec * safe_letpast p \<phi>"
  "safe_letpast p (Formula.Since \<phi> I \<psi>) = safe_letpast p \<phi> \<squnion>
    (if memL I 0 then NonFutuRec else PastRec) * safe_letpast p \<psi>"
  "safe_letpast p (Formula.Until \<phi> I \<psi>) = AnyRec * (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  "safe_letpast p (Formula.Trigger \<phi> I \<psi>) = safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>"
  "safe_letpast p (Formula.Release \<phi> I \<psi>) = AnyRec * (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  "safe_letpast p (Formula.MatchP I r) = \<Squnion> Regex.atms (Regex.map_regex (safe_letpast p) r)"
  "safe_letpast p (Formula.MatchF I r) =  AnyRec * \<Squnion> Regex.atms (Regex.map_regex (safe_letpast p) r)"
  "safe_letpast p (Formula.TP t) = Unused"
  "safe_letpast p (Formula.TS t) = Unused"
  by (auto simp add: regex.set_map)

lemma Sup_rec_safety_set[code_unfold]:
  "\<Squnion> (set l :: rec_safety set) = fold (\<squnion>) l Unused"
  by (simp add: Sup_rec_safety_def comp_fun_idem_on.fold_set_fold[OF comp_fun_idem_sup[unfolded comp_fun_idem_def']])

lemma Sup_rec_safety_atms[code_unfold]:
  "\<Squnion> (Regex.atms r :: rec_safety set) = fold (\<squnion>) (csorted_list_of_set (Regex.atms r)) Unused"
  by (simp add: Sup_rec_safety_def csorted_list_of_set_def ccompare_rec_safety_def ID_def
      linorder.set_sorted_list_of_set[OF comparator.linorder] comparator_rec_safety
      flip: comp_fun_idem_on.fold_set_fold[OF comp_fun_idem_sup[unfolded comp_fun_idem_def']])

lift_definition delete_cnt_cfc::"aggargs \<Rightarrow> (event_data tuple, (bool \<times> nat agg_map)) comp_fun_commute" is
  "\<lambda>args. delete_cnt args" using delete_cnt_comm by unfold_locales auto

lemma delete_cnt_code[code_unfold]: "Finite_Set.fold (delete_cnt args) (v, m) data = set_fold_cfc (delete_cnt_cfc args) (v, m) data"
  by(transfer) auto

lift_definition delete_sum_cfc::"aggargs \<Rightarrow> (event_data tuple, (bool \<times> ((nat \<times> integer) agg_map))) comp_fun_commute" is
  "\<lambda>args. delete_sum args" using delete_sum_comm by unfold_locales auto

lemma delete_sum_code[code_unfold]: "Finite_Set.fold (delete_sum args) (v, m) data = set_fold_cfc (delete_sum_cfc args) (v, m) data"
  by(transfer) auto

lift_definition delete_rank_cfc::"aggargs \<Rightarrow> type \<Rightarrow> (event_data tuple, bool \<times> list_aux agg_map) comp_fun_commute" is
  "\<lambda>args. delete_rank args" using delete_rank_comm by unfold_locales auto

lemma delete_rank_code[code_unfold]: "Finite_Set.fold (delete_rank args type) (v, m) data = set_fold_cfc (delete_rank_cfc args type) (v, m) data"
  by(transfer) auto

lift_definition insert_cnt_cfc::"aggargs \<Rightarrow> (event_data tuple, (bool \<times> nat agg_map)) comp_fun_commute" is
  "\<lambda>args. insert_cnt args" using insert_cnt_comm by unfold_locales auto

lemma insert_cnt_code[code_unfold]: "Finite_Set.fold (insert_cnt args) (v, m) data = set_fold_cfc (insert_cnt_cfc args) (v, m) data"
  by(transfer) auto

lift_definition insert_sum_cfc::"aggargs \<Rightarrow> (event_data tuple, (bool \<times> ((nat \<times> integer) agg_map))) comp_fun_commute" is
  "\<lambda>args. insert_sum args" using insert_sum_comm by unfold_locales auto

lemma insert_sum_code[code_unfold]: "Finite_Set.fold (insert_sum args) (v, m) data = set_fold_cfc (insert_sum_cfc args) (v, m) data"
  by(transfer) auto

lift_definition insert_rank_cfc::"aggargs \<Rightarrow> type \<Rightarrow> (event_data tuple, bool \<times> list_aux agg_map) comp_fun_commute" is
  "\<lambda>args. insert_rank args" using insert_rank_comm by unfold_locales auto

lemma insert_rank_code[code_unfold]: "Finite_Set.fold (insert_rank args type) (v, m) data = set_fold_cfc (insert_rank_cfc args type) (v, m) data"
  by(transfer) auto

lemma set_diff_code[code_unfold]: "X - Mapping.keys tuple_in = Set.filter (\<lambda>k. Mapping.lookup tuple_in k = None) X"
  by(transfer) auto

lemma add_new_mmuaux_code[code]: 
  "add_new_mmuaux args rel1 rel2 nt aux =
    (let (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done) =
    shift_mmuaux args nt aux;
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tstp_map = Mapping.update tp nt tstp_map;
    tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (restrict (args_L args) (args_R args) as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {});
    tmp = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp;
    table = snd ` tmp;
    tables = append_queue (table, if memL I 0 then Inr tp else Inl nt) tables;
    a2_map = Mapping.update (tp + 1) Mapping.empty
      (upd_nested_max_tstp a2_map new_tstp tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    tss = append_queue nt tss in
    (tp + 1, tss, tables, len + 1, result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp), a1_map, a2_map, tstp_map, done))" 
  by(auto simp: upd_nested_max_tstp_def add_new_mmuaux_def split:option.splits prod.splits)

lemma add_new_mmauaux_code[code]:
  "add_new_mmauaux args rel1 rel2 nt (mmuaux, aggaux) =
    (case args_agg args of 
     None \<Rightarrow> let (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done) = add_new_mmuaux args rel1 rel2 nt mmuaux in
  ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), aggaux) |
     Some aggargs \<Rightarrow>
    (let ((tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done), aggaux) = shift_mmauaux args nt (mmuaux, aggaux);
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tstp_map = Mapping.update tp nt tstp_map;
    m = case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow> m;
    tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (restrict (args_L args) (args_R args) as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {});
    tmp = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp;
    table = snd ` tmp;
    tables = append_queue (table, if memL I 0 then Inr tp else Inl nt) tables;
    a2_map' = Mapping.update (tp + 1) Mapping.empty
      (upd_nested_max_tstp a2_map new_tstp tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    to_add = to_add_set (tp - len) m tmp;
    aggaux = insert_maggaux' aggargs to_add aggaux;
    tss = append_queue nt tss in
    ((tp + 1, tss, tables, len + 1, result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp), a1_map, a2_map', tstp_map, done), aggaux)))"
  by(auto simp add: to_add_set_def  upd_nested_max_tstp_def split:option.splits prod.splits)

definition empty_db :: database where "empty_db = Mapping.empty"

definition insert_into_db :: "string8 \<times> nat \<Rightarrow> event_data tuple \<Rightarrow> database \<Rightarrow> database" where
  "insert_into_db p xs db = update_mapping_with (\<lambda>_ tbl _. map (Set.insert xs) tbl) p [{xs}] db"

definition rbt_fold :: "_ \<Rightarrow> event_data tuple set_rbt \<Rightarrow> _ \<Rightarrow> _" where
  "rbt_fold = RBT_Set2.fold"

fun finite_multiset_insert_fun :: "event_data \<times> enat \<Rightarrow> bool \<Rightarrow> bool" where
  "finite_multiset_insert_fun (_, k) v = ((if k = Extended_Nat.infinity then False else True) \<and> v)"

lemma finite_mset_insert_idem: 
  "comp_fun_idem finite_multiset_insert_fun"
proof -
   have *: "(finite_multiset_insert_fun (a, b) \<circ> finite_multiset_insert_fun (c, d)) e =
       (finite_multiset_insert_fun (c, d) \<circ> finite_multiset_insert_fun (a, b)) e" for a b c d e by auto
  then have aux1: "(finite_multiset_insert_fun (a, b) \<circ> finite_multiset_insert_fun (c, d)) =
       (finite_multiset_insert_fun (c, d) \<circ> finite_multiset_insert_fun (a, b))" for a b c d 
    using *[of a b c d] by presburger
  have *: "(finite_multiset_insert_fun (a, b) \<circ> finite_multiset_insert_fun (a, b)) c =
       (finite_multiset_insert_fun (a, b) c)" for a b c by auto
  then have aux2: "finite_multiset_insert_fun (a, b) \<circ> finite_multiset_insert_fun (a, b) =
       finite_multiset_insert_fun (a, b)" for a b using *[of a b] by presburger
  show ?thesis
    using aux1 aux2 by unfold_locales auto
qed

lemma finite_multiset_eq:
  assumes "finite M"
  shows "finite_multiset M = 
         Finite_Set.fold finite_multiset_insert_fun True M"
proof -
  interpret comp_fun_idem finite_multiset_insert_fun
    using finite_mset_insert_idem by auto
  from assms show ?thesis
  proof (induction M)
    case empty
    then show ?case by(auto simp:finite_multiset_def)
  next
    case (insert a A)
    have fin: "finite ((\<lambda>(x, y). case_enat (\<lambda>nat. True) False y) ` A)"
      using insert(1) by auto
    obtain s e where a_def: "a = (s, e)" by force
    then show ?case unfolding fold_insert[OF insert(1-2)] unfolding a_def
      using insert(3) by(cases e) (auto simp:finite_multiset_def)
  qed 
qed

lift_definition finite_multiset_cfi :: "(event_data \<times> enat, bool) comp_fun_idem" is 
  "finite_multiset_insert_fun"
  using finite_mset_insert_idem .

lemma finite_multiset_code[code]:
  "finite_multiset M = (if finite M then set_fold_cfi finite_multiset_cfi True M else False)"
  using finite_multiset_def finite_multiset_eq by transfer auto

(*<*)
end
(*>*)

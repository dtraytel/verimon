(*<*)
theory Monitor_Impl
  imports
    Optimized_Trigger
    Optimized_Agg_Temporal
    Optimized_Until_Deque
    "HOL-Library.Code_Target_Nat"
    Containers.Containers
    "VeriMon_Base.Proj_Code"
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

lemma Rep_mbuf_t_cases[simp]:
  "mbuf_t_cases xs = (None, xs') \<Longrightarrow> Rep_mbuf_t xs = []"
  "mbuf_t_cases xs = (None, xs') \<Longrightarrow> Rep_mbuf_t xs' = []"
  "mbuf_t_cases xs = (Some x, xs') \<Longrightarrow> Rep_mbuf_t xs = x # Rep_mbuf_t xs'"
  subgoal by transfer (auto split: option.splits list.splits)
  subgoal by transfer (auto split: option.splits list.splits)
  subgoal by transfer (auto split: option.splits list.splits)
  done

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

lemma meprev_next: "meprev_next I xs ts = (zs, xs', ts') \<Longrightarrow> mprev_next I (Rep_mbuf_t xs) (Rep_mbuf_t ts) =
  (zs, Rep_mbuf_t xs', Rep_mbuf_t ts')"
proof (induction I xs ts arbitrary: zs xs' ts' rule: meprev_next.induct)
  case (1 I xs ts)
  obtain xo xs'' where xs_def: "mbuf_t_cases xs = (xo, xs'')"
    by fastforce
  obtain to ts'' where ts_def: "mbuf_t_cases ts = (to, ts'')"
    by fastforce
  obtain to' ts''' where ts''_def: "mbuf_t_cases ts'' = (to', ts''')"
    by fastforce
  show ?case
    using 1
    by (cases xo; cases to; cases to')
       (auto simp: xs_def ts_def ts''_def mbuf_t_empty.rep_eq mbuf_t_Cons.rep_eq split: prod.splits)
qed

fun mebuf2_add where
  "mebuf2_add xs' ys' (xs, ys) = (xs @@ xs', ys @@ ys')"

lemma mbuf2_add: "mbuf2_add xs ys (map_prod Rep_mbuf_t Rep_mbuf_t buf) 
  = map_prod Rep_mbuf_t Rep_mbuf_t (mebuf2_add xs ys buf)"
  by (cases buf) (auto simp: mbuf_t_append.rep_eq)

fun mebuf2S_add :: "event_data table list \<Rightarrow> event_data table list \<Rightarrow> ts list 
  \<Rightarrow> event_data mebuf2S \<Rightarrow> event_data mebuf2S" 
  where "mebuf2S_add xs' ys' ts' (xs, ys, ts, skew) = (xs @@ xs', ys @@ ys', ts @@ ts', skew)"

fun mebuf2_take where
  "mebuf2_take f (xs, ys) = (case mbuf_t_cases xs of (None, xs') \<Rightarrow> ([], (xs', ys)) | (Some x, xs') \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow> ([], (x ## xs', ys')) | (Some y, ys') \<Rightarrow>
    let (zs, buf) = mebuf2_take f (xs', ys') in (f x y # zs, buf)))"

lemma mebuf2_take_aux: "mebuf2_take f (xs, ys) = (zs, (xs', ys')) \<Longrightarrow>
  mbuf2_take f (Rep_mbuf_t xs, Rep_mbuf_t ys) = (zs, (Rep_mbuf_t xs', Rep_mbuf_t ys'))"
proof (induction f "(xs, ys)" arbitrary: xs ys zs xs' ys' rule: mebuf2_take.induct)
  case (1 f xs ys)
  obtain x xs'' where xs_def: "mbuf_t_cases xs = (x, xs'')"
    by fastforce
  obtain y ys'' where ys_def: "mbuf_t_cases ys = (y, ys'')"
    by fastforce
  show ?case
    using 1 xs_def ys_def
    by (cases x; cases y) (auto simp: mbuf_t_Cons.rep_eq split: prod.splits)
qed

lemma mebuf2_take: "mebuf2_take f buf = (zs, buf') \<Longrightarrow>
  mbuf2_take f (map_prod Rep_mbuf_t Rep_mbuf_t buf) = (zs, (map_prod Rep_mbuf_t Rep_mbuf_t buf'))"
  using mebuf2_take_aux
  by (cases buf; cases buf') fastforce

fun mebuf2t_take :: "(event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow>
    event_data mebuf2 \<Rightarrow> ts \<Rightarrow> ts mbuf_t \<Rightarrow> 'b \<times> event_data mebuf2 \<times> ts \<times> ts mbuf_t" where
  "mebuf2t_take f z (xs, ys) t0 ts =
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> (z, (xs, ys), t0, ts') | (Some t, ts') \<Rightarrow>
    (case mbuf_t_cases xs of (None, xs') \<Rightarrow> (z, (xs', ys), t, t ## ts') | (Some x, xs') \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow> (z, (x ## xs', ys'), t, t ## ts') | (Some y, ys') \<Rightarrow>
    mebuf2t_take f (f x y t z) (xs', ys') t ts')))"

lemma mebuf2t_take_aux: "mebuf2t_take f z (xs, ys) t ts = (zs, (xs', ys'), nt, ts') \<Longrightarrow>
  mbuf2t_take f z (Rep_mbuf_t xs, Rep_mbuf_t ys) t (Rep_mbuf_t ts) = (zs, (Rep_mbuf_t xs', Rep_mbuf_t ys'), nt, Rep_mbuf_t ts')"
proof (induction f z "(xs, ys)" t ts arbitrary: xs ys rule: mebuf2t_take.induct)
  case (1 f z xs ys t ts)
  obtain x xs'' where xs_def: "mbuf_t_cases xs = (x, xs'')"
    by fastforce
  obtain y ys'' where ys_def: "mbuf_t_cases ys = (y, ys'')"
    by fastforce
  obtain t ts'' where ts_def: "mbuf_t_cases ts = (t, ts'')"
    by fastforce
  show ?case
    using 1 xs_def ys_def ts_def
    by (cases x; cases y; cases t) (auto simp: mbuf_t_Cons.rep_eq split: prod.splits list.splits)
qed

lemma mebuf2t_take: "mebuf2t_take f z buf t ts = (zs, buf', nt, nts) \<Longrightarrow>
  mbuf2t_take f z (map_prod Rep_mbuf_t Rep_mbuf_t buf) t (Rep_mbuf_t ts) = (zs, (map_prod Rep_mbuf_t Rep_mbuf_t buf'), nt, Rep_mbuf_t nts)"
  using mebuf2t_take_aux
  by (cases buf; cases buf') fastforce

fun mebuf2T_take :: "(event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow>
    event_data mebuf2 \<Rightarrow> ts mbuf_t \<Rightarrow> 'b \<times> event_data mebuf2 \<times> ts mbuf_t" where
  "mebuf2T_take f z (xs, ys) ts =
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> (z, (xs, ys), ts') | (Some t, ts') \<Rightarrow>
    (case mbuf_t_cases xs of (None, xs') \<Rightarrow> (z, (xs', ys), t ## ts') | (Some x, xs') \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow> (z, (x ## xs', ys'), t ## ts') | (Some y, ys') \<Rightarrow>
    mebuf2T_take f (f x y t z) (xs', ys') ts')))" (* TODO: replace with mebuf2t_take *)

lemma mebuf2T_take_aux: "mebuf2T_take f z (xs, ys) ts = (zs, (xs', ys'), ts') \<Longrightarrow>
  mbuf2T_take f z (Rep_mbuf_t xs, Rep_mbuf_t ys) (Rep_mbuf_t ts) = (zs, (Rep_mbuf_t xs', Rep_mbuf_t ys'), Rep_mbuf_t ts')"
proof (induction f z "(xs, ys)" ts arbitrary: xs ys rule: mebuf2T_take.induct)
  case (1 f z xs ys ts)
  obtain x xs'' where xs_def: "mbuf_t_cases xs = (x, xs'')"
    by fastforce
  obtain y ys'' where ys_def: "mbuf_t_cases ys = (y, ys'')"
    by fastforce
  obtain t ts'' where ts_def: "mbuf_t_cases ts = (t, ts'')"
    by fastforce
  show ?case
    using 1 xs_def ys_def ts_def
    by (cases x; cases y; cases t) (auto simp: mbuf_t_Cons.rep_eq split: prod.splits list.splits)
qed

lemma mebuf2T_take: "mebuf2T_take f z buf ts = (zs, buf', nts) \<Longrightarrow>
  mbuf2T_take f z (map_prod Rep_mbuf_t Rep_mbuf_t buf) (Rep_mbuf_t ts) = (zs, (map_prod Rep_mbuf_t Rep_mbuf_t buf'), Rep_mbuf_t nts)"
  using mebuf2T_take_aux
  by (cases buf; cases buf') 
    fastforce

fun mebufn_add :: "event_data table list list \<Rightarrow> event_data mebufn \<Rightarrow> event_data mebufn" 
  where "mebufn_add xs' xs = List.map2 (@@) xs xs'"

lemma mbufn_add: "mbufn_add xss (map Rep_mbuf_t buf) = map Rep_mbuf_t (mebufn_add xss buf)"
  by (auto simp: comp_def zip_map1 mbuf_t_append.rep_eq)

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

lemma mbuf_t_is_empty_in_set: "[] \<in> set (map Rep_mbuf_t buf) \<longleftrightarrow> (\<exists>x \<in> set buf. mbuf_t_is_empty x)"
  by transfer auto

lemma hd_Rep_mbuf_t:
  assumes "\<And>x. x \<in> set buf \<Longrightarrow> \<not> mbuf_t_is_empty x"
  shows "map (hd \<circ> Rep_mbuf_t) buf = map (the \<circ> fst \<circ> mbuf_t_cases) buf"
  using assms
  by transfer (auto split: list.splits)

lemma tl_Rep_mbuf_t:
  assumes "\<And>x. x \<in> set buf \<Longrightarrow> \<not> mbuf_t_is_empty x"
  shows "map (tl \<circ> Rep_mbuf_t) buf = map Rep_mbuf_t (map (snd \<circ> mbuf_t_cases) buf)"
  using assms
  by transfer (auto split: list.splits)

lemma mebufn_take: "mebufn_take f z buf = (z', buf') \<Longrightarrow>
  mbufn_take f z (map Rep_mbuf_t buf) = (z', map Rep_mbuf_t buf')"
proof (induction f z buf arbitrary: z' buf' rule: mebufn_take.induct)
  case (1 f z buf)
  show ?case
    using 1(1,2)
    unfolding mebufn_take.simps[of _ _ buf] mbufn_take.simps[of _ _ "map Rep_mbuf_t buf"] mbuf_t_is_empty_in_set map_is_Nil_conv
    by (auto simp del: mbufn_take.simps mebufn_take.simps simp: hd_Rep_mbuf_t tl_Rep_mbuf_t split: if_splits)
qed

lemma mbufn_take_app: "mbufn_take (\<lambda>xs zs. zs @@ [f xs]) zs buf = (buf', zs') \<Longrightarrow>
  mbufn_take (\<lambda>xs zs. zs @ [f xs]) (Rep_mbuf_t zs) buf = (buf'', zs'') \<Longrightarrow>
  buf'' = Rep_mbuf_t buf' \<and> zs'' = zs'"
proof (induction "\<lambda>xs zs. zs @@ [f xs]" zs buf rule: mbufn_take.induct)
  case (1 z buf)
  then show ?case
    by (auto simp: mbufn_take.simps[where ?buf="buf"] mbuf_t_append.rep_eq simp del: mbufn_take.simps split: if_splits)
qed

fun mebufnt_take :: "(event_data table list \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
    'b \<Rightarrow> event_data mebufn \<Rightarrow> ts \<Rightarrow> ts mbuf_t \<Rightarrow> 'b \<times> event_data mebufn \<times> ts \<times> ts mbuf_t" where
  "mebufnt_take f z buf t0 ts =
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> (z, buf, t0, ts) | (Some t, ts') \<Rightarrow>
    (if (\<exists>x \<in> set buf. mbuf_t_is_empty x) then (z, buf, t, t ## ts')
    else mebufnt_take f (f (map (the \<circ> fst \<circ> mbuf_t_cases) buf) t z) (map (snd \<circ> mbuf_t_cases) buf) t ts'))"

lemma mebufnt_take: "mebufnt_take f z buf t nts = (z', buf', nt, nts') \<Longrightarrow>
  mbufnt_take f z (map Rep_mbuf_t buf) t (Rep_mbuf_t nts) = (z', map Rep_mbuf_t buf', nt, Rep_mbuf_t nts')"
proof (induction f z buf t nts arbitrary: z' buf' nts' rule: mebufnt_take.induct)
  case (1 f z buf t ts)
  obtain to ts'' where ts_def: "mbuf_t_cases ts = (to, ts'')"
    by fastforce
  show ?case
    using 1(1,2) ts_def
    unfolding mebufnt_take.simps[of _ _ buf] mbufnt_take.simps[of _ _ "map Rep_mbuf_t buf"] mbuf_t_is_empty_in_set map_is_Nil_conv
    by (cases to) (auto simp del: mbufnt_take.simps mebufnt_take.simps simp: hd_Rep_mbuf_t tl_Rep_mbuf_t mbuf_t_Cons.rep_eq split: if_splits)
qed

lemma mbufnt_take_app: "mbufnt_take (\<lambda>xs t (zs, aux). case f xs t aux of (z, aux) \<Rightarrow> (zs @@ [z], aux)) (zs, aux) buf t0 ts = ((zs', aux'), buf', nt', ts') \<Longrightarrow>
  mbufnt_take (\<lambda>xs t (zs, aux). case f xs t aux of (z, aux) \<Rightarrow> (zs @ [z], aux)) (Rep_mbuf_t zs, aux) buf t0 ts = ((zs'', aux''), buf'', nt'', ts'') \<Longrightarrow>
  zs'' = Rep_mbuf_t zs' \<and> aux'' = aux' \<and> buf'' = buf' \<and> nt'' = nt' \<and> ts'' = ts'"
proof (induction "\<lambda>xs t (zs, aux). case f xs t aux of (z, aux) \<Rightarrow> (zs @@ [z], aux)" "(zs, aux)" buf t0 ts arbitrary: zs aux rule: mbufnt_take.induct)
  case (1 buf t0 ts)
  then show ?case
    by (auto simp: mbufnt_take.simps[where ?ts=ts] mbuf_t_append.rep_eq simp del: mbufnt_take.simps split: if_splits prod.splits)
qed

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

global_interpretation verimon_maux: maux valid_vmsaux init_vmsaux add_new_ts_vmsaux join_vmsaux
  add_new_table_vmsaux result_vmsaux valid_vmuaux init_vmuaux add_new_vmuaux length_vmuaux
  eval_vmuaux valid_mmtaux init_mmtaux update_mmtaux result_mmtaux
  defines vminit0 = "maux.minit0 (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: _ \<Rightarrow> ty Formula.formula \<Rightarrow> _"
  and vminit = "maux.minit (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: ty Formula.formula \<Rightarrow> _"
  and vminit_safe = "maux.minit_safe (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: ty Formula.formula \<Rightarrow> _"
  and vmeval_since = "maux.eval_since add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> event_data table)"
  and vmeval = "maux.meval add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _) update_mmtaux result_mmtaux"
  and letpast_vmeval = "maux.letpast_meval add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _) update_mmtaux result_mmtaux"
  and vmstep = "maux.mstep add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _) update_mmtaux result_mmtaux"
  and vmsteps0_stateless = "maux.msteps0_stateless add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _) update_mmtaux result_mmtaux"
  and vmsteps_stateless = "maux.msteps_stateless add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _) update_mmtaux result_mmtaux"
  and vmonitor = "maux.monitor init_vmsaux add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) init_vmuaux add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _) init_mmtaux update_mmtaux result_mmtaux"
  unfolding valid_vmsaux_def init_vmsaux_def add_new_ts_vmsaux_def join_vmsaux_def
    add_new_table_vmsaux_def result_vmsaux_def valid_vmuaux_def init_vmuaux_def add_new_vmuaux_def
    length_vmuaux_def eval_vmuaux_def 
proof (unfold_locales, goal_cases)
next
  case (2 args cur aux auxlist nt)
  then show ?case
    by clarsimp
next
  case (3 args cur aux auxlist rel1)
  then show ?case
    by clarsimp
next
  case (4 args cur aux auxlist rel2)
  then show ?case
    by clarsimp
next
  case (5 args cur aux auxlist)
  then show ?case
    by clarsimp
next
  case (7 args cur aux auxlist rel1 rel2 nt)
  then show ?case
    by clarsimp
next
  case (8 args cur aux auxlist)
  then show ?case
    by clarsimp
next
  case (9 args cur aux auxlist nt res aux' res' auxlist')
  then show ?case
    by clarsimp
next
  case (10 I L R pos n agg)
  then show ?case
    using valid_init_mmtaux[of I L R pos n agg]
    by (auto simp: Let_def split: if_splits)
next
  case (11 cur nt args l r aux auxlist)
  then show ?case 
    using valid_update_mmtaux by blast
next
  case (12 args cur aux auxlist)
  then show ?case 
    using valid_result_mmtaux by blast
qed simp_all

global_interpretation default_maux: maux 
  (* msaux *) valid_mmasaux "init_mmasaux :: _ \<Rightarrow> mmasaux" add_new_ts_mmasaux gc_join_mmasaux 
    add_new_table_mmasaux result_mmasaux
  (* muaux *) valid_muaux_dq "init_muaux_dq :: _ \<Rightarrow> muaux_dq" add_new_muaux_dq
    length_muaux_dq eval_muaux_dq
  (* mtaux *) valid_mmtaux init_mmtaux update_mmtaux result_mmtaux
  defines minit0 = "maux.minit0 (init_mmasaux :: _ \<Rightarrow> mmasaux) (init_muaux_dq :: _ \<Rightarrow> muaux_dq) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: _ \<Rightarrow> ty Formula.formula \<Rightarrow> _"
  and minit = "maux.minit (init_mmasaux :: _ \<Rightarrow> mmasaux) (init_muaux_dq :: _ \<Rightarrow> muaux_dq) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: ty Formula.formula \<Rightarrow> _"
  and minit_safe = "maux.minit_safe (init_mmasaux :: _ \<Rightarrow> mmasaux) (init_muaux_dq :: _ \<Rightarrow> muaux_dq) (init_mmtaux :: _ \<Rightarrow> event_data mmtaux) :: ty Formula.formula \<Rightarrow> _"
  and meval_since = "maux.eval_since add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> event_data table)"
  and meval = "maux.meval add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux"
  and letpast_meval = "maux.letpast_meval add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux"
  and mstep = "maux.mstep add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux"
  and msteps0_stateless = "maux.msteps0_stateless add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux"
  and msteps_stateless = "maux.msteps_stateless add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) update_mmtaux result_mmtaux"
  and monitor = "maux.monitor init_mmasaux add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) init_muaux_dq add_new_muaux_dq (eval_muaux_dq :: _ \<Rightarrow> _ \<Rightarrow> muaux_dq \<Rightarrow> _) init_mmtaux update_mmtaux result_mmtaux"
  by unfold_locales

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

lemma upd_set_empty[simp]: "upd_set m f {} = m"
  by transfer auto

lemma upd_set_insert[simp]: "upd_set m f (Set.insert x A) = Mapping.update x (f x) (upd_set m f A)"
  by (rule mapping_eqI) (auto simp: Mapping_lookup_upd_set Mapping.lookup_update')

lemma upd_set_fold:
  assumes "finite A"
  shows "upd_set m f A = Finite_Set.fold (\<lambda>a. Mapping.update a (f a)) m A"
proof -
  interpret comp_fun_idem "\<lambda>a. Mapping.update a (f a)"
    by unfold_locales (transfer; auto simp: fun_eq_iff)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) auto
qed

lift_definition upd_cfi :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, ('a, 'b) mapping) comp_fun_idem"
  is "\<lambda>f a m. Mapping.update a (f a) m"
  by unfold_locales (transfer; auto simp: fun_eq_iff)+

lemma upd_set_code[code]:
  "upd_set m f A = (if finite A then set_fold_cfi (upd_cfi f) m A else Code.abort (STR ''upd_set: infinite'') (\<lambda>_. upd_set m f A))"
  by (transfer fixing: m) (auto simp: upd_set_fold)

declare [[code drop: lexordp_eq]]

lemma lexordp_eq_code[code]: "lexordp_eq xs ys \<longleftrightarrow> (case xs of [] \<Rightarrow> True
  | x # xs \<Rightarrow> (case ys of [] \<Rightarrow> False
    | y # ys \<Rightarrow> if x < y then True else if x > y then False else lexordp_eq xs ys))"
  by (subst lexordp_eq.simps) (auto split: list.split)

definition "filter_mapping m X t = Mapping.filter (filter_cond X m t) m"

lemma filter_mapping_empty[simp]: "filter_mapping m {} t = m"
  unfolding filter_mapping_def
  by transfer (auto simp: fun_eq_iff split: option.splits)

lemma filter_mapping_insert[simp]: "filter_mapping m (Set.insert x A) t = (let m' = filter_mapping m A t in
  case Mapping.lookup m' x of Some u \<Rightarrow> if t = u then Mapping.delete x m' else m' | _ \<Rightarrow> m')"
  unfolding filter_mapping_def
  by transfer (auto simp: fun_eq_iff Let_def split: option.splits)

lemma filter_mapping_fold:
  assumes "finite A"
  shows "filter_mapping m A t = Finite_Set.fold (\<lambda>a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m) m A"
proof -
  interpret comp_fun_idem "\<lambda>a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m"
    by unfold_locales
      (transfer; auto simp: fun_eq_iff split: option.splits)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) (auto simp: Let_def)
qed

lift_definition filter_mapping_cfi :: "'b \<Rightarrow> ('a, ('a, 'b) mapping) comp_fun_idem"
  is "\<lambda>t a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m"
  by unfold_locales
    (transfer; auto simp: fun_eq_iff split: option.splits)+

lemma filter_mapping_code[code]:
  "filter_mapping m A t = (if finite A then set_fold_cfi (filter_mapping_cfi t) m A else Code.abort (STR ''filter_mapping: infinite'') (\<lambda>_. filter_mapping m A t))"
  by (transfer fixing: m) (auto simp: filter_mapping_fold)

definition "filter_set' Z m X t = {as \<in> Z. filter_cond' X m t as}"

lemma filter_set'_empty[simp]: "filter_set' Z m {} t = Z"
  unfolding filter_set'_def
  by transfer (auto simp: fun_eq_iff split: option.splits)

lemma filter_set'_insert[simp]: "filter_set' Z m (Set.insert x A) t = (let Z' = filter_set' Z m A t in
  case Mapping.lookup m x of Some u \<Rightarrow> if t = u then Z' - {x} else Z' | _ \<Rightarrow> Z')"
  unfolding filter_set'_def
  by transfer (auto simp: Let_def split: option.splits)

lemma filter_set'_fold:
  assumes "finite A"
  shows "filter_set' Z m A t = Finite_Set.fold (\<lambda>a Z'.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Z' - {a} else Z' | _ \<Rightarrow> Z') Z A"
proof -
  interpret comp_fun_idem "\<lambda>a Z'.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Z' - {a} else Z' | _ \<Rightarrow> Z'"
    by unfold_locales
      (transfer; auto simp: fun_eq_iff split: option.splits)+
  from assms show ?thesis
    by (induct A arbitrary: Z rule: finite.induct) (auto simp: Let_def)
qed

lift_definition filter_set_cfi :: "('a, 'b) mapping \<Rightarrow> 'b \<Rightarrow> ('a, 'a set) comp_fun_idem"
  is "\<lambda>m t a Z'.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Z' - {a} else Z' | _ \<Rightarrow> Z'"
  by (unfold_locales, transfer) (fastforce simp: comp_def split: option.splits)+

lemma filter_set'_code[code]:
  "filter_set' Z m A t = (if finite A then set_fold_cfi (filter_set_cfi m t) Z A else Code.abort (STR ''filter_set: infinite'') (\<lambda>_. filter_set' Z m A t))"
  by transfer (auto simp: filter_set'_fold)

declare [[code drop: shift_end]]
declare shift_end.simps[folded filter_mapping_def filter_set'_def, code]

lemma upd_set'_insert: "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_set' m d f (Set.insert x A) =
  (let m' = (upd_set' m d f A) in case Mapping.lookup m' x of None \<Rightarrow> Mapping.update x d m'
  | Some v \<Rightarrow> Mapping.update x (f v) m')"
  by (rule mapping_eqI) (auto simp: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux1: "upd_set' Mapping.empty d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k d (upd_set' Mapping.empty d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: Let_def upd_set'_lookup Mapping.lookup_update'
      split: option.splits)

lemma upd_set'_aux2: "Mapping.lookup m k = None \<Longrightarrow> upd_set' m d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k d (upd_set' m d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux3: "Mapping.lookup m k = Some v \<Longrightarrow> upd_set' m d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k (f v) (upd_set' m d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux4: "k \<notin> fst ` A \<Longrightarrow> upd_set' Mapping.empty d f {b. (k, b) \<in> A} = Mapping.empty"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' Domain.DomainI fst_eq_Domain
      split: option.splits)

lemma filter_set_empty[simp]: "filter_set (t, {}) (m, Y) = (m, Y)"
  unfolding filter_set.simps
  by transfer (auto simp: Let_def fun_eq_iff split: option.splits)

definition upd_nested_step :: "'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> ('a, ('b, 'c) mapping) mapping \<Rightarrow>
  ('a, ('b, 'c) mapping) mapping" where
  "upd_nested_step d f x m = (case x of (k, k') \<Rightarrow>
    (case Mapping.lookup m k of Some m' \<Rightarrow>
      (case Mapping.lookup m' k' of Some v \<Rightarrow> Mapping.update k (Mapping.update k' (f v) m') m
      | None \<Rightarrow> Mapping.update k (Mapping.update k' d m') m)
    | None \<Rightarrow> Mapping.update k (Mapping.update k' d Mapping.empty) m))"

lemma upd_nested_empty[simp]: "upd_nested m d f {} = m"
  by (rule mapping_eqI)
    (clarsimp simp: upd_nested_def Mapping.lookup.abs_eq split: option.splits)

lemma upd_nested_insert:
  "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_nested m d f (Set.insert x A) =
  upd_nested_step d f x (upd_nested m d f A)"
  unfolding upd_nested_step_def
  using upd_set'_aux1[of d f _ _ A] upd_set'_aux2[of _ _ d f _ A] upd_set'_aux3[of _ _ _ d f _ A]
    upd_set'_aux4[of _ A d f]
  by (auto simp add: Let_def upd_nested_lookup upd_set'_lookup Mapping.lookup_update'
      split: option.splits prod.splits if_splits intro!: mapping_eqI)

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

lemma filter_join_False_empty: "filter_join False {} m = m"
  unfolding filter_join_def
  by transfer (auto split: option.splits)

lemma filter_join_False_insert: "filter_join False (Set.insert a A) m =
  filter_join False A (Mapping.delete a m)"
proof -
  {
    fix x
    have "Mapping.lookup (filter_join False (Set.insert a A) m) x =
      Mapping.lookup (filter_join False A (Mapping.delete a m)) x"
      by (auto simp add: filter_join_def Mapping.lookup_filter Mapping_lookup_delete
          split: option.splits)
  }
  then show ?thesis
    by (simp add: mapping_eqI)
qed

lemma filter_set_insert[simp]: "filter_set (t, Set.insert x A) (m, Y) = (let (m', Y') = filter_set (t, A) (m, Y) in
  case Mapping.lookup m' x of Some u \<Rightarrow> if t = u then (Mapping.delete x m', Y' \<union> {x}) else (m', Y') | _ \<Rightarrow> (m', Y'))"
  unfolding filter_set.simps
  by transfer (auto simp: fun_eq_iff Let_def split: option.splits)

lemma filter_set_fold:
  assumes "finite A"
  shows "filter_set (t, A) (m, Y) = Finite_Set.fold (\<lambda>a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)) (m, Y) A"
proof -
  interpret comp_fun_idem "\<lambda>a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)"
    by unfold_locales
      (transfer; auto simp: fun_eq_iff split: option.splits)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) (auto simp: Let_def)
qed

lift_definition filter_cfi :: "'b \<Rightarrow> ('a, ('a, 'b) mapping \<times> 'a set) comp_fun_idem"
  is "\<lambda>t a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)"
  by unfold_locales (transfer; auto simp: fun_eq_iff split: option.splits)+

lemma filter_set_code[code]:
  "filter_set (t, A) (m, Y) = (if finite A then set_fold_cfi (filter_cfi t) (m, Y) A else Code.abort (STR ''upd_set: infinite'') (\<lambda>_. filter_set (t, A) (m, Y)))"
  by (transfer fixing: m) (auto simp: filter_set_fold)

lemma mapping_delete_set_empty: "mapping_delete_set m {} = m"
  unfolding mapping_delete_set_def
  by (auto simp: Mapping_lookup_filter_Some intro!: mapping_eqI)

lemma mapping_delete_set_insert: "mapping_delete_set m (Set.insert a X) = Mapping.delete a (mapping_delete_set m X)"
proof(rule mapping_eqI)
  fix x
  show "Mapping.lookup (mapping_delete_set m (Set.insert a X)) x =
        Mapping.lookup (Mapping.delete a (mapping_delete_set m X)) x"
    unfolding Mapping_lookup_delete mapping_delete_set_def
    by (auto simp add: Mapping_lookup_filter_None)
       (metis (mono_tags, lifting) Mapping_lookup_filter_None Mapping_lookup_filter_Some)
qed

lemma mapping_delete_fold:
  assumes "finite A"
  shows "mapping_delete_set m A = Finite_Set.fold Mapping.delete m A"
proof -
  interpret comp_fun_idem "Mapping.delete" by(unfold_locales; transfer; simp add: fun_eq_iff)
  from assms show ?thesis
  proof (induction A arbitrary: m)
    case empty
    then show ?case using mapping_delete_set_empty by auto
  next
    case (insert a A)
    then show ?case using mapping_delete_set_insert[of m a A] fold_insert[OF insert(1-2), of m] by(simp)
  qed
qed

lift_definition mapping_delete_set_cfi :: "('a, ('a, 'b) mapping) comp_fun_idem" is
  Mapping.delete by(unfold_locales; transfer; simp add:fun_eq_iff)

lemma mapping_delete_set_code[code]:
  "mapping_delete_set m A = (if finite A then set_fold_cfi mapping_delete_set_cfi m A else Code.abort (STR ''mapping_delete_set: infinite'') (\<lambda>_. mapping_delete_set m A))"
  using mapping_delete_fold[of A m] by (simp add: mapping_delete_set_cfi.rep_eq set_fold_cfi.rep_eq)

declare [[code drop: join_mmsaux]]
declare join_mmsaux.simps[folded filter_join_def, code]

definition remove_Union where
  "remove_Union A X B = A - (\<Union>x \<in> X. B x)"

lemma remove_Union_finite:
  assumes "finite X"
  shows "remove_Union A X B = Finite_Set.fold (\<lambda>x A. A - B x) A X"
proof -
  interpret comp_fun_idem "\<lambda>x A. A - B x"
    by unfold_locales auto
  from assms show ?thesis
    by (induct X arbitrary: A rule: finite_induct) (auto simp: remove_Union_def)
qed

lift_definition remove_Union_cfi :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a, 'b set) comp_fun_idem" is "\<lambda>B x A. A - B x"
  by unfold_locales auto

lemma remove_Union_code[code]: "remove_Union A X B =
  (if finite X then set_fold_cfi (remove_Union_cfi B) A X else A - (\<Union>x \<in> X. B x))"
  by (transfer fixing: A X B) (use remove_Union_finite[of X A B] in \<open>auto simp add: remove_Union_def\<close>)

lemma tabulate_remdups: "Mapping.tabulate xs f = Mapping.tabulate (remdups xs) f"
  by (transfer fixing: xs f) (auto simp: map_of_map_restrict)

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
  by (simp add: Sup_rec_safety_def comp_fun_idem_on.fold_set_fold[OF comp_fun_idem_on_sup])

lemma Sup_rec_safety_atms[code_unfold]:
  "\<Squnion> (Regex.atms r :: rec_safety set) = fold (\<squnion>) (csorted_list_of_set (Regex.atms r)) Unused"
  by (simp add: Sup_rec_safety_def csorted_list_of_set_def ccompare_rec_safety_def ID_def
      linorder.set_sorted_list_of_set[OF comparator.linorder] comparator_rec_safety
      flip: comp_fun_idem_on.fold_set_fold[OF comp_fun_idem_on_sup])

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

instantiation treelist :: (equal) equal begin
lift_definition equal_treelist :: "'a treelist \<Rightarrow> 'a treelist \<Rightarrow> bool" is "(=)" .
instance by (standard; transfer; auto)
end

instantiation wf_wbt :: (linorder) equal begin
lift_definition equal_wf_wbt :: "'a wf_wbt \<Rightarrow> 'a wf_wbt \<Rightarrow> bool" is "(=)" .
instance by(standard; transfer; auto)
end

lemma eq_treelist_code[code]: "equal_class.equal (Collapse y1) (Collapse y2) = (if y2 = empty_tree then (y1 = empty_tree) else (tree_inorder y1 = tree_inorder y2))"
proof -
  have eq: "equal_class.equal (Collapse y1) (Collapse y2) \<longleftrightarrow> tree_inorder y1 = tree_inorder y2"
    by transfer simp
  have "tree_inorder y1 = tree_inorder empty_tree \<longleftrightarrow> y1 = empty_tree"
    by transfer (auto elim: Tree2.inorder.elims)
  then show ?thesis
    by (simp add: eq)
qed

definition to_add_set where
  "to_add_set a m tmp = {b. (a, b) \<in> tmp \<and> Mapping.lookup m b = None}"

definition to_add_set_fun :: "'b \<Rightarrow> ('a, 'c) mapping \<Rightarrow> 'b \<times> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "to_add_set_fun a m elem s = (if a = fst elem \<and> Mapping.lookup m (snd elem) = None then Set.insert (snd elem) s else s)"

lemma to_add_set_empty: "to_add_set a m {} = {}"
  unfolding to_add_set_def by auto

lemma to_add_set_insert: "to_add_set a m (Set.insert x X) = to_add_set_fun a m x (to_add_set a m X) "
  unfolding to_add_set_def to_add_set_fun_def
  by transfer auto

lemma to_add_set_fold:
  assumes "finite tmp"
  shows "to_add_set a m tmp = Finite_Set.fold (to_add_set_fun a m) {} tmp"
proof -
  interpret comp_fun_idem "to_add_set_fun a m"
    by(unfold_locales) (auto simp:to_add_set_fun_def comp_def split:if_splits)
  from assms show ?thesis
  proof (induction tmp)
    case empty
    then show ?case using to_add_set_empty[of a m] by simp
  next
    case (insert a A)
    show ?case unfolding fold_insert[OF insert(1-2)] insert(3)[symmetric] unfolding to_add_set_def to_add_set_fun_def
      by transfer auto
   qed 
 qed

lift_definition to_add_set_cfi :: "'b \<Rightarrow> ('a, 'c) mapping \<Rightarrow> (('b \<times> 'a), 'a set) comp_fun_idem" is 
  "\<lambda>a m. to_add_set_fun a m" by(unfold_locales) (auto simp:to_add_set_fun_def comp_def split:if_splits)

lemma to_add_set_code[code]: "to_add_set a m tmp = (if finite tmp then set_fold_cfi (to_add_set_cfi a m) {} tmp else Code.abort (STR ''to_add_set: infinite set'') (\<lambda>_. to_add_set a m tmp))"
  using to_add_set_fold[of tmp a m] by transfer auto

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


lift_definition update_mapping_with :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>f k v m. case m k of None \<Rightarrow> m(k \<mapsto> v) | Some v' \<Rightarrow> m(k \<mapsto> f k v' v)" .

lemma update_mapping_with_alt: "update_mapping_with f k v m =
  (case Mapping.lookup m k of
      None \<Rightarrow> Mapping.update k v m
    | Some v' \<Rightarrow> Mapping.update k (f k v' v) m)"
  by transfer simp

lift_definition mapping_rbt_insertwk :: "('a::ccompare \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b 
  \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt" is
  "rbt_comp_insert_with_key ccomp"
  by (auto 0 3 intro: linorder.rbt_insertwk_is_rbt ID_ccompare simp: rbt_comp_insert_with_key[OF ID_ccompare'])

declare [[code drop: update_mapping_with]]

lemma update_mapping_with_code[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "update_mapping_with f k v (RBT_Mapping t) =
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''update_mapping_with RBT_Mapping: ccompare = None'') (\<lambda>_. update_mapping_with f k v (RBT_Mapping t))
  | Some _ \<Rightarrow> RBT_Mapping (mapping_rbt_insertwk f k v t))"
  by (clarsimp split: option.split, transfer fixing: f k v)
    (auto simp add: rbt_comp_lookup[OF ID_ccompare'] rbt_comp_insert_with_key[OF ID_ccompare']
      linorder.rbt_lookup_rbt_insertwk[OF ID_ccompare] ord.is_rbt_rbt_sorted
      split: option.split)

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

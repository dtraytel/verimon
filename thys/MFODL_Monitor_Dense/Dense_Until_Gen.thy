(*<*)
theory Dense_Until_Gen
  imports Dense_Aux
begin
(*>*)

section \<open>The Until structure, over a bare element type\<close>

text \<open>
  The deque structure of @{theory MFODL_Monitor_Devel.Optimized_Until_Deque} was monomorphised at
  @{typ event_data} for code generation, so it is restated here over a bare element type
  \<open>'b\<close>, where the kernel's is over @{typ "'a option"}: the dense evaluator runs it at
  @{typ "event_data option"}, where it is the kernel's structure, and the unboxed evaluator at
  @{typ event_data}.  Two things genuinely change.

  @{const eval_step_dq} passes the finished table through @{const eval_args_agg}, which is an
  aggregation over @{typ event_data} and cannot be generic.  The dense fragment only ever builds
  an Until node when @{term "args_agg args = None"}, where that call is the identity, so the
  generic step omits it and the agreement lemmas below assume it.

  The kernel reads the front of its deques with @{const dq_nth}, which is unspecified past the
  end -- and unspecified differently at every element type, so that the structure over short
  tuples could not be related to the one over the kernel's tuples on a malformed state at all.
  The generic operations read through @{text dq_nth_s}, which returns a default past the end.
  On the well-shaped states the kernel's invariant guarantees the two readings agree, which is
  what the agreement lemmas say; the refinement to short tuples then needs no invariant.
\<close>

definition dq_nth_s :: "'a dq \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "dq_nth_s d k z = (if k < dq_len d then dq_nth d k else z)"

lemma dq_nth_s_in: "k < dq_len d \<Longrightarrow> dq_nth_s d k z = dq_nth d k"
  by (simp add: dq_nth_s_def)

text \<open>The front of a deque, read off its lists rather than its counters, so that it commutes with
  a map over the elements on every deque and not only on a consistent one.\<close>

definition dq_hd_s :: "'a dq \<Rightarrow> 'a \<Rightarrow> 'a" where
  "dq_hd_s d z = (case dq_f d of x # _ \<Rightarrow> x | [] \<Rightarrow> (case dq_b d of [] \<Rightarrow> z | _ \<Rightarrow> last (dq_b d)))"

lemma dq_hd_s_nth: "dq_inv d \<Longrightarrow> 0 < dq_len d \<Longrightarrow> dq_hd_s d z = dq_nth d 0"
  by (auto simp: dq_hd_s_def dq_nth_def dq_inv_def dq_len_def last_conv_nth hd_conv_nth
      split: list.splits)

text \<open>An indexed read off the lists, for the same reason.\<close>

definition dq_nth_l :: "'a dq \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "dq_nth_l d k z = (if k < dq_nf d then (if k < length (dq_f d) then dq_f d ! k else z)
     else (let j = dq_nb d - 1 - (k - dq_nf d) in if j < length (dq_b d) then dq_b d ! j else z))"

lemma dq_nth_l_in: "dq_inv d \<Longrightarrow> k < dq_len d \<Longrightarrow> dq_nth_l d k z = dq_nth d k"
  by (auto simp: dq_nth_l_def dq_nth_def dq_inv_def dq_len_def Let_def)

text \<open>Read as written, the bound check walks the list to its end and the indexing walks it again
  to the index; the deques the Until structure indexes are as long as its window, so that is two
  traversals per entry read where one does.  @{text nth_def} is the single walk, and the
  equation below is unconditional -- the default past the end is the same one.\<close>

fun nth_def :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "nth_def [] k z = z"
| "nth_def (x # xs) 0 z = x"
| "nth_def (x # xs) (Suc k) z = nth_def xs k z"

lemma nth_def_eq: "nth_def xs k z = (if k < length xs then xs ! k else z)"
  by (induct xs k z rule: nth_def.induct) auto

lemma dq_nth_l_code[code]:
  "dq_nth_l d k z = (if k < dq_nf d then nth_def (dq_f d) k z
     else nth_def (dq_b d) (dq_nb d - 1 - (k - dq_nf d)) z)"
  by (simp add: dq_nth_l_def nth_def_eq Let_def)

text \<open>The kernel's update of the nested deque, reading the entry off the lists.\<close>

definition gupd_nested_step_dq :: "nat \<Rightarrow> 'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> nat \<times> 'b \<Rightarrow> ('b, 'c) mapping dq \<Rightarrow>
    ('b, 'c) mapping dq" where
  "gupd_nested_step_dq base d f x dq = (case x of (k, k') \<Rightarrow>
    if base \<le> k \<and> k - base < dq_len dq then
      (let i = k - base; m' = dq_nth_l dq i Mapping.empty in
       dq_upd dq i (case Mapping.lookup m' k' of Some v \<Rightarrow> Mapping.update k' (f v) m'
         | None \<Rightarrow> Mapping.update k' d m'))
    else dq)"

lemma gupd_nested_step_dq_eq:
  assumes inv: "dq_inv dq"
  shows "gupd_nested_step_dq base d f x dq = upd_nested_step_dq base d f x dq"
proof -
  obtain k k' where x: "x = (k, k')" by (cases x)
  show ?thesis
  proof (cases "base \<le> k \<and> k - base < dq_len dq")
    case True
    then have "dq_nth_l dq (k - base) Mapping.empty = dq_nth dq (k - base)"
      using inv by (simp add: dq_nth_l_in)
    then show ?thesis unfolding gupd_nested_step_dq_def upd_nested_step_dq_def x Let_def
      by (simp split: option.splits)
  next
    case False
    then show ?thesis unfolding gupd_nested_step_dq_def upd_nested_step_dq_def x by auto
  qed
qed

lemma dq_inv_upd_nested_step_dq: "dq_inv dq \<Longrightarrow> dq_inv (upd_nested_step_dq base d f x dq)"
  by (auto simp: upd_nested_step_dq_def Let_def split: prod.splits)

lemma dq_inv_gupd_nested_step_dq: "dq_inv dq \<Longrightarrow> dq_inv (gupd_nested_step_dq base d f x dq)"
  by (auto simp: gupd_nested_step_dq_def Let_def split: prod.splits)

type_synonym 'b gmuaux = "tp \<times> ts queue \<times> ('b list set \<times> (ts + tp)) queue \<times> nat \<times>
  bool list \<times> bool list \<times> 'b list set \<times> ('b list, tp) mapping \<times>
  ('b list, ts + tp) mapping dq \<times> ts dq \<times> 'b list set list"

type_synonym 'b guntil_acc = "'b list set \<times> ('b list, ts + tp) mapping dq \<times> 'b list set"

definition ginit_dq :: "args \<Rightarrow> 'b gmuaux" where
  "ginit_dq args = (0, empty_queue, empty_queue, 0,
     join_mask (args_n args) (args_L args), join_mask (args_n args) (args_R args),
     {}, Mapping.empty, dq_push Mapping.empty dq_empty, dq_empty, [])"

fun geval_step_dq :: "args \<Rightarrow> 'b gmuaux \<Rightarrow> 'b gmuaux" where
  "geval_step_dq args (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) =
    (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (let m = dq_hd_s a2_dq Mapping.empty;
        I = args_ivl args;
        T = result;
        tss' = tl_queue tss';
        (ts', tss'') = case safe_hd tss' of
              (Some ts', tss'') \<Rightarrow> (ts', tss'') |
              (None, tss'') \<Rightarrow> (0, tss'');
        (tables, taken) = takedropWhile_queue
           (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables;
        to_del_approx = \<Union>(set (map fst taken));
        to_del = Set.filter (\<lambda>x. case Mapping.lookup m x of
              Some tstp \<Rightarrow> (\<not> ts_tp_lt I ts' (tp - len + 1) tstp) | None \<Rightarrow> False) to_del_approx;
        m'' = mapping_delete_set m to_del;
        a2_dq' = dq_tl a2_dq;
        m' = dq_hd_s a2_dq' Mapping.empty;
        result' = if len = 1 then {} else (result - to_del) \<union> Mapping.keys m';
        a2_dq = dq_upd a2_dq' 0 (if len = 1 then Mapping.empty
          else Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' m');
        tstp_dq = dq_tl tstp_dq in
        (tp, tss'', tables, len - 1, maskL, maskR, result', a1_map, a2_dq, tstp_dq, T # dn)))"

fun gshift_dq :: "args \<Rightarrow> ts \<Rightarrow> 'b gmuaux \<Rightarrow> 'b gmuaux" where
  "gshift_dq args nt (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) =
    (let (tss_queue, tss') = takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss in
    foldl (\<lambda>aux _. geval_step_dq args aux) (tp, tss', tables, len, maskL, maskR,
      result, a1_map, a2_dq, tstp_dq, dn) (linearize tss_queue))"

fun geval_dq :: "args \<Rightarrow> ts \<Rightarrow> 'b gmuaux \<Rightarrow> 'b list set list \<times> 'b gmuaux" where
  "geval_dq args nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) =
       gshift_dq args nt aux in
    (rev dn, (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, [])))"

fun glength_dq :: "args \<Rightarrow> 'b gmuaux \<Rightarrow> nat" where
  "glength_dq args (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) =
    length dn + len"

definition guntil_step_dq :: "(nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> nat \<Rightarrow> nat \<times> 'b list \<Rightarrow>
    'b guntil_acc \<Rightarrow> 'b guntil_acc" where
  "guntil_step_dq P d t0 p acc = (case acc of (tbl, a2, res) \<Rightarrow> if P (fst p) then
     (Set.insert (snd p) tbl, gupd_nested_step_dq t0 d (max_tstp d) p a2,
      if fst p = t0 then Set.insert (snd p) res else res)
   else acc)"

definition guntil_elem_step_dq :: "('b list, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    bool \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> 'b list \<Rightarrow> 'b guntil_acc \<Rightarrow> 'b guntil_acc" where
  "guntil_elem_step_dq a1_map msk pos tp len inz P d as acc =
    (let acc' = (if inz then guntil_step_dq P d (tp - len) (tp, as) acc else acc) in
     case Mapping.lookup a1_map (dproj msk as) of
        None \<Rightarrow> (if \<not>pos then guntil_step_dq P d (tp - len) (tp - len, as) acc' else acc')
      | Some tp' \<Rightarrow> guntil_step_dq P d (tp - len) (if pos then (max (tp - len) tp', as)
          else (max (tp - len) (tp' + 1), as)) acc')"

definition gadd_new_dq :: "args \<Rightarrow> bool list \<Rightarrow> 'b :: ccompare list set \<Rightarrow> 'b list set \<Rightarrow> ts \<Rightarrow>
    'b gmuaux \<Rightarrow> 'b gmuaux" where
  "gadd_new_dq args msk rel1 rel2 nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) =
       gshift_dq args nt aux;
     I = args_ivl args; pos = args_pos args; inz = memL I 0;
     new_tstp = (if inz then Inr tp else Inl nt);
     tstp_dq = dq_push nt tstp_dq;
     P = (\<lambda>t. memL I (nt - dq_nth_s tstp_dq (t - (tp - len)) 0));
     (tbl, a2_dq', result') = fold (guntil_elem_step_dq a1_map msk pos tp len inz P new_tstp)
       (csl rel2) ({}, a2_dq, result);
     tables = append_queue (tbl, new_tstp) tables;
     a2_dq = dq_push Mapping.empty a2_dq';
     a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
       (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
     tss = append_queue nt tss in
     (tp + 1, tss, tables, len + 1, maskL, maskR, result', a1_map, a2_dq, tstp_dq, dn))"

subsection \<open>The shape of a state\<close>

text \<open>What the safe readings need: the deques are consistent and hold one entry per pending
  time point (plus the front map), and the time stamp queue holds exactly the pending ones.\<close>

fun ushape :: "'b gmuaux \<Rightarrow> bool" where
  "ushape (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) \<longleftrightarrow>
     dq_inv a2_dq \<and> dq_len a2_dq = len + 1 \<and> dq_inv tstp_dq \<and> dq_len tstp_dq = len \<and>
     length (linearize tss) = len"

fun ulen :: "'b gmuaux \<Rightarrow> nat" where
  "ulen (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) = len"

fun utp :: "'b gmuaux \<Rightarrow> nat" where
  "utp (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) = tp"

fun ua1 :: "'b gmuaux \<Rightarrow> ('b list, nat) mapping" where
  "ua1 (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) = a1_map"

subsection \<open>Agreement with the kernel's structure at the option instance\<close>

lemma ginit_dq_eq: "ginit_dq args = (init_dq args :: event_data mmuaux_dq)"
  by (simp add: ginit_dq_def init_dq_def)

lemma glength_dq_eq: "glength_dq args (d :: event_data mmuaux_dq) = length_dq args d"
  by (cases d rule: mmuaux_dq_cases) simp

lemma geval_step_dq_eq:
  assumes ag: "args_agg args = None"
    and sh: "ushape (d :: event_data mmuaux_dq)" and l: "1 \<le> ulen d"
  shows "geval_step_dq args d = eval_step_dq args d"
    and "ushape (eval_step_dq args d)" and "ulen (eval_step_dq args d) = ulen d - 1"
    and "utp (eval_step_dq args d) = utp d" and "ua1 (eval_step_dq args d) = ua1 d"
proof -
  obtain tp tss tables len mL mR result a1_map a2_dq tstp_dq dn
    where d: "d = (tp, tss, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases d rule: mmuaux_dq_cases)
  have inv: "dq_inv a2_dq" and la2: "dq_len a2_dq = len + 1" and invt: "dq_inv tstp_dq"
    and lt: "dq_len tstp_dq = len" and ls: "length (linearize tss) = len"
    using sh unfolding d by simp_all
  have len: "1 \<le> len" using l unfolding d by simp
  have n0: "dq_hd_s a2_dq z = dq_nth a2_dq 0" for z :: "(event_data tuple, ts + tp) mapping"
    by (simp add: dq_hd_s_nth[OF inv] la2)
  have n1: "dq_hd_s (dq_tl a2_dq) z = dq_nth (dq_tl a2_dq) 0"
    for z :: "(event_data tuple, ts + tp) mapping"
    using len by (simp add: dq_hd_s_nth[OF dq_inv_tl[OF inv]] dq_len_tl[OF inv] la2)
  obtain h tss1 where sh1: "safe_hd tss = (h, tss1)" by (cases "safe_hd tss")
  have ne: "linearize tss \<noteq> []" using ls len by auto
  obtain t where h: "h = Some t" using safe_hd_rep[OF sh1] ne by (cases h) auto
  have l1: "linearize tss1 = linearize tss" using safe_hd_rep[OF sh1] by simp
  obtain h2 tss2 where sh2: "safe_hd (tl_queue tss1) = (h2, tss2)"
    by (cases "safe_hd (tl_queue tss1)")
  have l2: "linearize tss2 = tl (linearize tss)"
    using safe_hd_rep[OF sh2] by (simp add: tl_queue_rep l1)
  show "geval_step_dq args d = eval_step_dq args d"
    unfolding d by (simp add: Let_def n0 n1 eval_args_agg_def ag split: prod.splits option.splits)
  have "ushape (eval_step_dq args d) \<and> ulen (eval_step_dq args d) = ulen d - 1 \<and>
      utp (eval_step_dq args d) = utp d \<and> ua1 (eval_step_dq args d) = ua1 d"
    unfolding d using inv la2 invt lt ls len l2
    by (cases h2)
      (simp_all add: sh1 h sh2 Let_def dq_len_tl dq_len_upd dq_inv_tl dq_inv_upd
        split: prod.splits)
  then show "ushape (eval_step_dq args d)" "ulen (eval_step_dq args d) = ulen d - 1"
    "utp (eval_step_dq args d) = utp d" "ua1 (eval_step_dq args d) = ua1 d" by simp_all
qed

lemma foldl_geval_step_dq_eq:
  assumes ag: "args_agg args = None"
    and sh: "ushape (d :: event_data mmuaux_dq)" and l: "length xs \<le> ulen d"
  shows "foldl (\<lambda>aux _. geval_step_dq args aux) d xs = foldl (\<lambda>aux _. eval_step_dq args aux) d xs \<and>
     ushape (foldl (\<lambda>aux _. eval_step_dq args aux) d xs) \<and>
     ulen (foldl (\<lambda>aux _. eval_step_dq args aux) d xs) = ulen d - length xs \<and>
     utp (foldl (\<lambda>aux _. eval_step_dq args aux) d xs) = utp d \<and>
     ua1 (foldl (\<lambda>aux _. eval_step_dq args aux) d xs) = ua1 d"
  using sh l
proof (induct xs arbitrary: d)
  case (Cons x xs)
  note step = geval_step_dq_eq[OF ag Cons.prems(1)]
  have l1: "1 \<le> ulen d" using Cons.prems(2) by simp
  have "length xs \<le> ulen (eval_step_dq args d)" using Cons.prems(2) step(3)[OF l1] by simp
  from Cons.hyps[OF step(2)[OF l1] this] show ?case
    using step(1)[OF l1] step(3)[OF l1] step(4)[OF l1] step(5)[OF l1] by simp
qed simp

lemma gshift_dq_eq:
  assumes ag: "args_agg args = None" and sh: "ushape (d :: event_data mmuaux_dq)"
  shows "gshift_dq args nt d = shift_dq args nt d"
    and "ushape (shift_dq args nt d)" and "utp (shift_dq args nt d) = utp d"
    and "ua1 (shift_dq args nt d) = ua1 d"
proof -
  obtain tp tss tables len mL mR result a1_map a2_dq tstp_dq dn
    where d: "d = (tp, tss, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases d rule: mmuaux_dq_cases)
  obtain tq tss' where tw: "takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss = (tq, tss')"
    by (cases "takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss")
  have ltq: "length (linearize tq) \<le> length (linearize tss)"
    using takeWhile_queue_rep_fst[of "\<lambda>t. \<not> memR (args_ivl args) (nt - t)" tss]
    unfolding tw by (simp add: length_takeWhile_le)
  have lts: "linearize tss' = linearize tss"
    using takeWhile_queue_rep_snd[of "\<lambda>t. \<not> memR (args_ivl args) (nt - t)" tss]
    unfolding tw by simp
  let ?s = "(tp, tss', tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"
  have sh': "ushape ?s" using sh unfolding d by (simp add: lts)
  have l: "length (linearize tq) \<le> ulen ?s" using ltq sh unfolding d by simp
  note f = foldl_geval_step_dq_eq[OF ag sh' l]
  have g: "gshift_dq args nt d = foldl (\<lambda>aux _. geval_step_dq args aux) ?s (linearize tq)"
    and s: "shift_dq args nt d = foldl (\<lambda>aux _. eval_step_dq args aux) ?s (linearize tq)"
    unfolding d gshift_dq.simps shift_dq.simps tw by (simp_all add: Let_def)
  show "gshift_dq args nt d = shift_dq args nt d" unfolding g s using f by simp
  show "ushape (shift_dq args nt d)" "utp (shift_dq args nt d) = utp d"
    "ua1 (shift_dq args nt d) = ua1 d" unfolding s using f unfolding d by simp_all
qed

lemma geval_dq_eq:
  assumes "args_agg args = None" and "ushape (d :: event_data mmuaux_dq)"
  shows "geval_dq args nt d = eval_dq args nt d"
  by (simp add: gshift_dq_eq[OF assms] split: prod.splits)

lemma guntil_step_dq_eq:
  "P (fst p) = P' (fst p) \<Longrightarrow> dq_inv (fst (snd acc)) \<Longrightarrow>
     guntil_step_dq P d t0 (p :: nat \<times> event_data tuple) acc = until_step_dq P' d t0 p acc"
  by (cases acc) (auto simp: guntil_step_dq_def until_step_dq_def gupd_nested_step_dq_eq)

lemma dq_inv_guntil_step_dq:
  "dq_inv (fst (snd acc)) \<Longrightarrow> dq_inv (fst (snd (guntil_step_dq P d t0 p acc)))"
  by (cases acc) (auto simp: guntil_step_dq_def dq_inv_gupd_nested_step_dq)

lemma dq_inv_until_step_dq:
  "dq_inv (fst (snd acc)) \<Longrightarrow> dq_inv (fst (snd (until_step_dq P d t0 p acc)))"
  by (cases acc) (auto simp: until_step_dq_def dq_inv_upd_nested_step_dq)

lemma dq_inv_guntil_elem_step_dq:
  "dq_inv (fst (snd acc)) \<Longrightarrow>
     dq_inv (fst (snd (guntil_elem_step_dq a1_map msk pos tp len inz P d as acc)))"
  by (simp add: guntil_elem_step_dq_def Let_def dq_inv_guntil_step_dq split: option.splits)

lemma guntil_elem_step_dq_eq:
  assumes P: "\<And>t. t \<le> tp \<Longrightarrow> P t = P' t"
    and a1: "\<And>k v. Mapping.lookup a1_map k = Some v \<Longrightarrow> v < tp"
    and inv: "dq_inv (fst (snd acc))"
  shows "guntil_elem_step_dq a1_map msk pos tp len inz P d (as :: event_data tuple) acc
       = duntil_elem_step_dq a1_map msk pos tp len inz P' d as acc"
proof -
  have s: "fst p \<le> tp \<Longrightarrow> dq_inv (fst (snd acc)) \<Longrightarrow>
      guntil_step_dq P d (tp - len) p acc = until_step_dq P' d (tp - len) p acc" for p acc
    by (cases acc) (auto simp: guntil_step_dq_def until_step_dq_def P gupd_nested_step_dq_eq)
  show ?thesis
    unfolding guntil_elem_step_dq_def duntil_elem_step_dq_def Let_def
    by (auto simp: s inv dq_inv_until_step_dq Suc_le_eq dest!: a1 split: option.splits)
qed

lemma fold_guntil_elem_step_dq_eq:
  assumes P: "\<And>t. t \<le> tp \<Longrightarrow> P t = P' t"
    and a1: "\<And>k v. Mapping.lookup a1_map k = Some v \<Longrightarrow> v < tp"
  shows "dq_inv (fst (snd acc)) \<Longrightarrow>
    fold (guntil_elem_step_dq a1_map msk pos tp len inz P d) (xs :: event_data tuple list) acc
    = fold (duntil_elem_step_dq a1_map msk pos tp len inz P' d) xs acc"
proof (induct xs arbitrary: acc)
  case (Cons a xs)
  have e: "guntil_elem_step_dq a1_map msk pos tp len inz P d a acc
      = duntil_elem_step_dq a1_map msk pos tp len inz P' d a acc"
    by (rule guntil_elem_step_dq_eq[OF P a1 Cons.prems])
  have i: "dq_inv (fst (snd (guntil_elem_step_dq a1_map msk pos tp len inz P d a acc)))"
    by (rule dq_inv_guntil_elem_step_dq[OF Cons.prems])
  show ?case using Cons.hyps[OF i] e by simp
qed simp

lemma gadd_new_dq_eq:
  assumes ag: "args_agg args = None" and sh: "ushape (d :: event_data mmuaux_dq)"
    and a1: "\<And>k v. Mapping.lookup (ua1 d) k = Some v \<Longrightarrow> v < utp d"
  shows "gadd_new_dq args msk rel1 rel2 nt d = dadd_new_dq args msk rel1 rel2 nt d"
proof -
  obtain tp tss tables len mL mR result a1_map a2_dq tstp_dq dn
    where s: "shift_dq args nt d = (tp, tss, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases "shift_dq args nt d" rule: mmuaux_dq_cases)
  note sh' = gshift_dq_eq[OF ag sh, of nt]
  have invt: "dq_inv tstp_dq" and lt: "dq_len tstp_dq = len" using sh'(2) unfolding s by simp_all
  have tp: "tp = utp d" and a1m: "a1_map = ua1 d" using sh'(3) sh'(4) unfolding s by simp_all
  have P: "\<And>t. t \<le> tp \<Longrightarrow>
      memL (args_ivl args) (nt - dq_nth_s (dq_push nt tstp_dq) (t - (tp - len)) 0)
      = memL (args_ivl args) (nt - dq_nth (dq_push nt tstp_dq) (t - (tp - len)))"
    by (simp add: dq_nth_s_in dq_len_push[OF invt] lt)
  have a1': "\<And>k v. Mapping.lookup a1_map k = Some v \<Longrightarrow> v < tp"
    using a1 unfolding tp a1m .
  have inva: "dq_inv a2_dq" using sh'(2) unfolding s by simp
  show ?thesis
    unfolding gadd_new_dq_def dadd_new_dq_def sh'(1) s
    by (simp add: Let_def fold_guntil_elem_step_dq_eq[OF P a1'] inva split: prod.splits)
qed

subsection \<open>The shape follows from the kernel's invariant\<close>

lemma dvalid_muaux_ushape:
  assumes v: "dvalid_muaux args msk cur d auxlist"
  shows "ushape d" and "\<And>k v. Mapping.lookup (ua1 d) k = Some v \<Longrightarrow> v < utp d"
proof -
  obtain tp tss tables len mL mR result a1_map a2_dq tstp_dq dn
    where d: "d = (tp, tss, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases d rule: mmuaux_dq_cases)
  have vm: "valid_muaux_dq args cur (MU_dq (wkeys_uaux msk d)) auxlist"
    and mk: "fst (lft_of d) = msk"
    and na: "\<And>k. k \<in> Mapping.keys (snd (lft_of d)) \<Longrightarrow> dnarrow_tuple msk k"
    using v by (auto simp: dvalid_muaux_def)
  obtain a where rel: "rel_uaux (wkeys_uaux msk d) a" and va: "valid_mmuaux args cur a auxlist"
    using vm by auto
  obtain tp' tss' tables' len' mL' mR' result' a1' a2m tstpm dn'
    where a: "a = (tp', tss', tables', len', mL', mR', result', a1', a2m, tstpm, dn')"
    by (cases a) auto
  have eqs: "tp' = tp" "tss' = tss" "len' = len" "a1' = wkeys msk a1_map"
    and ra2: "rel_a2 tp len a2_dq a2m" and rt: "rel_tstp tp len tstp_dq tstpm"
    using rel unfolding d a by simp_all
  have lts: "length (linearize tss) = len"
    and a1b: "\<forall>xs \<in> Mapping.keys (wkeys msk a1_map).
      case Mapping.lookup (wkeys msk a1_map) xs of Some tp' \<Rightarrow> tp' < tp"
    using va unfolding a valid_mmuaux_def eqs by simp_all
  show "ushape d" unfolding d using ra2 rt lts by (simp add: rel_a2_def rel_tstp_def)
  fix k v assume kv: "Mapping.lookup (ua1 d) k = Some v"
  have k: "Mapping.lookup a1_map k = Some v" using kv unfolding d by simp
  have nk: "dnarrow_tuple msk k" using na k unfolding d by (auto simp: Mapping.keys_is_none_rep)
  have lk: "Mapping.lookup (wkeys msk a1_map) (dwiden msk k) = Some v"
    by (simp add: lookup_wkeys_dwiden[OF nk, of a1_map] k)
  then have mem: "dwiden msk k \<in> Mapping.keys (wkeys msk a1_map)"
    by (simp add: Mapping.keys_is_none_rep)
  from bspec[OF a1b mem] show "v < utp d" unfolding lk d by simp
qed

lemma duaux'_ushape:
  assumes "duaux' n cs_R cs_L args cur d auxlist"
  shows "ushape d" and "\<And>k v. Mapping.lookup (ua1 d) k = Some v \<Longrightarrow> v < utp d"
  using dvalid_muaux_ushape assms unfolding duaux'_def by blast+

(*<*)
end
(*>*)

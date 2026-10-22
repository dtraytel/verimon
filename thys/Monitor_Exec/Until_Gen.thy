(*<*)
theory Until_Gen
  imports Frame_Aux
begin
(*>*)



section \<open>The Until structure, over a bare element type\<close>

text \<open>
  The deque structure of @{theory Monitor_Impl.Optimized_Until_Deque} is monomorphised at
  @{typ event_data} for code generation, so it is restated here over a bare element type
  \<open>'b\<close>.  Three things change.

  @{const eval_step_dq} passes the finished table through @{const eval_args_agg}, which is an
  aggregation over @{typ event_data} and cannot be generic.  The executable fragment only ever builds
  an Until node when @{term "args_agg args = None"}, where that call is the identity, so the
  generic step omits it and the agreement lemmas below assume it.

  The kernel reads the front of its deques with @{const dq_nth}, which is unspecified past the
  end.  The generic operations read through @{text dq_nth_s}, which returns a default past the
  end.  On the well-shaped states the kernel's invariant guarantees the two readings agree, which
  is what the agreement lemmas say.

  The kernel maintains the verdict of the oldest pending time point as a set of its own; the
  generic operations read it off the nested deque's front entry instead, whose key set it
  always is.  The agreement lemmas therefore relate a generic state to the kernel's through
  @{text fix_res}, which writes that key set into the field.
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
  to the index.  @{text nth_def} is the single walk, and the equation below is unconditional --
  the default past the end is the same one.\<close>

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

type_synonym 'b gmuaux = "tp \<times> ts queue \<times> ('b list set \<times> (ts + tp)) queue \<times> nat \<times>
  'b list set \<times> ('b list, tp) mapping \<times>
  ('b list, ts + tp) mapping dq \<times> ts dq \<times> 'b list set list"

type_synonym 'b guntil_acc = "'b list set \<times> ('b list, ts + tp) mapping dq"

definition ginit_dq :: "args \<Rightarrow> 'b gmuaux" where
  "ginit_dq args = (0, empty_queue, empty_queue, 0,
     {}, Mapping.empty, dq_push Mapping.empty dq_empty, dq_empty, [])"

fun geval_step_dq :: "args \<Rightarrow> 'b gmuaux \<Rightarrow> 'b gmuaux" where
  "geval_step_dq args (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) =
    (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (let m = dq_hd_s a2_dq Mapping.empty;
        I = args_ivl args;
        T = Mapping.keys m;
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
        a2_dq = dq_upd a2_dq' 0 (if len = 1 then Mapping.empty
          else Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' m');
        tstp_dq = dq_tl tstp_dq in
        (tp, tss'', tables, len - 1, result, a1_map, a2_dq, tstp_dq, T # dn)))"

fun gshift_dq :: "args \<Rightarrow> ts \<Rightarrow> 'b gmuaux \<Rightarrow> 'b gmuaux" where
  "gshift_dq args nt (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) =
    (let (tss_queue, tss') = takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss in
    foldl (\<lambda>aux _. geval_step_dq args aux) (tp, tss', tables, len,
      result, a1_map, a2_dq, tstp_dq, dn) (linearize tss_queue))"

fun geval_dq :: "args \<Rightarrow> ts \<Rightarrow> 'b gmuaux \<Rightarrow> 'b list set list \<times> 'b gmuaux" where
  "geval_dq args nt aux =
    (let (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) =
       gshift_dq args nt aux in
    (rev dn, (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, [])))"

fun glength_dq :: "args \<Rightarrow> 'b gmuaux \<Rightarrow> nat" where
  "glength_dq args (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) =
    length dn + len"

definition guntil_step_dq :: "(nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> nat \<Rightarrow> nat \<times> 'b list \<Rightarrow>
    'b guntil_acc \<Rightarrow> 'b guntil_acc" where
  "guntil_step_dq P d t0 p acc = (case acc of (tbl, a2) \<Rightarrow> if P (fst p) then
     (Set.insert (snd p) tbl, gupd_nested_step_dq t0 d (max_tstp d) p a2)
   else acc)"

definition guntil_elem_step_dq :: "('b list, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    bool \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> 'b list \<Rightarrow> 'b guntil_acc \<Rightarrow> 'b guntil_acc" where
  "guntil_elem_step_dq a1_map msk pos tp len inz P d as acc =
    (let acc' = (if inz then guntil_step_dq P d (tp - len) (tp, as) acc else acc) in
     case Mapping.lookup a1_map (eproj msk as) of
        None \<Rightarrow> (if \<not>pos then guntil_step_dq P d (tp - len) (tp - len, as) acc' else acc')
      | Some tp' \<Rightarrow> guntil_step_dq P d (tp - len) (if pos then (max (tp - len) tp', as)
          else (max (tp - len) (tp' + 1), as)) acc')"

definition gadd_new_dq :: "args \<Rightarrow> bool list \<Rightarrow> 'b :: ccompare list set \<Rightarrow> 'b list set \<Rightarrow> ts \<Rightarrow>
    'b gmuaux \<Rightarrow> 'b gmuaux" where
  "gadd_new_dq args msk rel1 rel2 nt aux =
    (let (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) =
       gshift_dq args nt aux;
     I = args_ivl args; pos = args_pos args; inz = memL I 0;
     new_tstp = (if inz then Inr tp else Inl nt);
     tstp_dq = dq_push nt tstp_dq;
     P = (\<lambda>t. memL I (nt - dq_nth_s tstp_dq (t - (tp - len)) 0));
     (tbl, a2_dq') = fold (guntil_elem_step_dq a1_map msk pos tp len inz P new_tstp)
       (csl rel2) ({}, a2_dq);
     tables = append_queue (tbl, new_tstp) tables;
     a2_dq = dq_push Mapping.empty a2_dq';
     a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
       (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
     tss = append_queue nt tss in
     (tp + 1, tss, tables, len + 1, result, a1_map, a2_dq, tstp_dq, dn))"

subsection \<open>The shape of a state\<close>

text \<open>What the safe readings need: the deques are consistent and hold one entry per pending
  time point (plus the front map), and the time stamp queue holds exactly the pending ones.\<close>

fun ushape :: "'b gmuaux \<Rightarrow> bool" where
  "ushape (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) \<longleftrightarrow>
     dq_inv a2_dq \<and> dq_len a2_dq = len + 1 \<and> dq_inv tstp_dq \<and> dq_len tstp_dq = len \<and>
     length (linearize tss) = len"

fun ulen :: "'b gmuaux \<Rightarrow> nat" where
  "ulen (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) = len"

fun utp :: "'b gmuaux \<Rightarrow> nat" where
  "utp (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) = tp"

fun ua1 :: "'b gmuaux \<Rightarrow> ('b list, nat) mapping" where
  "ua1 (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) = a1_map"

subsection \<open>The result, read off the front map\<close>

fun fix_res :: "'b gmuaux \<Rightarrow> 'b gmuaux" where
  "fix_res (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) =
     (tp, tss, tables, len, Mapping.keys (dq_hd_s a2_dq Mapping.empty), a1_map,
      a2_dq, tstp_dq, dn)"

lemma ushape_fix_res[simp]: "ushape (fix_res d) = ushape d"
  and ulen_fix_res[simp]: "ulen (fix_res d) = ulen d"
  and utp_fix_res[simp]: "utp (fix_res d) = utp d"
  and ua1_fix_res[simp]: "ua1 (fix_res d) = ua1 d"
  and glength_fix_res[simp]: "glength_dq args (fix_res d) = glength_dq args d"
  by (induct d rule: fix_res.induct, simp)+

lemma fix_res_ginit_dq[simp]: "fix_res (ginit_dq args) = ginit_dq args"
  by (simp add: ginit_dq_def dq_hd_s_def dq_push_def dq_empty_def)

lemma dq_hd_s_list: "dq_inv d \<Longrightarrow> 0 < dq_len d \<Longrightarrow> dq_hd_s d z = hd (dq_list d)"
  by (simp add: dq_hd_s_nth dq_nth dq_len_list hd_conv_nth)

lemma dq_hd_s_push: "dq_inv d \<Longrightarrow> 0 < dq_len d \<Longrightarrow> dq_hd_s (dq_push x d) z = dq_hd_s d z"
  by (simp add: dq_hd_s_list dq_len_push dq_len_list)

lemma dq_hd_s_upd0: "dq_inv d \<Longrightarrow> 0 < dq_len d \<Longrightarrow> dq_hd_s (dq_upd d 0 x) z = x"
  by (simp add: dq_hd_s_list dq_len_upd dq_list_upd dq_len_list hd_conv_nth)

lemma dq_hd_s_upd_pos:
  "dq_inv d \<Longrightarrow> 0 < k \<Longrightarrow> k < dq_len d \<Longrightarrow> dq_hd_s (dq_upd d k x) z = dq_hd_s d z"
  using dq_hd_s_list[of "dq_upd d k x" z] dq_hd_s_list[of d z]
  by (cases "dq_list d"; cases k) (auto simp: dq_len_upd dq_list_upd dq_len_list)

lemma ginit_dq_eq: "ginit_dq args = (init_dq args :: event_data mmuaux_dq)"
  by (simp add: ginit_dq_def init_dq_def)

lemma geval_step_dq_eq:
  assumes ag: "args_agg args = None"
    and sh: "ushape (d :: event_data mmuaux_dq)" and l: "1 \<le> ulen d"
  shows "fix_res (geval_step_dq args d) = eval_step_dq args (fix_res d)"
    and "ushape (geval_step_dq args d)" and "ulen (geval_step_dq args d) = ulen d - 1"
    and "utp (geval_step_dq args d) = utp d" and "ua1 (geval_step_dq args d) = ua1 d"
proof -
  obtain tp tss tables len result a1_map a2_dq tstp_dq dn
    where d: "d = (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn)"
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
  have u0: "dq_hd_s (dq_upd (dq_tl a2_dq) 0 X) z = X"
    for X z :: "(event_data tuple, ts + tp) mapping"
    using len by (simp add: dq_hd_s_upd0[OF dq_inv_tl[OF inv]] dq_len_tl[OF inv] la2)
  obtain h tss1 where sh1: "safe_hd tss = (h, tss1)" by (cases "safe_hd tss")
  have ne: "linearize tss \<noteq> []" using ls len by auto
  obtain t where h: "h = Some t" using safe_hd_rep[OF sh1] ne by (cases h) auto
  have l1: "linearize tss1 = linearize tss" using safe_hd_rep[OF sh1] by simp
  obtain h2 tss2 where sh2: "safe_hd (tl_queue tss1) = (h2, tss2)"
    by (cases "safe_hd (tl_queue tss1)")
  have l2: "linearize tss2 = tl (linearize tss)"
    using safe_hd_rep[OF sh2] by (simp add: tl_queue_rep l1)
  show "fix_res (geval_step_dq args d) = eval_step_dq args (fix_res d)"
    unfolding d fix_res.simps using len
    by (simp add: sh1 h Let_def n0 n1 u0 eval_args_agg_def ag split: prod.splits option.splits)
  have "ushape (geval_step_dq args d) \<and> ulen (geval_step_dq args d) = ulen d - 1 \<and>
      utp (geval_step_dq args d) = utp d \<and> ua1 (geval_step_dq args d) = ua1 d"
    unfolding d using inv la2 invt lt ls len l2
    by (cases h2)
      (simp_all add: sh1 h sh2 Let_def dq_len_tl dq_len_upd
        split: prod.splits)
  then show "ushape (geval_step_dq args d)" "ulen (geval_step_dq args d) = ulen d - 1"
    "utp (geval_step_dq args d) = utp d" "ua1 (geval_step_dq args d) = ua1 d" by simp_all
qed

lemma foldl_geval_step_dq_eq:
  assumes ag: "args_agg args = None"
    and sh: "ushape (d :: event_data mmuaux_dq)" and l: "length xs \<le> ulen d"
  shows "fix_res (foldl (\<lambda>aux _. geval_step_dq args aux) d xs)
       = foldl (\<lambda>aux _. eval_step_dq args aux) (fix_res d) xs \<and>
     ushape (foldl (\<lambda>aux _. geval_step_dq args aux) d xs) \<and>
     ulen (foldl (\<lambda>aux _. geval_step_dq args aux) d xs) = ulen d - length xs \<and>
     utp (foldl (\<lambda>aux _. geval_step_dq args aux) d xs) = utp d \<and>
     ua1 (foldl (\<lambda>aux _. geval_step_dq args aux) d xs) = ua1 d"
  using sh l
proof (induct xs arbitrary: d)
  case (Cons x xs)
  note step = geval_step_dq_eq[OF ag Cons.prems(1)]
  have l1: "1 \<le> ulen d" using Cons.prems(2) by simp
  have "length xs \<le> ulen (geval_step_dq args d)" using Cons.prems(2) step(3)[OF l1] by simp
  from Cons.hyps[OF step(2)[OF l1] this] show ?case
    using step(1)[OF l1] step(3)[OF l1] step(4)[OF l1] step(5)[OF l1] by simp
qed simp

lemma gshift_dq_eq:
  assumes ag: "args_agg args = None" and sh: "ushape (d :: event_data mmuaux_dq)"
  shows "fix_res (gshift_dq args nt d) = shift_dq args nt (fix_res d)"
    and "ushape (gshift_dq args nt d)" and "utp (gshift_dq args nt d) = utp d"
    and "ua1 (gshift_dq args nt d) = ua1 d"
proof -
  obtain tp tss tables len result a1_map a2_dq tstp_dq dn
    where d: "d = (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases d rule: mmuaux_dq_cases)
  obtain tq tss' where tw: "takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss = (tq, tss')"
    by (cases "takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss")
  have ltq: "length (linearize tq) \<le> length (linearize tss)"
    using takeWhile_queue_rep_fst[of "\<lambda>t. \<not> memR (args_ivl args) (nt - t)" tss]
    unfolding tw by (simp add: length_takeWhile_le)
  have lts: "linearize tss' = linearize tss"
    using takeWhile_queue_rep_snd[of "\<lambda>t. \<not> memR (args_ivl args) (nt - t)" tss]
    unfolding tw by simp
  let ?s = "(tp, tss', tables, len, result, a1_map, a2_dq, tstp_dq, dn)"
  have sh': "ushape ?s" using sh unfolding d by (simp add: lts)
  have l: "length (linearize tq) \<le> ulen ?s" using ltq sh unfolding d by simp
  note f = foldl_geval_step_dq_eq[OF ag sh' l]
  have g: "gshift_dq args nt d = foldl (\<lambda>aux _. geval_step_dq args aux) ?s (linearize tq)"
    and s: "shift_dq args nt (fix_res d)
      = foldl (\<lambda>aux _. eval_step_dq args aux) (fix_res ?s) (linearize tq)"
    unfolding d gshift_dq.simps shift_dq.simps fix_res.simps tw by (simp_all add: Let_def)
  show "fix_res (gshift_dq args nt d) = shift_dq args nt (fix_res d)" unfolding g s using f by simp
  show "ushape (gshift_dq args nt d)" "utp (gshift_dq args nt d) = utp d"
    "ua1 (gshift_dq args nt d) = ua1 d" unfolding g using f unfolding d by simp_all
qed

lemma geval_dq_eq:
  assumes "args_agg args = None" and "ushape (d :: event_data mmuaux_dq)"
  shows "fst (geval_dq args nt d) = fst (eval_dq args nt (fix_res d))"
    and "fix_res (snd (geval_dq args nt d)) = snd (eval_dq args nt (fix_res d))"
  using gshift_dq_eq(1)[OF assms, of nt, symmetric]
  by (cases "gshift_dq args nt d" rule: mmuaux_dq_cases; simp)+

text \<open>The insertion.  The kernel's fold carries the result along with the table and the nested
  deque, and adds a tuple to it exactly when the tuple is entered into the front entry; so if
  the result starts as the key set of the front entry, it stays that.\<close>

definition lift_acc :: "'b guntil_acc \<Rightarrow> 'b list set \<times> ('b list, ts + tp) mapping dq \<times> 'b list set"
  where "lift_acc acc = (fst acc, snd acc, Mapping.keys (dq_hd_s (snd acc) Mapping.empty))"

definition qacc :: "nat \<Rightarrow> 'b guntil_acc \<Rightarrow> bool" where
  "qacc n acc \<longleftrightarrow> dq_inv (snd acc) \<and> dq_len (snd acc) = n \<and> 0 < n"

lemma dq_len_upd_nested_step_dq:
  "dq_inv dq \<Longrightarrow> dq_len (upd_nested_step_dq base d f x dq) = dq_len dq"
  by (auto simp: upd_nested_step_dq_def Let_def dq_len_upd split: prod.splits)

lemma keys_hd_upd_nested_step_dq:
  assumes inv: "dq_inv dq" and l: "0 < dq_len dq"
  shows "Mapping.keys (dq_hd_s (upd_nested_step_dq t0 d f (k, k') dq) Mapping.empty)
    = (if k = t0 then Set.insert k' (Mapping.keys (dq_hd_s dq Mapping.empty))
       else Mapping.keys (dq_hd_s dq Mapping.empty))"
  using inv l
  by (auto simp: upd_nested_step_dq_def Let_def dq_hd_s_upd0 dq_hd_s_upd_pos dq_hd_s_nth
      split: option.splits)

lemma until_step_dq_lift:
  assumes P: "P (fst p) = P' (fst p)" and q: "qacc n acc"
  shows "until_step_dq P' d t0 (p :: nat \<times> event_data tuple) (lift_acc acc)
      = lift_acc (guntil_step_dq P d t0 p acc)"
    and "qacc n (guntil_step_dq P d t0 p acc)"
proof -
  obtain tbl a2 where acc: "acc = (tbl, a2)" by (cases acc)
  obtain k k' where p: "p = (k, k')" by (cases p)
  have inv: "dq_inv a2" and l: "0 < dq_len a2" and ln: "dq_len a2 = n"
    using q unfolding acc qacc_def by simp_all
  show "until_step_dq P' d t0 p (lift_acc acc) = lift_acc (guntil_step_dq P d t0 p acc)"
    using P unfolding acc p
    by (simp add: lift_acc_def until_step_dq_def guntil_step_dq_def gupd_nested_step_dq_eq[OF inv]
        keys_hd_upd_nested_step_dq[OF inv l])
  show "qacc n (guntil_step_dq P d t0 p acc)"
    using inv l ln q unfolding acc p
    by (simp add: qacc_def guntil_step_dq_def gupd_nested_step_dq_eq[OF inv]
        dq_len_upd_nested_step_dq)
qed

lemma euntil_elem_step_dq_lift:
  assumes P: "\<And>t. t \<le> tp \<Longrightarrow> P t = P' t"
    and a1: "\<And>k v. Mapping.lookup a1_map k = Some v \<Longrightarrow> v < tp"
    and q: "qacc n acc"
  shows "euntil_elem_step_dq a1_map msk pos tp len inz P' d (as :: event_data tuple) (lift_acc acc)
       = lift_acc (guntil_elem_step_dq a1_map msk pos tp len inz P d as acc)"
    and "qacc n (guntil_elem_step_dq a1_map msk pos tp len inz P d as acc)"
proof -
  have s1: "fst p \<le> tp \<Longrightarrow> qacc n acc \<Longrightarrow>
      until_step_dq P' d (tp - len) p (lift_acc acc) = lift_acc (guntil_step_dq P d (tp - len) p acc)"
    for p :: "nat \<times> event_data tuple" and acc using until_step_dq_lift(1) P by blast
  have s2: "qacc n acc \<Longrightarrow> qacc n (guntil_step_dq P d (tp - len) p acc)"
    for p :: "nat \<times> event_data tuple" and acc
    by (rule until_step_dq_lift(2)[OF refl])
  show "euntil_elem_step_dq a1_map msk pos tp len inz P' d as (lift_acc acc)
       = lift_acc (guntil_elem_step_dq a1_map msk pos tp len inz P d as acc)"
    unfolding guntil_elem_step_dq_def euntil_elem_step_dq_def Let_def
    by (auto simp: s1 s2 q Suc_le_eq dest!: a1 split: option.splits)
  show "qacc n (guntil_elem_step_dq a1_map msk pos tp len inz P d as acc)"
    unfolding guntil_elem_step_dq_def Let_def by (auto simp: s2 q split: option.splits)
qed

lemma fold_euntil_elem_step_dq_lift:
  assumes P: "\<And>t. t \<le> tp \<Longrightarrow> P t = P' t"
    and a1: "\<And>k v. Mapping.lookup a1_map k = Some v \<Longrightarrow> v < tp"
  shows "qacc n acc \<Longrightarrow>
    fold (euntil_elem_step_dq a1_map msk pos tp len inz P' d) (xs :: event_data tuple list)
      (lift_acc acc)
    = lift_acc (fold (guntil_elem_step_dq a1_map msk pos tp len inz P d) xs acc) \<and>
    qacc n (fold (guntil_elem_step_dq a1_map msk pos tp len inz P d) xs acc)"
proof (induct xs arbitrary: acc)
  case (Cons a xs)
  note e = euntil_elem_step_dq_lift[OF P a1 Cons.prems,
      where msk = msk and pos = pos and len = len and inz = inz and d = d and as = a]
  show ?case using Cons.hyps[OF e(2)] e(1) by simp
qed simp

lemma gadd_new_dq_eq:
  assumes ag: "args_agg args = None" and sh: "ushape (d :: event_data mmuaux_dq)"
    and a1: "\<And>k v. Mapping.lookup (ua1 d) k = Some v \<Longrightarrow> v < utp d"
  shows "fix_res (gadd_new_dq args msk rel1 rel2 nt d) = eadd_new_dq args msk rel1 rel2 nt (fix_res d)"
    and "ushape (gadd_new_dq args msk rel1 rel2 nt d)"
proof -
  obtain tp tss tables len result a1_map a2_dq tstp_dq dn
    where s: "gshift_dq args nt d = (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases "gshift_dq args nt d" rule: mmuaux_dq_cases)
  note sh' = gshift_dq_eq[OF ag sh, of nt]
  have fs: "shift_dq args nt (fix_res d) = (tp, tss, tables, len,
      Mapping.keys (dq_hd_s a2_dq Mapping.empty), a1_map, a2_dq, tstp_dq, dn)"
    using sh'(1) unfolding s by simp
  have invt: "dq_inv tstp_dq" and lt: "dq_len tstp_dq = len" and inva: "dq_inv a2_dq"
    and la: "dq_len a2_dq = len + 1" and lts: "length (linearize tss) = len"
    using sh'(2) unfolding s by simp_all
  have tp: "tp = utp d" and a1m: "a1_map = ua1 d" using sh'(3) sh'(4) unfolding s by simp_all
  define Pg where "Pg = (\<lambda>t. memL (args_ivl args) (nt - dq_nth_s (dq_push nt tstp_dq) (t - (tp - len)) 0))"
  define Pk where "Pk = (\<lambda>t. memL (args_ivl args) (nt - dq_nth (dq_push nt tstp_dq) (t - (tp - len))))"
  have P: "\<And>t. t \<le> tp \<Longrightarrow> Pg t = Pk t"
    by (simp add: Pg_def Pk_def dq_nth_s_in dq_len_push[OF invt] lt)
  have a1': "\<And>k v. Mapping.lookup a1_map k = Some v \<Longrightarrow> v < tp"
    using a1 unfolding tp a1m .
  define nts where "nts = (if memL (args_ivl args) 0 then Inr tp else Inl nt)"
  define g where "g = guntil_elem_step_dq a1_map msk (args_pos args) tp len
    (memL (args_ivl args) 0) Pg nts"
  obtain tbl a2' where f: "fold g (csl rel2) ({}, a2_dq) = (tbl, a2')"
    by (cases "fold g (csl rel2) ({}, a2_dq)")
  have q0: "qacc (len + 1) ({}, a2_dq)" using inva la by (simp add: qacc_def)
  have fl: "fold (euntil_elem_step_dq a1_map msk (args_pos args) tp len (memL (args_ivl args) 0) Pk
      nts) (csl rel2) (lift_acc ({}, a2_dq)) = lift_acc (tbl, a2') \<and> qacc (len + 1) (tbl, a2')"
    using fold_euntil_elem_step_dq_lift[where P = Pg and P' = Pk and a1_map = a1_map and tp = tp,
      OF P a1' q0, where msk = msk and pos = "args_pos args" and len = len
      and inz = "memL (args_ivl args) 0" and d = nts and xs = "csl rel2"]
    unfolding g_def[symmetric] f .
  have q1: "dq_inv a2'" "0 < dq_len a2'" "dq_len a2' = len + 1"
    using fl by (simp_all add: qacc_def)
  have fd: "fold (euntil_elem_step_dq a1_map msk (args_pos args) tp len (memL (args_ivl args) 0) Pk
      nts) (csl rel2) ({}, a2_dq, Mapping.keys (dq_hd_s a2_dq Mapping.empty))
    = (tbl, a2', Mapping.keys (dq_hd_s a2' Mapping.empty))"
    using conjunct1[OF fl] unfolding lift_acc_def fst_conv snd_conv .
  have ga: "gadd_new_dq args msk rel1 rel2 nt d = (tp + 1, append_queue nt tss,
      append_queue (tbl, nts) tables, len + 1,
      result, if args_pos args then Mapping.filter (\<lambda>as _. as \<in> rel1)
        (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1,
      dq_push Mapping.empty a2', dq_push nt tstp_dq, dn)"
    unfolding gadd_new_dq_def s Let_def using f unfolding g_def Pg_def nts_def
    by (simp split: prod.splits)
  show "fix_res (gadd_new_dq args msk rel1 rel2 nt d) = eadd_new_dq args msk rel1 rel2 nt (fix_res d)"
    unfolding ga eadd_new_dq_def fs Let_def using fd unfolding Pk_def nts_def
    by (simp add: dq_hd_s_push[OF q1(1,2)] split: prod.splits)
  show "ushape (gadd_new_dq args msk rel1 rel2 nt d)"
    unfolding ga using q1 invt lt lts by (simp add: dq_len_push append_queue_rep)
qed

lemma evalid_muaux_ushape:
  assumes v: "evalid_muaux args msk cur d auxlist"
  shows "ushape d" and "\<And>k v. Mapping.lookup (ua1 d) k = Some v \<Longrightarrow> v < utp d"
proof -
  obtain tp tss tables len result a1_map a2_dq tstp_dq dn
    where d: "d = (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases d rule: mmuaux_dq_cases)
  obtain a where rel: "rel_uaux d a" and va: "valid_mmuaux args cur a auxlist"
    using v by (auto simp: evalid_muaux_def)
  obtain tp' tss' tables' len' result' a1' a2m tstpm dn'
    where a: "a = (tp', tss', tables', len', result', a1', a2m, tstpm, dn')"
    by (cases a) auto
  have eqs: "tp' = tp" "tss' = tss" "len' = len" "a1' = a1_map"
    and ra2: "rel_a2 tp len a2_dq a2m" and rt: "rel_tstp tp len tstp_dq tstpm"
    using rel unfolding d a by simp_all
  have lts: "length (linearize tss) = len"
    and a1b: "\<forall>xs \<in> Mapping.keys a1_map. case Mapping.lookup a1_map xs of Some tp' \<Rightarrow> tp' < tp"
    using va unfolding a valid_mmuaux_def eqs by simp_all
  show "ushape d" unfolding d using ra2 rt lts by (simp add: rel_a2_def rel_tstp_def)
  fix k v assume kv: "Mapping.lookup (ua1 d) k = Some v"
  have k: "Mapping.lookup a1_map k = Some v" using kv unfolding d by simp
  then have mem: "k \<in> Mapping.keys a1_map" by (simp add: Mapping.keys_is_none_rep)
  from bspec[OF a1b mem] show "v < utp d" unfolding k d by simp
qed

lemma euaux'_ushape:
  assumes "euaux' kL cL kR cR args cur d auxlist"
  shows "ushape d" and "\<And>k v. Mapping.lookup (ua1 d) k = Some v \<Longrightarrow> v < utp d"
  using evalid_muaux_ushape assms unfolding euaux'_def by blast+

(*<*)
end
(*>*)

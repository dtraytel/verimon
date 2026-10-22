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

text \<open>The front of a deque, read off its lists rather than its counters, so that it commutes with
  a map over the elements on every deque and not only on a consistent one.\<close>

definition dq_hd_s :: "'a dq \<Rightarrow> 'a \<Rightarrow> 'a" where
  "dq_hd_s d z = (case dq_f d of x # _ \<Rightarrow> x | [] \<Rightarrow> (case dq_b d of [] \<Rightarrow> z | _ \<Rightarrow> last (dq_b d)))"

text \<open>An indexed read off the lists, for the same reason.\<close>

definition dq_nth_l :: "'a dq \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "dq_nth_l d k z = (if k < dq_nf d then (if k < length (dq_f d) then dq_f d ! k else z)
     else (let j = dq_nb d - 1 - (k - dq_nf d) in if j < length (dq_b d) then dq_b d ! j else z))"

text \<open>Read as written, the bound check walks the list to its end and the indexing walks it again
  to the index.  @{text nth_def} is the single walk, and the equation below is unconditional --
  the default past the end is the same one.\<close>

fun nth_def :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "nth_def [] k z = z"
| "nth_def (x # xs) 0 z = x"
| "nth_def (x # xs) (Suc k) z = nth_def xs k z"

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

lemma fix_res_ginit_dq[simp]: "fix_res (ginit_dq args) = ginit_dq args"
  by (simp add: ginit_dq_def dq_hd_s_def dq_push_def dq_empty_def)

subsection \<open>Agreement with the kernel's structure\<close>

lemma ginit_dq_eq: "ginit_dq args = (init_dq args :: event_data mmuaux_dq)"
  by (simp add: ginit_dq_def init_dq_def)

text \<open>The insertion.  The kernel's fold carries the result along with the table and the nested
  deque, and adds a tuple to it exactly when the tuple is entered into the front entry; so if
  the result starts as the key set of the front entry, it stays that.\<close>

definition lift_acc :: "'b guntil_acc \<Rightarrow> 'b list set \<times> ('b list, ts + tp) mapping dq \<times> 'b list set"
  where "lift_acc acc = (fst acc, snd acc, Mapping.keys (dq_hd_s (snd acc) Mapping.empty))"

definition qacc :: "nat \<Rightarrow> 'b guntil_acc \<Rightarrow> bool" where
  "qacc n acc \<longleftrightarrow> dq_inv (snd acc) \<and> dq_len (snd acc) = n \<and> 0 < n"

subsection \<open>The shape follows from the kernel's invariant\<close>

end
(*>*)

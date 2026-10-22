(*<*)
theory Optimized_Until_Deque
  imports Optimized_Agg_Temporal
begin
(*>*)

section \<open>Until with deques instead of time-point-indexed mappings\<close>

text \<open>
  The Until structure of @{theory Monitor_Impl.Optimized_Until} keeps two mappings indexed
  by the time points of the window, @{text a2_map} (one mapping of tuples per time point) and
  @{text tstp_map} (the time stamp of every time point). Their keys always form the contiguous
  ranges @{term "{tp - len..tp}"} and @{term "{tp - len..<tp}"}: entries are removed at the
  smallest key and added at the largest one. We replace both by deques (two lists with cached
  lengths) with constant-time access at both ends, and connect the resulting structure to the
  original one by a simulation relation, so that the existing invariant proofs are reused.
\<close>

section \<open>Deques with constant-time access at both ends\<close>

datatype 'a dq = Dq (dq_f: "'a list") (dq_b: "'a list") (dq_nf: nat) (dq_nb: nat)

definition dq_list :: "'a dq \<Rightarrow> 'a list" where
  "dq_list d = dq_f d @ rev (dq_b d)"

definition dq_inv :: "'a dq \<Rightarrow> bool" where
  "dq_inv d \<longleftrightarrow> dq_nf d = length (dq_f d) \<and> dq_nb d = length (dq_b d)"

definition dq_empty :: "'a dq" where
  "dq_empty = Dq [] [] 0 0"

definition dq_len :: "'a dq \<Rightarrow> nat" where
  "dq_len d = dq_nf d + dq_nb d"

text \<open>
  The front list is empty only for the empty deque: @{text dq_push} builds the front when it
  is empty, and @{text dq_tl} normalises after removing the head. Otherwise an access to the
  oldest entry (the common case in @{text add_new}) would walk the whole back list.
\<close>

definition dq_push :: "'a \<Rightarrow> 'a dq \<Rightarrow> 'a dq" where
  "dq_push x d = (if dq_f d = [] then Dq (rev (x # dq_b d)) [] (dq_nb d + 1) 0
     else Dq (dq_f d) (x # dq_b d) (dq_nf d) (dq_nb d + 1))"

text \<open>
  When the front list is exhausted, only the older half of the back list is moved to the
  front, so that the newest entries stay at the head of the back list: the entries accessed
  by @{text add_new} are the newest ones, and a walk of the whole window is avoided.
\<close>

definition dq_norm :: "'a dq \<Rightarrow> 'a dq" where
  "dq_norm d = (if dq_f d = [] then (let h = dq_nb d div 2 in
     Dq (rev (drop h (dq_b d))) (take h (dq_b d)) (dq_nb d - h) h) else d)"

definition dq_tl :: "'a dq \<Rightarrow> 'a dq" where
  "dq_tl d = (let d' = dq_norm d in dq_norm (Dq (tl (dq_f d')) (dq_b d') (dq_nf d' - 1) (dq_nb d')))"

definition dq_nth :: "'a dq \<Rightarrow> nat \<Rightarrow> 'a" where
  "dq_nth d k = (if k < dq_nf d then dq_f d ! k else dq_b d ! (dq_nb d - 1 - (k - dq_nf d)))"

definition dq_upd :: "'a dq \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a dq" where
  "dq_upd d k x = (if k < dq_nf d then Dq ((dq_f d)[k := x]) (dq_b d) (dq_nf d) (dq_nb d)
     else Dq (dq_f d) ((dq_b d)[dq_nb d - 1 - (k - dq_nf d) := x]) (dq_nf d) (dq_nb d))"

lemma dq_inv_empty[simp]: "dq_inv dq_empty"
  by (simp add: dq_inv_def dq_empty_def)

lemma dq_list_empty[simp]: "dq_list dq_empty = []"
  by (simp add: dq_list_def dq_empty_def)

lemma dq_inv_push[simp]: "dq_inv d \<Longrightarrow> dq_inv (dq_push x d)"
  by (auto simp add: dq_inv_def dq_push_def)

lemma dq_list_push[simp]: "dq_list (dq_push x d) = dq_list d @ [x]"
  by (auto simp add: dq_list_def dq_push_def)

lemma dq_inv_norm[simp]:
  assumes inv: "dq_inv d"
  shows "dq_inv (dq_norm d)"
proof (cases "dq_f d = []")
  case True
  have nb: "dq_nb d = length (dq_b d)" using inv unfolding dq_inv_def by simp
  have "min (length (dq_b d) div 2) (length (dq_b d)) = length (dq_b d) div 2"
    by (rule min_absorb1) (rule div_le_dividend)
  then show ?thesis using True unfolding dq_norm_def dq_inv_def Let_def nb by simp
next
  case False
  then show ?thesis using inv by (simp add: dq_norm_def)
qed

lemma dq_list_norm[simp]: "dq_list (dq_norm d) = dq_list d"
proof (cases "dq_f d = []")
  case True
  have "rev (drop h (dq_b d)) @ rev (take h (dq_b d)) = rev (dq_b d)" for h
    by (metis append_take_drop_id rev_append)
  then show ?thesis using True by (simp add: dq_list_def dq_norm_def)
qed (simp add: dq_list_def dq_norm_def)

lemma dq_f_norm:
  assumes "dq_inv d" "dq_list d \<noteq> []"
  shows "dq_f (dq_norm d) \<noteq> []"
proof (cases "dq_f d = []")
  case True
  then have "dq_b d \<noteq> []" using assms(2) by (simp add: dq_list_def)
  then have "0 < length (dq_b d)" by simp
  then have "length (dq_b d) div 2 < length (dq_b d)" by presburger
  then show ?thesis using True assms(1) by (simp add: dq_norm_def dq_inv_def)
qed (simp add: dq_norm_def)

lemma dq_inv_tl[simp]:
  assumes inv: "dq_inv d"
  shows "dq_inv (dq_tl d)"
proof -
  have "dq_inv (Dq (tl (dq_f (dq_norm d))) (dq_b (dq_norm d)) (dq_nf (dq_norm d) - 1) (dq_nb (dq_norm d)))"
    using dq_inv_norm[OF inv] unfolding dq_inv_def by simp
  then show ?thesis unfolding dq_tl_def Let_def by (rule dq_inv_norm)
qed

lemma dq_list_tl[simp]:
  assumes inv: "dq_inv d"
  shows "dq_list (dq_tl d) = tl (dq_list d)"
proof -
  have *: "dq_list (dq_tl d) = tl (dq_f (dq_norm d)) @ rev (dq_b (dq_norm d))"
    unfolding dq_tl_def Let_def dq_list_norm by (simp add: dq_list_def)
  show ?thesis
  proof (cases "dq_list d = []")
    case True
    then have "dq_f (dq_norm d) = []" "dq_b (dq_norm d) = []" using dq_list_norm[of d] by (auto simp: dq_list_def)
    then show ?thesis using True * by simp
  next
    case False
    have "dq_list (dq_tl d) = tl (dq_f (dq_norm d) @ rev (dq_b (dq_norm d)))"
      using dq_f_norm[OF inv False] * by simp
    then show ?thesis using dq_list_norm[of d] by (simp add: dq_list_def)
  qed
qed

lemma dq_inv_upd[simp]: "dq_inv d \<Longrightarrow> dq_inv (dq_upd d k x)"
  by (auto simp add: dq_inv_def dq_upd_def)

definition dq_of_list :: "'a list \<Rightarrow> 'a dq" where
  "dq_of_list xs = Dq xs [] (length xs) 0"

lemma dq_inv_of_list[simp]: "dq_inv (dq_of_list xs)"
  by (simp add: dq_inv_def dq_of_list_def)

lemma dq_list_of_list[simp]: "dq_list (dq_of_list xs) = xs"
  by (simp add: dq_list_def dq_of_list_def)

section \<open>The Until structure with deques for the time-point-indexed mappings\<close>

type_synonym 'a mmuaux_dq = "tp \<times> ts queue \<times> ('a table \<times> (ts + tp)) queue \<times> nat \<times>
  'a table \<times> ('a tuple, tp) mapping \<times> ('a tuple, ts + tp) mapping dq \<times> ts dq \<times> 'a table list"

definition rel_a2 :: "tp \<Rightarrow> nat \<Rightarrow> ('a tuple, ts + tp) mapping dq \<Rightarrow> (tp, ('a tuple, ts + tp) mapping) mapping \<Rightarrow> bool" where
  "rel_a2 tp len d m \<longleftrightarrow> dq_inv d \<and> dq_len d = len + 1 \<and> Mapping.keys m = {tp - len..tp} \<and>
    (\<forall>k \<le> len. Mapping.lookup m (tp - len + k) = Some (dq_nth d k))"

definition rel_tstp :: "tp \<Rightarrow> nat \<Rightarrow> ts dq \<Rightarrow> (tp, ts) mapping \<Rightarrow> bool" where
  "rel_tstp tp len d m \<longleftrightarrow> dq_inv d \<and> dq_len d = len \<and> Mapping.keys m = {tp - len..<tp} \<and>
    (\<forall>k < len. Mapping.lookup m (tp - len + k) = Some (dq_nth d k))"

fun rel_uaux :: "event_data mmuaux_dq \<Rightarrow> event_data mmuaux \<Rightarrow> bool" where
  "rel_uaux (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done)
     (tp', tss', tables', len', result', a1_map', a2_map, tstp_map, done') \<longleftrightarrow>
   tp' = tp \<and> tss' = tss \<and> tables' = tables \<and> len' = len \<and>
   result' = result \<and> a1_map' = a1_map \<and> done' = done \<and> len \<le> tp \<and>
   rel_a2 tp len a2_dq a2_map \<and> rel_tstp tp len tstp_dq tstp_map"

subsection \<open>Operations\<close>

fun eval_step_dq :: "args \<Rightarrow> event_data mmuaux_dq \<Rightarrow> event_data mmuaux_dq" where
  "eval_step_dq args (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done) =
    (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (let m = dq_nth a2_dq 0;
        I = args_ivl args;
        T = eval_args_agg args result;
        tss' = tl_queue tss';
        (ts', tss'') = case safe_hd tss' of
              (Some ts', tss'') \<Rightarrow> (ts', tss'') |
              (None, tss'') \<Rightarrow> (0, tss'');
        (tables, taken) = takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables;
        to_del_approx = \<Union>(set (map fst taken));
        to_del = Set.filter (\<lambda>x. case Mapping.lookup m x of Some tstp \<Rightarrow> (\<not>ts_tp_lt I ts' (tp - len + 1) tstp) |
                                                            None \<Rightarrow> False) to_del_approx;
        m'' = mapping_delete_set m to_del;
        a2_dq' = dq_tl a2_dq;
        m' = dq_nth a2_dq' 0;
        result' = if len = 1 then {} else (result - to_del) \<union> Mapping.keys m';
        a2_dq = dq_upd a2_dq' 0 (if len = 1 then Mapping.empty
          else Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' m');
        tstp_dq = dq_tl tstp_dq in
        (tp, tss'', tables, len - 1, result', a1_map, a2_dq, tstp_dq, T # done)))"

fun shift_dq :: "args \<Rightarrow> ts \<Rightarrow> event_data mmuaux_dq \<Rightarrow> event_data mmuaux_dq" where
  "shift_dq args nt (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done) =
    (let (tss_queue, tss') = takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss in
    foldl (\<lambda>aux _. eval_step_dq args aux) (tp, tss', tables, len,
      result, a1_map, a2_dq, tstp_dq, done) (linearize tss_queue))"

fun eval_dq :: "args \<Rightarrow> ts \<Rightarrow> event_data mmuaux_dq \<Rightarrow> event_data table list \<times> event_data mmuaux_dq" where
  "eval_dq args nt aux =
    (let (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done) = shift_dq args nt aux in
    (rev done, (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, [])))"

definition init_dq :: "args \<Rightarrow> event_data mmuaux_dq" where
  "init_dq args = (0, empty_queue, empty_queue, 0,
  {}, Mapping.empty, dq_push Mapping.empty dq_empty, dq_empty, [])"

fun length_dq :: "args \<Rightarrow> event_data mmuaux_dq \<Rightarrow> nat" where
  "length_dq args (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done) = length done + len"

subsection \<open>Nested update on the deque\<close>

lemma upd_set'_empty_dq[simp]: "upd_set' m d f {} = m"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup)

definition upd_nested_step_dq :: "nat \<Rightarrow> 'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> nat \<times> 'b \<Rightarrow> ('b, 'c) mapping dq \<Rightarrow> ('b, 'c) mapping dq" where
  "upd_nested_step_dq base d f x dq = (case x of (k, k') \<Rightarrow>
    if base \<le> k \<and> k - base < dq_len dq then
      (let i = k - base; m' = dq_nth dq i in
       dq_upd dq i (case Mapping.lookup m' k' of Some v \<Rightarrow> Mapping.update k' (f v) m' | None \<Rightarrow> Mapping.update k' d m'))
    else dq)"

definition upd_nested_dq :: "nat \<Rightarrow> 'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> (nat \<times> 'b) list \<Rightarrow> ('b, 'c) mapping dq \<Rightarrow> ('b, 'c) mapping dq" where
  "upd_nested_dq base d f xs dq = foldr (upd_nested_step_dq base d f) xs dq"

lemma upd_nested_dq_Nil[simp]: "upd_nested_dq base d f [] dq = dq"
  by (simp add: upd_nested_dq_def)

lemma upd_nested_dq_Cons: "upd_nested_dq base d f (x # xs) dq = upd_nested_step_dq base d f x (upd_nested_dq base d f xs dq)"
  by (simp add: upd_nested_dq_def)

lemma dq_inv_nested_step[simp]: "dq_inv dq \<Longrightarrow> dq_inv (upd_nested_step_dq base d f x dq)"
  by (auto simp: upd_nested_step_dq_def split: prod.splits)

lemma dq_inv_upd_nested_dq[simp]: "dq_inv dq \<Longrightarrow> dq_inv (upd_nested_dq base d f xs dq)"
  by (induction xs) (auto simp: upd_nested_dq_Cons)

definition a2_of_dq :: "tp \<Rightarrow> nat \<Rightarrow> 'a dq \<Rightarrow> (tp, 'a) mapping" where
  "a2_of_dq tp len dq = Mapping.tabulate [tp - len..<tp + 1] (\<lambda>t. dq_nth dq (t - (tp - len)))"

definition tstp_of_dq :: "tp \<Rightarrow> nat \<Rightarrow> 'a dq \<Rightarrow> (tp, 'a) mapping" where
  "tstp_of_dq tp len dq = Mapping.tabulate [tp - len..<tp] (\<lambda>t. dq_nth dq (t - (tp - len)))"

fun uaux_of_dq :: "event_data mmuaux_dq \<Rightarrow> event_data mmuaux" where
  "uaux_of_dq (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done) =
    (tp, tss, tables, len, result, a1_map, a2_of_dq tp len a2_dq, tstp_of_dq tp len tstp_dq, done)"

definition dq_of_a2 :: "tp \<Rightarrow> nat \<Rightarrow> (tp, 'a) mapping \<Rightarrow> 'a dq" where
  "dq_of_a2 tp len m = dq_of_list (map (\<lambda>k. the (Mapping.lookup m (tp - len + k))) [0..<len + 1])"

definition dq_of_tstp :: "tp \<Rightarrow> nat \<Rightarrow> (tp, 'a) mapping \<Rightarrow> 'a dq" where
  "dq_of_tstp tp len m = dq_of_list (map (\<lambda>k. the (Mapping.lookup m (tp - len + k))) [0..<len])"

fun dq_of_uaux :: "event_data mmuaux \<Rightarrow> event_data mmuaux_dq" where
  "dq_of_uaux (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done) =
    (tp, tss, tables, len, result, a1_map, dq_of_a2 tp len a2_map, dq_of_tstp tp len tstp_map, done)"

subsection \<open>Adding a new time point\<close>

text \<open>
  The candidate pairs (time point, tuple) of the new operand table are processed in one fold
  over the table: each pair that passes the interval check is inserted into the table appended
  to the queue, into the deque entry of its time point and, if its time point is the oldest of
  the window, into the result. The fold is over the sorted list of the table, so no commutativity
  argument is needed; the definition is executable as it stands.
\<close>

type_synonym 'a until_acc_dq = "'a table \<times> ('a tuple, ts + tp) mapping dq \<times> 'a table"

definition until_step_dq :: "(nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> nat \<Rightarrow> nat \<times> 'a tuple \<Rightarrow> 'a until_acc_dq \<Rightarrow> 'a until_acc_dq" where
  "until_step_dq P d t0 p acc = (case acc of (tbl, a2, res) \<Rightarrow> if P (fst p) then
     (Set.insert (snd p) tbl, upd_nested_step_dq t0 d (max_tstp d) p a2,
      if fst p = t0 then Set.insert (snd p) res else res)
   else acc)"

definition until_cand :: "('a tuple, nat) mapping \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a tuple \<Rightarrow> (nat \<times> 'a tuple) set" where
  "until_cand a1_map L R pos tp len as = (case Mapping.lookup a1_map (restrict L R as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)})"

definition until_pairs_list :: "('a tuple, nat) mapping \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'a tuple \<Rightarrow> (nat \<times> 'a tuple) list" where
  "until_pairs_list a1_map L R pos tp len inz as =
    (case Mapping.lookup a1_map (restrict L R as) of
        None \<Rightarrow> (if \<not>pos then [(tp - len, as)] else [])
      | Some tp' \<Rightarrow> [if pos then (max (tp - len) tp', as) else (max (tp - len) (tp' + 1), as)]) @
    (if inz then [(tp, as)] else [])"

definition until_elem_step_dq :: "('a tuple, nat) mapping \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
  (nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> 'a tuple \<Rightarrow> 'a until_acc_dq \<Rightarrow> 'a until_acc_dq" where
  "until_elem_step_dq a1_map L R pos tp len inz P d as acc =
    (let acc' = (if inz then until_step_dq P d (tp - len) (tp, as) acc else acc) in
     case Mapping.lookup a1_map (restrict L R as) of
        None \<Rightarrow> (if \<not>pos then until_step_dq P d (tp - len) (tp - len, as) acc' else acc')
      | Some tp' \<Rightarrow> until_step_dq P d (tp - len) (if pos then (max (tp - len) tp', as) else (max (tp - len) (tp' + 1), as)) acc')"

definition add_new_dq :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> event_data mmuaux_dq \<Rightarrow> event_data mmuaux_dq" where
  "add_new_dq args rel1 rel2 nt aux = (if finite rel2 then
    (let (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done) = shift_dq args nt aux;
    I = args_ivl args; pos = args_pos args; inz = memL I 0;
    new_tstp = (if inz then Inr tp else Inl nt);
    tstp_dq = dq_push nt tstp_dq;
    P = (\<lambda>t. memL I (nt - dq_nth tstp_dq (t - (tp - len))));
    (tbl, a2_dq', result') = fold (until_elem_step_dq a1_map (args_L args) (args_R args) pos tp len inz P new_tstp)
      (csorted_list_of_set rel2) ({}, a2_dq, result);
    tables = append_queue (tbl, new_tstp) tables;
    a2_dq = dq_push Mapping.empty a2_dq';
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    tss = append_queue nt tss in
    (tp + 1, tss, tables, len + 1, result', a1_map, a2_dq, tstp_dq, done))
  else dq_of_uaux (add_new_mmuaux args rel1 rel2 nt (uaux_of_dq aux)))"

subsection \<open>Combined structure: deques without aggregation, the aggregation structure otherwise\<close>

datatype muaux_dq = MU_agg mmauaux | MU_dq "event_data mmuaux_dq"

definition init_muaux_dq :: "args \<Rightarrow> muaux_dq" where
  "init_muaux_dq args = (if args_agg args = None then MU_dq (init_dq args) else MU_agg (init_mmauaux args))"

fun add_new_muaux_dq :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> muaux_dq \<Rightarrow> muaux_dq" where
  "add_new_muaux_dq args rel1 rel2 nt (MU_dq d) = MU_dq (add_new_dq args rel1 rel2 nt d)"
| "add_new_muaux_dq args rel1 rel2 nt (MU_agg a) = MU_agg (add_new_mmauaux args rel1 rel2 nt a)"

fun length_muaux_dq :: "args \<Rightarrow> muaux_dq \<Rightarrow> nat" where
  "length_muaux_dq args (MU_dq d) = length_dq args d"
| "length_muaux_dq args (MU_agg a) = length_mmauaux args a"

fun eval_muaux_dq :: "args \<Rightarrow> ts \<Rightarrow> muaux_dq \<Rightarrow> event_data table list \<times> muaux_dq" where
  "eval_muaux_dq args nt (MU_dq d) = (let (res, d') = eval_dq args nt d in (res, MU_dq d'))"
| "eval_muaux_dq args nt (MU_agg a) = (let (res, a') = eval_mmauaux' args nt a in (res, MU_agg a'))"

fun valid_muaux_dq :: "args \<Rightarrow> ts \<Rightarrow> muaux_dq \<Rightarrow> event_data muaux \<Rightarrow> bool" where
  "valid_muaux_dq args cur (MU_dq d) auxlist \<longleftrightarrow> (\<exists>a. rel_uaux d a \<and> valid_mmuaux args cur a auxlist)"
| "valid_muaux_dq args cur (MU_agg a) auxlist \<longleftrightarrow> valid_mmauaux args cur a auxlist"

lemma ID_ccompare_etuple_dq: "ID CCOMPARE(event_data tuple) \<noteq> None"
  by (simp add: ccompare_list_def ccompare_option_def ccompare_event_data_def ID_def split: option.splits)

end
(*>*)

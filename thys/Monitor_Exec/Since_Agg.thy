(*<*)
theory Since_Agg
  imports Window Frame_Aux Agg_Gen
begin
(*>*)



section \<open>The Since window with the aggregation fused in\<close>

text \<open>
  The kernel folds an aggregation over a Since into the Since node (@{const args_agg}) and its
  structure keeps the aggregate incrementally, in @{typ aggaux}: a count, a sum or a rank tree
  per group, updated as tuples enter and leave.  The executable evaluator unfuses the two, a
  @{text EAgg} node over a @{text ESince} whose window reports the plain union, and recomputes
  the aggregate from the union at every time point.  This theory fuses them again for the
  window: the count set already makes a tuple's entry into and exit from the union explicit, and
  those are exactly the events the kernel's incremental structure takes.

  The executable aggregation @{const uagg} is stated on the window's own tuples, which list the
  operand's columns in ascending order.  The kernel's @{const eval_agg}, and hence
  @{const valid_maggaux}, reads its tuples over an arbitrary column list, so the window's tuples
  are themselves tuples of the kernel at the ascending column list of the operand, and the first
  lemma below says that the executable aggregation is the kernel's there, with the result column
  moved from the front, where the kernel puts it, to its place in the ascending order -- an
  instance of @{thm [source] uagg_eval_agg}.
\<close>

subsection \<open>The executable aggregation as the kernel's\<close>

text \<open>The parameters of a @{text EAgg} node: @{text g0}, the operator, the term, the number of
  bound variables and the position of the result column.\<close>

type_synonym eaggp = "bool \<times> ty Formula.agg_op \<times> Formula.trm \<times> nat \<times> nat"

fun eagg_p :: "eaggp \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "eagg_p (g0, \<omega>, f, k, pos) = uagg g0 \<omega> f k pos"

text \<open>What the parameters must satisfy at a window over tuples of width @{text w}.\<close>

fun eagg_ok :: "eaggp \<Rightarrow> nat \<Rightarrow> bool" where
  "eagg_ok (g0, \<omega>, f, k, pos) w \<longleftrightarrow>
     k \<le> w \<and> pos \<le> w - k \<and> Formula.fv_trm f \<subseteq> {0..<w} \<and> (g0 \<longrightarrow> w = k)"

text \<open>The kernel's frame: the group columns are all of the result's columns but the result
  column, and the term reads the tuple at those columns.\<close>

fun eagg_gcols :: "eaggp \<Rightarrow> nat \<Rightarrow> cols" where
  "eagg_gcols (g0, \<omega>, f, k, pos) w = [0..<pos] @ [Suc pos..<Suc (w - k)]"

fun shift_trm :: "nat \<Rightarrow> Formula.trm \<Rightarrow> Formula.trm" where
  "shift_trm b (Formula.Var x) = Formula.Var (if x < b then x else Suc x)"
| "shift_trm b (Formula.Const c) = Formula.Const c"
| "shift_trm b (Formula.Plus a c) = Formula.Plus (shift_trm b a) (shift_trm b c)"
| "shift_trm b (Formula.Minus a c) = Formula.Minus (shift_trm b a) (shift_trm b c)"
| "shift_trm b (Formula.UMinus a) = Formula.UMinus (shift_trm b a)"
| "shift_trm b (Formula.Mult a c) = Formula.Mult (shift_trm b a) (shift_trm b c)"
| "shift_trm b (Formula.Div a c) = Formula.Div (shift_trm b a) (shift_trm b c)"
| "shift_trm b (Formula.Mod a c) = Formula.Mod (shift_trm b a) (shift_trm b c)"
| "shift_trm b (Formula.F2i a) = Formula.F2i (shift_trm b a)"
| "shift_trm b (Formula.I2f a) = Formula.I2f (shift_trm b a)"

fun eagg_ccols :: "eaggp \<Rightarrow> nat \<Rightarrow> cols" where
  "eagg_ccols (g0, \<omega>, f, k, pos) w = agg_cols k (eagg_gcols (g0, \<omega>, f, k, pos) w)"

fun eagg_args :: "eaggp \<Rightarrow> nat \<Rightarrow> aggargs" where
  "eagg_args (g0, \<omega>, f, k, pos) w =
     \<lparr>aggargs_cols = eagg_ccols (g0, \<omega>, f, k, pos) w, aggargs_n = Suc (w - k),
      aggargs_g0 = g0, aggargs_y = pos, aggargs_\<omega> = \<omega>, aggargs_tys = replicate k Formula.TInt,
      aggargs_f = shift_trm (k + pos) f\<rparr>"

abbreviation ewf_table :: "nat \<Rightarrow> 'b list set \<Rightarrow> bool" where
  "ewf_table w T \<equiv> \<forall>x \<in> T. length x = w"

text \<open>The kernel puts the result column in front of the group key; the executable order puts it at
  its place among the group's columns.\<close>

definition slot :: "nat \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "slot p x = take p (tl x) @ hd x # drop p (tl x)"

subsection \<open>The aggregate alongside the count set\<close>

text \<open>
  The count set makes a tuple's entry into and exit from the window's union explicit: a table
  added contributes the tuples not yet in the union, a table removed takes out the tuples it was
  the last to hold.  Those are the insertions and deletions the kernel's incremental structure
  takes.  The structure is optional, as in the kernel: @{const None} once an operation reports
  that it cannot maintain the aggregate, and then the result is computed from the union
  directly.  The kernel's operations are named @{text kag_} here: the window keeps the
  structure of the next subsection, which they serve as the specification of.
\<close>

definition cnt_enter :: "event_data table \<Rightarrow> cntset \<Rightarrow> event_data table" where
  "cnt_enter T cc = T - snd cc"

definition cnt_leave :: "event_data table \<Rightarrow> cntset \<Rightarrow> event_data table" where
  "cnt_leave T cc = Set.filter (\<lambda>x. Mapping.lookup (fst cc) x = Some 1) T"

definition kag_init :: "eaggp \<Rightarrow> nat \<Rightarrow> aggaux option" where
  "kag_init p w = init_maggaux' (eagg_args p w)"

definition kag_ins :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data table \<Rightarrow> cntset \<Rightarrow> aggaux option \<Rightarrow> aggaux option" where
  "kag_ins p w T cc ax = insert_maggaux' (eagg_args p w) (cnt_enter T cc) ax"

definition kag_del :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data table \<Rightarrow> cntset \<Rightarrow> aggaux option \<Rightarrow> aggaux option" where
  "kag_del p w T cc ax = delete_maggaux' (eagg_args p w) (cnt_leave T cc) ax"

definition kag_inv :: "eaggp \<Rightarrow> nat \<Rightarrow> cntset \<Rightarrow> aggaux option \<Rightarrow> bool" where
  "kag_inv p w cc ax \<longleftrightarrow> valid_maggaux' (eagg_args p w) ax (snd cc)"

subsection \<open>The aggregate over the window's own tuples\<close>

text \<open>
  The kernel's structure keys a group by @{const agg_key}, which at the ascending frame is the
  tuple's suffix after the bound columns, and reads the value by the shifted term, which there
  is the term itself.  The structure @{typ "event_data gagg"} of
  @{theory MFODL_Monitor_Exec.Agg_Gen} reads both off the tuple directly, and
  @{text Rk} maps it to the kernel's.  The kernel's steps are the steps below under
  @{text Rk}, and so are the folds, the initial structure and the result.
\<close>

fun Rk :: "event_data gagg \<Rightarrow> aggaux" where
  "Rk (GCnt m) = CntAux m"
| "Rk (GSum m) = SumAux m"
| "Rk (GRank m ty) = RankAux (m, ty)"

text \<open>The window's aggregate: the structure over the window's own tuples, fed with the sorted
  list of what enters and what leaves, and read with the result column filled in.  Its
  invariant is the kernel's, under @{const Rk}.\<close>

type_synonym egagg = "event_data gagg"

definition ag_init :: "eaggp \<Rightarrow> nat \<Rightarrow> 'b gagg option" where
  "ag_init p w = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> ginit \<omega>)"

definition ag_ins :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data table \<Rightarrow> cntset \<Rightarrow> egagg option \<Rightarrow> egagg option" where
  "ag_ins p w T cc ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     gins k (umeval_trm f) (filter (\<lambda>t. t \<notin> snd cc) (csl T)) ax)"

definition ag_del :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data table \<Rightarrow> cntset \<Rightarrow> egagg option \<Rightarrow> egagg option" where
  "ag_del p w T cc ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     gdel k (umeval_trm f) (filter (\<lambda>t. Mapping.lookup (fst cc) t = Some 1) (csl T)) ax)"

definition ag_res :: "eaggp \<Rightarrow> nat \<Rightarrow> cntset \<Rightarrow> egagg option \<Rightarrow> event_data table" where
  "ag_res p w cc ax = (case ax of
     None \<Rightarrow> eagg_p p (snd cc)
   | Some a \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gres g0 \<omega> pos id a))"

definition ag_inv :: "eaggp \<Rightarrow> nat \<Rightarrow> cntset \<Rightarrow> egagg option \<Rightarrow> bool" where
  "ag_inv p w cc ax \<longleftrightarrow> kag_inv p w cc (map_option Rk ax)"

subsection \<open>The window, with the aggregate\<close>

text \<open>
  The window of @{theory MFODL_Monitor_Exec.Window} again, with the aggregate carried along:
  the two scans update it with every table that enters or leaves, the reset on a failed left
  operand starts it afresh, and the result is the aggregate's rather than the union.  The
  structure's validity is the window's, at a frame whose columns are all of the node's, together
  with the aggregate's invariant for the window's count set.
\<close>

type_synonym swagg = "swaux \<times> egagg option"

function sa_move :: "args \<Rightarrow> eaggp \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow>
    (ts \<times> event_data table) queue \<Rightarrow> cntset \<Rightarrow> egagg option \<Rightarrow>
    (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times> cntset \<times> egagg option" where
  "sa_move args p nt pend win cc ax =
     (case safe_hd pend of
        (None, pend') \<Rightarrow> (pend', win, cc, ax)
      | (Some e, pend') \<Rightarrow>
        (if memL (args_ivl args) (nt - fst e)
         then (if memR (args_ivl args) (nt - fst e)
               then sa_move args p nt (tl_queue pend') (append_queue e win) (cnt_add (snd e) cc)
                      (ag_ins p (args_n args) (snd e) cc ax)
               else sa_move args p nt (tl_queue pend') win cc ax)
         else (pend', win, cc, ax)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, p, nt, pend, win, cc, ax). length (linearize pend))")
     (fastforce split: prod.splits)+

declare sa_move.simps[simp del]

function sa_expire :: "args \<Rightarrow> eaggp \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow> cntset \<Rightarrow>
    egagg option \<Rightarrow> (ts \<times> event_data table) queue \<times> cntset \<times> egagg option" where
  "sa_expire args p nt win cc ax =
     (case safe_hd win of
        (None, win') \<Rightarrow> (win', cc, ax)
      | (Some e, win') \<Rightarrow>
        (if memR (args_ivl args) (nt - fst e) then (win', cc, ax)
         else sa_expire args p nt (tl_queue win') (cnt_del (snd e) cc)
                (ag_del p (args_n args) (snd e) cc ax)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, p, nt, win, cc, ax). length (linearize win))")
     (fastforce split: prod.splits)+

declare sa_expire.simps[simp del]

fun sw_cc :: "swaux \<Rightarrow> cntset" where
  "sw_cc (t, pend, win, cc) = cc"

definition sa_init :: "args \<Rightarrow> eaggp \<Rightarrow> swagg" where
  "sa_init args p = (sw_init args, ag_init p (args_n args))"

definition sa_add_new_ts :: "args \<Rightarrow> eaggp \<Rightarrow> ts \<Rightarrow> swagg \<Rightarrow> swagg" where
  "sa_add_new_ts args p nt aux = (case aux of ((t, pend, win, cc), ax) \<Rightarrow>
     (case sa_move args p nt pend win cc ax of (pend', win', cc', ax') \<Rightarrow>
      (case sa_expire args p nt win' cc' ax' of (win'', cc'', ax'') \<Rightarrow>
        ((nt, pend', win'', cc''), ax''))))"

definition sa_join :: "args \<Rightarrow> eaggp \<Rightarrow> event_data table \<Rightarrow> swagg \<Rightarrow> swagg" where
  "sa_join args p X aux = (case aux of (w, ax) \<Rightarrow>
     (sw_join args X w,
      if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then ax
      else ag_init p (args_n args)))"

definition sa_add_new_table :: "args \<Rightarrow> eaggp \<Rightarrow> event_data table \<Rightarrow> swagg \<Rightarrow> swagg" where
  "sa_add_new_table args p X aux = (case aux of ((t, pend, win, cc), ax) \<Rightarrow>
     (if memL (args_ivl args) 0
      then ((t, pend, append_queue (t, X) win, cnt_add X cc), ag_ins p (args_n args) X cc ax)
      else ((t, append_queue (t, X) pend, win, cc), ax)))"

definition sa_result :: "args \<Rightarrow> eaggp \<Rightarrow> swagg \<Rightarrow> event_data table" where
  "sa_result args p aux = (case aux of (w, ax) \<Rightarrow> ag_res p (args_n args) (sw_cc w) ax)"

definition valid_sa :: "args \<Rightarrow> eaggp \<Rightarrow> ts \<Rightarrow> swagg \<Rightarrow> event_data msaux \<Rightarrow> bool" where
  "valid_sa args p cur aux auxlist \<longleftrightarrow> (case aux of (w, ax) \<Rightarrow>
     valid_sw args cur w auxlist \<and> length (args_R args) = args_n args \<and>
     eagg_ok p (args_n args) \<and> ag_inv p (args_n args) (sw_cc w) ax)"

section \<open>The executable fused Since window\<close>

text \<open>
  The fused aggregation window the executable evaluator runs: its count structure is a mapping alone,
  and its read is guarded by the node's constraint; the result cache of
  @{text Agg_Cache} is built on it.  This section provides the window, and proves that it
  refines the fused window above.
\<close>

subsection \<open>The count mapping\<close>

text \<open>
  The count structure of @{theory MFODL_Monitor_Exec.Window} keeps the tuples' counts in a
  mapping and their keys in a set beside it, so that the plain window can hand out its union in
  one step.  The fused window never hands out that union -- it hands out the aggregate, and reads
  the count structure only to learn which tuples enter the window and which leave it.  The
  mapping answers both, so the fused window keeps the mapping alone and pays one tree operation
  per tuple where the plain window pays two.  @{text ucc} reads the count structure off it: the
  key set is the mapping's domain, which is what the plain window's second half always was.
\<close>

type_synonym ucnt = "(event_data list, nat) mapping"

definition ucnt_add1 :: "event_data list \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_add1 t c = (case Mapping.lookup c t of
     None \<Rightarrow> Mapping.update t 1 c
   | Some k \<Rightarrow> Mapping.update t (k + 1) c)"

definition ucnt_del1 :: "event_data list \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_del1 t c = (case Mapping.lookup c t of
     None \<Rightarrow> c
   | Some k \<Rightarrow> (if k \<le> 1 then Mapping.delete t c else Mapping.update t (k - 1) c))"

definition ucnt_add :: "event_data list set \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_add T c = fold ucnt_add1 (csl T) c"

definition ucnt_del :: "event_data list set \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_del T c = fold ucnt_del1 (csl T) c"

fun ucc :: "ucnt \<Rightarrow> cntset" where
  "ucc c = (c, Mapping.keys c)"

declare ucc.simps[simp del]

lemma fold_cnt_del1_ucc: "fold cnt_del1 xs (ucc c) = ucc (fold ucnt_del1 xs c)"
  by (induct xs arbitrary: c) (simp_all add: cnt_del1_ucc)

lemma cnt_add_ucc[simp]: "cnt_add T (ucc c) = ucc (ucnt_add T c)"
  by (simp add: cnt_add_def ucnt_add_def fold_cnt_add1_ucc)

lemma cnt_del_ucc[simp]: "cnt_del T (ucc c) = ucc (ucnt_del T c)"
  by (simp add: cnt_del_def ucnt_del_def fold_cnt_del1_ucc)

text \<open>What enters the window is what the mapping does not hold yet, and what leaves it is what
  it holds exactly once: both are read off the mapping, one lookup per tuple.\<close>

type_synonym ugagg = "event_data gagg"

definition uag_ins :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> ucnt \<Rightarrow>
    ugagg option \<Rightarrow> ugagg option" where
  "uag_ins p w T c ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     gins k (umeval_trm f) (filter (\<lambda>t. Mapping.lookup c t = None) (csl T)) ax)"

definition uag_del :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> ucnt \<Rightarrow>
    ugagg option \<Rightarrow> ugagg option" where
  "uag_del p w T c ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     gdel k (umeval_trm f) (filter (\<lambda>t. Mapping.lookup c t = Some 1) (csl T)) ax)"

lemma ag_ins_ucc[simp]: "ag_ins p w T (ucc c) ax = uag_ins p w T c ax"
  by (cases p) (simp add: ag_ins_def uag_ins_def ucc.simps lookup_None_keys)

lemma ag_del_ucc[simp]: "ag_del p w T (ucc c) ax = uag_del p w T c ax"
  by (cases p) (simp add: ag_del_def uag_del_def ucc.simps)

subsection \<open>The node's guard\<close>

text \<open>
  A node whose result is an aggregate is often read through a constraint on the aggregate's own
  value: \<^verbatim>\<open>(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r\<close> is the shape of a whole family of
  policies.  Compiled as a filter over the node, that builds the table of all groups and then
  drops most of it again -- every group that fails the constraint is inserted into a tree only
  to be removed from the next one.  The constraint is carried by the node instead, as the guard
  below, and the read inserts only the groups that pass.  The guard is @{const None} at a node
  that carries no constraint, and then it admits everything.
\<close>

type_synonym uconstr = "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"

definition uqok :: "uconstr option \<Rightarrow> event_data list \<Rightarrow> bool" where
  "uqok q = (case q of None \<Rightarrow> (\<lambda>_. True) | Some c \<Rightarrow> ueval_constraint c)"

definition ufilt :: "uconstr option \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "ufilt q X = Set.filter (uqok q) X"

lemma uqok_None[simp]: "uqok None = (\<lambda>_. True)"
  by (simp add: uqok_def)

lemma ufilt_None[simp]: "ufilt None = id"
  by (simp add: ufilt_def fun_eq_iff)

lemma ufilt_idem[simp]: "ufilt q (ufilt q X) = ufilt q X"
  by (auto simp: ufilt_def)

text \<open>The result writes the aggregate into each group and keeps what passes the node's guard.
  The fused form walks the mapping's entries -- the key and its value together, so no lookup --
  and inserts the node's own tuple straight into the answer.\<close>

definition ugmr :: "(event_data list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ('b \<Rightarrow> event_data) \<Rightarrow>
    (event_data list, 'b) mapping \<Rightarrow> event_data list set" where
  "ugmr q p f m = Set.filter q (gmr p (\<lambda>x. x) f m)"

lemma ugmr_code[code]:
  fixes t :: "(event_data list, 'b) mapping_rbt"
  shows "ugmr q p f (RBT_Mapping t) =
    (case ID CCOMPARE(event_data list) of
       None \<Rightarrow> Code.abort (STR ''ugmr RBT_Mapping: ccompare = None'')
                (\<lambda>_. ugmr q p f (RBT_Mapping t))
     | Some _ \<Rightarrow> fold (\<lambda>e A. let v = take p (fst e) @ f (snd e) # drop p (fst e)
                    in if q v then Set.insert v A else A)
                  (RBT_Mapping2.entries t) {})"
proof (cases "ID CCOMPARE(event_data list)")
  case (Some c)
  note comp = ID_ccompare'[OF Some]
  have dist: "distinct (map fst (RBT_Mapping2.entries t))"
    using Some by (transfer fixing: c)
      (simp add: ord.is_rbt_def linorder.distinct_entries[OF comparator.linorder[OF comp]])
  have mo: "map_of (RBT_Mapping2.entries t) (fst e) = Some (snd e)"
    if "e \<in> set (RBT_Mapping2.entries t)" for e
    using dist that by (cases e) simp
  have lk: "Mapping.lookup (RBT_Mapping t) = map_of (RBT_Mapping2.entries t)"
    by (simp add: lookup_Mapping_code(1) Some del: RBT_Mapping_def)
  have ky: "Mapping.keys (RBT_Mapping t) = fst ` set (RBT_Mapping2.entries t)"
    unfolding Mapping.keys_dom_lookup lk by (rule dom_map_of_conv_image_fst)
  have "ugmr q p f (RBT_Mapping t)
      = Set.filter q ((\<lambda>e. take p (fst e) @ f (snd e) # drop p (fst e))
          ` set (RBT_Mapping2.entries t))"
    unfolding ugmr_def gmr_def ky lk image_image
    by (intro arg_cong[of _ _ "Set.filter q"] image_cong[OF refl]) (simp add: mo)
  then show ?thesis using Some by (simp add: fold_insert_filter_image)
qed simp

definition ugres :: "(event_data list \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> ugagg \<Rightarrow>
    event_data list set" where
  "ugres q g0 \<omega> p a = Set.filter q (gres g0 \<omega> p (\<lambda>x. x) a)"

lemma ugres_code[code]:
  "ugres q g0 \<omega> p a = (case a of
     GCnt m \<Rightarrow> (if g0 \<and> Mapping.is_empty m then Set.filter q {[eval_agg_op \<omega> {}]}
       else ugmr q p (\<lambda>k. EInt (integer_of_int k)) m)
   | GSum m \<Rightarrow> (if g0 \<and> Mapping.is_empty m then Set.filter q {[eval_agg_op \<omega> {}]}
       else (case fst \<omega> of
         Formula.Agg_Sum \<Rightarrow> ugmr q p (\<lambda>k. EInt (snd k)) m
       | Formula.Agg_Avg \<Rightarrow> ugmr q p
           (\<lambda>k. EFloat (double_of_event_data (EInt (snd k)) / double_of_int (fst k))) m
       | _ \<Rightarrow> {}))
   | GRank m ty \<Rightarrow> (if g0 \<and> Mapping.is_empty m then Set.filter q {[eval_agg_op \<omega> {}]}
       else (case fst \<omega> of
         Formula.Agg_Min \<Rightarrow> ugmr q p (\<lambda>k. get_edata_list k 0) m
       | Formula.Agg_Max \<Rightarrow> ugmr q p (\<lambda>k. get_edata_list k (get_length k - 1)) m
       | Formula.Agg_Med \<Rightarrow> ugmr q p (\<lambda>k. let u = get_length k; u' = u div 2;
           aggval = (if even u
             then (double_of_event_data_agg (get_edata_list k (u' - 1))
                   + double_of_event_data_agg (get_edata_list k u')) / double_of_int 2
             else double_of_event_data_agg (get_edata_list k u'))
           in EFloat aggval) m
       | _ \<Rightarrow> {})))"
  by (cases a) (simp_all add: ugres_def ugmr_def Mapping.is_empty_def
      split: Formula.agg_type.splits)

definition uag_res :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> ucnt \<Rightarrow>
    ugagg option \<Rightarrow> event_data list set" where
  "uag_res q p w c ax = ufilt q (case ax of
     None \<Rightarrow> eagg_p p (Mapping.keys c)
   | Some a \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gres g0 \<omega> pos (\<lambda>x. x) a))"

lemma uag_res_code[code]:
  "uag_res q p w c ax = (case ax of
     None \<Rightarrow> ufilt q (eagg_p p (Mapping.keys c))
   | Some a \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> ugres (uqok q) g0 \<omega> pos a))"
  by (simp add: uag_res_def ugres_def ufilt_def split: option.splits prod.splits)

lemma ag_res_ucc_None[simp]: "ag_res p w (ucc c) ax = uag_res None p w c ax"
  using ag_res_ucc[of None] by simp

(*<*)
end
(*>*)

(*<*)
theory Dense_Imp
  imports Monitor_Imp2
begin
(*>*)

section \<open>Tuples without their empty columns\<close>

text \<open>
  Every table of the monitor is a set of tuples of one width, the number of free variables of the
  whole formula, and @{const wf_tuple} says that a tuple carries @{const None} at exactly the
  positions outside the free variables of the subformula that produced it.  Those positions are
  therefore the same for every tuple of a table and are known from the formula alone: on the P2
  benchmark 65\% of the positions the comparator walks are such holes, on P3 64\%, and the
  predicate @{term "report(t)"} of P2 is stored as three positions of which one carries a value.

  This theory represents a table by its tuples with the holes removed, and keeps the column list
  -- the free variables, in increasing order -- next to the table in the formula.  The order of
  two tuples is unchanged by deleting a fixed set of positions from both, so every operation that
  only compares or collects tuples works on the short form untouched; that is why the Since and
  Until structures of Sections 16 and 17 need no change at all.  What does need the column list
  is every operation that reads a tuple by position: the join, the projection, the predicate, and
  the constraints.

  Definitions only, no proofs, as elsewhere in this session.
\<close>

type_synonym cols = "nat list"

subsection \<open>Masks\<close>

text \<open>A mask marks the positions of a tuple that a projection keeps.  Unlike @{const proj_tuple},
  which overwrites the dropped positions with @{const None} and so preserves the width, the
  projection here deletes them.\<close>

fun dproj :: "bool list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
  "dproj [] xs = []"
| "dproj (True # bs) (x # xs) = x # dproj bs xs"
| "dproj (False # bs) (x # xs) = dproj bs xs"
| "dproj (b # bs) [] = []"

text \<open>The inverse, for the boundary with the unmodified evaluator.\<close>

fun dwiden :: "bool list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
  "dwiden [] xs = []"
| "dwiden (False # bs) xs = None # dwiden bs xs"
| "dwiden (True # bs) (x # xs) = x # dwiden bs xs"
| "dwiden (True # bs) [] = []"

text \<open>The mask of a column list inside the full width, and the mask of a sublist of columns
  inside a column list.  Both argument lists are strictly increasing.\<close>

fun wide_mask_at :: "nat \<Rightarrow> nat \<Rightarrow> cols \<Rightarrow> bool list" where
  "wide_mask_at i 0 cs = []"
| "wide_mask_at i (Suc k) cs =
     (case cs of [] \<Rightarrow> False # wide_mask_at (Suc i) k []
      | c # cs' \<Rightarrow> if c = i then True # wide_mask_at (Suc i) k cs'
                   else False # wide_mask_at (Suc i) k cs)"

definition wide_mask :: "nat \<Rightarrow> cols \<Rightarrow> bool list" where
  "wide_mask n cs = wide_mask_at 0 n cs"

fun sub_mask :: "cols \<Rightarrow> cols \<Rightarrow> bool list" where
  "sub_mask [] ds = []"
| "sub_mask (c # cs) [] = False # sub_mask cs []"
| "sub_mask (c # cs) (d # ds) =
    (if c = d then True # sub_mask cs ds else False # sub_mask cs (d # ds))"

definition all_true :: "bool list \<Rightarrow> bool" where
  "all_true bs = list_all id bs"

subsection \<open>Merging two column lists\<close>

datatype mrg = MLft | MRgt | MBth

fun mrg_plan :: "cols \<Rightarrow> cols \<Rightarrow> mrg list" where
  "mrg_plan [] ds = map (\<lambda>_. MRgt) ds"
| "mrg_plan (c # cs) [] = MLft # mrg_plan cs []"
| "mrg_plan (c # cs) (d # ds) =
    (if c < d then MLft # mrg_plan cs (d # ds)
     else if d < c then MRgt # mrg_plan (c # cs) ds
     else MBth # mrg_plan cs ds)"

fun merge_cols :: "cols \<Rightarrow> cols \<Rightarrow> cols" where
  "merge_cols [] ds = ds"
| "merge_cols (c # cs) [] = c # merge_cols cs []"
| "merge_cols (c # cs) (d # ds) =
    (if c < d then c # merge_cols cs (d # ds)
     else if d < c then d # merge_cols (c # cs) ds
     else c # merge_cols cs ds)"

text \<open>The two masks that select the shared columns out of each side, and the mask that selects
  the left side's own columns out of the merged tuple.\<close>

fun mrg_left_key :: "mrg list \<Rightarrow> bool list" where
  "mrg_left_key [] = []"
| "mrg_left_key (MLft # p) = False # mrg_left_key p"
| "mrg_left_key (MRgt # p) = mrg_left_key p"
| "mrg_left_key (MBth # p) = True # mrg_left_key p"

fun mrg_right_key :: "mrg list \<Rightarrow> bool list" where
  "mrg_right_key [] = []"
| "mrg_right_key (MLft # p) = mrg_right_key p"
| "mrg_right_key (MRgt # p) = False # mrg_right_key p"
| "mrg_right_key (MBth # p) = True # mrg_right_key p"

subsection \<open>Joining two tuples\<close>

fun djoin1 :: "mrg list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple option" where
  "djoin1 [] xs ys = Some []"
| "djoin1 (MLft # p) (x # xs) ys = map_option (Cons x) (djoin1 p xs ys)"
| "djoin1 (MRgt # p) xs (y # ys) = map_option (Cons y) (djoin1 p xs ys)"
| "djoin1 (MBth # p) (x # xs) (y # ys) =
    (if x = y then map_option (Cons x) (djoin1 p xs ys) else None)"
| "djoin1 (m # p) xs ys = None"

text \<open>The merge of a tuple with one that is known to agree on the shared columns: no test.\<close>

fun dmerge :: "mrg list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
  "dmerge [] xs ys = []"
| "dmerge (MLft # p) (x # xs) ys = x # dmerge p xs ys"
| "dmerge (MRgt # p) xs (y # ys) = y # dmerge p xs ys"
| "dmerge (MBth # p) (x # xs) (y # ys) = x # dmerge p xs ys"
| "dmerge (m # p) xs ys = []"

subsection \<open>Joining two tables\<close>

text \<open>
  Three shapes.  When the right operand's columns are among the left's, every tuple of the left
  either does or does not have a partner and the join is a filter on a projection -- this is the
  anti-join of @{term "\<phi> AND NOT \<psi>"} and the intersection of two operands with equal columns.
  When the left's are among the right's it is the same the other way round.  Otherwise the right
  operand is indexed by the shared columns and the left probes it.
\<close>

definition dsemi :: "bool list \<Rightarrow> bool \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dsemi msk pos A B = Set.filter (\<lambda>a. (dproj msk a \<in> B) = pos) A"

definition dindex_step :: "bool list \<Rightarrow> event_data tuple \<Rightarrow>
    (event_data tuple, event_data tuple list) mapping \<Rightarrow>
    (event_data tuple, event_data tuple list) mapping" where
  "dindex_step msk b m = (let k = dproj msk b in
     (case Mapping.lookup m k of None \<Rightarrow> Mapping.update k [b] m
      | Some l \<Rightarrow> Mapping.update k (b # l) m))"

definition dindex :: "bool list \<Rightarrow> event_data table \<Rightarrow>
    (event_data tuple, event_data tuple list) mapping" where
  "dindex msk B = fold (dindex_step msk) (csorted_list_of_set B) Mapping.empty"

definition dprobe_step :: "mrg list \<Rightarrow> bool list \<Rightarrow>
    (event_data tuple, event_data tuple list) mapping \<Rightarrow> event_data tuple \<Rightarrow>
    event_data table \<Rightarrow> event_data table" where
  "dprobe_step p msk m a acc = (case Mapping.lookup m (dproj msk a) of
      None \<Rightarrow> acc
    | Some l \<Rightarrow> fold (\<lambda>b acc. Set.insert (dmerge p a b) acc) l acc)"

definition dgen_join :: "mrg list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
    event_data table \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dgen_join p lk rk A B =
     (let m = dindex rk B in fold (dprobe_step p lk m) (csorted_list_of_set A) empty_table)"

datatype djoin_plan =
    DJSub "bool list" | DJSup "bool list" | DJGen "mrg list" "bool list" "bool list"

definition no_right :: "mrg list \<Rightarrow> bool" where
  "no_right p = list_all (\<lambda>m. m \<noteq> MRgt) p"

definition no_left :: "mrg list \<Rightarrow> bool" where
  "no_left p = list_all (\<lambda>m. m \<noteq> MLft) p"

definition mk_djoin :: "cols \<Rightarrow> cols \<Rightarrow> djoin_plan" where
  "mk_djoin cs1 cs2 = (let p = mrg_plan cs1 cs2 in
     if no_right p then DJSub (mrg_left_key p)
     else if no_left p then DJSup (mrg_right_key p)
     else DJGen p (mrg_left_key p) (mrg_right_key p))"

text \<open>A negative join whose right operand has a column the left does not have cannot remove
  anything: the merged tuple would be wider than the one it is asked to equal.\<close>

fun dbin_join :: "djoin_plan \<Rightarrow> event_data table \<Rightarrow> bool \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dbin_join (DJSub msk) A pos B = dsemi msk pos A B"
| "dbin_join (DJSup msk) A pos B = (if pos then Set.filter (\<lambda>b. dproj msk b \<in> A) B else A)"
| "dbin_join (DJGen p lk rk) A pos B = (if pos then dgen_join p lk rk A B else A)"

subsection \<open>Narrowing at the boundary with the unmodified evaluator\<close>

definition dnarrow :: "bool list \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dnarrow msk r = (if all_true msk then r else dproj msk ` r)"

text \<open>A predicate whose arguments repeat a variable or carry a constant is matched tuple by
  tuple.  The image is taken on the table itself and the partial results are collected with
  @{const Option.these} at the type of tuples, as the kernel does: an image into the type of
  the matching functions has no comparator and would leave the result in a representation the
  printer cannot fold.\<close>

definition dmatch_table :: "Formula.trm list \<Rightarrow> cols \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dmatch_table tms cs X = Option.these ((\<lambda>x. map_option (\<lambda>f. map f cs) (match tms x)) ` X)"

subsection \<open>Re-indexing a term\<close>

fun col_pos :: "cols \<Rightarrow> nat \<Rightarrow> nat" where
  "col_pos [] x = 0"
| "col_pos (c # cs) x = (if c = x then 0 else Suc (col_pos cs x))"

fun reindex_trm :: "cols \<Rightarrow> Formula.trm \<Rightarrow> Formula.trm" where
  "reindex_trm cs (Formula.Var x) = Formula.Var (col_pos cs x)"
| "reindex_trm cs (Formula.Const c) = Formula.Const c"
| "reindex_trm cs (Formula.Plus a b) = Formula.Plus (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.Minus a b) = Formula.Minus (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.UMinus a) = Formula.UMinus (reindex_trm cs a)"
| "reindex_trm cs (Formula.Mult a b) = Formula.Mult (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.Div a b) = Formula.Div (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.Mod a b) = Formula.Mod (reindex_trm cs a) (reindex_trm cs b)"
| "reindex_trm cs (Formula.F2i a) = Formula.F2i (reindex_trm cs a)"
| "reindex_trm cs (Formula.I2f a) = Formula.I2f (reindex_trm cs a)"

definition reindex_constraint ::
    "cols \<Rightarrow> Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow>
     Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm" where
  "reindex_constraint cs conf = (case conf of (t1, p, c, t2) \<Rightarrow>
     (reindex_trm cs t1, p, c, reindex_trm cs t2))"

section \<open>A monitor over the short tuples\<close>

text \<open>
  The formula carries, at every node, the columns of the table the node produces.  A constructor
  the theory does not handle yet is wrapped in @{term DPure}, which evaluates it with the
  evaluation function of @{theory MFODL_Monitor_Imp.Monitor_Imp2} and deletes the holes from its
  result, so the two representations can be mixed and the fragment can grow one constructor at a
  time.  At the root the columns are all of them, so the verdicts have the width the printer
  expects and nothing is converted there.
\<close>

fun trm_vars :: "Formula.trm \<Rightarrow> nat list" where
  "trm_vars (Formula.Var x) = [x]"
| "trm_vars (Formula.Const c) = []"
| "trm_vars (Formula.Plus a b) = trm_vars a @ trm_vars b"
| "trm_vars (Formula.Minus a b) = trm_vars a @ trm_vars b"
| "trm_vars (Formula.UMinus a) = trm_vars a"
| "trm_vars (Formula.Mult a b) = trm_vars a @ trm_vars b"
| "trm_vars (Formula.Div a b) = trm_vars a @ trm_vars b"
| "trm_vars (Formula.Mod a b) = trm_vars a @ trm_vars b"
| "trm_vars (Formula.F2i a) = trm_vars a"
| "trm_vars (Formula.I2f a) = trm_vars a"

definition tms_cols :: "Formula.trm list \<Rightarrow> cols" where
  "tms_cols tms = csorted_list_of_set (set (concat (map trm_vars tms)))"

definition set_cols :: "nat set \<Rightarrow> cols" where
  "set_cols A = csorted_list_of_set A"

text \<open>The columns a subformula produces, where they can be read off it.\<close>

fun mcols :: "nat \<Rightarrow> mformula_j \<Rightarrow> cols option" where
  "mcols n (MPred e tms mode) = Some (tms_cols tms)"
| "mcols n (MAnd A \<phi> pos B \<psi> buf) =
    Some (if pos then merge_cols (set_cols A) (set_cols B) else set_cols A)"
| "mcols n (MAndRel \<phi> conf) = mcols n \<phi>"
| "mcols n (MOr \<phi> \<psi> buf) = mcols n \<phi>"
| "mcols n (MNeg \<phi>) = Some []"
| "mcols n (MExists \<phi>) = (case mcols (Suc n) \<phi> of None \<Rightarrow> None
    | Some cs \<Rightarrow> Some (map (\<lambda>x. x - 1) (filter (\<lambda>x. x \<noteq> 0) cs)))"
| "mcols n (MPrev I \<phi> first buf nts) = mcols n \<phi>"
| "mcols n (MNext I \<phi> first nts) = mcols n \<phi>"
| "mcols n (MSince args \<phi> \<psi> buf aux) = Some (set_cols (args_R args))"
| "mcols n (MUntil args \<phi> \<psi> buf nts t aux) = Some (set_cols (args_R args))"
| "mcols n \<phi> = None"

datatype dformula =
    DPure mformula_j nat "bool list"
  | DRel "event_data table"
  | DPredS Formula.name nat
  | DPredM Formula.name nat "Formula.trm list" cols
  | DAnd djoin_plan dformula bool dformula "event_data mebuf2"
  | DAndRel dformula "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | DOr dformula dformula "event_data mebuf2"
  | DNeg dformula
  | DExists dformula bool
  | DPrev \<I> dformula bool "event_data table mbuf_t" "ts mbuf_t"
  | DNext \<I> dformula bool "ts mbuf_t"
  | DSince args dformula dformula "event_data mebuf2S" msaux_j
  | DUntil args dformula dformula "event_data mebuf2" "ts mbuf_t" ts muaux_j

subsection \<open>Building it\<close>

fun dformula_of :: "nat \<Rightarrow> cols \<Rightarrow> mformula_j \<Rightarrow> dformula Heap" where
  "dformula_of n cs (MPred e tms mode) =
     return (if mode \<noteq> Match \<and> cs = tms_cols tms then DPredS e (length tms)
             else DPredM e (length tms) tms cs)"
| "dformula_of n cs (MRel rel) = return (DRel (dnarrow (wide_mask n cs) rel))"
| "dformula_of n cs (MAnd A \<phi> pos B \<psi> buf) = do {
     \<phi>d \<leftarrow> dformula_of n (set_cols A) \<phi>;
     \<psi>d \<leftarrow> dformula_of n (set_cols B) \<psi>;
     return (DAnd (mk_djoin (set_cols A) (set_cols B)) \<phi>d pos \<psi>d buf) }"
| "dformula_of n cs (MAndRel \<phi> conf) = do {
     \<phi>d \<leftarrow> dformula_of n cs \<phi>;
     return (DAndRel \<phi>d (reindex_constraint cs conf)) }"
| "dformula_of n cs (MOr \<phi> \<psi> buf) = do {
     \<phi>d \<leftarrow> dformula_of n cs \<phi>; \<psi>d \<leftarrow> dformula_of n cs \<psi>;
     return (DOr \<phi>d \<psi>d buf) }"
| "dformula_of n cs (MNeg \<phi>) = do {
     \<phi>d \<leftarrow> dformula_of n [] \<phi>; return (DNeg \<phi>d) }"
| "dformula_of n cs (MExists \<phi>) = (case mcols (Suc n) \<phi> of
     None \<Rightarrow> return (DPure (MExists \<phi>) n (wide_mask n cs))
   | Some ccs \<Rightarrow> do {
       \<phi>d \<leftarrow> dformula_of (Suc n) ccs \<phi>;
       return (DExists \<phi>d (case ccs of [] \<Rightarrow> False | c # _ \<Rightarrow> c = 0)) })"
| "dformula_of n cs (MPrev I \<phi> first buf nts) = do {
     \<phi>d \<leftarrow> dformula_of n cs \<phi>; return (DPrev I \<phi>d first buf nts) }"
| "dformula_of n cs (MNext I \<phi> first nts) = do {
     \<phi>d \<leftarrow> dformula_of n cs \<phi>; return (DNext I \<phi>d first nts) }"
| "dformula_of n cs (MSince args \<phi> \<psi> buf aux) =
     (if sevt_applies args then do {
        \<phi>d \<leftarrow> dformula_of n (set_cols (args_L args)) \<phi>;
        \<psi>d \<leftarrow> dformula_of n (set_cols (args_R args)) \<psi>;
        q \<leftarrow> init_j args;
        return (DSince args \<phi>d \<psi>d buf q) }
      else return (DPure (MSince args \<phi> \<psi> buf aux) n (wide_mask n cs)))"
| "dformula_of n cs (MUntil args \<phi> \<psi> buf nts t aux) =
     (if evt_applies args \<and> \<not> use_heap_until then do {
        \<phi>d \<leftarrow> dformula_of n (set_cols (args_L args)) \<phi>;
        \<psi>d \<leftarrow> dformula_of n (set_cols (args_R args)) \<psi>;
        d \<leftarrow> init_u_j args;
        return (DUntil args \<phi>d \<psi>d buf nts t d) }
      else return (DPure (MUntil args \<phi> \<psi> buf nts t aux) n (wide_mask n cs)))"
| "dformula_of n cs \<phi> = return (DPure \<phi> n (wide_mask n cs))"

subsection \<open>Evaluating it\<close>

fun deval :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> dformula \<Rightarrow> (event_data table list \<times> dformula) Heap" where
  "deval j ts db (DPure \<phi> n msk) = do {
     (xs, \<phi>) \<leftarrow> meval_j j n ts db \<phi>;
     return (map (dnarrow msk) xs, DPure \<phi> n msk) }"
| "deval j ts db (DRel rel) = return (replicate (length ts) rel, DRel rel)"
| "deval j ts db (DPredS e ar) = return
     ((case Mapping.lookup db (e, ar) of None \<Rightarrow> replicate (length ts) empty_table | Some xs \<Rightarrow> xs),
      DPredS e ar)"
| "deval j ts db (DPredM e ar tms cs) = return
     ((case Mapping.lookup db (e, ar) of None \<Rightarrow> replicate (length ts) empty_table
       | Some xs \<Rightarrow> map (dmatch_table tms cs) xs),
      DPredM e ar tms cs)"
| "deval j ts db (DAnd pl \<phi> pos \<psi> buf) = do {
     (xs, \<phi>) \<leftarrow> deval j ts db \<phi>;
     (ys, \<psi>) \<leftarrow> deval j ts db \<psi>;
     return (let (zs, buf) = mebuf2_take (\<lambda>r1 r2. dbin_join pl r1 pos r2) (mebuf2_add xs ys buf)
       in (zs, DAnd pl \<phi> pos \<psi> buf)) }"
| "deval j ts db (DAndRel \<phi> conf) = do {
     (xs, \<phi>) \<leftarrow> deval j ts db \<phi>;
     return (map (Set.filter (eval_constraint conf)) xs, DAndRel \<phi> conf) }"
| "deval j ts db (DOr \<phi> \<psi> buf) = do {
     (xs, \<phi>) \<leftarrow> deval j ts db \<phi>;
     (ys, \<psi>) \<leftarrow> deval j ts db \<psi>;
     return (let (zs, buf) = mebuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mebuf2_add xs ys buf)
       in (zs, DOr \<phi> \<psi> buf)) }"
| "deval j ts db (DNeg \<phi>) = do {
     (xs, \<phi>) \<leftarrow> deval j ts db \<phi>;
     return (map (\<lambda>r. if r = empty_table then unit_table 0 else empty_table) xs, DNeg \<phi>) }"
| "deval j ts db (DExists \<phi> drop0) = do {
     (xs, \<phi>) \<leftarrow> deval j ts db \<phi>;
     return (if drop0 then map (\<lambda>r. tl ` r) xs else xs, DExists \<phi> drop0) }"
| "deval j ts db (DPrev I \<phi> first buf nts) = do {
     (xs, \<phi>) \<leftarrow> deval j ts db \<phi>;
     return (if first \<and> ts = [] then ([], DPrev I \<phi> True (buf @@ xs) (nts @@ ts))
       else let (zs, buf, nts) = meprev_next I (buf @@ xs) (nts @@ ts)
         in (if first then empty_table # zs else zs, DPrev I \<phi> False buf nts)) }"
| "deval j ts db (DNext I \<phi> first nts) = do {
     (xs, \<phi>) \<leftarrow> deval j ts db \<phi>;
     return (let (xs, first) = (case (xs, first) of (_ # xs, True) \<Rightarrow> (xs, False) | a \<Rightarrow> a);
       (zs, buf, nts) = meprev_next I (mbuf_t_empty @@ xs) (nts @@ ts)
       in (zs, DNext I \<phi> first nts)) }"
| "deval j ts db (DSince args \<phi> \<psi> buf aux) = do {
     (xs, \<phi>) \<leftarrow> deval j ts db \<phi>;
     (ys, \<psi>) \<leftarrow> deval j ts db \<psi>;
     (zs, buf, aux) \<leftarrow> eval_since_j args [] (mebuf2S_add xs ys ts buf) aux;
     return (zs, DSince args \<phi> \<psi> buf aux) }"
| "deval j ts db (DUntil args \<phi> \<psi> buf nts t aux) = do {
     (xs, \<phi>) \<leftarrow> deval j ts db \<phi>;
     (ys, \<psi>) \<leftarrow> deval j ts db \<psi>;
     r \<leftarrow> mebuf2t_take_j (add_new_u_j args) aux (mebuf2_add xs ys buf) t (nts @@ ts);
     (case r of (aux, buf, nt, nts') \<Rightarrow>
      do { z \<leftarrow> eval_u_j args nt aux;
           return (fst z, DUntil args \<phi> \<psi> buf nts' nt (snd z)) }) }"

subsection \<open>The state\<close>

type_synonym dstate = "nat \<times> nat \<times> dformula \<times> nat \<times> ts queue"

definition mstep_d :: "database \<times> ts \<Rightarrow> dstate \<Rightarrow> ((nat \<times> ts \<times> event_data table) list \<times> dstate) Heap" where
  "mstep_d tdb sti = (case sti of (i, j, m, n, tq) \<Rightarrow> do {
     (vs, m') \<leftarrow> deval (j + 1) [snd tdb] (fst tdb) m;
     return (case annotate_verdicts_j i (append_queue (snd tdb) tq) vs [] of
       (i', tq', vs') \<Rightarrow> (vs', (i', j + 1, m', n, tq'))) })"

definition minit_safe_d :: "ty Formula.formula \<Rightarrow> dstate Heap" where
  "minit_safe_d \<phi> = do {
     m \<leftarrow> mformula_j_of (meinit0 (Formula.nfv \<phi>) \<phi>);
     d \<leftarrow> dformula_of (Formula.nfv \<phi>) [0..<Formula.nfv \<phi>] m;
     return (0, 0, d, Formula.nfv \<phi>, empty_queue) }"

(*<*)
end
(*>*)

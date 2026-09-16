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

definition set_cols :: "nat set \<Rightarrow> cols" where
  "set_cols A = csorted_list_of_set A"

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

text \<open>The index is built on the smaller side and the larger one probes it, as in
  @{const bin_join}: indexing costs a lookup per tuple of the indexed side and probing one per
  tuple of the other, so indexing the larger side buys a big index that is read a few times.
  The first version of this join always indexed the right operand, which on the complex
  benchmark is the sliding window of an @{text ONCE} against a fifty-tuple predicate, and it
  was slower than the kernel's own pure join.\<close>

definition dprobe_step_l :: "mrg list \<Rightarrow> bool list \<Rightarrow>
    (event_data tuple, event_data tuple list) mapping \<Rightarrow> event_data tuple \<Rightarrow>
    event_data table \<Rightarrow> event_data table" where
  "dprobe_step_l p rk m y acc = (case Mapping.lookup m (dproj rk y) of
      None \<Rightarrow> acc
    | Some l \<Rightarrow> fold (\<lambda>x acc. Set.insert (dmerge p x y) acc) l acc)"

definition dgen_join :: "mrg list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
    event_data table \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dgen_join p lk rk A B =
     (if card A \<le> card B
      then (let m = dindex lk A in fold (dprobe_step_l p rk m) (csorted_list_of_set B) empty_table)
      else (let m = dindex rk B in fold (dprobe_step p lk m) (csorted_list_of_set A) empty_table))"

datatype djoin_plan =
    DJEq | DJEmp | DJSub "bool list" | DJSup "bool list"
  | DJGen "mrg list" "bool list" "bool list"

definition no_right :: "mrg list \<Rightarrow> bool" where
  "no_right p = list_all (\<lambda>m. m \<noteq> MRgt) p"

definition no_left :: "mrg list \<Rightarrow> bool" where
  "no_left p = list_all (\<lambda>m. m \<noteq> MLft) p"

definition mk_djoin :: "cols \<Rightarrow> cols \<Rightarrow> djoin_plan" where
  "mk_djoin cs1 cs2 = (if cs1 = cs2 then DJEq else if cs2 = [] then DJEmp
     else (let p = mrg_plan cs1 cs2 in
       if no_right p then DJSub (mrg_left_key p)
       else if no_left p then DJSup (mrg_right_key p)
       else DJGen p (mrg_left_key p) (mrg_right_key p)))"

text \<open>
  The cases of @{const bin_join}, over the short tuples.  Two of them are worth keeping apart
  from the general one for the same reason the kernel keeps them apart: equal columns make the
  join a set intersection or difference, which on two red-black trees over one order is a merge
  that shares structure rather than a lookup per tuple, and a right operand with no columns
  decides the whole join with one membership test.

  A negative join whose right operand has a column the left does not have cannot remove
  anything: the merged tuple would be wider than the one it is asked to equal.
\<close>

fun dbin_join0 :: "djoin_plan \<Rightarrow> event_data table \<Rightarrow> bool \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dbin_join0 DJEq A pos B = (if pos then A \<inter> B else A - B)"
| "dbin_join0 DJEmp A pos B = (if pos = ([] \<in> B) then A else empty_table)"
| "dbin_join0 (DJSub msk) A pos B = dsemi msk pos A B"
| "dbin_join0 (DJSup msk) A pos B = (if pos then Set.filter (\<lambda>b. dproj msk b \<in> A) B else A)"
| "dbin_join0 (DJGen p lk rk) A pos B = (if pos then dgen_join p lk rk A B else A)"

definition dbin_join :: "djoin_plan \<Rightarrow> event_data table \<Rightarrow> bool \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dbin_join pl A pos B = (if Set.is_empty A then empty_table
     else if Set.is_empty B then (if pos then empty_table else A)
     else dbin_join0 pl A pos B)"

subsection \<open>Indexing a join on the heap\<close>

text \<open>
  The same index as @{theory MFODL_Monitor_Imp.Join_Imp2}, over the short tuples.  Two things
  the sparse version has to worry about go away.  Its guard requires both operands to be
  complete on the common columns, because a tuple with a hole there means ``any value'' and a
  hash index would miss the matches; a short tuple has no holes at all, so the guard is
  vacuous and the index applies wherever the shape is right.  And the key is the projection
  onto the shared columns, which here is as short as the shared columns rather than as long as
  the formula is wide, so it is cheaper both to build and to hash.
\<close>

partial_function (heap) didx_ins :: "bool list \<Rightarrow> event_data tuple list \<Rightarrow> jidx \<Rightarrow> jidx Heap" where
  [code]:
  "didx_ins msk xs q = (case xs of [] \<Rightarrow> return q
     | x # r \<Rightarrow> (let k = dproj msk x; h = ihash k in
         do { v \<leftarrow> im_lookup_h q h k;
              q \<leftarrow> im_update_h q h k (case v of None \<Rightarrow> [x] | Some l \<Rightarrow> x # l);
              didx_ins msk r q }))"

text \<open>The index holds the right operand and the left probes it.\<close>

partial_function (heap) dprobe_r :: "mrg list \<Rightarrow> bool list \<Rightarrow> jidx \<Rightarrow>
    event_data tuple list \<Rightarrow> event_data table \<Rightarrow> event_data table Heap" where
  [code]:
  "dprobe_r p lk q xs acc = (case xs of [] \<Rightarrow> return acc
     | x # r \<Rightarrow> (let k = dproj lk x in
         do { v \<leftarrow> im_lookup_h q (ihash k) k;
              dprobe_r p lk q r (case v of None \<Rightarrow> acc
                | Some l \<Rightarrow> fold (\<lambda>y acc. Set.insert (dmerge p x y) acc) l acc) }))"

text \<open>The index holds the left operand and the right probes it; the merge keeps its sides.\<close>

partial_function (heap) dprobe_l :: "mrg list \<Rightarrow> bool list \<Rightarrow> jidx \<Rightarrow>
    event_data tuple list \<Rightarrow> event_data table \<Rightarrow> event_data table Heap" where
  [code]:
  "dprobe_l p rk q ys acc = (case ys of [] \<Rightarrow> return acc
     | y # r \<Rightarrow> (let k = dproj rk y in
         do { v \<leftarrow> im_lookup_h q (ihash k) k;
              dprobe_l p rk q r (case v of None \<Rightarrow> acc
                | Some l \<Rightarrow> fold (\<lambda>x acc. Set.insert (dmerge p x y) acc) l acc) }))"

text \<open>As in the sparse code, the smaller side is indexed and the larger probes it, and only the
  case in which neither operand's columns contain the other's is taken away from the tree.\<close>

fun dbin_join_h :: "djoin_plan \<Rightarrow> event_data table \<Rightarrow> bool \<Rightarrow> event_data table \<Rightarrow>
    event_data table Heap" where
  "dbin_join_h (DJGen p lk rk) A pos B =
     (if \<not> dense_heap_join \<or> \<not> pos \<or> Set.is_empty A \<or> Set.is_empty B
      then return (dbin_join (DJGen p lk rk) A pos B)
      else (let xs = csorted_list_of_set A; ys = csorted_list_of_set B in
        if length ys \<le> length xs
        then (if \<not> heap_join_ok ys then return (dbin_join (DJGen p lk rk) A pos B)
              else do { q \<leftarrow> im_new (2 * integer_of_nat (length ys));
                        q \<leftarrow> didx_ins rk ys q;
                        dprobe_r p lk q xs empty_table })
        else (if \<not> heap_join_ok xs then return (dbin_join (DJGen p lk rk) A pos B)
              else do { q \<leftarrow> im_new (2 * integer_of_nat (length xs));
                        q \<leftarrow> didx_ins lk xs q;
                        dprobe_l p rk q ys empty_table })))"
| "dbin_join_h pl A pos B = return (dbin_join pl A pos B)"

subsection \<open>The multi-way conjunction\<close>

text \<open>
  A conjunction of more than two conjuncts -- and in practice nearly every conjunction, see
  @{theory MFODL_Monitor_Imp.Join_Imp2} -- is compiled to @{term MAnds}, so without this case
  the short tuples would never reach a join at all.  The positive conjuncts are joined
  left-deep and the negative ones subtracted afterwards, as in the sparse code; the columns of
  every intermediate result are known at build time, so all the plans are made once.
\<close>

fun dands_plans :: "cols \<Rightarrow> cols list \<Rightarrow> djoin_plan list" where
  "dands_plans acc [] = []"
| "dands_plans acc (c # cs) = mk_djoin acc c # dands_plans (merge_cols acc c) cs"

fun dands_cols :: "cols \<Rightarrow> cols list \<Rightarrow> cols" where
  "dands_cols acc [] = acc"
| "dands_cols acc (c # cs) = dands_cols (merge_cols acc c) cs"

fun dands_pos_h :: "djoin_plan list \<Rightarrow> event_data table \<Rightarrow> event_data table list \<Rightarrow>
    event_data table Heap" where
  "dands_pos_h [] t us = return t"
| "dands_pos_h (p # ps) t [] = return t"
| "dands_pos_h (p # ps) t (u # us) = do { t \<leftarrow> dbin_join_h p t True u; dands_pos_h ps t us }"

fun dands_neg_h :: "djoin_plan list \<Rightarrow> event_data table \<Rightarrow> event_data table list \<Rightarrow>
    event_data table Heap" where
  "dands_neg_h [] t us = return t"
| "dands_neg_h (p # ps) t [] = return t"
| "dands_neg_h (p # ps) t (u # us) = do { t \<leftarrow> dbin_join_h p t False u; dands_neg_h ps t us }"

definition dmulti_join :: "djoin_plan list \<Rightarrow> djoin_plan list \<Rightarrow> event_data table list \<Rightarrow>
    event_data table Heap" where
  "dmulti_join ps ns us = (case us of [] \<Rightarrow> return empty_table
     | t # r \<Rightarrow> do { t \<leftarrow> dands_pos_h ps t (take (length ps) r);
                     dands_neg_h ns t (drop (length ps) r) })"

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

subsection \<open>Aggregation\<close>

text \<open>
  @{const eval_agg} groups the operand by @{term "drop (length tys)"} of each tuple -- the
  aggregation's bound variables occupy the bottom of the frame, so the group key is the rest --
  and writes the aggregate into position @{term y} of the key.  Over short tuples the same two
  steps are the same two steps: @{term "{0..<length tys}"} is contained in the operand's free
  variables, so those columns are the first @{term "length tys"} of every short tuple and the
  group key is again a suffix, and the aggregate is inserted at the one position that @{term y}
  occupies among the group's columns.  The clustering and the value counting are the kernel's,
  with the term read at the short tuple's positions.
\<close>

definition dagg :: "bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> Formula.trm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    event_data table \<Rightarrow> event_data table" where
  "dagg g0 \<omega> f k pos rel =
     (if g0 \<and> Set.is_empty rel then {[Some (eval_agg_op \<omega> {})]}
      else (let groups = cluster (Some \<circ> drop k) rel in
        (\<lambda>g. case Mapping.lookup groups g of
                None \<Rightarrow> g
              | Some G \<Rightarrow> take pos g @ Some (eval_agg_op \<omega> (agg_values f G)) # drop pos g)
          ` Mapping.keys groups))"

text \<open>The columns of the operand, of the groups, and of the result.\<close>

definition dagg_child_cols :: "aggargs \<Rightarrow> cols" where
  "dagg_child_cols args = set_cols (aggargs_cols args)"

definition dagg_group_cols :: "aggargs \<Rightarrow> cols" where
  "dagg_group_cols args = map (\<lambda>c. c - length (aggargs_tys args))
     (drop (length (aggargs_tys args)) (dagg_child_cols args))"

definition dagg_cols :: "aggargs \<Rightarrow> cols" where
  "dagg_cols args = merge_cols (dagg_group_cols args) [aggargs_y args]"

definition dagg_pos :: "aggargs \<Rightarrow> nat" where
  "dagg_pos args = length (filter (\<lambda>c. c < aggargs_y args) (dagg_group_cols args))"

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

text \<open>The columns a subformula produces, where they can be read off it.\<close>

fun mcols :: "nat \<Rightarrow> mformula_j \<Rightarrow> cols option" where
  "mcols n (MPred e tms mode) = Some (tms_cols tms)"
| "mcols n (MAnd A \<phi> pos B \<psi> buf) =
    Some (if pos then merge_cols (set_cols A) (set_cols B) else set_cols A)"
| "mcols n (MAnds A_pos A_neg L buf) =
    (case A_pos of [] \<Rightarrow> None
     | A # As \<Rightarrow> Some (dands_cols (set_cols A) (map set_cols As)))"
| "mcols n (MAgg args \<phi>) = Some (dagg_cols args)"
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
  | DAnds "djoin_plan list" "djoin_plan list" "dformula list" "event_data mebufn"
  | DAndRel dformula "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | DOr dformula dformula "event_data mebuf2"
  | DNeg dformula
  | DExists dformula bool
  | DAgg bool "ty Formula.agg_op" Formula.trm nat nat dformula
  | DPrev \<I> dformula bool "event_data table mbuf_t" "ts mbuf_t"
  | DNext \<I> dformula bool "ts mbuf_t"
  | DSince args dformula dformula "event_data mebuf2S" msaux_j
  | DUntil args dformula dformula "event_data mebuf2" "ts mbuf_t" ts muaux_j

subsection \<open>Building it\<close>

fun dformula_of :: "nat \<Rightarrow> cols \<Rightarrow> mformula_j \<Rightarrow> dformula Heap"
  and dformula_of_list :: "nat \<Rightarrow> cols list \<Rightarrow> mformula_j list \<Rightarrow> dformula list Heap" where
  "dformula_of_list n cs [] = return []"
| "dformula_of_list n cs (\<phi> # r) = do {
     \<phi>d \<leftarrow> dformula_of n (case cs of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) \<phi>;
     \<phi>s \<leftarrow> dformula_of_list n (case cs of [] \<Rightarrow> [] | _ # r' \<Rightarrow> r') r;
     return (\<phi>d # \<phi>s) }"
| "dformula_of n cs (MAnds A_pos A_neg L buf) =
     (case A_pos of [] \<Rightarrow> return (DPure (MAnds A_pos A_neg L buf) n (wide_mask n cs))
      | A # As \<Rightarrow>
        (let cs_pos = set_cols A # map set_cols As;
             fin = dands_cols (set_cols A) (map set_cols As);
             cs_neg = map set_cols A_neg in
         if length L \<noteq> length A_pos + length A_neg
         then return (DPure (MAnds A_pos A_neg L buf) n (wide_mask n cs))
         else do {
           Ld \<leftarrow> dformula_of_list n (cs_pos @ cs_neg) L;
           return (DAnds (dands_plans (set_cols A) (map set_cols As))
                     (map (mk_djoin fin) cs_neg) Ld buf) }))"
| "dformula_of n cs (MPred e tms mode) =
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
| "dformula_of n cs (MAgg args \<phi>) = do {
     \<phi>d \<leftarrow> dformula_of (length (aggargs_tys args) + n) (dagg_child_cols args) \<phi>;
     return (DAgg (aggargs_g0 args) (aggargs_\<omega> args)
               (reindex_trm (dagg_child_cols args) (aggargs_f args))
               (length (aggargs_tys args)) (dagg_pos args) \<phi>d) }"
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

fun deval :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> dformula \<Rightarrow> (event_data table list \<times> dformula) Heap"
  and deval_list :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> dformula list \<Rightarrow>
    ((event_data table list \<times> dformula) list) Heap" where
  "deval_list j ts db [] = return []"
| "deval_list j ts db (\<phi> # r) = do {
     x \<leftarrow> deval j ts db \<phi>; xs \<leftarrow> deval_list j ts db r; return (x # xs) }"
| "deval j ts db (DAnds ps ns L buf) = do {
     R \<leftarrow> deval_list j ts db L;
     p \<leftarrow> mebufn_take_j (dmulti_join ps ns) mbuf_t_empty (mebufn_add (map fst R) buf);
     return (Rep_mbuf_t (fst p), DAnds ps ns (map snd R) (snd p)) }"
| "deval j ts db (DPure \<phi> n msk) = do {
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
     r \<leftarrow> mebuf2_take_j (\<lambda>r1 r2. dbin_join_h pl r1 pos r2) (mebuf2_add xs ys buf);
     return (fst r, DAnd pl \<phi> pos \<psi> (snd r)) }"
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
| "deval j ts db (DAgg g0 \<omega> f k pos \<phi>) = do {
     (xs, \<phi>) \<leftarrow> deval j ts db \<phi>;
     return (map (dagg g0 \<omega> f k pos) xs, DAgg g0 \<omega> f k pos \<phi>) }"
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

fun dpure_nodes :: "dformula \<Rightarrow> nat" and dpure_nodes_list :: "dformula list \<Rightarrow> nat" where
  "dpure_nodes_list [] = 0"
| "dpure_nodes_list (\<phi> # r) = dpure_nodes \<phi> + dpure_nodes_list r"
| "dpure_nodes (DPure \<phi> n msk) = 1"
| "dpure_nodes (DAnds ps ns L buf) = dpure_nodes_list L"
| "dpure_nodes (DAnd pl \<phi> pos \<psi> buf) = dpure_nodes \<phi> + dpure_nodes \<psi>"
| "dpure_nodes (DAndRel \<phi> conf) = dpure_nodes \<phi>"
| "dpure_nodes (DOr \<phi> \<psi> buf) = dpure_nodes \<phi> + dpure_nodes \<psi>"
| "dpure_nodes (DNeg \<phi>) = dpure_nodes \<phi>"
| "dpure_nodes (DExists \<phi> b) = dpure_nodes \<phi>"
| "dpure_nodes (DAgg g0 \<omega> f k pos \<phi>) = dpure_nodes \<phi>"
| "dpure_nodes (DPrev I \<phi> f buf nts) = dpure_nodes \<phi>"
| "dpure_nodes (DNext I \<phi> f nts) = dpure_nodes \<phi>"
| "dpure_nodes (DSince args \<phi> \<psi> buf aux) = dpure_nodes \<phi> + dpure_nodes \<psi>"
| "dpure_nodes (DUntil args \<phi> \<psi> buf nts t aux) = dpure_nodes \<phi> + dpure_nodes \<psi>"
| "dpure_nodes \<phi> = 0"

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

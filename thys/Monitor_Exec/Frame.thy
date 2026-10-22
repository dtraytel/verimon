(*<*)
theory Frame
  imports Tuple_Fields
begin
(*>*)



section \<open>Tables over ascending columns: the verified core\<close>

text \<open>
  A table of the kernel is a set of tuples over a list of columns, the free variables of the
  subformula that produced it in the order of @{const Formula.fv_list}.  The executable monitor keeps
  the same tables over the same columns in ascending order: its joins merge two column lists
  instead of looking them up, and its plans are computed once from the two lists.  A kernel
  tuple over @{term ks} becomes the short tuple over @{term cs} by reading it at the columns in
  their ascending order, @{term "restrict cs ks x"}.

  This theory proves that the reordering loses nothing -- it is a bijection between the tables
  over the two column lists -- and that the executable operations over the ascending columns agree
  with the kernel's over its own.
\<close>

type_synonym cols = "nat list"

text \<open>A ascending frame: the kernel's column list of a table, and the same columns in ascending
  order.\<close>

definition eframe :: "cols \<Rightarrow> cols \<Rightarrow> bool" where
  "eframe ks cs \<longleftrightarrow> distinct ks \<and> sorted_wrt (<) cs \<and> set cs = set ks"

text \<open>The executable projection by a mask, used between ascending frames.\<close>

fun eproj :: "bool list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "eproj [] xs = []"
| "eproj (True # bs) (x # xs) = x # eproj bs xs"
| "eproj (False # bs) (x # xs) = eproj bs xs"
| "eproj (b # bs) [] = []"

subsection \<open>The representation relation\<close>

definition etabc :: "cols \<Rightarrow> cols \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "etabc ks cs T = restrict cs ks ` T"

definition etabw :: "cols \<Rightarrow> cols \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "etabw ks cs D = restrict ks cs ` D"

lemma etabc_empty[simp]: "etabc ks cs {} = {}"
  by (simp add: etabc_def)

lemma etabc_empty_iff: "(etabc ks cs T = {}) = (T = {})"
  by (auto simp: etabc_def)

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

fun ejoin1 :: "mrg list \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list option" where
  "ejoin1 [] xs ys = Some []"
| "ejoin1 (MLft # p) (x # xs) ys = map_option (Cons x) (ejoin1 p xs ys)"
| "ejoin1 (MRgt # p) xs (y # ys) = map_option (Cons y) (ejoin1 p xs ys)"
| "ejoin1 (MBth # p) (x # xs) (y # ys) =
    (if x = y then map_option (Cons x) (ejoin1 p xs ys) else None)"
| "ejoin1 (m # p) xs ys = None"

subsection \<open>Projecting a short tuple onto a sublist of its columns\<close>

fun mrg_left_key :: "mrg list \<Rightarrow> bool list" where
  "mrg_left_key [] = []"
| "mrg_left_key (MLft # p) = False # mrg_left_key p"
| "mrg_left_key (MRgt # p) = mrg_left_key p"
| "mrg_left_key (MBth # p) = True # mrg_left_key p"

definition no_right :: "mrg list \<Rightarrow> bool" where
  "no_right p = list_all (\<lambda>m. m \<noteq> MRgt) p"

subsection \<open>The join when one operand's columns are among the other's\<close>

definition esemi :: "bool list \<Rightarrow> bool \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "esemi msk pos A B = Set.filter (\<lambda>a. (eproj msk a \<in> B) = pos) A"

subsection \<open>The join the other way round\<close>

fun mrg_right_key :: "mrg list \<Rightarrow> bool list" where
  "mrg_right_key [] = []"
| "mrg_right_key (MLft # p) = mrg_right_key p"
| "mrg_right_key (MRgt # p) = False # mrg_right_key p"
| "mrg_right_key (MBth # p) = True # mrg_right_key p"

definition no_left :: "mrg list \<Rightarrow> bool" where
  "no_left p = list_all (\<lambda>m. m \<noteq> MLft) p"

text \<open>The plan the other way round swaps the two sides, so the right-hand facts are the
  left-hand ones.\<close>

fun mrg_swap :: "mrg \<Rightarrow> mrg" where
  "mrg_swap MLft = MRgt"
| "mrg_swap MRgt = MLft"
| "mrg_swap MBth = MBth"

subsection \<open>The general join: an index on the shared columns\<close>

text \<open>
  When neither operand's columns are contained in the other's, one side is indexed by the
  shared columns and the other probes the index.  A probe that hits knows the two tuples agree
  on the shared columns, so the merge needs no test at all.
\<close>

fun emerge :: "mrg list \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "emerge [] xs ys = []"
| "emerge (MLft # p) (x # xs) ys = x # emerge p xs ys"
| "emerge (MRgt # p) xs (y # ys) = y # emerge p xs ys"
| "emerge (MBth # p) (x # xs) (y # ys) = x # emerge p xs ys"
| "emerge (m # p) xs ys = []"

definition gindex_step :: "bool list \<Rightarrow> 'b list \<Rightarrow>
    ('b list, 'b list list) mapping \<Rightarrow> ('b list, 'b list list) mapping" where
  "gindex_step msk b m = (let k = eproj msk b in
     (case Mapping.lookup m k of None \<Rightarrow> Mapping.update k [b] m
      | Some l \<Rightarrow> Mapping.update k (b # l) m))"

definition gindex :: "bool list \<Rightarrow> 'b :: ccompare list set \<Rightarrow>
    ('b list, 'b list list) mapping" where
  "gindex msk B = fold (gindex_step msk) (csl B) Mapping.empty"

definition gprobe_step :: "mrg list \<Rightarrow> bool list \<Rightarrow>
    ('b list, 'b list list) mapping \<Rightarrow> 'b list \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "gprobe_step p msk m a acc = (case Mapping.lookup m (eproj msk a) of
      None \<Rightarrow> acc
    | Some l \<Rightarrow> fold (\<lambda>b acc. Set.insert (emerge p a b) acc) l acc)"

definition gprobe_step_l :: "mrg list \<Rightarrow> bool list \<Rightarrow>
    ('b list, 'b list list) mapping \<Rightarrow> 'b list \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "gprobe_step_l p rk m y acc = (case Mapping.lookup m (eproj rk y) of
      None \<Rightarrow> acc
    | Some l \<Rightarrow> fold (\<lambda>x acc. Set.insert (emerge p x y) acc) l acc)"

text \<open>The index is built on the smaller side and the larger one probes it: indexing costs a
  lookup per tuple of the indexed side and probing one per tuple of the other, so indexing the
  larger side buys a big index that is read a few times.\<close>

definition ggen_join :: "mrg list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
    'b :: ccompare list set \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "ggen_join p lk rk A B =
     (if card A \<le> card B
      then (let m = gindex lk A in fold (gprobe_step_l p rk m) (csl B) {})
      else (let m = gindex rk B in fold (gprobe_step p lk m) (csl A) {}))"

definition bucket :: "(event_data tuple, event_data tuple list) mapping \<Rightarrow>
    event_data tuple \<Rightarrow> event_data tuple list" where
  "bucket m k = (case Mapping.lookup m k of None \<Rightarrow> [] | Some l \<Rightarrow> l)"

subsection \<open>Dispatching on the shape of the two column lists\<close>

text \<open>
  The plan is computed once, when the formula is compiled, and replayed at every time point;
  the kernel's @{const bin_join} recomputes the same case distinction from the two column lists
  on every call.
\<close>

datatype ejoin_plan =
    EJEq | EJEmp | EJSub "bool list" | EJSup "bool list"
  | EJGen "mrg list" "bool list" "bool list"

definition mk_djoin :: "cols \<Rightarrow> cols \<Rightarrow> ejoin_plan" where
  "mk_djoin cs1 cs2 = (if cs1 = cs2 then EJEq else if cs2 = [] then EJEmp
     else (let p = mrg_plan cs1 cs2 in
       if no_right p then EJSub (mrg_left_key p)
       else if no_left p then EJSup (mrg_right_key p)
       else EJGen p (mrg_left_key p) (mrg_right_key p)))"

fun gbin_join0 :: "ejoin_plan \<Rightarrow> 'b :: ccompare list set \<Rightarrow> bool \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "gbin_join0 EJEq A pos B = (if pos then A \<inter> B else A - B)"
| "gbin_join0 EJEmp A pos B = (if pos = ([] \<in> B) then A else {})"
| "gbin_join0 (EJSub msk) A pos B = esemi msk pos A B"
| "gbin_join0 (EJSup msk) A pos B = (if pos then Set.filter (\<lambda>b. eproj msk b \<in> A) B else A)"
| "gbin_join0 (EJGen p lk rk) A pos B = (if pos then ggen_join p lk rk A B else A)"

definition gbin_join :: "ejoin_plan \<Rightarrow> 'b :: ccompare list set \<Rightarrow> bool \<Rightarrow> 'b list set \<Rightarrow>
    'b list set" where
  "gbin_join pl A pos B = (if Set.is_empty A then {}
     else if Set.is_empty B then (if pos then {} else A)
     else gbin_join0 pl A pos B)"

text \<open>And hence the short join refines the kernel's @{const bin_join}.\<close>

subsection \<open>The multi-way join\<close>

text \<open>
  The kernel's @{const mmulti_join} picks a strategy at run time; the executable evaluator joins left
  to right against a plan list computed once.  Both compute the tuples over the union of the
  positive operands' columns that restrict into every positive operand and into no negative
  one, which the left-to-right folds below are shown to compute as well.
\<close>

fun eands_plans :: "cols \<Rightarrow> cols list \<Rightarrow> ejoin_plan list" where
  "eands_plans acc [] = []"
| "eands_plans acc (c # cs) = mk_djoin acc c # eands_plans (merge_cols acc c) cs"

fun eands_cols :: "cols \<Rightarrow> cols list \<Rightarrow> cols" where
  "eands_cols acc [] = acc"
| "eands_cols acc (c # cs) = eands_cols (merge_cols acc c) cs"

fun gands_pos :: "ejoin_plan list \<Rightarrow> 'b :: ccompare list set \<Rightarrow> 'b list set list \<Rightarrow>
    'b list set" where
  "gands_pos [] t us = t"
| "gands_pos (p # ps) t [] = t"
| "gands_pos (p # ps) t (u # us) = gands_pos ps (gbin_join p t True u) us"

fun gands_neg :: "ejoin_plan list \<Rightarrow> 'b :: ccompare list set \<Rightarrow> 'b list set list \<Rightarrow>
    'b list set" where
  "gands_neg [] t us = t"
| "gands_neg (p # ps) t [] = t"
| "gands_neg (p # ps) t (u # us) = gands_neg ps (gbin_join p t False u) us"

text \<open>The kernel's tables of the same folds, over the kernel's column orders.\<close>

fun kands_cols :: "cols \<Rightarrow> cols list \<Rightarrow> cols" where
  "kands_cols acc [] = acc"
| "kands_cols acc (k # ks) = kands_cols (cols_union acc k) ks"

fun kands_pos :: "cols \<Rightarrow> 'a table \<Rightarrow> (cols \<times> 'a table) list \<Rightarrow> 'a table" where
  "kands_pos acc t [] = t"
| "kands_pos acc t ((k, u) # us) = kands_pos (cols_union acc k) (join acc t True k u) us"

fun kands_neg :: "cols \<Rightarrow> 'a table \<Rightarrow> (cols \<times> 'a table) list \<Rightarrow> 'a table" where
  "kands_neg acc t [] = t"
| "kands_neg acc t ((k, u) # us) = kands_neg acc (join acc t False k u) us"

text \<open>An operand of the multi-way join: its kernel columns, its ascending columns, and its table.\<close>

definition wf_operand :: "cols \<Rightarrow> cols \<Rightarrow> event_data table \<Rightarrow> bool" where
  "wf_operand k c U \<longleftrightarrow> eframe k c \<and> table k U \<and> finite U"

section \<open>Aggregation over short tuples\<close>

subsection \<open>Reading a term at the short tuple's positions\<close>

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

subsection \<open>The group key is a suffix of the short tuple\<close>

text \<open>
  The aggregation's bound variables occupy the bottom of the frame and are contained in the
  operand's free variables, so the operand's ascending column list is @{term "[0..<m]"} followed by
  the group's columns shifted up by @{term m}.  Under that decomposition the group key -- which
  the kernel reads off its own tuple with @{const agg_key}, over @{term "shift_cols m cs"} --
  is @{term "drop m"} of the short tuple, over the group's columns.
\<close>

abbreviation agg_cols :: "nat \<Rightarrow> cols \<Rightarrow> cols" where
  "agg_cols m gcols \<equiv> [0..<m] @ map (\<lambda>c. c + m) gcols"

subsection \<open>Writing the aggregate into the group key\<close>

definition ins_pos :: "cols \<Rightarrow> nat \<Rightarrow> nat" where
  "ins_pos cs y = length (filter (\<lambda>c. c < y) cs)"

section \<open>Predicates, relations, and the existential\<close>

subsection \<open>Turning a set of columns into a column list\<close>

definition set_cols :: "nat set \<Rightarrow> cols" where
  "set_cols A = csorted_list_of_set A"

lemma set_cols_eqI:
  assumes f: "finite A" and s: "sorted_wrt (<) xs" and e: "set xs = A"
  shows "xs = set_cols A"
  by (rule strict_sorted_equal) (use s e set_cols[OF f] in auto)

lemma set_cols_empty: "set_cols {} = []"
  by (rule set_cols_eqI[symmetric]) simp_all

subsection \<open>A predicate whose arguments are distinct variables in ascending order\<close>

text \<open>Then the kernel's columns are already ascending: the argument tuples of the database are
  the short tuples.\<close>

fun smp_cols :: "Formula.trm list \<Rightarrow> cols" where
  "smp_cols [] = []"
| "smp_cols (Formula.Var y # ts) = y # smp_cols ts"
| "smp_cols (t # ts) = []"

subsection \<open>The existential\<close>

text \<open>
  The kernel drops the column of variable @{term 0} and shifts the others down by one.  Over
  ascending columns the first column is either variable @{term 0} -- and then it is the head,
  which is dropped -- or not, and then there is nothing to do.
\<close>

definition ex_drop0 :: "cols \<Rightarrow> bool" where
  "ex_drop0 ccs = (case ccs of [] \<Rightarrow> False | c # _ \<Rightarrow> c = 0)"

definition eex_cols :: "cols \<Rightarrow> cols" where
  "eex_cols ccs = map (\<lambda>c. c - Suc 0) (if ex_drop0 ccs then tl ccs else ccs)"

section \<open>The temporal operators over ascending columns\<close>

text \<open>
  The @{locale msaux} and @{locale muaux} specifications are stated over an abstract auxiliary
  list of timestamped tables, and everything they do to it is a join, a union, an intersection,
  or a filter on timestamps.  All of them commute with the reordering, so the verified structures
  can be run unchanged over the ascending columns -- which is what the theorems of this section
  say, one per operation of the two locales.
\<close>

definition eargs :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> args" where
  "eargs cs_R cs_L args = init_args (args_ivl args) (length cs_R) cs_L cs_R (args_pos args) None"

lemma eargs_simps[simp]:
  "args_ivl (eargs cs_R cs_L args) = args_ivl args"
  "args_n (eargs cs_R cs_L args) = length cs_R"
  "args_L (eargs cs_R cs_L args) = cs_L"
  "args_R (eargs cs_R cs_L args) = cs_R"
  "args_pos (eargs cs_R cs_L args) = args_pos args"
  "args_agg (eargs cs_R cs_L args) = None"
  by (simp_all add: eargs_def init_args_def)

lemma eval_args_agg_None[simp]: "args_agg args = None \<Longrightarrow> eval_args_agg args X = X"
  by (simp add: eval_args_agg_def)

subsection \<open>The Since structure's auxiliary list\<close>

definition eauxlist :: "cols \<Rightarrow> cols \<Rightarrow> (ts \<times> 'b list set) list \<Rightarrow> (ts \<times> 'b list set) list" where
  "eauxlist ks cs aux = map (\<lambda>(t, rel). (t, etabc ks cs rel)) aux"

subsection \<open>The Until structure's auxiliary list\<close>

definition eauxlist3 :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow>
    (ts \<times> 'b list set \<times> 'b list set) list" where
  "eauxlist3 kL cL kR cR aux = map (\<lambda>(t, a1, a2). (t, etabc kL cL a1, etabc kR cR a2)) aux"

subsection \<open>The multi-way buffer\<close>

text \<open>
  @{const mbufn_take} lines up one table per conjunct, and each conjunct has its own column list,
  so the morphism is a list of reorderings applied slotwise.  The step condition is relational for
  the same reason as @{thm [source] mbuf2t_take_rel_ts}, and it is restricted to tables drawn from
  fixed sets @{term Ss}, one per slot, because the tables the operands produce have to be well
  formed for the multi-way join theorem to apply and the buffer only ever shrinks.
\<close>

lemma length_map2_map[simp]: "length hs = length buf \<Longrightarrow> length (map2 map hs buf) = length buf"
  by simp

text \<open>Hence a negation node, whose operand has no columns at all, only has to look at
  emptiness -- which the reordering preserves in both directions.\<close>

lemma etabc_empty_table[simp]: "etabc ks cs empty_table = empty_table"
  by (simp add: empty_table_def)

section \<open>The multi-way join the monitor runs\<close>

text \<open>This is the shape the evaluator calls: one plan list for the positive operands, one for
  the negative ones, and the operand tables as a single list.\<close>

definition gmulti_join :: "ejoin_plan list \<Rightarrow> ejoin_plan list \<Rightarrow> 'b :: ccompare list set list \<Rightarrow>
    'b list set" where
  "gmulti_join ps ns us = (case us of [] \<Rightarrow> {}
     | t # r \<Rightarrow> gands_neg ns (gands_pos ps t (take (length ps) r)) (drop (length ps) r))"

lemma length_eands_plans[simp]: "length (eands_plans acc css) = length css"
  by (induct css arbitrary: acc) auto

section \<open>Comparisons on short tuples\<close>

text \<open>
  A constraint node only filters; it never changes a tuple.  Reindexing its two terms against
  the node's column list makes the filter read the short tuple at the position the column
  occupies there, which by @{thm [source] umeval_trm_reindex} evaluates to the same value.
  Filtering commutes with an image without any injectivity, so the reordering passes through.
\<close>

definition reindex_constraint ::
    "cols \<Rightarrow> Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow>
     Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm" where
  "reindex_constraint cs conf = (case conf of (t1, p, c, t2) \<Rightarrow>
     (reindex_trm cs t1, p, c, reindex_trm cs t2))"

section \<open>The plan of a left operand inside the right one's frame\<close>

text \<open>A Since structure joins its left operand into the running tables: the plan records, for each
  column of the right operand, the position the column occupies among the left operand's, if any.
  It is computed once, when the formula is compiled.\<close>

definition emb_plan :: "cols \<Rightarrow> cols \<Rightarrow> nat option list" where
  "emb_plan cs_R cs_L = map (\<lambda>c. if c \<in> set cs_L then Some (col_pos cs_L c) else None) cs_R"

text \<open>The operand's column list is the node's without the assigned column, and putting the
  latter back is the merge the theorem above asks for.\<close>

subsection \<open>The time point and the timestamp\<close>

text \<open>
  The two nodes that turn a number into a table produce either a one-column table holding that
  number or a zero-column truth value; the kernel's tables are already the executable ones.
\<close>

definition mtrm_ecols :: "mtrm \<Rightarrow> cols" where
  "mtrm_ecols mt = (case mt of MVar v \<Rightarrow> [v] | MConst c \<Rightarrow> [])"

lemma length_eauxlist3[simp]: "length (eauxlist3 kL cL kR cR auxlist) = length auxlist"
  by (simp add: eauxlist3_def)

section \<open>An index for the executable semi-join\<close>

text \<open>
  The Since and the Until probe their stored tables with the left operand's table.  Over ascending
  columns the probe table \<^emph>\<open>is\<close> the key set: a stored tuple is kept exactly when its projection at
  the merge plan's key mask is in the probe table, or, for a negative operand, out of it.  So the
  index is a plain clustering of the stored table by that projection, and the probe is a
  restriction of the mapping.
\<close>

definition eidx :: "bool list \<Rightarrow> 'b list set \<Rightarrow> ('b list, 'b list set) mapping" where
  "eidx msk T = cluster (Some \<circ> eproj msk) T"

definition esemi_idx :: "bool list \<Rightarrow> bool \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow> 'b list set \<Rightarrow>
    'b list set" where
  "esemi_idx msk pos idx X = set_of_idx (Mapping.filter (\<lambda>k _. (k \<in> X) = pos) idx)"

lemma in_set_of_idx: "(y \<in> set_of_idx m) = (\<exists>k Y. Mapping.lookup m k = Some Y \<and> y \<in> Y)"
  by transfer (auto simp: ran_def)

lemma lookup_eidx: "Mapping.lookup (eidx msk T) k =
  (if k \<in> eproj msk ` T then Some {y \<in> T. eproj msk y = k} else None)"
  unfolding eidx_def by transfer auto

theorem esemi_idx_dsemi: "esemi_idx msk pos (eidx msk T) X = esemi msk pos T X"
proof (intro set_eqI iffI)
  fix y assume "y \<in> esemi_idx msk pos (eidx msk T) X"
  then show "y \<in> esemi msk pos T X"
    by (auto simp: esemi_idx_def esemi_def in_set_of_idx Mapping.lookup_filter lookup_eidx
        split: if_splits option.splits)
next
  fix y assume "y \<in> esemi msk pos T X"
  then have yT: "y \<in> T" and yp: "(eproj msk y \<in> X) = pos" by (auto simp: esemi_def)
  have "Mapping.lookup (Mapping.filter (\<lambda>k _. (k \<in> X) = pos) (eidx msk T)) (eproj msk y)
      = Some {z \<in> T. eproj msk z = eproj msk y}"
    using yT yp by (simp add: Mapping.lookup_filter lookup_eidx)
  then show "y \<in> esemi_idx msk pos (eidx msk T) X"
    using yT by (auto simp: esemi_idx_def in_set_of_idx)
qed

(*<*)
end
(*>*)

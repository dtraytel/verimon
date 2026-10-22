(*<*)
theory Agg_Cache
  imports Until_Agg
begin
(*>*)



section \<open>The window's aggregate with its result table\<close>

text \<open>
  A fused aggregation over a past window (@{const sa_result}) reads its result at every time
  point, and the read builds the table of all groups afresh from the aggregate's mapping, one
  insertion per group.  From one time point to the next only the groups of the tuples entering
  and leaving the window can change -- and for MIN and MAX few of those do.  This theory keeps the
  result table next to the aggregate and updates it at the touched groups only.

  The aggregate and its result are kept together in the type @{text ucache}, whose invariant is
  that the table is the (filtered) result of the aggregate, so that reading it off is correct on
  every value of the type and no invariant has to be carried through the evaluator.  The table is
  built for one node, its key: a structure built for a different constraint or aggregation is
  rebuilt by the first step.  The window over it, @{text uswaggc}, is the window of
  @{theory MFODL_Monitor_Exec.Since_Agg} with the count set over a mapping
  (Section ``The executable fused Since window'' of @{theory MFODL_Monitor_Exec.Since_Agg}) and the aggregate moved into the new type, and
  it maps onto that window (@{text rsc}) with every operation commuting.

  The per-group reading rests on the result tuple of a group, @{text mkr}: the group with the
  aggregate inserted at the result's position, which determines the group and the value
  (@{text mkr_eq_iff}), so a group's old tuple can be removed without touching another group's.
\<close>

subsection \<open>The result, group by group\<close>

definition mkr :: "nat \<Rightarrow> 'b list \<Rightarrow> 'b \<Rightarrow> 'b list" where
  "mkr p g v = take p g @ v # drop p g"

lemma length_mkr[simp]: "length (mkr p g v) = Suc (length g)"
  by (simp add: mkr_def)

fun gval :: "ty Formula.agg_op \<Rightarrow> 'b gagg \<Rightarrow> 'b list \<Rightarrow> event_data option" where
  "gval \<omega> (GCnt m) g = map_option (\<lambda>k. EInt (integer_of_int k)) (Mapping.lookup m g)"
| "gval \<omega> (GSum m) g = (case fst \<omega> of
       Formula.Agg_Sum \<Rightarrow> map_option (\<lambda>k. EInt (snd k)) (Mapping.lookup m g)
     | Formula.Agg_Avg \<Rightarrow> map_option
         (\<lambda>k. EFloat (double_of_event_data (EInt (snd k)) / double_of_int (fst k))) (Mapping.lookup m g)
     | _ \<Rightarrow> None)"
| "gval \<omega> (GRank m ty) g = (case fst \<omega> of
       Formula.Agg_Min \<Rightarrow> map_option (\<lambda>k. get_edata_list k 0) (Mapping.lookup m g)
     | Formula.Agg_Max \<Rightarrow> map_option (\<lambda>k. get_edata_list k (get_length k - 1)) (Mapping.lookup m g)
     | Formula.Agg_Med \<Rightarrow> map_option (\<lambda>k. let u = get_length k; u' = u div 2;
         aggval = (if even u
           then (double_of_event_data_agg (get_edata_list k (u' - 1))
                 + double_of_event_data_agg (get_edata_list k u')) / double_of_int 2
           else double_of_event_data_agg (get_edata_list k u'))
         in EFloat aggval) (Mapping.lookup m g)
     | _ \<Rightarrow> None)"

definition gvset :: "ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> event_data gagg \<Rightarrow> event_data list set" where
  "gvset \<omega> p a = {mkr p g v | g v. gval \<omega> a g = Some v}"

definition cupd :: "(event_data list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> event_data list \<Rightarrow> event_data option \<Rightarrow>
    event_data option \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "cupd Q p g ov nv C = (if ov = nv then C else
     (let C' = (case ov of Some v \<Rightarrow> if Q (mkr p g v) then Set.remove (mkr p g v) C else C
                | None \<Rightarrow> C) in
      case nv of Some v \<Rightarrow> if Q (mkr p g v) then Set.insert (mkr p g v) C' else C' | None \<Rightarrow> C'))"

subsection \<open>The counts and the aggregate, in one pass\<close>

text \<open>When a time point's table enters the window or leaves it, the node updates the count of
  every tuple in the window and the aggregate, which sees only the tuples that newly enter or
  finally leave.  The tuples of a table are distinct, so each one's count can be read and updated
  in the same pass as the aggregate without seeing another tuple's update: @{text cnt_ins_fold}
  and @{text cnt_del_fold} are that pass.\<close>

definition cnt_ins_fold :: "(event_data list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> event_data list list \<Rightarrow> ucnt \<Rightarrow> 'b \<Rightarrow>
    ucnt \<times> 'b" where
  "cnt_ins_fold F xs c b = fold (\<lambda>t (c, acc). case Mapping.lookup c t of
       None \<Rightarrow> (Mapping.update t 1 c, F t acc)
     | Some k \<Rightarrow> (Mapping.update t (k + 1) c, acc)) xs (c, b)"

definition cnt_del_fold :: "(event_data list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> event_data list list \<Rightarrow> ucnt \<Rightarrow> 'b \<Rightarrow>
    ucnt \<times> 'b" where
  "cnt_del_fold F xs c b = fold (\<lambda>t (c, acc). case Mapping.lookup c t of
       None \<Rightarrow> (c, acc)
     | Some k \<Rightarrow> (if k \<le> 1 then (Mapping.delete t c, if k = 1 then F t acc else acc)
                 else (Mapping.update t (k - 1) c, acc))) xs (c, b)"

subsection \<open>The aggregate with its result\<close>

definition gcache :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> ugagg \<Rightarrow> event_data list set" where
  "gcache q p a = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> Set.filter (uqok q) (gvset \<omega> pos a))"

text \<open>The table pays where a group's aggregate rarely changes with a tuple, which is MIN and MAX:
  for them a tuple changes its group's value only when it is the group's extreme.  The count, the
  sum and the average change with every tuple, and keeping the table then costs more than building
  it; for those the structure keeps no table, and the read builds it as before.\<close>

definition cachedp :: "eaggp \<Rightarrow> bool" where
  "cachedp p = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> fst \<omega> = Formula.Agg_Min \<or> fst \<omega> = Formula.Agg_Max)"

subsection \<open>The count set, by group\<close>

text \<open>For a count or a sum, the count set can be kept split by group: an outer map from each group
  to its summary (the count or the count and the sum) together with the count set of the group's
  tuples.  A tuple's step then descends the outer map once and the group's small map once, where
  the flat representation descends the count set and the aggregate's map separately.  The flat
  count set and the aggregate are the projections @{text nflat} and @{text nsumm}.\<close>

type_synonym 'a nmap = "(event_data list, 'a \<times> ucnt) mapping"

definition nflat :: "nat \<Rightarrow> 'a nmap \<Rightarrow> ucnt" where
  "nflat k M = Mapping.Mapping (\<lambda>t. case Mapping.lookup M (drop k t) of None \<Rightarrow> None
     | Some aI \<Rightarrow> Mapping.lookup (snd aI) t)"

lemma lookup_nflat: "Mapping.lookup (nflat k M) t = (case Mapping.lookup M (drop k t) of None \<Rightarrow> None
     | Some aI \<Rightarrow> Mapping.lookup (snd aI) t)"
  unfolding nflat_def by (simp add: Mapping.lookup.abs_eq)

definition nsumm :: "'a nmap \<Rightarrow> (event_data list, 'a) mapping" where
  "nsumm M = Mapping.map_values (\<lambda>_ v. fst v) M"

lemma lookup_nsumm: "Mapping.lookup (nsumm M) g = map_option fst (Mapping.lookup M g)"
  by (simp add: nsumm_def lookup_map_values)

text \<open>A tuple entering: its count, and the summary of its group when it is new.\<close>

definition nins :: "nat \<Rightarrow> (event_data list \<Rightarrow> 'a) \<Rightarrow> (event_data list \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    event_data list \<Rightarrow> 'a nmap \<Rightarrow> 'a nmap" where
  "nins k si su t M = (let g = drop k t in case Mapping.lookup M g of
     None \<Rightarrow> Mapping.update g (si t, Mapping.update t 1 Mapping.empty) M
   | Some (a, I) \<Rightarrow> (case Mapping.lookup I t of
       None \<Rightarrow> Mapping.update g (su t a, Mapping.update t 1 I) M
     | Some m \<Rightarrow> Mapping.update g (a, Mapping.update t (m + 1) I) M))"

definition ndel :: "nat \<Rightarrow> (event_data list \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> event_data list \<Rightarrow> 'a nmap \<Rightarrow> 'a nmap" where
  "ndel k sd t M = (let g = drop k t in case Mapping.lookup M g of
     None \<Rightarrow> M
   | Some (a, I) \<Rightarrow> (case Mapping.lookup I t of
       None \<Rightarrow> M
     | Some m \<Rightarrow> (if m \<le> 1 then (let I' = Mapping.delete t I in
          if Mapping.is_empty I' then Mapping.delete g M else Mapping.update g (sd t a, I') M)
        else Mapping.update g (a, Mapping.update t (m - 1) I) M)))"

definition gupd :: "nat \<Rightarrow> (event_data list \<Rightarrow> 'a) \<Rightarrow> (event_data list \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    event_data list \<Rightarrow> (event_data list, 'a) mapping \<Rightarrow> (event_data list, 'a) mapping" where
  "gupd k si su t m = (let g = drop k t in case Mapping.lookup m g of
     None \<Rightarrow> Mapping.update g (si t) m | Some a \<Rightarrow> Mapping.update g (su t a) m)"

text \<open>The summary of a group, when its tuples leave: the step of the aggregate's deletion.  Its
  agreement with the summaries rests on the invariant: every tuple lies in its own group, every
  count is positive, and a summary counts its group's tuples.\<close>

definition gdn :: "nat \<Rightarrow> (event_data list \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow>
    event_data list \<Rightarrow> (event_data list, 'a) mapping \<Rightarrow> (event_data list, 'a) mapping" where
  "gdn k sd nc t m = (let g = drop k t in case Mapping.lookup m g of
     None \<Rightarrow> m | Some a \<Rightarrow> if nc a = 1 then Mapping.delete g m else Mapping.update g (sd t a) m)"

definition ninv :: "nat \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a nmap \<Rightarrow> bool" where
  "ninv k nc M = (finite (Mapping.keys M) \<and> (\<forall>g a I. Mapping.lookup M g = Some (a, I) \<longrightarrow>
     (\<forall>t \<in> Mapping.keys I. drop k t = g) \<and> finite (Mapping.keys I) \<and>
     nc a = card (Mapping.keys I) \<and> (\<forall>t m. Mapping.lookup I t = Some m \<longrightarrow> 1 \<le> m)))"

lemma ninv_empty[simp]: "ninv k nc Mapping.empty"
  by (simp add: ninv_def)

text \<open>The count set read off in full, for the rare step that has to go back to the flat
  structure: every group's tuples, inserted one by one.\<close>

definition nflat_x :: "'a nmap \<Rightarrow> ucnt" where
  "nflat_x M = fold (\<lambda>g c. case Mapping.lookup M g of None \<Rightarrow> c
     | Some aI \<Rightarrow> fold (\<lambda>t c. case Mapping.lookup (snd aI) t of None \<Rightarrow> c
         | Some n \<Rightarrow> Mapping.update t n c) (csl (Mapping.keys (snd aI))) c)
     (csl (Mapping.keys M)) Mapping.empty"

subsection \<open>The two instances: the count and the count with the sum\<close>

definition cins :: "(event_data list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> event_data list \<Rightarrow> ucnt \<times> 'b \<Rightarrow> ucnt \<times> 'b" where
  "cins F t ca = (case ca of (c, acc) \<Rightarrow> (case Mapping.lookup c t of
       None \<Rightarrow> (Mapping.update t 1 c, F t acc)
     | Some k \<Rightarrow> (Mapping.update t (k + 1) c, acc)))"

definition cdel :: "(event_data list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> event_data list \<Rightarrow> ucnt \<times> 'b \<Rightarrow> ucnt \<times> 'b" where
  "cdel F t ca = (case ca of (c, acc) \<Rightarrow> (case Mapping.lookup c t of
       None \<Rightarrow> (c, acc)
     | Some k \<Rightarrow> (if k \<le> 1 then (Mapping.delete t c, if k = 1 then F t acc else acc)
                 else (Mapping.update t (k - 1) c, acc))))"

definition ival :: "event_data \<Rightarrow> integer" where
  "ival e = (case e of EInt i \<Rightarrow> i | _ \<Rightarrow> 0)"

definition is_eint :: "event_data \<Rightarrow> bool" where
  "is_eint e = (case e of EInt i \<Rightarrow> True | _ \<Rightarrow> False)"

subsection \<open>The representation: flat, or grouped for a count or a sum\<close>

text \<open>The representation of the count set and the aggregate: flat, the count set next to the
  aggregate, or grouped, for a count (@{text UNCnt}, the group's count of tuples) or a sum
  (@{text UNSum}, the group's count and sum).  A grouped representation is made only for an empty
  window (@{text urmk}); a sum whose value is not an integer goes back to the flat one, as the flat
  aggregate does then.  The projections @{text rcnt} and @{text rax} give the flat pair.\<close>

datatype ucrep = UFlat ucnt "ugagg option" | UNCnt "nat nmap" | UNSum "(nat \<times> integer) nmap"

fun rcnt :: "nat \<Rightarrow> ucrep \<Rightarrow> ucnt" where
  "rcnt k (UFlat c ax) = c"
| "rcnt k (UNCnt M) = nflat k M"
| "rcnt k (UNSum M) = nflat k M"

fun rax :: "ucrep \<Rightarrow> ugagg option" where
  "rax (UFlat c ax) = ax"
| "rax (UNCnt M) = Some (GCnt (nsumm M))"
| "rax (UNSum M) = Some (GSum (nsumm M))"

fun rinv :: "nat \<Rightarrow> ucrep \<Rightarrow> bool" where
  "rinv k (UFlat c ax) = True"
| "rinv k (UNCnt M) = ninv k id M"
| "rinv k (UNSum M) = ninv k fst M"

fun rflat_x :: "ucrep \<Rightarrow> ucnt" where
  "rflat_x (UFlat c ax) = c"
| "rflat_x (UNCnt M) = nflat_x M"
| "rflat_x (UNSum M) = nflat_x M"

fun rins :: "nat \<Rightarrow> (event_data list \<Rightarrow> event_data) \<Rightarrow> event_data list \<Rightarrow> ucrep \<Rightarrow> ucrep" where
  "rins k ev t (UFlat c ax) = (case cins (gstep_ins k ev) t (c, ax) of (c', ax') \<Rightarrow> UFlat c' ax')"
| "rins k ev t (UNCnt M) = UNCnt (nins k (\<lambda>_. 1) (\<lambda>_ a. Suc a) t M)"
| "rins k ev t (UNSum M) = (if is_eint (ev t) \<or> Mapping.lookup (nflat k M) t \<noteq> None
     then UNSum (nins k (\<lambda>t. (1, ival (ev t))) (\<lambda>t a. (Suc (fst a), snd a + ival (ev t))) t M)
     else UFlat (ucnt_add1 t (nflat_x M)) None)"

fun rdel :: "nat \<Rightarrow> (event_data list \<Rightarrow> event_data) \<Rightarrow> event_data list \<Rightarrow> ucrep \<Rightarrow> ucrep" where
  "rdel k ev t (UFlat c ax) = (case cdel (gstep_del k ev) t (c, ax) of (c', ax') \<Rightarrow> UFlat c' ax')"
| "rdel k ev t (UNCnt M) = UNCnt (ndel k (\<lambda>_ a. a - 1) t M)"
| "rdel k ev t (UNSum M) = (if is_eint (ev t) \<or> Mapping.lookup (nflat k M) t \<noteq> Some 1
     then UNSum (ndel k (\<lambda>t a. (fst a - 1, snd a - ival (ev t))) t M)
     else UFlat (ucnt_del1 t (nflat_x M)) None)"

definition ek :: "eaggp \<Rightarrow> nat" where
  "ek p = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> k)"

definition urmk :: "eaggp \<Rightarrow> ucnt \<Rightarrow> ugagg option \<Rightarrow> ucrep" where
  "urmk p c ax = (if \<not> cachedp p \<and> Mapping.is_empty c then (case ax of
      Some (GCnt m) \<Rightarrow> if Mapping.is_empty m then UNCnt Mapping.empty else UFlat c ax
    | Some (GSum m) \<Rightarrow> if Mapping.is_empty m then UNSum Mapping.empty else UFlat c ax
    | _ \<Rightarrow> UFlat c ax) else UFlat c ax)"

text \<open>The cache: its key (the constraint and the aggregation it was made for), the
  representation and the result table.  The representation is grouped at the key's group arity
  (@{text ek}).  A step of an aggregation that keeps no table keeps the grouped representation
  whenever the arity agrees, whatever the rest of the key: the representation does not depend on
  it, and the constraint on the result is pushed into the node after the cache is made, so that
  comparing the whole key would lose the grouping at the first step.\<close>

typedef ucache = "{x :: (uconstr option \<times> eaggp) \<times> ucrep \<times> event_data list set.
    case x of (key, R, C) \<Rightarrow> rinv (ek (snd key)) R \<and>
      (cachedp (snd key) \<longrightarrow> (\<forall>a. rax R = Some a \<longrightarrow> C = gcache (fst key) (snd key) a))}"
  by (rule exI[of _ "(undefined, UFlat Mapping.empty None, {})"]) simp

lifting_forget mapping.lifting

setup_lifting type_definition_ucache

lift_definition uc_key :: "ucache \<Rightarrow> uconstr option \<times> eaggp" is "\<lambda>(k, R, C). k" .
lift_definition uc_cnt :: "ucache \<Rightarrow> ucnt" is "\<lambda>(k, R, C). rcnt (ek (snd k)) R" .
lift_definition uc_ax :: "ucache \<Rightarrow> ugagg option" is "\<lambda>(k, R, C). rax R" .
lift_definition uc_set :: "ucache \<Rightarrow> event_data list set" is "\<lambda>(k, R, C). C" .
lift_definition uc_rep :: "ucache \<Rightarrow> ucrep" is "\<lambda>(k, R, C). R" .

definition cset :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> ugagg option \<Rightarrow> event_data list set" where
  "cset q p ax = (case ax of None \<Rightarrow> {} | Some a \<Rightarrow> gcache q p a)"

lift_definition uc_mk :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> ucnt \<Rightarrow> ugagg option \<Rightarrow> ucache" is
  "\<lambda>q p c ax. ((q, p), urmk p c ax, cset q p ax)"
  by (simp add: cset_def urmk)

lemma uc_mk[simp]: "uc_cnt (uc_mk q p c ax) = c" "uc_ax (uc_mk q p c ax) = ax"
  by (transfer; simp add: urmk)+

text \<open>A tuple's step, on the aggregate and its result together: the result changes only at the
  tuple's group, from the group's value before the step to its value after.\<close>

definition cstep :: "(nat \<Rightarrow> (event_data list \<Rightarrow> event_data) \<Rightarrow> event_data list \<Rightarrow> ugagg option \<Rightarrow>
    ugagg option) \<Rightarrow> uconstr option \<Rightarrow> eaggp \<Rightarrow> event_data list \<Rightarrow>
    ugagg option \<times> event_data list set \<Rightarrow> ugagg option \<times> event_data list set" where
  "cstep S q p t axC = (case axC of (ax, C) \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     (case ax of None \<Rightarrow> (None, C)
      | Some a \<Rightarrow> (case S k (umeval_trm f) t (Some a) of None \<Rightarrow> (None, C)
         | Some a' \<Rightarrow> (Some a', cupd (uqok q) pos (drop k t) (gval \<omega> a (drop k t))
              (gval \<omega> a' (drop k t)) C)))))"

definition cinv :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> ugagg option \<times> event_data list set \<Rightarrow> bool" where
  "cinv q p axC = (\<forall>a. fst axC = Some a \<longrightarrow> snd axC = gcache q p a)"

lemma gstep_ins_None[simp]: "gstep_ins k ev t None = None"
  by (simp add: gstep_ins_def)

lemma gstep_del_None[simp]: "gstep_del k ev t None = None"
  by (simp add: gstep_del_def)

lift_definition uc_step_ins :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
    ucache \<Rightarrow> ucache" is
  "\<lambda>q p w X x. case x of (key, R, C) \<Rightarrow> (if cachedp p then (if key = (q, p)
     then (case cnt_ins_fold (cstep gstep_ins q p) (csl X) (rflat_x R) (rax R, C) of
       (c', ax', C') \<Rightarrow> (key, UFlat c' ax', C'))
     else ((q, p), UFlat (ucnt_add X (rflat_x R)) (uag_ins p w X (rflat_x R) (rax R)),
       cset q p (uag_ins p w X (rflat_x R) (rax R))))
     else (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> if ek (snd key) = k
       then ((q, p), fold (rins k (umeval_trm f)) (csl X) R, C)
       else (case cnt_ins_fold (gstep_ins k (umeval_trm f)) (csl X) (rflat_x R) (rax R) of
         (c', ax') \<Rightarrow> ((q, p), UFlat c' ax', C))))"
  subgoal premises inv for q p w X x
  proof -
    obtain key R C where x: "x = (key, R, C)" by (cases x) auto
    obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
    have R: "rinv (ek (snd key)) R"
      and C: "cachedp (snd key) \<Longrightarrow> rax R = Some a \<Longrightarrow> C = gcache (fst key) (snd key) a" for a
      using inv by (simp_all add: x)
    show ?thesis
    proof (cases "cachedp p")
      case cp: True
      show ?thesis
      proof (cases "key = (q, p)")
        case True
        obtain c' ax' C' where
          c: "cnt_ins_fold (cstep gstep_ins q p) (csl X) (rflat_x R) (rax R, C) = (c', ax', C')"
          by (metis prod.collapse)
        have "\<forall>a. rax R = Some a \<longrightarrow> C = gcache q p a" using C cp True by simp
        then have "\<forall>a. ax' = Some a \<longrightarrow> C' = gcache q p a" by (rule cnt_ins_fold_cinv[OF _ c])
        then show ?thesis using cp True by (simp add: x c)
      next
        case False
        then show ?thesis using cp by (simp add: x cset_gcache)
      qed
    next
      case ncp: False
      show ?thesis
      proof (cases "ek (snd key) = k")
        case True
        then show ?thesis using ncp R fold_rins[of k R "umeval_trm f" "csl X"]
          by (simp add: x p ek_def)
      next
        case False
        obtain c' ax' where
          c: "cnt_ins_fold (gstep_ins k (umeval_trm f)) (csl X) (rflat_x R) (rax R) = (c', ax')"
          by (metis prod.collapse)
        show ?thesis using ncp False by (simp add: x p c)
      qed
    qed
  qed
  done

lemma uc_step_ins_cnt[simp]: "uc_cnt (uc_step_ins q p w X x) = ucnt_add X (uc_cnt x)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  show ?thesis
  proof (cases "cachedp p")
    case True
    then show ?thesis by (simp add: uc_step_ins_c ucnt_add_def)
  next
    case False
    from uc_step_ins_nc[OF False p, of q w X x] show ?thesis
      by (simp add: cnt_ins_fold_eq[OF distinct_csl_edl] ucnt_add_def)
  qed
qed

lemma uc_step_ins_ax[simp]: "uc_ax (uc_step_ins q p w X x) = uag_ins p w X (uc_cnt x) (uc_ax x)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  show ?thesis
  proof (cases "cachedp p")
    case True
    then show ?thesis by (simp add: uc_step_ins_c)
  next
    case False
    from uc_step_ins_nc[OF False p, of q w X x] show ?thesis
      by (simp add: cnt_ins_fold_eq[OF distinct_csl_edl] p uag_ins_def gins_def)
  qed
qed

lift_definition uc_step_del :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
    ucache \<Rightarrow> ucache" is
  "\<lambda>q p w X x. case x of (key, R, C) \<Rightarrow> (if cachedp p then (if key = (q, p)
     then (case cnt_del_fold (cstep gstep_del q p) (csl X) (rflat_x R) (rax R, C) of
       (c', ax', C') \<Rightarrow> (key, UFlat c' ax', C'))
     else ((q, p), UFlat (ucnt_del X (rflat_x R)) (uag_del p w X (rflat_x R) (rax R)),
       cset q p (uag_del p w X (rflat_x R) (rax R))))
     else (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> if ek (snd key) = k
       then ((q, p), fold (rdel k (umeval_trm f)) (csl X) R, C)
       else (case cnt_del_fold (gstep_del k (umeval_trm f)) (csl X) (rflat_x R) (rax R) of
         (c', ax') \<Rightarrow> ((q, p), UFlat c' ax', C))))"
  subgoal premises inv for q p w X x
  proof -
    obtain key R C where x: "x = (key, R, C)" by (cases x) auto
    obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
    have R: "rinv (ek (snd key)) R"
      and C: "cachedp (snd key) \<Longrightarrow> rax R = Some a \<Longrightarrow> C = gcache (fst key) (snd key) a" for a
      using inv by (simp_all add: x)
    show ?thesis
    proof (cases "cachedp p")
      case cp: True
      show ?thesis
      proof (cases "key = (q, p)")
        case True
        obtain c' ax' C' where
          c: "cnt_del_fold (cstep gstep_del q p) (csl X) (rflat_x R) (rax R, C) = (c', ax', C')"
          by (metis prod.collapse)
        have "\<forall>a. rax R = Some a \<longrightarrow> C = gcache q p a" using C cp True by simp
        then have "\<forall>a. ax' = Some a \<longrightarrow> C' = gcache q p a" by (rule cnt_del_fold_cinv[OF _ c])
        then show ?thesis using cp True by (simp add: x c)
      next
        case False
        then show ?thesis using cp by (simp add: x cset_gcache)
      qed
    next
      case ncp: False
      show ?thesis
      proof (cases "ek (snd key) = k")
        case True
        then show ?thesis using ncp R fold_rdel[of k R "umeval_trm f" "csl X"]
          by (simp add: x p ek_def)
      next
        case False
        obtain c' ax' where
          c: "cnt_del_fold (gstep_del k (umeval_trm f)) (csl X) (rflat_x R) (rax R) = (c', ax')"
          by (metis prod.collapse)
        show ?thesis using ncp False by (simp add: x p c)
      qed
    qed
  qed
  done

lemma uc_step_del_cnt[simp]: "uc_cnt (uc_step_del q p w X x) = ucnt_del X (uc_cnt x)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  show ?thesis
  proof (cases "cachedp p")
    case True
    then show ?thesis by (simp add: uc_step_del_c ucnt_del_def)
  next
    case False
    from uc_step_del_nc[OF False p, of q w X x] show ?thesis
      by (simp add: cnt_del_fold_eq[OF distinct_csl_edl] ucnt_del_def)
  qed
qed

lemma uc_step_del_ax[simp]: "uc_ax (uc_step_del q p w X x) = uag_del p w X (uc_cnt x) (uc_ax x)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  show ?thesis
  proof (cases "cachedp p")
    case True
    then show ?thesis by (simp add: uc_step_del_c)
  next
    case False
    from uc_step_del_nc[OF False p, of q w X x] show ?thesis
      by (simp add: cnt_del_fold_eq[OF distinct_csl_edl] p uag_del_def gdel_def)
  qed
qed

lifting_update mapping.lifting

subsection \<open>The result, read off\<close>

fun gempty :: "'b gagg \<Rightarrow> bool" where
  "gempty (GCnt m) = Mapping.is_empty m"
| "gempty (GSum m) = Mapping.is_empty m"
| "gempty (GRank m ty) = Mapping.is_empty m"

definition uc_res :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> ucache \<Rightarrow> event_data list set" where
  "uc_res q p w x = (case uc_ax x of
     None \<Rightarrow> ufilt q (eagg_p p (Mapping.keys (uc_cnt x)))
   | Some a \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> if uc_key x = (q, p) \<and> cachedp p
       then (if g0 \<and> gempty a then ufilt q {[eval_agg_op \<omega> {}]} else uc_set x)
       else ugres (uqok q) g0 \<omega> pos a))"

text \<open>The result read off the grouped representation directly, without the projection.\<close>

definition nis_empty :: "'a nmap \<Rightarrow> bool" where
  "nis_empty M = Mapping.is_empty M"

lemma is_empty_nsumm[simp]: "Mapping.is_empty (nsumm M) \<longleftrightarrow> Mapping.is_empty M"
  by (simp add: nsumm_def Mapping.is_empty_def)

definition ugres_nc :: "uconstr option \<Rightarrow> bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> nat nmap \<Rightarrow>
    event_data list set" where
  "ugres_nc q g0 \<omega> p M = ugres (uqok q) g0 \<omega> p (GCnt (nsumm M))"

definition ugres_ns :: "uconstr option \<Rightarrow> bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> (nat \<times> integer) nmap \<Rightarrow>
    event_data list set" where
  "ugres_ns q g0 \<omega> p M = ugres (uqok q) g0 \<omega> p (GSum (nsumm M))"

lemma ugres_nc_code[code]: "ugres_nc q g0 \<omega> p M =
    (if g0 \<and> nis_empty M then Set.filter (uqok q) {[eval_agg_op \<omega> {}]}
     else ugmr (uqok q) p (\<lambda>v. EInt (integer_of_int (fst v))) M)"
  by (simp add: nis_empty_def ugres_nc_def ugres_code nsumm_def ugmr_map_values)

lemma ugres_ns_code[code]: "ugres_ns q g0 \<omega> p M =
    (if g0 \<and> nis_empty M then Set.filter (uqok q) {[eval_agg_op \<omega> {}]}
     else (case fst \<omega> of
       Formula.Agg_Sum \<Rightarrow> ugmr (uqok q) p (\<lambda>v. EInt (snd (fst v))) M
     | Formula.Agg_Avg \<Rightarrow> ugmr (uqok q) p
         (\<lambda>v. EFloat (double_of_event_data (EInt (snd (fst v))) / double_of_int (fst (fst v)))) M
     | _ \<Rightarrow> {}))"
  by (simp add: nis_empty_def ugres_ns_def ugres_code nsumm_def ugmr_map_values split: Formula.agg_type.splits)

lemma uc_res_code[code]: "uc_res q p w x = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> (case uc_rep x of
     UFlat c ax \<Rightarrow> (case ax of
       None \<Rightarrow> ufilt q (eagg_p p (Mapping.keys c))
     | Some a \<Rightarrow> if uc_key x = (q, p) \<and> cachedp p
       then (if g0 \<and> gempty a then ufilt q {[eval_agg_op \<omega> {}]} else uc_set x)
       else ugres (uqok q) g0 \<omega> pos a)
   | UNCnt M \<Rightarrow> if uc_key x = (q, p) \<and> cachedp p
       then (if g0 \<and> nis_empty M then ufilt q {[eval_agg_op \<omega> {}]} else uc_set x)
       else ugres_nc q g0 \<omega> pos M
   | UNSum M \<Rightarrow> if uc_key x = (q, p) \<and> cachedp p
       then (if g0 \<and> nis_empty M then ufilt q {[eval_agg_op \<omega> {}]} else uc_set x)
       else ugres_ns q g0 \<omega> pos M))"
  by (auto simp: uc_res_def uc_ax_rep uc_cnt_rep ugres_nc_def ugres_ns_def nis_empty_def
      split: ucrep.splits prod.splits option.splits)

text \<open>The code reads the count set through the executable flattening, and a tuple's count through
  its group's map; the projection @{const nflat} itself is a lookup function, not a tree.\<close>

lemma uc_cnt_code[code]: "uc_cnt x = rflat_x (uc_rep x)"
  using rflat_x[OF uc_rep_inv[of x]] by (simp add: uc_cnt_rep)

definition nlk :: "nat \<Rightarrow> 'a nmap \<Rightarrow> event_data list \<Rightarrow> nat option" where
  "nlk k M t = (case Mapping.lookup M (drop k t) of None \<Rightarrow> None | Some aI \<Rightarrow> Mapping.lookup (snd aI) t)"

lemma lookup_nflat_nlk[code_unfold]: "Mapping.lookup (nflat k M) t = nlk k M t"
  by (simp add: lookup_nflat nlk_def)

subsection \<open>The window over it\<close>

type_synonym uswaggc = "(ts \<times> (ts \<times> event_data list set) queue \<times> (ts \<times> event_data list set) queue) \<times>
  ucache"

fun rsc :: "uswaggc \<Rightarrow> swagg" where
  "rsc ((t, pend, win), x) = ((t, pend, win, ucc (uc_cnt x)), uc_ax x)"

function usc_move :: "args \<Rightarrow> eaggp \<Rightarrow> uconstr option \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data list set) queue \<Rightarrow>
    (ts \<times> event_data list set) queue \<Rightarrow> ucache \<Rightarrow>
    (ts \<times> event_data list set) queue \<times> (ts \<times> event_data list set) queue \<times> ucache" where
  "usc_move args p q nt pend win x =
     (case safe_hd pend of
        (None, pend') \<Rightarrow> (pend', win, x)
      | (Some e, pend') \<Rightarrow>
        (if memL (args_ivl args) (nt - fst e)
         then (if memR (args_ivl args) (nt - fst e)
               then usc_move args p q nt (tl_queue pend') (append_queue e win)
                      (uc_step_ins q p (args_n args) (snd e) x)
               else usc_move args p q nt (tl_queue pend') win x)
         else (pend', win, x)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, p, q, nt, pend, win, x). length (linearize pend))")
     (fastforce split: prod.splits)+

declare usc_move.simps[simp del]

function usc_expire :: "args \<Rightarrow> eaggp \<Rightarrow> uconstr option \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data list set) queue \<Rightarrow>
    ucache \<Rightarrow> (ts \<times> event_data list set) queue \<times> ucache" where
  "usc_expire args p q nt win x =
     (case safe_hd win of
        (None, win') \<Rightarrow> (win', x)
      | (Some e, win') \<Rightarrow>
        (if memR (args_ivl args) (nt - fst e) then (win', x)
         else usc_expire args p q nt (tl_queue win') (uc_step_del q p (args_n args) (snd e) x)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, p, q, nt, win, x). length (linearize win))")
     (fastforce split: prod.splits)+

declare usc_expire.simps[simp del]

definition usc_init :: "args \<Rightarrow> eaggp \<Rightarrow> uconstr option \<Rightarrow> uswaggc" where
  "usc_init args p q = ((0, empty_queue, empty_queue), uc_mk q p Mapping.empty (ag_init p (args_n args)))"

definition usc_add_new_ts :: "args \<Rightarrow> eaggp \<Rightarrow> uconstr option \<Rightarrow> ts \<Rightarrow> uswaggc \<Rightarrow> uswaggc" where
  "usc_add_new_ts args p q nt aux = (case aux of ((t, pend, win), x) \<Rightarrow>
     (case usc_move args p q nt pend win x of (pend', win', x') \<Rightarrow>
      (case usc_expire args p q nt win' x' of (win'', x'') \<Rightarrow> ((nt, pend', win''), x''))))"

definition usc_join :: "args \<Rightarrow> eaggp \<Rightarrow> uconstr option \<Rightarrow> event_data list set \<Rightarrow> uswaggc \<Rightarrow> uswaggc" where
  "usc_join args p q X aux = (case aux of ((t, pend, win), x) \<Rightarrow>
     (if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then aux
      else ((t, empty_queue, empty_queue), uc_mk q p Mapping.empty (ag_init p (args_n args)))))"

definition usc_add_new_table :: "args \<Rightarrow> eaggp \<Rightarrow> uconstr option \<Rightarrow> event_data list set \<Rightarrow>
    uswaggc \<Rightarrow> uswaggc" where
  "usc_add_new_table args p q X aux = (case aux of ((t, pend, win), x) \<Rightarrow>
     (if memL (args_ivl args) 0
      then ((t, pend, append_queue (t, X) win), uc_step_ins q p (args_n args) X x)
      else ((t, append_queue (t, X) pend, win), x)))"

definition usc_result :: "uconstr option \<Rightarrow> args \<Rightarrow> eaggp \<Rightarrow> uswaggc \<Rightarrow> event_data list set" where
  "usc_result q args p aux = (case aux of ((t, pend, win), x) \<Rightarrow> uc_res q p (args_n args) x)"

end
(*>*)

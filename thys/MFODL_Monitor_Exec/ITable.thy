(*<*)
theory ITable
  imports Idx_Code
begin
(*>*)

section \<open>Tables with indices\<close>

text \<open>
  An indexed table is a table together with any number of indices on it, each clustering the
  table by its projection at a column mask (@{const eidx}).  The table is what the kernel sees; the
  indices are a cache that a consumer of the table may use instead of building its own.  Which
  masks a table carries is its producer's business: a table built at one time point carries
  none, and a structure that keeps a table across time points may keep indices with it and update
  them with the tuples that enter and leave.  The type's invariant is that every index is the
  clustering of the table at its mask, so every operation below is an equality with the
  operation on the underlying tables: the indices change the cost of an evaluation, never its
  result, and no proof about the evaluation has to carry an invariant of its indices.
\<close>

type_synonym 'b eindex = "('b list, 'b list set) mapping"

definition iinv :: "'b list set \<times> (bool list, 'b eindex) mapping \<Rightarrow> bool" where
  "iinv TI \<longleftrightarrow> (\<forall>msk m. Mapping.lookup (snd TI) msk = Some m \<longrightarrow> m = eidx msk (fst TI))"

typedef 'b itab = "{TI :: 'b list set \<times> (bool list, 'b eindex) mapping. iinv TI}"
  morphisms Rep_itab Abs_itab
  by (rule exI[of _ "({}, Mapping.empty)"]) (simp add: iinv_def)

lemma Abs_itab_Rep_itab_code[code abstype]: "Abs_itab (Rep_itab A) = A"
  by (fact Rep_itab_inverse)

definition iset :: "'b itab \<Rightarrow> 'b list set" where
  "iset A = fst (Rep_itab A)"

definition iidxs :: "'b itab \<Rightarrow> (bool list, 'b eindex) mapping" where
  "iidxs A = snd (Rep_itab A)"

lemma iidxs_eidx: "Mapping.lookup (iidxs A) msk = Some m \<Longrightarrow> m = eidx msk (iset A)"
  using Rep_itab[of A] by (auto simp: iinv_def iset_def iidxs_def)

lemma Rep_itab_inverse': "iinv TI \<Longrightarrow> Rep_itab (Abs_itab TI) = TI"
  by (simp add: Abs_itab_inverse)

subsection \<open>A table without indices, and adding indices\<close>

definition itab :: "'b list set \<Rightarrow> 'b itab" where
  "itab T = Abs_itab (T, Mapping.empty)"

lemma Rep_itab_itab[code abstract]: "Rep_itab (itab T) = (T, Mapping.empty)"
  by (simp add: itab_def Rep_itab_inverse' iinv_def)

lemma iset_itab[simp]: "iset (itab T) = T"
  by (simp add: iset_def Rep_itab_itab)

definition iindex :: "bool list \<Rightarrow> 'b itab \<Rightarrow> 'b eindex" where
  "iindex msk A = (case Mapping.lookup (iidxs A) msk of Some m \<Rightarrow> m | None \<Rightarrow> eidx msk (iset A))"

lemma iindex_eidx[simp]: "iindex msk A = eidx msk (iset A)"
  by (auto simp: iindex_def dest: iidxs_eidx split: option.splits)

definition iensure1 :: "'b list set \<Rightarrow> bool list \<Rightarrow> (bool list, 'b eindex) mapping \<Rightarrow>
    (bool list, 'b eindex) mapping" where
  "iensure1 T msk I = (case Mapping.lookup I msk of
     None \<Rightarrow> Mapping.update msk (eidx msk T) I | Some _ \<Rightarrow> I)"

lemma lookup_fold_iensure1:
  "Mapping.lookup (fold (iensure1 T) msks I) msk =
     (if msk \<in> set msks \<and> Mapping.lookup I msk = None then Some (eidx msk T)
      else Mapping.lookup I msk)"
  by (induct msks arbitrary: I)
    (auto simp: iensure1_def Mapping.lookup_update' split: option.splits)

definition iensure :: "bool list list \<Rightarrow> 'b itab \<Rightarrow> 'b itab" where
  "iensure msks A = Abs_itab (iset A, fold (iensure1 (iset A)) msks (iidxs A))"

lemma Rep_itab_iensure[code abstract]:
  "Rep_itab (iensure msks A) = (iset A, fold (iensure1 (iset A)) msks (iidxs A))"
  unfolding iensure_def
  by (rule Rep_itab_inverse') (auto simp: iinv_def lookup_fold_iensure1 dest: iidxs_eidx)

lemma iset_iensure[simp]: "iset (iensure msks A) = iset A"
  by (simp add: iset_def Rep_itab_iensure)

lemma iensure_has:
  "msk \<in> set msks \<Longrightarrow> Mapping.lookup (iidxs (iensure msks A)) msk \<noteq> None"
  by (simp add: iidxs_def Rep_itab_iensure lookup_fold_iensure1)

subsection \<open>Updating a table and its indices\<close>

text \<open>Adding the tuples @{term X} and then removing the tuples @{term D}: every index is updated
  by the two tables, which the code equations of @{theory MFODL_Monitor_Exec.Idx_Code} turn into
  a visit of the buckets of the moving tuples only.\<close>

definition iupd :: "'b list set \<Rightarrow> 'b list set \<Rightarrow> 'b itab \<Rightarrow> 'b itab" where
  "iupd X D A = Abs_itab ((iset A \<union> X) - D,
     Mapping.map_values (\<lambda>msk m. eidx_minus (eidx_union m (eidx msk X)) (eidx msk D)) (iidxs A))"

lemma Rep_itab_iupd[code abstract]: "Rep_itab (iupd X D A) = ((iset A \<union> X) - D,
     Mapping.map_values (\<lambda>msk m. eidx_minus (eidx_union m (eidx msk X)) (eidx msk D)) (iidxs A))"
  unfolding iupd_def
  by (rule Rep_itab_inverse')
    (auto simp: iinv_def Mapping.lookup_map_values eidx_union_eq eidx_minus_eq dest: iidxs_eidx)

lemma iset_iupd[simp]: "iset (iupd X D A) = (iset A \<union> X) - D"
  by (simp add: iset_def Rep_itab_iupd)

lemma iidxs_iupd_None: "Mapping.lookup (iidxs (iupd X D A)) msk = None \<longleftrightarrow>
    Mapping.lookup (iidxs A) msk = None"
  by (simp add: iidxs_def Rep_itab_iupd Mapping.lookup_map_values)


text \<open>Inserting and removing one tuple visits one bucket of each index.\<close>

lemma eidx_insert: "eidx msk (Set.insert x T) = eidx_add1 msk x (eidx msk T)"
  by (rule mapping_eqI) (auto simp: lookup_eidx lookup_eidx_add1 ebucket_def image_iff)

lemma eidx_remove: "eidx msk (T - {x}) = eidx_del1 msk x (eidx msk T)"
proof (rule mapping_eqI)
  fix k
  have b: "ebucket (eidx msk T) k = {y \<in> T. eproj msk y = k}"
    by (auto simp: ebucket_def lookup_eidx)
  show "Mapping.lookup (eidx msk (T - {x})) k = Mapping.lookup (eidx_del1 msk x (eidx msk T)) k"
  proof (cases "k = eproj msk x")
    case True
    have "{y \<in> T. eproj msk y = k} - {x} = {y \<in> T - {x}. eproj msk y = k}"
      and "(k \<in> eproj msk ` (T - {x})) = ({y \<in> T - {x}. eproj msk y = k} \<noteq> {})"
      by auto
    then show ?thesis using True by (simp add: lookup_eidx lookup_eidx_del1 b[unfolded True])
  next
    case False
    have "(k \<in> eproj msk ` (T - {x})) = (k \<in> eproj msk ` T)"
      and "{y \<in> T - {x}. eproj msk y = k} = {y \<in> T. eproj msk y = k}"
      using False by auto
    then show ?thesis using False by (simp add: lookup_eidx lookup_eidx_del1)
  qed
qed

definition iins :: "'b list \<Rightarrow> 'b itab \<Rightarrow> 'b itab" where
  "iins x A = Abs_itab (Set.insert x (iset A), Mapping.map_values (\<lambda>msk m. eidx_add1 msk x m) (iidxs A))"

lemma Rep_itab_iins[code abstract]:
  "Rep_itab (iins x A) = (Set.insert x (iset A), Mapping.map_values (\<lambda>msk m. eidx_add1 msk x m) (iidxs A))"
  unfolding iins_def
  by (rule Rep_itab_inverse') (auto simp: iinv_def Mapping.lookup_map_values eidx_insert dest: iidxs_eidx)

lemma iset_iins[simp]: "iset (iins x A) = Set.insert x (iset A)"
  by (simp add: iset_def Rep_itab_iins)

definition idel :: "'b list \<Rightarrow> 'b itab \<Rightarrow> 'b itab" where
  "idel x A = Abs_itab (Set.remove x (iset A), Mapping.map_values (\<lambda>msk m. eidx_del1 msk x m) (iidxs A))"

lemma Rep_itab_idel[code abstract]:
  "Rep_itab (idel x A) = (Set.remove x (iset A), Mapping.map_values (\<lambda>msk m. eidx_del1 msk x m) (iidxs A))"
  unfolding idel_def
  by (rule Rep_itab_inverse') (auto simp: iinv_def Mapping.lookup_map_values eidx_remove dest: iidxs_eidx)

lemma iset_idel[simp]: "iset (idel x A) = Set.remove x (iset A)"
  by (simp add: iset_def Rep_itab_idel)

text \<open>A table without indices, which is most tables, is updated without visiting its (empty)
  map of indices.\<close>

lemma map_values_no_keys: "Mapping.keys m = {} \<Longrightarrow> Mapping.map_values f m = m"
  by (rule mapping_eqI) (auto simp: Mapping.lookup_map_values Mapping.keys_dom_lookup split: option.splits)

lemma Rep_itab_iins_code[code abstract]:
  "Rep_itab (iins x A) = (Set.insert x (iset A), if Mapping.keys (iidxs A) = {} then iidxs A
     else Mapping.map_values (\<lambda>msk m. eidx_add1 msk x m) (iidxs A))"
  by (simp add: Rep_itab_iins map_values_no_keys)

lemma Rep_itab_idel_code[code abstract]:
  "Rep_itab (idel x A) = (Set.remove x (iset A), if Mapping.keys (iidxs A) = {} then iidxs A
     else Mapping.map_values (\<lambda>msk m. eidx_del1 msk x m) (iidxs A))"
  by (simp add: Rep_itab_idel map_values_no_keys)

text \<open>Adding and removing a set of tuples at once updates each index by the tuples' index.\<close>

definition iadd :: "'b list set \<Rightarrow> 'b itab \<Rightarrow> 'b itab" where
  "iadd X A = Abs_itab (iset A \<union> X, Mapping.map_values (\<lambda>msk m. eidx_union m (eidx msk X)) (iidxs A))"

lemma Rep_itab_iadd: "Rep_itab (iadd X A) =
    (iset A \<union> X, Mapping.map_values (\<lambda>msk m. eidx_union m (eidx msk X)) (iidxs A))"
  unfolding iadd_def
  by (rule Rep_itab_inverse')
    (auto simp: iinv_def Mapping.lookup_map_values eidx_union_eq dest: iidxs_eidx)

lemma Rep_itab_iadd_code[code abstract]: "Rep_itab (iadd X A) =
    (iset A \<union> X, if Mapping.keys (iidxs A) = {} then iidxs A
      else Mapping.map_values (\<lambda>msk m. eidx_union m (eidx msk X)) (iidxs A))"
  by (simp add: Rep_itab_iadd map_values_no_keys)

lemma iset_iadd[simp]: "iset (iadd X A) = iset A \<union> X"
  by (simp add: iset_def Rep_itab_iadd)

definition isub :: "'b list set \<Rightarrow> 'b itab \<Rightarrow> 'b itab" where
  "isub D A = Abs_itab (iset A - D, Mapping.map_values (\<lambda>msk m. eidx_minus m (eidx msk D)) (iidxs A))"

lemma Rep_itab_isub: "Rep_itab (isub D A) =
    (iset A - D, Mapping.map_values (\<lambda>msk m. eidx_minus m (eidx msk D)) (iidxs A))"
  unfolding isub_def
  by (rule Rep_itab_inverse')
    (auto simp: iinv_def Mapping.lookup_map_values eidx_minus_eq dest: iidxs_eidx)

lemma Rep_itab_isub_code[code abstract]: "Rep_itab (isub D A) =
    (iset A - D, if Mapping.keys (iidxs A) = {} then iidxs A
      else Mapping.map_values (\<lambda>msk m. eidx_minus m (eidx msk D)) (iidxs A))"
  by (simp add: Rep_itab_isub map_values_no_keys)

lemma iset_isub[simp]: "iset (isub D A) = iset A - D"
  by (simp add: iset_def Rep_itab_isub)
subsection \<open>Union\<close>

text \<open>The union keeps the left operand's indices, extended by the right operand's tuples.\<close>

definition iunion :: "'b itab \<Rightarrow> 'b itab \<Rightarrow> 'b itab" where
  "iunion A B = Abs_itab (iset A \<union> iset B,
     Mapping.map_values (\<lambda>msk m. eidx_union m (iindex msk B)) (iidxs A))"

lemma Rep_itab_iunion[code abstract]: "Rep_itab (iunion A B) = (iset A \<union> iset B,
     Mapping.map_values (\<lambda>msk m. eidx_union m (iindex msk B)) (iidxs A))"
  unfolding iunion_def
  by (rule Rep_itab_inverse')
    (auto simp: iinv_def Mapping.lookup_map_values eidx_union_eq dest: iidxs_eidx)

lemma iset_iunion[simp]: "iset (iunion A B) = iset A \<union> iset B"
  by (simp add: iset_def Rep_itab_iunion)

subsection \<open>Joins that use the operands' indices\<close>

text \<open>
  The probe of the general join by an index on the other operand's shared columns: every tuple
  of the probing side is merged with the bucket at its key.
\<close>

definition iprobe :: "mrg list \<Rightarrow> bool list \<Rightarrow> 'b eindex \<Rightarrow> 'b :: ccompare list set \<Rightarrow>
    'b list set" where
  "iprobe p lk m A = fold (\<lambda>a acc. acc \<union> emerge p a ` ebucket m (eproj lk a)) (csl A) {}"

definition iprobe_l :: "mrg list \<Rightarrow> bool list \<Rightarrow> 'b eindex \<Rightarrow> 'b :: ccompare list set \<Rightarrow>
    'b list set" where
  "iprobe_l p rk m B = fold (\<lambda>b acc. acc \<union> (\<lambda>a. emerge p a b) ` ebucket m (eproj rk b)) (csl B) {}"

lemma fold_union_image: "fold (\<lambda>x acc. acc \<union> f x) l acc = acc \<union> (\<Union>x \<in> set l. f x)"
  by (induct l arbitrary: acc) auto

lemma ebucket_eidx: "ebucket (eidx msk T) k = {y \<in> T. eproj msk y = k}"
  by (auto simp: ebucket_def lookup_eidx)

lemma iprobe_eq:
  "set (csl A) = A \<Longrightarrow>
   iprobe p lk (eidx rk B) A = {emerge p a b | a b. a \<in> A \<and> b \<in> B \<and> eproj lk a = eproj rk b}"
  by (auto simp: iprobe_def fold_union_image ebucket_eidx) metis

lemma iprobe_l_eq:
  "set (csl B) = B \<Longrightarrow>
   iprobe_l p rk (eidx lk A) B = {emerge p a b | a b. a \<in> A \<and> b \<in> B \<and> eproj lk a = eproj rk b}"
  by (simp add: iprobe_l_def fold_union_image ebucket_eidx) blast

text \<open>
  The join of two indexed tables by a plan: an operand that carries an index at the mask the plan
  probes is probed through it, and otherwise the join is that of the underlying tables.  An index
  helps
  \<^item> for @{const EJGen}: the operand indexed by its shared columns is probed by the other one;
  \<^item> for a positive @{const EJSup}: the right operand, whose columns include the left one's, is
    restricted to the keys of the left operand, which visits only those keys instead of filtering
    all of its tuples;
  \<^item> for a positive @{const EJSub}: the same with the roles swapped.
\<close>

fun ijoin0 :: "ejoin_plan \<Rightarrow> 'b :: ccompare itab \<Rightarrow> bool \<Rightarrow> 'b itab \<Rightarrow> 'b list set" where
  "ijoin0 (EJSub msk) A pos B = (case (pos, Mapping.lookup (iidxs A) msk) of
       (True, Some m) \<Rightarrow> esemi_idx msk True m (iset B)
     | _ \<Rightarrow> gbin_join0 (EJSub msk) (iset A) pos (iset B))"
| "ijoin0 (EJSup msk) A pos B = (case (pos, Mapping.lookup (iidxs B) msk) of
       (True, Some m) \<Rightarrow> esemi_idx msk True m (iset A)
     | _ \<Rightarrow> gbin_join0 (EJSup msk) (iset A) pos (iset B))"
| "ijoin0 (EJGen p lk rk) A pos B = (if pos \<and> finite (iset A) \<and> finite (iset B) then
       (case (Mapping.lookup (iidxs B) rk, Mapping.lookup (iidxs A) lk) of
         (Some m, _) \<Rightarrow> iprobe p lk m (iset A)
       | (None, Some m) \<Rightarrow> iprobe_l p rk m (iset B)
       | _ \<Rightarrow> gbin_join0 (EJGen p lk rk) (iset A) pos (iset B))
     else gbin_join0 (EJGen p lk rk) (iset A) pos (iset B))"
| "ijoin0 pl A pos B = gbin_join0 pl (iset A) pos (iset B)"

text \<open>The test of finiteness costs nothing on the tree-based sets of the Containers framework,
  which are finite by construction.\<close>

theorem ijoin0_eq:
  fixes A B :: "event_data itab"
  shows "ijoin0 pl A pos B = gbin_join0 pl (iset A) pos (iset B)"
proof (cases pl)
  case (EJSub msk)
  then show ?thesis
    by (cases pos; cases "Mapping.lookup (iidxs A) msk")
      (auto simp: esemi_idx_dsemi dest!: iidxs_eidx)
next
  case (EJSup msk)
  then show ?thesis
    by (cases pos; cases "Mapping.lookup (iidxs B) msk")
      (auto simp: esemi_idx_dsemi esemi_def dest!: iidxs_eidx)
next
  case (EJGen p lk rk)
  show ?thesis
  proof (cases "pos \<and> finite (iset A) \<and> finite (iset B)")
    case True
    then have cA: "set (csl (iset A)) = iset A" and cB: "set (csl (iset B)) = iset B"
      by (simp_all add: set_csl_ed)
    show ?thesis
      using EJGen True
      apply (cases "Mapping.lookup (iidxs B) rk"; cases "Mapping.lookup (iidxs A) lk")
         apply (auto simp: iprobe_eq[OF cA] iprobe_l_eq[OF cB] ggen_join_eq[OF cA cB] dest!: iidxs_eidx)
      apply blast+
      done
  next
    case False
    then show ?thesis
      using EJGen by (simp only: ijoin0.simps if_not_P[OF False] if_False)
  qed
qed simp_all

definition ijoin :: "ejoin_plan \<Rightarrow> 'b :: ccompare itab \<Rightarrow> bool \<Rightarrow> 'b itab \<Rightarrow> 'b list set" where
  "ijoin pl A pos B = (if Set.is_empty (iset A) then {}
     else if Set.is_empty (iset B) then (if pos then {} else iset A)
     else ijoin0 pl A pos B)"

theorem ijoin_eq:
  fixes A B :: "event_data itab"
  shows "ijoin pl A pos B = gbin_join pl (iset A) pos (iset B)"
  using ijoin0_eq by (simp add: ijoin_def gbin_join_def)
(*<*)
end
(*>*)

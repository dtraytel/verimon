(*<*)
theory Release_Window
  imports Frame_Aux "Monitor_DS.Sliding_Window_Agg"
begin
(*>*)



section \<open>The release structure\<close>

text \<open>
  The release node keeps one entry per pending time-point in the list of
  @{const eupdate_release}: the tuples whose right operand has held and the left one not since
  that point, and the tuples still alive at it.  Every step touches every entry inside the
  interval, so a step costs the window's length times the size of a table.  This structure does
  a bounded number of operations on tables per step instead.

  The fate of a tuple over a stretch of points is one of three: the right operand held
  throughout and the left one never did (the tuple is still pending), the left and the right
  operand held together at some point before the right one first failed (the tuple is released),
  or neither (it is dead).  A stretch is summarised by its pending and its released tuples,
  and summaries compose associatively: a tuple pending over the
  first stretch takes its fate over the second.  An entry's pending and alive tuples are the
  pending and the pending-or-released tuples of the summary of the points from it to the last
  one.  So the window is a sliding window aggregation over this monoid, kept as the two-list
  queue of theory @{text Sliding_Window_Agg}: an entry leaves the queue together with its front
  summary and the back's, and is read off by composing the two.  Every point's summary is thus
  composed a bounded number of times.

  An entry is read off when a point arrives whose timestamp is outside its interval.  That happens
  before the point is added, so that the entry's summary is the one of the queue, and the result
  is kept until the structure is read.
\<close>

type_synonym 'b esum = "'b list set \<times> 'b list set"

definition ecomp :: "'b esum \<Rightarrow> 'b esum \<Rightarrow> 'b esum" where
  "ecomp x y = (case x of (a1, r1) \<Rightarrow> case y of (a2, r2) \<Rightarrow>
     (a1 \<inter> a2, if r2 = {} then r1 else r1 \<union> (a1 \<inter> r2)))"

definition esum_of :: "args \<Rightarrow> bool list \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> 'b esum" where
  "esum_of args msk l r = (if l = {} then (if args_pos args then (r, {}) else ({}, r))
     else (esemi msk (\<not> args_pos args) r l, esemi msk (args_pos args) r l))"

definition eunion :: "'b esum \<Rightarrow> 'b list set" where
  "eunion x = fst x \<union> snd x"

type_synonym 'b eraux = "ts \<times> 'b list set list \<times> (ts, 'b esum, 'b esum) swag"

definition eraux_init :: "'b eraux" where
  "eraux_init = (0, [], sw_empty)"

definition eraux_shift :: "\<I> \<Rightarrow> ts \<Rightarrow> 'b eraux \<Rightarrow> 'b eraux" where
  "eraux_shift I nt aux = (case aux of (cur, outs, s) \<Rightarrow>
     (case sw_popx ecomp id (\<lambda>t. \<not> memR I (nt - t)) s of (ys, s') \<Rightarrow>
       (cur, outs @ map (\<lambda>y. eunion (sw_out ecomp y)) ys, s')))"

definition eraux_update :: "args \<Rightarrow> bool list \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> ts \<Rightarrow>
    'b eraux \<Rightarrow> 'b eraux" where
  "eraux_update args msk l r nt aux = (case eraux_shift (args_ivl args) nt aux of
     (cur, outs, s) \<Rightarrow> (nt, outs, sw_push ecomp id nt (esum_of args msk l r) s))"

definition eraux_eval :: "\<I> \<Rightarrow> ts \<Rightarrow> 'b eraux \<Rightarrow> 'b list set list \<times> 'b eraux" where
  "eraux_eval I nt aux = (case eraux_shift I nt aux of
     (cur, outs, s) \<Rightarrow> (outs, (cur, [], s)))"


lemma ecomp_alt: "ecomp (a1, r1) (a2, r2) = (a1 \<inter> a2, r1 \<union> (a1 \<inter> r2))"
  by (auto simp: ecomp_def)

lemma ecomp_assoc: "ecomp (ecomp x y) z = ecomp x (ecomp y z)"
  by (cases x; cases y; cases z) (auto simp: ecomp_alt)

lemma sw_assoc_ecomp: "sw_assoc ecomp"
  by (simp add: sw_assoc_def ecomp_assoc)

abbreviation efold :: "'b esum list \<Rightarrow> 'b esum option" where
  "efold \<equiv> sw_fold ecomp"

definition eout :: "'b esum \<Rightarrow> 'b list set \<times> 'b list set" where
  "eout x = (fst x, fst x \<union> snd x)"

definition edisj :: "'b esum \<Rightarrow> bool" where
  "edisj x \<longleftrightarrow> fst x \<inter> snd x = {}"

lemma edisj_ecomp: "edisj x \<Longrightarrow> edisj y \<Longrightarrow> edisj (ecomp x y)"
  by (cases x; cases y) (auto simp: edisj_def ecomp_alt)

lemma edisj_efold: "\<forall>e \<in> set es. edisj e \<Longrightarrow> efold es = Some x \<Longrightarrow> edisj x"
proof (induct es arbitrary: x)
  case (Cons e es)
  then show ?case by (cases "efold es") (auto simp: sw_comp_def intro: edisj_ecomp)
qed simp
lemma esum_of_eq: "esum_of args msk l r =
    (esemi msk (\<not> args_pos args) r l, esemi msk (args_pos args) r l)"
  by (auto simp: esum_of_def esemi_def)

lemma edisj_esum_of: "edisj (esum_of args msk l r)"
  by (auto simp: esum_of_eq edisj_def esemi_def)

lemma eout_esum_of: "eout (esum_of args msk l r) = (esemi msk (\<not> args_pos args) r l, r)"
  by (auto simp: esum_of_eq eout_def esemi_def)

lemma eout_ecomp_esum_of:
  assumes "edisj x"
  shows "(esemi msk (\<not> args_pos args) (fst (eout x) \<inter> r) l, snd (eout x) - (fst (eout x) - r)) =
    eout (ecomp x (esum_of args msk l r))"
  using assms by (cases x) (auto simp: eout_def ecomp_alt esum_of_eq esemi_def edisj_def)

lemma snd_eout: "snd (eout x) = eunion x"
  by (simp add: eout_def eunion_def)

subsection \<open>The structure refines the list\<close>

text \<open>
  The structure stands for a list of @{const eupdate_release} as follows.  The results kept but
  not yet read are the alive tuples of the list's first entries, whose points are outside the
  interval as seen from @{term c}.  The other entries are the queue's points, with summaries
  @{term es}, and each entry's pending and alive tuples are read off the summary from its point
  to the last one.  Their timestamps are sorted and at most the last one.
\<close>

definition erel' :: "\<I> \<Rightarrow> ts \<Rightarrow> 'b eraux \<Rightarrow> (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow> bool" where
  "erel' I c aux L \<longleftrightarrow> (case aux of (cur, outs, s) \<Rightarrow> \<exists>es.
     length outs + length es = length L \<and>
     map (\<lambda>x. snd (snd x)) (take (length outs) L) = outs \<and>
     (\<forall>x \<in> set (take (length outs) L). \<not> memR I (c - fst x)) \<and>
     sw_rel ecomp id s (zip (map fst (drop (length outs) L)) es) \<and>
     List.sorted (map fst (drop (length outs) L)) \<and> (\<forall>x \<in> set (drop (length outs) L). fst x \<le> cur) \<and>
     (\<forall>e \<in> set es. edisj e) \<and>
     (\<forall>k < length es. snd (drop (length outs) L ! k) = eout (the (efold (drop k es)))))"
definition erel :: "\<I> \<Rightarrow> 'b eraux \<Rightarrow> (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow> bool" where
  "erel I aux L = erel' I (fst aux) aux L"

lemma erel_init: "erel I eraux_init []"
  by (auto simp: erel_def erel'_def eraux_init_def sw_rel_empty intro!: exI[of _ "[]"])

lemma fst_eraux_update[simp]: "fst (eraux_update args msk l r nt aux) = nt"
  by (simp add: eraux_update_def Let_def split: prod.splits)

lemma takeWhile_zip_fst: "length xs = length ys \<Longrightarrow>
    takeWhile (\<lambda>x. P (fst x)) (zip xs ys) = take (length (takeWhile P xs)) (zip xs ys)"
  by (induct xs arbitrary: ys) (auto simp: Suc_length_conv)

lemma dropWhile_zip_fst: "length xs = length ys \<Longrightarrow>
    dropWhile (\<lambda>x. P (fst x)) (zip xs ys) = drop (length (takeWhile P xs)) (zip xs ys)"
  by (induct xs arbitrary: ys) (auto simp: Suc_length_conv)

lemma sorted_dropWhile_memR:
  "List.sorted (map fst xs) \<Longrightarrow> x \<in> set (dropWhile (\<lambda>x. \<not> memR I (nt - fst x)) xs) \<Longrightarrow>
     memR I (nt - fst x)"
proof (induct xs)
  case (Cons a xs)
  show ?case
  proof (cases "memR I (nt - fst a)")
    case True
    then have x: "x = a \<or> x \<in> set xs" using Cons(3) by auto
    have "fst a \<le> fst x" if "x \<in> set xs" using Cons(2) that by simp
    then show ?thesis using x True by auto
  next
    case False
    then show ?thesis using Cons by simp
  qed
qed simp
lemma erel_shift:
  fixes L :: "(ts \<times> 'b list set \<times> 'b list set) list"
  assumes rel: "erel' I c aux L" and cn: "c \<le> nt"
  shows "erel' I nt (eraux_shift I nt aux) L \<and> fst (eraux_shift I nt aux) = fst aux \<and>
    fst (snd (eraux_shift I nt aux)) =
      map (\<lambda>x. snd (snd x)) (takeWhile (\<lambda>x. \<not> memR I (nt - fst x)) L) \<and>
    (\<forall>x \<in> set (drop (length (fst (snd (eraux_shift I nt aux)))) L). memR I (nt - fst x))"
proof -
  define Q where "Q = (\<lambda>t. \<not> memR I (nt - t))"
  obtain cur outs s where aux: "aux = (cur, outs, s)" by (cases aux)
  define m where "m = length outs"
  define Os where "Os = drop m L"
  obtain es where l1: "m + length es = length L"
    and outs: "map (\<lambda>x. snd (snd x)) (take m L) = outs"
    and cl: "\<forall>x \<in> set (take m L). \<not> memR I (c - fst x)"
    and sr: "sw_rel ecomp id s (zip (map fst Os) es)"
    and so: "List.sorted (map fst Os)" and leO: "\<forall>x \<in> set Os. fst x \<le> cur"
    and dj: "\<forall>e \<in> set es. edisj e"
    and out: "\<forall>k < length es. snd (Os ! k) = eout (the (efold (drop k es)))"
    using rel unfolding erel'_def aux prod.case m_def[symmetric] Os_def[symmetric] by blast
  have lO: "length Os = length es" using l1 by (simp add: Os_def)
  have lmf: "length (map fst Os) = length es" using lO by simp
  define W where "W = zip (map fst Os) es"
  define p where "p = length (takeWhile (\<lambda>x. Q (fst x)) Os)"
  have pO: "p \<le> length es" using lO length_takeWhile_le[of "\<lambda>x. Q (fst x)" Os] by (simp add: p_def)
  have pt: "length (takeWhile Q (map fst Os)) = p" by (simp add: p_def takeWhile_map comp_def)
  obtain ys s' where pp: "sw_popx ecomp id Q s = (ys, s')" by (meson surj_pair)
  note po = sw_popx[OF sr[folded W_def] pp]
  have tW: "takeWhile (\<lambda>x. Q (fst x)) W = take p W"
    unfolding W_def takeWhile_zip_fst[OF lmf] pt ..
  have dW: "dropWhile (\<lambda>x. Q (fst x)) W = drop p W"
    unfolding W_def dropWhile_zip_fst[OF lmf] pt ..
  have lys: "length ys = p"
  proof -
    have "length (sw_strip4 ys) = length (take p W)" using po tW by simp
    then show ?thesis using pO lO by (simp add: sw_strip4_def W_def)
  qed
  have agg: "Some (sw_out ecomp (ys ! k)) = efold (drop k es)" if k: "k < p" for k
  proof -
    have "Some (sw_out ecomp (ys ! k)) = sw_fold ecomp (map (id \<circ> snd) (drop k W))"
      using po sw_assoc_ecomp k lys by blast
    also have "map (id \<circ> snd) (drop k W) = drop k es"
      using lO by (simp add: W_def drop_zip drop_map)
    finally show ?thesis .
  qed
  have newo: "map (\<lambda>y. eunion (sw_out ecomp y)) ys = map (\<lambda>x. snd (snd x)) (take p Os)"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>y. eunion (sw_out ecomp y)) ys) = length (map (\<lambda>x. snd (snd x)) (take p Os))"
      using lys pO lO by simp
  next
    fix k assume "k < length (map (\<lambda>y. eunion (sw_out ecomp y)) ys)"
    then have k: "k < p" using lys by simp
    have "sw_out ecomp (ys ! k) = the (efold (drop k es))" using agg[OF k] by (metis option.sel)
    then have "eunion (sw_out ecomp (ys ! k)) = snd (eout (the (efold (drop k es))))"
      by (simp add: snd_eout)
    also have "\<dots> = snd (snd (Os ! k))" using out k pO by simp
    finally show "map (\<lambda>y. eunion (sw_out ecomp y)) ys ! k = map (\<lambda>x. snd (snd x)) (take p Os) ! k"
      using k lys pO lO by simp
  qed
  have sh: "eraux_shift I nt aux = (cur, outs @ map (\<lambda>y. eunion (sw_out ecomp y)) ys, s')"
    using pp by (simp add: eraux_shift_def aux Q_def[symmetric])
  define outs' where "outs' = outs @ map (\<lambda>y. eunion (sw_out ecomp y)) ys"
  have lo': "length outs' = m + p" using lys by (simp add: outs'_def m_def)
  have tk: "take (m + p) L = take m L @ take p Os" by (simp add: Os_def take_add)
  have dr': "drop (m + p) L = drop p Os" by (simp add: Os_def add.commute)
  have outs'': "map (\<lambda>x. snd (snd x)) (take (m + p) L) = outs'"
    unfolding tk outs'_def newo using outs by simp
  have tkQ: "take p Os = takeWhile (\<lambda>x. Q (fst x)) Os"
    unfolding p_def by (rule takeWhile_eq_take[symmetric])
  have clQ: "\<forall>x \<in> set (take m L). Q (fst x)"
  proof
    fix x assume "x \<in> set (take m L)"
    then have "\<not> memR I (c - fst x)" using cl by blast
    moreover have "c - fst x \<le> nt - fst x" using cn by (rule diff_le_mono)
    ultimately show "Q (fst x)" unfolding Q_def using memR_antimono by blast
  qed
  have cl': "\<forall>x \<in> set (take (m + p) L). \<not> memR I (nt - fst x)"
    unfolding tk tkQ using clQ by (auto simp: Q_def dest: set_takeWhileD)
  have sr': "sw_rel ecomp id s' (zip (map fst (drop p Os)) (drop p es))"
    using po dW by (simp add: W_def drop_zip drop_map)
  have rel': "erel' I nt (cur, outs', s') L"
    unfolding erel'_def prod.case lo' dr'
  proof (intro exI[of _ "drop p es"] conjI)
    show "m + p + length (drop p es) = length L" using l1 pO by simp
    show "map (\<lambda>x. snd (snd x)) (take (m + p) L) = outs'" by (rule outs'')
    show "\<forall>x \<in> set (take (m + p) L). \<not> memR I (nt - fst x)" by (rule cl')
    show "sw_rel ecomp id s' (zip (map fst (drop p Os)) (drop p es))" by (rule sr')
    show "List.sorted (map fst (drop p Os))" using so by (simp add: drop_map[symmetric])
    show "\<forall>x \<in> set (drop p Os). fst x \<le> cur" using leO by (auto dest: in_set_dropD)
    show "\<forall>e \<in> set (drop p es). edisj e" using dj by (auto dest: in_set_dropD)
    show "\<forall>k < length (drop p es). snd (drop p Os ! k) = eout (the (efold (drop k (drop p es))))"
      using out pO lO by (simp add: add.commute)
  qed
  have tL: "takeWhile (\<lambda>x. \<not> memR I (nt - fst x)) L = take (m + p) L"
  proof -
    have "takeWhile (\<lambda>x. Q (fst x)) (take m L @ drop m L) =
        take m L @ takeWhile (\<lambda>x. Q (fst x)) (drop m L)"
      by (rule takeWhile_append2) (use clQ in blast)
    then have "takeWhile (\<lambda>x. Q (fst x)) L = take m L @ takeWhile (\<lambda>x. Q (fst x)) Os"
      unfolding append_take_drop_id Os_def .
    then show ?thesis unfolding tk tkQ Q_def .
  qed
  have after: "\<forall>x \<in> set (drop (m + p) L). memR I (nt - fst x)"
  proof
    fix x assume "x \<in> set (drop (m + p) L)"
    then have "x \<in> set (drop p Os)" using dr' by simp
    then have "x \<in> set (dropWhile (\<lambda>x. Q (fst x)) Os)"
      unfolding p_def by (simp only: dropWhile_eq_drop)
    then show "memR I (nt - fst x)" unfolding Q_def by (rule sorted_dropWhile_memR[OF so])
  qed
  have sh': "eraux_shift I nt aux = (cur, outs', s')" using sh by (simp add: outs'_def)
  show ?thesis unfolding sh' using rel' tL after lo' outs'' by (simp add: aux)
qed

lemma eval_until_takeWhile: "eval_until I nt L =
  (map (\<lambda>(t, a1, a2). a2) (takeWhile (\<lambda>x. \<not> memR I (nt - fst x)) L),
   dropWhile (\<lambda>x. \<not> memR I (nt - fst x)) L)"
  by (induct I nt L rule: eval_until.induct) (auto simp: Let_def split: prod.splits)

lemma erel'_drop_outs:
  assumes "erel' I c (cur, outs, s) L"
  shows "erel' I c' (cur, [], s) (drop (length outs) L)"
proof -
  from assms obtain es where "length outs + length es = length L"
    "sw_rel ecomp id s (zip (map fst (drop (length outs) L)) es)"
    "List.sorted (map fst (drop (length outs) L))" "\<forall>x \<in> set (drop (length outs) L). fst x \<le> cur"
    "\<forall>e \<in> set es. edisj e"
    "\<forall>k < length es. snd (drop (length outs) L ! k) = eout (the (efold (drop k es)))"
    unfolding erel'_def prod.case by blast
  then show ?thesis unfolding erel'_def prod.case by (intro exI[of _ es]) auto
qed

lemma erel_eval:
  assumes rel: "erel I aux L" and le: "fst aux \<le> nt" and e: "eraux_eval I nt aux = (ys, aux')"
  shows "fst (eval_until I nt L) = ys \<and> erel I aux' (snd (eval_until I nt L)) \<and> fst aux' = fst aux"
proof -
  note sh = erel_shift[OF rel[unfolded erel_def] le]
  obtain cur outs s where s: "eraux_shift I nt aux = (cur, outs, s)"
    by (cases "eraux_shift I nt aux") auto
  have ys: "ys = outs" and aux': "aux' = (cur, [], s)"
    using e by (simp_all add: eraux_eval_def s)
  have o: "outs = map (\<lambda>x. snd (snd x)) (takeWhile (\<lambda>x. \<not> memR I (nt - fst x)) L)"
    using conjunct1[OF conjunct2[OF conjunct2[OF sh]]] unfolding s snd_conv fst_conv .
  have dr: "drop (length outs) L = dropWhile (\<lambda>x. \<not> memR I (nt - fst x)) L"
    unfolding o length_map by (rule dropWhile_eq_drop[symmetric])
  have e1: "erel' I nt (cur, outs, s) L" using conjunct1[OF sh] unfolding s .
  have "erel' I cur (cur, [], s) (drop (length outs) L)" by (rule erel'_drop_outs[OF e1])
  then have "erel' I cur (cur, [], s) (dropWhile (\<lambda>x. \<not> memR I (nt - fst x)) L)"
    unfolding dr .
  moreover have "fst aux = cur" using conjunct1[OF conjunct2[OF sh]] unfolding s fst_conv by simp
  ultimately show ?thesis
    by (simp add: eval_until_takeWhile ys aux' o erel_def split_beta)
qed

lemma length_eupdate_release[simp]: "length (eupdate_release args msk l r nt L) = Suc (length L)"
  by (simp add: eupdate_release_def)

lemma erel_update:
  fixes L :: "(ts \<times> 'b list set \<times> 'b list set) list"
  assumes rel: "erel I aux L" and le: "fst aux \<le> nt" and I: "args_ivl args = I"
  shows "erel I (eraux_update args msk l r nt aux) (eupdate_release args msk l r nt L)"
proof -
  note sh = erel_shift[OF rel[unfolded erel_def] le]
  obtain cur outs s where s: "eraux_shift I nt aux = (cur, outs, s)"
    by (cases "eraux_shift I nt aux") auto
  define e where "e = esum_of args msk l r"
  have upd: "eraux_update args msk l r nt aux = (nt, outs, sw_push ecomp id nt e s)"
    unfolding eraux_update_def s I e_def by simp
  have "cur = fst aux" using conjunct1[OF conjunct2[OF sh]] unfolding s fst_conv by simp
  then have curle: "cur \<le> nt" using le by simp
  have sh1: "erel' I nt (cur, outs, s) L" using conjunct1[OF sh] unfolding s .
  define m where "m = length outs"
  define Os where "Os = drop m L"
  obtain es where l1: "m + length es = length L"
    and outs: "map (\<lambda>x. snd (snd x)) (take m L) = outs"
    and cl: "\<forall>x \<in> set (take m L). \<not> memR I (nt - fst x)"
    and sr: "sw_rel ecomp id s (zip (map fst Os) es)"
    and so: "List.sorted (map fst Os)" and leO: "\<forall>x \<in> set Os. fst x \<le> cur"
    and dj: "\<forall>e \<in> set es. edisj e"
    and out: "\<forall>k < length es. snd (Os ! k) = eout (the (efold (drop k es)))"
    using sh1 unfolding erel'_def prod.case m_def[symmetric] Os_def[symmetric] by blast
  have memO: "\<forall>x \<in> set Os. memR I (nt - fst x)"
    using conjunct2[OF conjunct2[OF conjunct2[OF sh]]] unfolding s snd_conv fst_conv Os_def m_def .
  have lO: "length Os = length es" using l1 by (simp add: Os_def)
  have mL: "m \<le> length L" using l1 by simp
  define g where "g = (\<lambda>(t, a1, a2). if memR (args_ivl args) (nt - t)
    then (t, esemi msk (\<not> args_pos args) (a1 \<inter> r) l, a2 - (a1 - r)) else (t, a1, a2))"
  have L': "eupdate_release args msk l r nt L = map g L @ [(nt, esemi msk (\<not> args_pos args) r l, r)]"
    by (simp add: eupdate_release_def g_def)
  have gC: "map g (take m L) = take m L"
    using cl by (intro map_idI) (auto simp: g_def I split: prod.splits)
  have tk: "take m (eupdate_release args msk l r nt L) = take m L"
    using mL gC by (simp add: L' take_map[symmetric])
  have dr: "drop m (eupdate_release args msk l r nt L) = map g Os @ [(nt, esemi msk (\<not> args_pos args) r l, r)]"
    using mL by (simp add: L' Os_def drop_map)
  have gO: "snd (g (Os ! k)) = eout (ecomp (the (efold (drop k es))) e)" if "k < length es" for k
  proof -
    have "drop k es \<noteq> []" using that by simp
    then obtain x where x: "efold (drop k es) = Some x" by (cases "drop k es") auto
    have dx: "edisj x" by (rule edisj_efold[OF _ x]) (use dj in \<open>auto dest: in_set_dropD\<close>)
    have m0: "memR (args_ivl args) (nt - fst (Os ! k))" using memO that lO I by auto
    have so: "snd (Os ! k) = eout x" using out that x by simp
    obtain t a1 a2 where Ok: "Os ! k = (t, a1, a2)" by (cases "Os ! k") auto
    show ?thesis
      using eout_ecomp_esum_of[OF dx, of msk args r l] m0 so Ok x
      by (simp add: g_def e_def eout_def)
  qed
  have mg: "map (fst \<circ> g) Os = map fst Os" by (induct Os) (auto simp: g_def split: prod.splits)
  have es_app: "efold (drop k (es @ [e])) = Some (ecomp (the (efold (drop k es))) e)"
    if "k < length es" for k
  proof -
    have "drop k es \<noteq> []" using that by simp
    then obtain x where x: "efold (drop k es) = Some x" by (cases "drop k es") auto
    have "drop k (es @ [e]) = drop k es @ [e]" using that by simp
    then show ?thesis using x by (simp add: sw_fold_snoc[OF sw_assoc_ecomp])
  qed
  have zs: "zip (map fst (drop m (eupdate_release args msk l r nt L))) (es @ [e]) =
      zip (map fst Os) es @ [(nt, e)]"
    using lO by (simp add: dr mg)
  have "erel' I nt (nt, outs, sw_push ecomp id nt e s) (eupdate_release args msk l r nt L)"
    unfolding erel'_def prod.case m_def[symmetric]
  proof (intro exI[of _ "es @ [e]"] conjI ballI allI impI)
    show "m + length (es @ [e]) = length (eupdate_release args msk l r nt L)" using l1 by simp
    show "map (\<lambda>x. snd (snd x)) (take m (eupdate_release args msk l r nt L)) = outs" using tk outs by simp
    show "sw_rel ecomp id (sw_push ecomp id nt e s)
        (zip (map fst (drop m (eupdate_release args msk l r nt L))) (es @ [e]))"
      unfolding zs by (rule sw_rel_push[OF sw_assoc_ecomp sr])
    show "List.sorted (map fst (drop m (eupdate_release args msk l r nt L)))"
      using so leO curle by (auto simp: dr sorted_append mg intro: order_trans)
  next
    fix x assume "x \<in> set (take m (eupdate_release args msk l r nt L))"
    then show "\<not> memR I (nt - fst x)" using tk cl by simp
  next
    fix x assume "x \<in> set (drop m (eupdate_release args msk l r nt L))"
    then show "fst x \<le> nt" using leO curle by (auto simp: dr g_def split: prod.splits)
  next
    fix x assume "x \<in> set (es @ [e])"
    then show "edisj x" using dj edisj_esum_of by (auto simp: e_def)
  next
    fix k assume k: "k < length (es @ [e])"
    show "snd (drop m (eupdate_release args msk l r nt L) ! k) = eout (the (efold (drop k (es @ [e]))))"
    proof (cases "k < length es")
      case True
      then show ?thesis using gO[OF True] es_app[OF True] lO by (simp add: dr nth_append)
    next
      case False
      then have "k = length es" using k by simp
      then show ?thesis using lO eout_esum_of[of args msk l r]
        by (simp add: dr nth_append e_def sw_comp_def)
    qed
  qed
  then show ?thesis by (simp add: upd erel_def)
qed
subsection \<open>The release node's structure\<close>

text \<open>
  At the node, the structure stands for the kernel's auxiliary list over the ascending columns.
  Like the Until's, it accepts a new timestamp only at or after the one it is at, so the relation
  also bounds the kernel's last timestamp and the pending ones by the node's timestamp bound.
\<close>

definition erelease_rel :: "cols \<Rightarrow> cols \<Rightarrow> \<I> \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow> event_data muaux \<Rightarrow>
    event_data eraux \<Rightarrow> ts list \<Rightarrow> bool" where
  "erelease_rel kR cR I tw t aux daux nts \<longleftrightarrow>
     (\<forall>(u, a1, a2) \<in> set aux. table kR a1 \<and> table kR a2) \<and>
     erel I daux (eauxlist3 kR cR kR cR aux) \<and> fst daux \<le> t \<and> t \<le> tw \<and>
     sorted nts \<and> (\<forall>u \<in> set nts. fst daux \<le> u \<and> u \<le> tw)"

lemma erelease_rel_init: "erelease_rel kR cR I tw 0 [] eraux_init []"
  by (simp add: erelease_rel_def eauxlist3_def erel_init) (simp add: eraux_init_def)

(*<*)
end
(*>*)

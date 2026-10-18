(*<*)
theory Release_Window
  imports Frame_Aux
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
  one.  So the window is a sliding window aggregation over this monoid, and it is kept as a queue
  of two lists: the front holds, for each of its points, the summary from that point to the end
  of the front, and the back holds the points' own summaries, newest first, together with the
  summary of all of them.  An entry is read off by composing its front summary with the back's.
  When the front runs out, the back is turned into a new front.  Every point's summary is thus
  composed a bounded number of times.

  An entry is read off when a point arrives whose timestamp is outside its interval.  That happens
  before the point is added, so that the entry's summary is the one of the queue, and the result
  is kept until the structure is read.
\<close>

type_synonym 'b esum = "'b list set \<times> 'b list set"

definition ecomp :: "'b esum \<Rightarrow> 'b esum \<Rightarrow> 'b esum" where
  "ecomp x y = (case x of (a1, r1) \<Rightarrow> case y of (a2, r2) \<Rightarrow>
     (a1 \<inter> a2, if r2 = {} then r1 else r1 \<union> (a1 \<inter> r2)))"

definition ecompo :: "'b esum \<Rightarrow> 'b esum option \<Rightarrow> 'b esum" where
  "ecompo x y = (case y of None \<Rightarrow> x | Some y' \<Rightarrow> ecomp x y')"

definition esum_of :: "args \<Rightarrow> bool list \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> 'b esum" where
  "esum_of args msk l r = (if l = {} then (if args_pos args then (r, {}) else ({}, r))
     else (esemi msk (\<not> args_pos args) r l, esemi msk (args_pos args) r l))"

definition eunion :: "'b esum \<Rightarrow> 'b list set" where
  "eunion x = fst x \<union> snd x"

type_synonym 'b eraux = "ts \<times> 'b list set list \<times> (ts \<times> 'b esum) list \<times> (ts \<times> 'b esum) list \<times>
  'b esum option"

definition eraux_init :: "'b eraux" where
  "eraux_init = (0, [], [], [], None)"

definition eraux_popfront :: "\<I> \<Rightarrow> ts \<Rightarrow> 'b esum option \<Rightarrow> (ts \<times> 'b esum) list \<Rightarrow>
    'b list set list \<times> (ts \<times> 'b esum) list" where
  "eraux_popfront I nt B fr =
     (map (\<lambda>(t, s). eunion (ecompo s B)) (takeWhile (\<lambda>(t, _). \<not> memR I (nt - t)) fr),
      dropWhile (\<lambda>(t, _). \<not> memR I (nt - t)) fr)"

fun eraux_flip :: "(ts \<times> 'b esum) list \<Rightarrow> (ts \<times> 'b esum) list \<Rightarrow> 'b esum option \<Rightarrow>
    (ts \<times> 'b esum) list" where
  "eraux_flip [] fr acc = fr"
| "eraux_flip ((t, e) # bk) fr acc = (let s = ecompo e acc in eraux_flip bk ((t, s) # fr) (Some s))"

definition eraux_shift :: "\<I> \<Rightarrow> ts \<Rightarrow> 'b eraux \<Rightarrow> 'b eraux" where
  "eraux_shift I nt aux = (case aux of (cur, outs, fr, bk, B) \<Rightarrow>
     (case eraux_popfront I nt B fr of (ys, fr') \<Rightarrow>
       (case fr' of
         [] \<Rightarrow> (case bk of
             [] \<Rightarrow> (cur, outs @ ys, [], [], B)
           | _ \<Rightarrow> (case eraux_popfront I nt None (eraux_flip bk [] None) of (zs, fr'') \<Rightarrow>
               (cur, outs @ ys @ zs, fr'', [], None)))
       | _ \<Rightarrow> (cur, outs @ ys, fr', bk, B))))"

definition eraux_update :: "args \<Rightarrow> bool list \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> ts \<Rightarrow>
    'b eraux \<Rightarrow> 'b eraux" where
  "eraux_update args msk l r nt aux = (case eraux_shift (args_ivl args) nt aux of
     (cur, outs, fr, bk, B) \<Rightarrow> let e = esum_of args msk l r in
       (nt, outs, fr, (nt, e) # bk, Some (case B of None \<Rightarrow> e | Some b \<Rightarrow> ecomp b e)))"

definition eraux_eval :: "\<I> \<Rightarrow> ts \<Rightarrow> 'b eraux \<Rightarrow> 'b list set list \<times> 'b eraux" where
  "eraux_eval I nt aux = (case eraux_shift I nt aux of
     (cur, outs, fr, bk, B) \<Rightarrow> (outs, (cur, [], fr, bk, B)))"


subsection \<open>The summaries\<close>

lemma ecomp_alt: "ecomp (a1, r1) (a2, r2) = (a1 \<inter> a2, r1 \<union> (a1 \<inter> r2))"
  by (auto simp: ecomp_def)

lemma ecomp_assoc: "ecomp (ecomp x y) z = ecomp x (ecomp y z)"
  by (cases x; cases y; cases z) (auto simp: ecomp_alt)

definition ecompoo :: "'b esum option \<Rightarrow> 'b esum option \<Rightarrow> 'b esum option" where
  "ecompoo x y = (case x of None \<Rightarrow> y | Some x' \<Rightarrow> Some (ecompo x' y))"

fun efold :: "'b esum list \<Rightarrow> 'b esum option" where
  "efold [] = None"
| "efold (e # es) = Some (ecompo e (efold es))"

lemma ecompoo_simps[simp]: "ecompoo None y = y" "ecompoo (Some x) y = Some (ecompo x y)"
  by (simp_all add: ecompoo_def)

lemma ecompo_ecompoo: "ecompo e (ecompoo X Y) = ecompo (ecompo e X) Y"
  by (cases X; cases Y) (auto simp: ecompoo_def ecompo_def ecomp_assoc)

lemma efold_append: "efold (xs @ ys) = ecompoo (efold xs) (efold ys)"
  by (induct xs) (simp_all add: ecompo_ecompoo)

lemma efold_Some: "es \<noteq> [] \<Longrightarrow> \<exists>x. efold es = Some x"
  by (cases es) auto

definition eout :: "'b esum \<Rightarrow> 'b list set \<times> 'b list set" where
  "eout x = (fst x, fst x \<union> snd x)"

definition edisj :: "'b esum \<Rightarrow> bool" where
  "edisj x \<longleftrightarrow> fst x \<inter> snd x = {}"

lemma edisj_ecomp: "edisj x \<Longrightarrow> edisj y \<Longrightarrow> edisj (ecomp x y)"
  by (cases x; cases y) (auto simp: edisj_def ecomp_alt)

lemma edisj_efold: "\<forall>e \<in> set es. edisj e \<Longrightarrow> efold es = Some x \<Longrightarrow> edisj x"
proof (induct es arbitrary: x)
  case (Cons e es)
  then show ?case by (cases "efold es") (auto simp: ecompo_def intro: edisj_ecomp)
qed simp

lemma esemi_Int: "esemi msk b (A \<inter> r) l = A \<inter> esemi msk b r l"
  by (auto simp: esemi_def)

lemma esemi_sub: "esemi msk b r l \<subseteq> r"
  by (auto simp: esemi_def)

lemma esum_of_eq: "esum_of args msk l r =
    (esemi msk (\<not> args_pos args) r l, esemi msk (args_pos args) r l)"
  by (auto simp: esum_of_def esemi_def)

lemma edisj_esum_of: "edisj (esum_of args msk l r)"
  by (auto simp: esum_of_eq edisj_def esemi_def)

lemma eout_esum_of: "eout (esum_of args msk l r) = (esemi msk (\<not> args_pos args) r l, r)"
  by (auto simp: esum_of_eq eout_def esemi_def)

text \<open>An entry the list updates is the composition of its summary with the new point's.\<close>

lemma eout_ecomp_esum_of:
  assumes "edisj x"
  shows "(esemi msk (\<not> args_pos args) (fst (eout x) \<inter> r) l, snd (eout x) - (fst (eout x) - r)) =
    eout (ecomp x (esum_of args msk l r))"
  using assms by (cases x) (auto simp: eout_def ecomp_alt esum_of_eq esemi_def edisj_def)

lemma snd_eout: "snd (eout x) = eunion x"
  by (simp add: eout_def eunion_def)

lemma eraux_flip_length: "length (eraux_flip bk fr acc) = length bk + length fr"
  by (induct bk fr acc rule: eraux_flip.induct) (auto simp: Let_def)

lemma eraux_flip_fst: "map fst (eraux_flip bk fr acc) = rev (map fst bk) @ map fst fr"
  by (induct bk fr acc rule: eraux_flip.induct) (auto simp: Let_def)

lemma eraux_flip_nth_fr: "k < length fr \<Longrightarrow> eraux_flip bk fr acc ! (length bk + k) = fr ! k"
proof (induct bk arbitrary: fr acc k)
  case (Cons x bk)
  obtain t e where x: "x = (t, e)" by (cases x)
  have "eraux_flip bk ((t, ecompo e acc) # fr) (Some (ecompo e acc)) ! (length bk + Suc k) =
      ((t, ecompo e acc) # fr) ! Suc k"
    by (rule Cons(1)) (use Cons(2) in simp)
  then show ?case by (simp add: x Let_def)
qed simp

lemma eraux_flip_snd: "k < length bk \<Longrightarrow>
    Some (snd (eraux_flip bk fr (efold ys) ! k)) = efold (drop k (rev (map snd bk)) @ ys)"
proof (induct bk arbitrary: fr ys k)
  case (Cons x bk)
  obtain t e where x: "x = (t, e)" by (cases x)
  have eq: "eraux_flip (x # bk) fr (efold ys) = eraux_flip bk ((t, ecompo e (efold ys)) # fr) (efold (e # ys))"
    by (simp add: x Let_def)
  show ?case
  proof (cases "k < length bk")
    case True
    then show ?thesis using Cons(1)[OF True, of "(t, ecompo e (efold ys)) # fr" "e # ys"]
      by (simp add: eq x Let_def)
  next
    case False
    then have k: "k = length bk" using Cons(2) by simp
    have "eraux_flip bk ((t, ecompo e (efold ys)) # fr) (efold (e # ys)) ! k = (t, ecompo e (efold ys))"
    proof -
      have "eraux_flip bk ((t, ecompo e (efold ys)) # fr) (efold (e # ys)) ! (length bk + 0) =
          ((t, ecompo e (efold ys)) # fr) ! 0"
        by (rule eraux_flip_nth_fr) simp
      then show ?thesis by (simp add: k)
    qed
    then show ?thesis by (simp add: eq x k Let_def)
  qed
qed simp

subsection \<open>The structure refines the list\<close>

text \<open>
  The structure stands for a list of @{const eupdate_release} as follows.  The results kept but
  not yet read are the alive tuples of the list's first entries, whose points are outside the
  interval as seen from @{term c}.  The other entries line up with the front and the reversed
  back; there are summaries @{term es} of their points such that the front holds the summaries of
  its suffixes, the back holds the summaries themselves and its aggregate, and each entry's
  pending and alive tuples are read off the summary from its point to the last one.  Their
  timestamps are sorted and at most the last one.
\<close>

definition erel' :: "\<I> \<Rightarrow> ts \<Rightarrow> 'b eraux \<Rightarrow> (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow> bool" where
  "erel' I c aux L \<longleftrightarrow> (case aux of (cur, outs, fr, bk, B) \<Rightarrow> \<exists>es.
     length outs + length es = length L \<and>
     map (\<lambda>x. snd (snd x)) (take (length outs) L) = outs \<and>
     (\<forall>x \<in> set (take (length outs) L). \<not> memR I (c - fst x)) \<and>
     length es = length fr + length bk \<and>
     map fst (drop (length outs) L) = map fst fr @ rev (map fst bk) \<and>
     List.sorted (map fst (drop (length outs) L)) \<and> (\<forall>x \<in> set (drop (length outs) L). fst x \<le> cur) \<and>
     (\<forall>e \<in> set es. edisj e) \<and>
     (\<forall>k < length fr. Some (snd (fr ! k)) = efold (drop k (take (length fr) es))) \<and>
     map snd bk = rev (drop (length fr) es) \<and> B = efold (drop (length fr) es) \<and>
     (\<forall>k < length es. snd (drop (length outs) L ! k) = eout (the (efold (drop k es)))))"

definition erel :: "\<I> \<Rightarrow> 'b eraux \<Rightarrow> (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow> bool" where
  "erel I aux L = erel' I (fst aux) aux L"

lemma erel_init: "erel I eraux_init []"
  by (auto simp: erel_def erel'_def eraux_init_def intro!: exI[of _ "[]"])

lemma fst_eraux_update[simp]: "fst (eraux_update args msk l r nt aux) = nt"
  by (simp add: eraux_update_def Let_def split: prod.splits)

lemma takeWhile_take: "takeWhile P (take n xs) = take n (takeWhile P xs)"
  by (induct xs arbitrary: n) (auto simp: take_Cons split: nat.splits)

lemma popfront_rel:
  fixes Os :: "(ts \<times> 'b list set \<times> 'b list set) list"
  assumes pf: "eraux_popfront I nt B fr = (ys, fr')"
    and fr: "\<forall>k < length fr. Some (snd (fr ! k)) = efold (drop k (take (length fr) es))"
    and B: "B = efold (drop (length fr) es)" and len: "length fr \<le> length es" "length es = length Os"
    and ts: "map fst (take (length fr) Os) = map fst fr"
    and out: "\<forall>k < length es. snd (Os ! k) = eout (the (efold (drop k es)))"
  shows "length ys = min (length fr) (length (takeWhile (\<lambda>x. \<not> memR I (nt - fst x)) Os))"
    and "ys = map (\<lambda>x. snd (snd x)) (take (length ys) Os)"
    and "fr' = drop (length ys) fr"
proof -
  define P :: "ts \<times> 'b esum \<Rightarrow> bool" where "P = (\<lambda>(t, _). \<not> memR I (nt - t))"
  define Q where "Q = (\<lambda>t. \<not> memR I (nt - t))"
  have ys: "ys = map (\<lambda>(t, s). eunion (ecompo s B)) (takeWhile P fr)" and fr': "fr' = dropWhile P fr"
    using pf by (simp_all add: eraux_popfront_def P_def)
  have P: "P = Q \<circ> fst" by (auto simp: P_def Q_def)
  have "map fst (takeWhile P fr) = takeWhile Q (map fst fr)" by (simp add: P takeWhile_map)
  also have "map fst fr = take (length fr) (map fst Os)" using ts by (simp add: take_map)
  then have "takeWhile Q (map fst fr) = take (length fr) (takeWhile Q (map fst Os))"
    by (simp add: takeWhile_take)
  also have "takeWhile Q (map fst Os) = map fst (takeWhile (Q \<circ> fst) Os)" by (simp add: takeWhile_map)
  finally have "map fst (takeWhile P fr) = take (length fr) (map fst (takeWhile (Q \<circ> fst) Os))" .
  then have "length (map fst (takeWhile P fr)) = length (take (length fr) (map fst (takeWhile (Q \<circ> fst) Os)))"
    by (rule arg_cong)
  then have "length (takeWhile P fr) = min (length fr) (length (takeWhile (Q \<circ> fst) Os))"
    by simp
  then show l: "length ys = min (length fr) (length (takeWhile (\<lambda>x. \<not> memR I (nt - fst x)) Os))"
    by (simp add: ys Q_def comp_def)
  define p where "p = length ys"
  have lys: "length ys = length (takeWhile P fr)" by (simp add: ys)
  have tk: "takeWhile P fr = take p fr" unfolding p_def lys by (rule takeWhile_eq_take)
  show "fr' = drop (length ys) fr" unfolding fr' lys by (rule dropWhile_eq_drop)
  have pf': "p \<le> length fr" using l by (simp add: p_def)
  have elem: "eunion (ecompo (snd (fr ! k)) B) = snd (snd (Os ! k))" if "k < p" for k
  proof -
    have k: "k < length fr" "k \<le> length fr" using that pf' by simp_all
    have "drop k es = drop k (take (length fr) es @ drop (length fr) es)" by simp
    also have "\<dots> = drop k (take (length fr) es) @ drop (length fr) es"
      using k(2) len(1) by (simp add: drop_append)
    finally have "efold (drop k es) = Some (ecompo (snd (fr ! k)) B)"
      using fr[rule_format, OF k(1), symmetric] B by (simp add: efold_append)
    then show ?thesis using out[rule_format, of k] k len by (simp add: snd_eout)
  qed
  show "ys = map (\<lambda>x. snd (snd x)) (take (length ys) Os)"
    using pf' len elem by (intro nth_equalityI) (auto simp: ys tk p_def[symmetric] split_beta)
qed

lemma erel_shift:
  fixes L :: "(ts \<times> 'b list set \<times> 'b list set) list"
  assumes rel: "erel' I c aux L" and cn: "c \<le> nt"
  shows "erel' I nt (eraux_shift I nt aux) L \<and> fst (eraux_shift I nt aux) = fst aux \<and>
    fst (snd (eraux_shift I nt aux)) =
      map (\<lambda>x. snd (snd x)) (takeWhile (\<lambda>x. \<not> memR I (nt - fst x)) L) \<and>
    (\<forall>x \<in> set (drop (length (fst (snd (eraux_shift I nt aux)))) L). memR I (nt - fst x))"
proof -
  define Q where "Q = (\<lambda>x :: ts \<times> 'b list set \<times> 'b list set. \<not> memR I (nt - fst x))"
  obtain cur outs fr bk B where aux: "aux = (cur, outs, fr, bk, B)" by (cases aux) auto
  define m where "m = length outs"
  define Os where "Os = drop m L"
  obtain es where l1: "m + length es = length L"
    and outs: "map (\<lambda>x. snd (snd x)) (take m L) = outs"
    and cl: "\<forall>x \<in> set (take m L). \<not> memR I (c - fst x)"
    and l2: "length es = length fr + length bk"
    and tsO: "map fst Os = map fst fr @ rev (map fst bk)"
    and so: "List.sorted (map fst Os)" and le: "\<forall>x \<in> set Os. fst x \<le> cur"
    and dj: "\<forall>e \<in> set es. edisj e"
    and frs: "\<forall>k < length fr. Some (snd (fr ! k)) = efold (drop k (take (length fr) es))"
    and bks: "map snd bk = rev (drop (length fr) es)" and Bs: "B = efold (drop (length fr) es)"
    and out: "\<forall>k < length es. snd (Os ! k) = eout (the (efold (drop k es)))"
    using rel unfolding erel'_def aux prod.case m_def[symmetric] Os_def[symmetric] by blast
  have lO: "length Os = length es" using l1 by (simp add: Os_def)
  have L: "L = take m L @ Os" by (simp add: Os_def)
  have clQ: "\<forall>x \<in> set (take m L). Q x"
  proof
    fix x assume "x \<in> set (take m L)"
    then have "\<not> memR I (c - fst x)" using cl by blast
    then show "Q x" unfolding Q_def by (auto dest: memR_antimono[OF _ diff_le_mono[OF cn]])
  qed
  have tW: "takeWhile Q L = take m L @ takeWhile Q Os"
    by (subst L) (simp add: takeWhile_append2 clQ)
  define p where "p = length (takeWhile Q Os)"
  have pO: "p \<le> length Os" by (simp add: p_def length_takeWhile_le)
  have takeO: "takeWhile Q Os = take p Os" unfolding p_def by (rule takeWhile_eq_take)
  have mem_after: "\<forall>x \<in> set (drop p Os). memR I (nt - fst x)"
  proof
    fix x assume "x \<in> set (drop p Os)"
    then obtain j where j: "j < length Os - p" "x = drop p Os ! j" by (metis in_set_conv_nth length_drop)
    have pl: "p < length Os" using j by simp
    have "\<not> Q (Os ! p)" using nth_length_takeWhile[of Q Os] pl by (simp add: p_def)
    then have m0: "memR I (nt - fst (Os ! p))" by (simp add: Q_def)
    have "fst (Os ! p) \<le> fst (Os ! (p + j))"
      using sorted_nth_mono[OF so, of p "p + j"] j by simp
    then show "memR I (nt - fst x)" using j pl
      by (auto intro: memR_antimono[OF m0])
  qed
  have tsfr: "map fst (take (length fr) Os) = map fst fr"
    using tsO by (metis append_eq_conv_conj length_map take_map)
  obtain ys fr1 where pf: "eraux_popfront I nt B fr = (ys, fr1)" by fastforce
  have ly: "length ys = min (length fr) p" and yso: "ys = map (\<lambda>x. snd (snd x)) (take (length ys) Os)"
    and fr1: "fr1 = drop (length ys) fr"
    using popfront_rel[OF pf frs Bs _ _ tsfr out] l2 lO by (simp_all add: p_def Q_def)
  have main: "\<exists>fr' bk' B'. eraux_shift I nt aux = (cur, outs @ map (\<lambda>x. snd (snd x)) (take p Os), fr', bk', B') \<and>
     length fr' + length bk' = length es - p \<and>
     map fst (drop p Os) = map fst fr' @ rev (map fst bk') \<and>
     (\<forall>k < length fr'. Some (snd (fr' ! k)) = efold (drop k (take (length fr') (drop p es)))) \<and>
     map snd bk' = rev (drop (length fr') (drop p es)) \<and> B' = efold (drop (length fr') (drop p es))"
  proof (cases "length ys < length fr")
    case True
    then have pe: "p = length ys" using ly by simp
    obtain x xs where fr1C: "fr1 = x # xs" using True fr1 by (cases fr1) auto
    have sh: "eraux_shift I nt aux = (cur, outs @ ys, fr1, bk, B)"
      by (simp add: aux eraux_shift_def pf fr1C)
    have pfr: "p \<le> length fr" using True pe by simp
    show ?thesis
    proof (intro exI conjI allI impI)
      show "eraux_shift I nt aux = (cur, outs @ map (\<lambda>x. snd (snd x)) (take p Os), fr1, bk, B)"
        using sh yso pe by simp
      show "length fr1 + length bk = length es - p" using fr1 pe l2 pfr by simp
      show "map fst (drop p Os) = map fst fr1 @ rev (map fst bk)"
        using tsO pfr fr1 pe by (simp add: drop_map[symmetric])
      show "map snd bk = rev (drop (length fr1) (drop p es))" using bks fr1 pe pfr by simp
      show "B = efold (drop (length fr1) (drop p es))" using Bs fr1 pe pfr by simp
    next
      fix k assume k: "k < length fr1"
      have "Some (snd (fr1 ! k)) = efold (drop (p + k) (take (length fr) es))"
        using frs[rule_format, of "p + k"] k fr1 pe by simp
      also have "drop (p + k) (take (length fr) es) = drop k (take (length fr1) (drop p es))"
        using fr1 pe by (simp add: drop_take add.commute drop_drop)
      finally show "Some (snd (fr1 ! k)) = efold (drop k (take (length fr1) (drop p es)))" .
    qed
  next
    case False
    then have lyf: "length ys = length fr" using ly by simp
    then have pge: "length fr \<le> p" using ly by simp
    have fr1N: "fr1 = []" using fr1 lyf by simp
    show ?thesis
    proof (cases bk)
      case Nil
      have pe: "p = length fr" using pge pO lO l2 Nil by simp
      have sh: "eraux_shift I nt aux = (cur, outs @ ys, [], [], B)"
        by (simp add: aux eraux_shift_def pf fr1N Nil)
      show ?thesis
      proof (intro exI conjI allI impI)
        show "eraux_shift I nt aux = (cur, outs @ map (\<lambda>x. snd (snd x)) (take p Os), [], [], B)"
          using sh yso lyf pe by simp
        show "B = efold (drop (length ([] :: (ts \<times> 'b esum) list)) (drop p es))"
          using Bs l2 Nil pe by simp
      qed (use tsO l2 Nil pe lO in auto)
    next
      case (Cons y bk')
      define fl where "fl = eraux_flip bk [] None"
      have fll: "length fl = length bk" by (simp add: fl_def eraux_flip_length)
      have flf: "map fst fl = rev (map fst bk)" by (simp add: fl_def eraux_flip_fst)
      have rbk: "rev (map snd bk) = drop (length fr) es" using bks by (metis rev_rev_ident)
      have fls: "\<forall>k < length fl. Some (snd (fl ! k)) = efold (drop k (take (length fl) (drop (length fr) es)))"
      proof (intro allI impI)
        fix k assume "k < length fl"
        then have "Some (snd (eraux_flip bk [] (efold []) ! k)) = efold (drop k (rev (map snd bk)) @ [])"
          by (intro eraux_flip_snd) (simp add: fll)
        then show "Some (snd (fl ! k)) = efold (drop k (take (length fl) (drop (length fr) es)))"
          using rbk fll l2 by (simp add: fl_def)
      qed
      obtain zs fr2 where pf2: "eraux_popfront I nt None fl = (zs, fr2)" by fastforce
      have tsfl: "map fst (take (length fl) (drop (length fr) Os)) = map fst fl"
        using tsO flf fll by (simp add: drop_map[symmetric] take_map[symmetric])
      have outd: "\<forall>k < length (drop (length fr) es). snd (drop (length fr) Os ! k) =
          eout (the (efold (drop k (drop (length fr) es))))"
        using out lO by (simp add: add.commute)
      have lz: "length zs = min (length fl) (length (takeWhile Q (drop (length fr) Os)))"
        and zso: "zs = map (\<lambda>x. snd (snd x)) (take (length zs) (drop (length fr) Os))"
        and fr2: "fr2 = drop (length zs) fl"
        using popfront_rel[OF pf2 fls _ _ _ tsfl outd] fll l2 lO by (simp_all add: Q_def)
      have allQ: "\<forall>x \<in> set (take (length fr) Os). Q x"
        using pge by (metis takeO set_takeWhileD take_take min.absorb1)
      have tW2: "takeWhile Q Os = take (length fr) Os @ takeWhile Q (drop (length fr) Os)"
        by (subst append_take_drop_id[symmetric, of Os "length fr"], subst takeWhile_append2)
          (use allQ in simp_all)
      have pz: "p = length fr + length zs"
        using lz tW2 fll l2 lO length_takeWhile_le[of Q "drop (length fr) Os"]
        by (simp add: p_def)
      have sh: "eraux_shift I nt aux = (cur, outs @ ys @ zs, fr2, [], None)"
        by (simp add: aux eraux_shift_def pf fr1N Cons pf2[unfolded fl_def, folded Cons])
      show ?thesis
      proof (intro exI conjI allI impI)
        show "eraux_shift I nt aux = (cur, outs @ map (\<lambda>x. snd (snd x)) (take p Os), fr2, [], None)"
          using sh yso zso lyf pz by (simp add: take_add)
        show "length fr2 + length ([] :: (ts \<times> 'b esum) list) = length es - p"
          using fr2 fll pz l2 by simp
        show "map fst (drop p Os) = map fst fr2 @ rev (map fst ([] :: (ts \<times> 'b esum) list))"
          using tsO flf fr2 pz by (simp add: drop_map[symmetric] add.commute drop_drop)
        show "map snd ([] :: (ts \<times> 'b esum) list) = rev (drop (length fr2) (drop p es))"
          using fr2 fll pz l2 by simp
        show "None = efold (drop (length fr2) (drop p es))"
          using fr2 fll pz l2 by simp
      next
        fix k assume k: "k < length fr2"
        have "Some (snd (fr2 ! k)) = efold (drop (length zs + k) (take (length fl) (drop (length fr) es)))"
          using fls[rule_format, of "length zs + k"] k fr2 by simp
        also have "\<dots> = efold (drop k (take (length fr2) (drop p es)))"
          using fr2 fll pz l2 by (simp add: drop_drop add.commute)
        finally show "Some (snd (fr2 ! k)) = efold (drop k (take (length fr2) (drop p es)))" .
      qed
    qed
  qed
  then obtain fr' bk' B' where sh: "eraux_shift I nt aux = (cur, outs @ map (\<lambda>x. snd (snd x)) (take p Os), fr', bk', B')"
    and ln: "length fr' + length bk' = length es - p"
    and ts': "map fst (drop p Os) = map fst fr' @ rev (map fst bk')"
    and frs': "\<forall>k < length fr'. Some (snd (fr' ! k)) = efold (drop k (take (length fr') (drop p es)))"
    and bks': "map snd bk' = rev (drop (length fr') (drop p es))"
    and Bs': "B' = efold (drop (length fr') (drop p es))" by blast
  define outs' where "outs' = outs @ map (\<lambda>x. snd (snd x)) (take p Os)"
  have lo': "length outs' = m + p" using pO by (simp add: outs'_def m_def)
  have tk': "take (m + p) L = take m L @ take p Os" by (simp add: Os_def take_add)
  have dr': "drop (m + p) L = drop p Os" by (simp add: Os_def add.commute drop_drop)
  have rel': "erel' I nt (cur, outs', fr', bk', B') L"
    unfolding erel'_def prod.case lo'
  proof (intro exI[of _ "drop p es"] conjI ballI allI impI)
    show "m + p + length (drop p es) = length L" using l1 pO lO by simp
    show "map (\<lambda>x. snd (snd x)) (take (m + p) L) = outs'" using outs tk' by (simp add: outs'_def)
    show "length (drop p es) = length fr' + length bk'" using ln by simp
    show "map fst (drop (m + p) L) = map fst fr' @ rev (map fst bk')" using ts' dr' by simp
    show "List.sorted (map fst (drop (m + p) L))" using so dr' by (simp add: drop_map[symmetric] sorted_wrt_drop)
    show "map snd bk' = rev (drop (length fr') (drop p es))" by (rule bks')
    show "B' = efold (drop (length fr') (drop p es))" by (rule Bs')
  next
    fix x assume "x \<in> set (take (m + p) L)"
    then have "x \<in> set (take m L) \<or> x \<in> set (takeWhile Q Os)" using tk' takeO by auto
    then show "\<not> memR I (nt - fst x)" using clQ by (auto dest: set_takeWhileD simp: Q_def)
  next
    fix x assume "x \<in> set (drop (m + p) L)"
    then show "fst x \<le> cur" using le dr' by (auto dest: in_set_dropD)
  next
    fix e assume "e \<in> set (drop p es)"
    then show "edisj e" using dj by (auto dest: in_set_dropD)
  next
    fix k assume "k < length fr'"
    then show "Some (snd (fr' ! k)) = efold (drop k (take (length fr') (drop p es)))" using frs' by blast
  next
    fix k assume k: "k < length (drop p es)"
    then show "snd (drop (m + p) L ! k) = eout (the (efold (drop k (drop p es))))"
      using out[rule_format, of "p + k"] dr' pO lO by (simp add: add.commute drop_drop)
  qed
  show ?thesis
    using sh rel' mem_after lo' dr' tW outs takeO by (simp add: aux outs'_def Q_def[symmetric])
qed

lemma eval_until_takeWhile: "eval_until I nt L =
  (map (\<lambda>(t, a1, a2). a2) (takeWhile (\<lambda>x. \<not> memR I (nt - fst x)) L),
   dropWhile (\<lambda>x. \<not> memR I (nt - fst x)) L)"
  by (induct I nt L rule: eval_until.induct) (auto simp: Let_def split: prod.splits)

lemma erel'_drop_outs: "erel' I c (cur, outs, fr, bk, B) L \<Longrightarrow>
    erel' I c' (cur, [], fr, bk, B) (drop (length outs) L)"
  unfolding erel'_def by auto

lemma erel_eval:
  fixes L :: "(ts \<times> 'b list set \<times> 'b list set) list"
  assumes rel: "erel I aux L" and le: "fst aux \<le> nt" and e: "eraux_eval I nt aux = (ys, aux')"
  shows "fst (eval_until I nt L) = ys \<and> erel I aux' (snd (eval_until I nt L)) \<and> fst aux' = fst aux"
proof -
  note sh = erel_shift[OF rel[unfolded erel_def] le]
  obtain cur outs fr bk B where s: "eraux_shift I nt aux = (cur, outs, fr, bk, B)"
    by (cases "eraux_shift I nt aux") auto
  have ys: "ys = outs" and aux': "aux' = (cur, [], fr, bk, B)"
    using e by (simp_all add: eraux_eval_def s)
  have o: "outs = map (\<lambda>x. snd (snd x)) (takeWhile (\<lambda>x. \<not> memR I (nt - fst x)) L)"
    using sh by (simp add: s)
  have "drop (length outs) L = dropWhile (\<lambda>x. \<not> memR I (nt - fst x)) L"
    unfolding o length_map by (rule dropWhile_eq_drop[symmetric])
  then have "erel' I cur (cur, [], fr, bk, B) (dropWhile (\<lambda>x. \<not> memR I (nt - fst x)) L)"
    using erel'_drop_outs[of I nt cur outs fr bk B L cur] sh by (simp add: s)
  moreover have "fst aux = cur" using sh by (simp add: s)
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
  obtain cur outs fr bk B where s: "eraux_shift I nt aux = (cur, outs, fr, bk, B)"
    by (cases "eraux_shift I nt aux") auto
  define e where "e = esum_of args msk l r"
  define B' where "B' = Some (case B of None \<Rightarrow> e | Some b \<Rightarrow> ecomp b e)"
  have upd: "eraux_update args msk l r nt aux = (nt, outs, fr, (nt, e) # bk, B')"
    by (simp add: eraux_update_def s I e_def B'_def Let_def)
  have curle: "cur \<le> nt" using sh le by (simp add: s)
  define m where "m = length outs"
  define Os where "Os = drop m L"
  obtain es where l1: "m + length es = length L"
    and outs: "map (\<lambda>x. snd (snd x)) (take m L) = outs"
    and cl: "\<forall>x \<in> set (take m L). \<not> memR I (nt - fst x)"
    and l2: "length es = length fr + length bk"
    and tsO: "map fst Os = map fst fr @ rev (map fst bk)"
    and so: "List.sorted (map fst Os)" and leO: "\<forall>x \<in> set Os. fst x \<le> cur"
    and dj: "\<forall>e \<in> set es. edisj e"
    and frs: "\<forall>k < length fr. Some (snd (fr ! k)) = efold (drop k (take (length fr) es))"
    and bks: "map snd bk = rev (drop (length fr) es)" and Bs: "B = efold (drop (length fr) es)"
    and out: "\<forall>k < length es. snd (Os ! k) = eout (the (efold (drop k es)))"
    using sh unfolding erel'_def s prod.case m_def[symmetric] Os_def[symmetric] by blast
  have memO: "\<forall>x \<in> set Os. memR I (nt - fst x)" using sh by (simp add: s Os_def m_def)
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
    obtain x where x: "efold (drop k es) = Some x" using efold_Some[of "drop k es"] that by auto
    have dx: "edisj x" by (rule edisj_efold[OF _ x]) (use dj in \<open>auto dest: in_set_dropD\<close>)
    have m0: "memR (args_ivl args) (nt - fst (Os ! k))" using memO that lO I by (auto simp: nth_mem)
    have so: "snd (Os ! k) = eout x" using out that x by simp
    obtain t a1 a2 where Ok: "Os ! k = (t, a1, a2)" by (cases "Os ! k") auto
    show ?thesis
      using eout_ecomp_esum_of[OF dx, of msk args r l] m0 so Ok x
      by (simp add: g_def e_def eout_def)
  qed
  have es_app: "efold (drop k (es @ [e])) = Some (ecomp (the (efold (drop k es))) e)"
    if "k < length es" for k
  proof -
    obtain x where x: "efold (drop k es) = Some x" using efold_Some[of "drop k es"] that by auto
    show ?thesis using that x by (simp add: efold_append ecompoo_def ecompo_def)
  qed
  have "erel' I nt (nt, outs, fr, (nt, e) # bk, B') (eupdate_release args msk l r nt L)"
    unfolding erel'_def prod.case m_def[symmetric]
  proof (intro exI[of _ "es @ [e]"] conjI ballI allI impI)
    show "m + length (es @ [e]) = length (eupdate_release args msk l r nt L)" using l1 by simp
    show "map (\<lambda>x. snd (snd x)) (take m (eupdate_release args msk l r nt L)) = outs" using tk outs by simp
    show "length (es @ [e]) = length fr + length ((nt, e) # bk)" using l2 by simp
    show "map fst (drop m (eupdate_release args msk l r nt L)) = map fst fr @ rev (map fst ((nt, e) # bk))"
      using tsO by (simp add: dr comp_def g_def split_beta[symmetric] case_prod_unfold if_distrib)
    show "List.sorted (map fst (drop m (eupdate_release args msk l r nt L)))"
    proof -
      have "map fst (map g Os) = map fst Os" by (auto simp: g_def split: prod.splits)
      then show ?thesis using so leO curle by (auto simp: dr sorted_append intro: order_trans)
    qed
    show "map snd ((nt, e) # bk) = rev (drop (length fr) (es @ [e]))" using bks l2 by simp
    show "B' = efold (drop (length fr) (es @ [e]))"
      using Bs l2 by (cases "drop (length fr) es = []")
        (auto simp: B'_def efold_append ecompoo_def ecompo_def split: option.splits dest: efold_Some)
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
    fix k assume k: "k < length fr"
    have "take (length fr) (es @ [e]) = take (length fr) es" using l2 by simp
    then show "Some (snd (fr ! k)) = efold (drop k (take (length fr) (es @ [e])))" using frs k by simp
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
        by (simp add: dr nth_append e_def ecompo_def)
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

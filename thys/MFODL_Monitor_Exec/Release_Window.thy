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
  the same work once per tuple.

  A tuple's \<^emph>\<open>run\<close> is a maximal stretch of points at which the right operand holds and the
  left one does not.  The pending tuples of an entry are those whose current run started at or
  before it, so a single mapping from each tuple to the start of its current run serves every
  entry.  A tuple dies at an entry when its run reaches past it and ends at a point, inside the
  interval, where the right operand fails; the structure records each such end as a
  \<^emph>\<open>kill\<close> \<open>(p, f, t\<^sub>f)\<close> -- the run started at \<open>p\<close>, ended at \<open>f\<close>, and \<open>t\<^sub>f\<close>
  is the timestamp of \<open>f\<close> -- in a queue per tuple.  Runs do not overlap, so a tuple's kills are
  ordered, and the only one that can reach the oldest pending entry is the first.  An entry is
  read off when it leaves the window: its tuples less those its first kill reaches.  A kill is
  dropped once the entries it reaches are gone, which happens when the entry just before its end
  leaves, and that entry contains the tuple.

  The state is the timestamp of the last point, the index of the oldest pending point, the index
  of the next one, the pending points' timestamps and right-operand tables, the run starts and
  the kills.
\<close>

type_synonym 'b eraux = "ts \<times> nat \<times> nat \<times> (ts \<times> 'b list set) queue \<times>
  ('b list, nat) mapping \<times> ('b list, (nat \<times> nat \<times> ts) queue) mapping"

definition kqq :: "('b list, (nat \<times> nat \<times> ts) queue) mapping \<Rightarrow> 'b list \<Rightarrow>
    (nat \<times> nat \<times> ts) queue" where
  "kqq K v = (case Mapping.lookup K v of None \<Rightarrow> empty_queue | Some q \<Rightarrow> q)"

definition eraux_init :: "'b eraux" where
  "eraux_init = (0, 0, 0, empty_queue, Mapping.empty, Mapping.empty)"

definition eraux_update :: "args \<Rightarrow> bool list \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> ts \<Rightarrow>
    'b eraux \<Rightarrow> 'b eraux" where
  "eraux_update args msk l r nt aux = (case aux of (cur, oi, n, pend, P, K) \<Rightarrow>
     let W = Mapping.keys P;
         W' = esemi msk (\<not> args_pos args) r l;
         K' = (if oi = n then K
           else upd_set K (\<lambda>v. append_queue (the (Mapping.lookup P v), n, nt) (kqq K v)) (W - r));
         P' = upd_set (Mapping.filter (\<lambda>v _. v \<in> W') P) (\<lambda>_. n) (W' - W)
     in (nt, oi, Suc n, append_queue (nt, r) pend, P', K'))"

definition front_dead :: "\<I> \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> (nat \<times> nat \<times> ts) queue \<Rightarrow> bool" where
  "front_dead I i t q = (case hd_queue q of None \<Rightarrow> False
     | Some (p, f, tf) \<Rightarrow> p \<le> i \<and> memR I (tf - t))"

definition eraux_prune :: "nat \<Rightarrow> ('b list, (nat \<times> nat \<times> ts) queue) mapping \<Rightarrow> 'b list set \<Rightarrow>
    ('b list, (nat \<times> nat \<times> ts) queue) mapping" where
  "eraux_prune i K X = (let
     K1 = upd_set K (\<lambda>v. dropWhile_queue (\<lambda>(p, f, tf). f \<le> Suc i) (kqq K v)) X
   in mapping_delete_set K1 (Set.filter (\<lambda>v. hd_queue (kqq K1 v) = None) X))"

fun eraux_pops :: "\<I> \<Rightarrow> nat \<Rightarrow> ('b list, (nat \<times> nat \<times> ts) queue) mapping \<Rightarrow>
    (ts \<times> 'b list set) list \<Rightarrow> 'b list set list \<times> ('b list, (nat \<times> nat \<times> ts) queue) mapping" where
  "eraux_pops I i K [] = ([], K)"
| "eraux_pops I i K ((t, X) # xs) =
     (let Y = Set.filter (\<lambda>v. \<not> front_dead I i t (kqq K v)) X;
          (ys, K') = eraux_pops I (Suc i) (eraux_prune i K X) xs
      in (Y # ys, K'))"

definition eraux_eval :: "\<I> \<Rightarrow> ts \<Rightarrow> 'b eraux \<Rightarrow> 'b list set list \<times> 'b eraux" where
  "eraux_eval I nt aux = (case aux of (cur, oi, n, pend, P, K) \<Rightarrow>
     let (pend', taken) = takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) pend;
         (ys, K') = eraux_pops I oi K taken
     in (ys, (cur, oi + length taken, n, pend', P, K')))"


subsection \<open>The structure refines the list\<close>

definition kq :: "('b list, (nat \<times> nat \<times> ts) queue) mapping \<Rightarrow> 'b list \<Rightarrow>
    (nat \<times> nat \<times> ts) list" where
  "kq K v = linearize (kqq K v)"

definition erdead :: "\<I> \<Rightarrow> (nat \<times> nat \<times> ts) list \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> bool" where
  "erdead I ks i t = (\<exists>(p, f, tf) \<in> set ks. p \<le> i \<and> i < f \<and> memR I (tf - t))"

text \<open>
  The structure stands for a list of @{const eupdate_release} when the pending points line up
  with its entries; an entry's alive tuples are its right operand's less those a kill reaches;
  while the entry is inside the interval, its pending tuples are those whose run started at or
  before it.  The remaining conjuncts are what keeps this true: run starts lie before the next
  point and after the kills of their tuple, every running tuple holds at the last point, a kill
  ends after the oldest pending point at a point that holds the tuple, and a tuple's kills are
  ordered.
\<close>

definition erel_list :: "\<I> \<Rightarrow> ts \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (ts \<times> 'b list set) list \<Rightarrow>
    ('b list, nat) mapping \<Rightarrow> ('b list, (nat \<times> nat \<times> ts) queue) mapping \<Rightarrow>
    (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow> bool" where
  "erel_list I cur oi n ps P K L \<longleftrightarrow> length ps = length L \<and> oi + length L = n \<and>
     (\<forall>k < length L. fst (ps ! k) = fst (L ! k) \<and>
       snd (snd (L ! k)) = {v \<in> snd (ps ! k). \<not> erdead I (kq K v) (oi + k) (fst (ps ! k))} \<and>
       (memR I (cur - fst (ps ! k)) \<longrightarrow>
         fst (snd (L ! k)) = {v \<in> Mapping.keys P. the (Mapping.lookup P v) \<le> oi + k})) \<and>
     (\<forall>v p. Mapping.lookup P v = Some p \<longrightarrow> p < n \<and> (\<forall>(p', f, tf) \<in> set (kq K v). f \<le> p)) \<and>
     (ps \<noteq> [] \<longrightarrow> Mapping.keys P \<subseteq> snd (last ps)) \<and>
     (\<forall>v. \<forall>(p, f, tf) \<in> set (kq K v). oi < f \<and> f \<le> n \<and> p < f \<and> v \<in> snd (ps ! (f - Suc oi))) \<and>
     (\<forall>v. sorted_wrt (\<lambda>(p, f, _) (p', f', _). f \<le> p') (kq K v))"

definition erel :: "\<I> \<Rightarrow> 'b eraux \<Rightarrow> (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow> bool" where
  "erel I aux L = (case aux of (cur, oi, n, pend, P, K) \<Rightarrow>
     erel_list I cur oi n (linearize pend) P K L)"

lemma erel_init: "erel I eraux_init []"
  by (simp add: erel_def eraux_init_def erel_list_def empty_queue_rep kq_def kqq_def)

lemma fst_eraux_update[simp]: "fst (eraux_update args msk l r nt aux) = nt"
  by (simp add: eraux_update_def Let_def split: prod.splits)

lemma esemi_Int: "esemi msk b (A \<inter> r) l = A \<inter> esemi msk b r l"
  by (auto simp: esemi_def)

lemma esemi_sub: "esemi msk b r l \<subseteq> r"
  by (auto simp: esemi_def)

lemma length_eupdate_release[simp]: "length (eupdate_release args msk l r nt L) = Suc (length L)"
  by (simp add: eupdate_release_def)

lemma eupdate_release_nth: "k < length L \<Longrightarrow> eupdate_release args msk l r nt L ! k =
  (case L ! k of (t, a1, a2) \<Rightarrow> if memR (args_ivl args) (nt - t)
    then (t, esemi msk (\<not> args_pos args) (a1 \<inter> r) l, a2 - (a1 - r)) else (t, a1, a2))"
  by (simp add: eupdate_release_def nth_append)

lemma eupdate_release_last: "eupdate_release args msk l r nt L ! length L =
  (nt, esemi msk (\<not> args_pos args) r l, r)"
  by (simp add: eupdate_release_def nth_append)

lemma erel_update:
  assumes rel: "erel I aux L" and le: "fst aux \<le> nt" and I: "args_ivl args = I"
  shows "erel I (eraux_update args msk l r nt aux) (eupdate_release args msk l r nt L)"
proof -
  obtain cur oi n pend P K where aux: "aux = (cur, oi, n, pend, P, K)" by (cases aux) auto
  define ps where "ps = linearize pend"
  define W where "W = Mapping.keys P"
  define W' where "W' = esemi msk (\<not> args_pos args) r l"
  define K' where "K' = (if oi = n then K
    else upd_set K (\<lambda>v. append_queue (the (Mapping.lookup P v), n, nt) (kqq K v)) (W - r))"
  define P' where "P' = upd_set (Mapping.filter (\<lambda>v _. v \<in> W') P) (\<lambda>_. n) (W' - W)"
  have upd: "eraux_update args msk l r nt aux = (nt, oi, Suc n, append_queue (nt, r) pend, P', K')"
    by (simp add: aux eraux_update_def Let_def W_def W'_def K'_def P'_def)
  have R: "erel_list I cur oi n ps P K L" using rel by (simp add: erel_def aux ps_def)
  have cur: "cur \<le> nt" using le by (simp add: aux)
  have len: "length ps = length L" and on: "oi + length L = n"
    and E0: "\<forall>k < length L. fst (ps ! k) = fst (L ! k) \<and>
       snd (snd (L ! k)) = {v \<in> snd (ps ! k). \<not> erdead I (kq K v) (oi + k) (fst (ps ! k))} \<and>
       (memR I (cur - fst (ps ! k)) \<longrightarrow>
         fst (snd (L ! k)) = {v \<in> Mapping.keys P. the (Mapping.lookup P v) \<le> oi + k})"
    and Pv0: "\<forall>v p. Mapping.lookup P v = Some p \<longrightarrow> p < n \<and> (\<forall>(p', f, tf) \<in> set (kq K v). f \<le> p)"
    and Pl0: "ps \<noteq> [] \<longrightarrow> Mapping.keys P \<subseteq> snd (last ps)"
    and Kv0: "\<forall>v. \<forall>(p, f, tf) \<in> set (kq K v). oi < f \<and> f \<le> n \<and> p < f \<and> v \<in> snd (ps ! (f - Suc oi))"
    and Ks0: "\<forall>v. sorted_wrt (\<lambda>(p, f, _) (p', f', _). f \<le> p') (kq K v)"
    using R unfolding erel_list_def by - (elim conjE; assumption)+
  have Ks: "sorted_wrt (\<lambda>(p, f, _) (p', f', _). f \<le> p') (kq K v)" for v
    using Ks0 by blast
  have E: "fst (ps ! k) = fst (L ! k) \<and>
      snd (snd (L ! k)) = {v \<in> snd (ps ! k). \<not> erdead I (kq K v) (oi + k) (fst (ps ! k))} \<and>
      (memR I (cur - fst (ps ! k)) \<longrightarrow>
        fst (snd (L ! k)) = {v \<in> Mapping.keys P. the (Mapping.lookup P v) \<le> oi + k})"
    if "k < length L" for k
    using E0 that by blast
  have Pv: "p < n \<and> (\<forall>(p', f, tf) \<in> set (kq K v). f \<le> p)" if "Mapping.lookup P v = Some p" for v p
    using Pv0 that by blast
  have Pl: "Mapping.keys P \<subseteq> snd (last ps)" if "ps \<noteq> []"
    using Pl0 that by blast
  have Kv: "oi < f \<and> f \<le> n \<and> p < f \<and> v \<in> snd (ps ! (f - Suc oi))" if "(p, f, tf) \<in> set (kq K v)"
    for v p f tf
    using Kv0 that by fast
  have lP': "Mapping.lookup P' v = (if v \<in> W' then (if v \<in> W then Mapping.lookup P v else Some n)
      else None)" for v
    by (auto simp: P'_def W_def Mapping_lookup_upd_set Mapping.lookup_filter keys_is_none_rep
        split: option.splits)
  have kP': "Mapping.keys P' = W'"
    by (auto simp: keys_is_none_rep lP' W_def split: if_splits)
  have kK': "kq K' v = (if oi \<noteq> n \<and> v \<in> W - r
      then kq K v @ [(the (Mapping.lookup P v), n, nt)] else kq K v)" for v
    by (auto simp: K'_def kq_def kqq_def Mapping_lookup_upd_set append_queue_rep)
  define L' where "L' = eupdate_release args msk l r nt L"
  define ps' where "ps' = ps @ [(nt, r)]"
  have ed: "erdead I (kq K' v) i t \<longleftrightarrow> erdead I (kq K v) i t \<or>
      (oi \<noteq> n \<and> v \<in> W - r \<and> the (Mapping.lookup P v) \<le> i \<and> memR I (nt - t))"
    if "i < n" for v i t
    using that by (auto simp: kK' erdead_def)
  have ed_n: "\<not> erdead I (kq K' v) n t" for v t
  proof -
    have "f \<le> n" if "(p, f, tf) \<in> set (kq K' v)" for p f tf
      using that by (auto simp: kK' split: if_splits dest: Kv)
    then show ?thesis by (fastforce simp: erdead_def)
  qed
  have P'n: "the (Mapping.lookup P' v) \<le> n" if "v \<in> W'" for v
    using that Pv by (cases "Mapping.lookup P v") (auto simp: lP' W_def keys_is_none_rep less_imp_le)
  have entries: "fst (ps' ! k) = fst (L' ! k) \<and>
      snd (snd (L' ! k)) = {v \<in> snd (ps' ! k). \<not> erdead I (kq K' v) (oi + k) (fst (ps' ! k))} \<and>
      (memR I (nt - fst (ps' ! k)) \<longrightarrow>
        fst (snd (L' ! k)) = {v \<in> Mapping.keys P'. the (Mapping.lookup P' v) \<le> oi + k})"
    if k: "k < Suc (length L)" for k
  proof (cases "k < length L")
    case True
    obtain t a1 a2 where Lk: "L ! k = (t, a1, a2)" by (cases "L ! k") auto
    have pk: "ps' ! k = ps ! k" using True len by (simp add: ps'_def nth_append)
    have t: "fst (ps ! k) = t"
      and a2: "a2 = {v \<in> snd (ps ! k). \<not> erdead I (kq K v) (oi + k) t}"
      and a1: "memR I (cur - t) \<Longrightarrow> a1 = {v \<in> W. the (Mapping.lookup P v) \<le> oi + k}"
      using E[OF True] Lk by (auto simp: W_def)
    have i: "oi + k < n" and nn: "oi \<noteq> n" using True on by simp_all
    show ?thesis
    proof (cases "memR I (nt - t)")
      case True2: True
      have mc: "memR I (cur - t)" by (rule memR_antimono[OF True2 diff_le_mono[OF cur]])
      have L'k: "L' ! k = (t, esemi msk (\<not> args_pos args) (a1 \<inter> r) l, a2 - (a1 - r))"
        using True True2 Lk by (simp add: L'_def eupdate_release_nth I)
      have "a2 - (a1 - r) = {v \<in> snd (ps ! k). \<not> erdead I (kq K' v) (oi + k) t}"
        unfolding a2 a1[OF mc] ed[OF i] using nn True2 by auto
      moreover have "esemi msk (\<not> args_pos args) (a1 \<inter> r) l =
          {v \<in> Mapping.keys P'. the (Mapping.lookup P' v) \<le> oi + k}"
        unfolding esemi_Int a1[OF mc] kP' W'_def[symmetric] using i
        by (auto simp: lP')
      ultimately show ?thesis using L'k pk t by simp
    next
      case False2: False
      have L'k: "L' ! k = (t, a1, a2)"
        using True False2 Lk by (simp add: L'_def eupdate_release_nth I)
      have "a2 = {v \<in> snd (ps ! k). \<not> erdead I (kq K' v) (oi + k) t}"
        unfolding a2 ed[OF i] using False2 by auto
      then show ?thesis using L'k pk t False2 by simp
    qed
  next
    case False
    then have kl: "k = length L" using k by simp
    have pk: "ps' ! k = (nt, r)" using kl len by (simp add: ps'_def nth_append)
    have L'k: "L' ! k = (nt, W', r)" using kl by (simp add: L'_def eupdate_release_last W'_def)
    have "W' = {v \<in> Mapping.keys P'. the (Mapping.lookup P' v) \<le> oi + k}"
      using P'n on kl by (auto simp: kP')
    then show ?thesis using pk L'k on kl ed_n by simp
  qed
  have Pv': "p < Suc n \<and> (\<forall>(p', f, tf) \<in> set (kq K' v). f \<le> p)"
    if "Mapping.lookup P' v = Some p" for v p
  proof (cases "v \<in> W")
    case True
    then have v: "v \<in> W'" "Mapping.lookup P v = Some p" using that by (auto simp: lP' split: if_splits)
    have "v \<notin> W - r" using v(1) esemi_sub[of msk _ r l] by (auto simp: W'_def)
    then show ?thesis using Pv[OF v(2)] by (simp add: kK')
  next
    case False
    then have "p = n" using that by (auto simp: lP' split: if_splits)
    then show ?thesis using Kv False by (fastforce simp: kK')
  qed
  have Pl': "Mapping.keys P' \<subseteq> snd (last ps')"
    using esemi_sub[of msk _ r l] by (simp add: kP' W'_def ps'_def)
  have Kv': "oi < f \<and> f \<le> Suc n \<and> p < f \<and> v \<in> snd (ps' ! (f - Suc oi))"
    if "(p, f, tf) \<in> set (kq K' v)" for v p f tf
  proof (cases "(p, f, tf) \<in> set (kq K v)")
    case True
    have "f - Suc oi < length ps" using Kv[OF True] on len by arith
    then show ?thesis using Kv[OF True] by (simp add: ps'_def nth_append)
  next
    case False
    then have new: "oi \<noteq> n" "v \<in> W - r" "p = the (Mapping.lookup P v)" "f = n"
      using that by (auto simp: kK' split: if_splits)
    have ne: "ps \<noteq> []" using new(1) on len by auto
    obtain q where q: "Mapping.lookup P v = Some q" using new(2) unfolding W_def by (auto dest: Mapping.in_keysD)
    have "n - Suc oi = length ps - 1" using on len by simp
    then have "ps' ! (f - Suc oi) = last ps" using ne new(4) by (simp add: ps'_def nth_append last_conv_nth)
    then show ?thesis using new q Pv[OF q] Pl[OF ne] on len ne by (auto simp: W_def)
  qed
  have Ks': "sorted_wrt (\<lambda>(p, f, _) (p', f', _). f \<le> p') (kq K' v)" for v
  proof (cases "oi \<noteq> n \<and> v \<in> W - r")
    case True
    obtain q where q: "Mapping.lookup P v = Some q" using True unfolding W_def by (auto dest: Mapping.in_keysD)
    show ?thesis using True Ks[of v] Pv[OF q] by (auto simp: kK' sorted_wrt_append q)
  qed (auto simp: kK' Ks)
  have "erel_list I nt oi (Suc n) ps' P' K' L'"
    unfolding erel_list_def
    using entries Pv' Pl' Kv' Ks' len on by (simp add: L'_def ps'_def; blast)
  then show ?thesis
    by (simp add: upd erel_def append_queue_rep ps_def[symmetric] L'_def ps'_def)
qed

lemma erdead_dropWhile:
  assumes "j \<le> i"
  shows "erdead I (dropWhile (\<lambda>(p, f, tf). f \<le> j) ks) i t = erdead I ks i t"
proof
  assume "erdead I (dropWhile (\<lambda>(p, f, tf). f \<le> j) ks) i t"
  then show "erdead I ks i t" by (fastforce simp: erdead_def dest: set_dropWhileD)
next
  assume "erdead I ks i t"
  then obtain p f tf where x: "(p, f, tf) \<in> set ks" "p \<le> i" "i < f" "memR I (tf - t)"
    by (auto simp: erdead_def)
  have "(p, f, tf) \<notin> set (takeWhile (\<lambda>(p, f, tf). f \<le> j) ks)"
    using x(3) assms by (auto dest: set_takeWhileD)
  then have "(p, f, tf) \<in> set (dropWhile (\<lambda>(p, f, tf). f \<le> j) ks)"
    using x(1) takeWhile_dropWhile_id[of "\<lambda>(p, f, tf). f \<le> j" ks] by (metis Un_iff set_append)
  then show "erdead I (dropWhile (\<lambda>(p, f, tf). f \<le> j) ks) i t"
    using x by (fastforce simp: erdead_def)
qed

lemma sorted_wrt_dropWhile: "sorted_wrt R xs \<Longrightarrow> sorted_wrt R (dropWhile P xs)"
  using takeWhile_dropWhile_id[of P xs] by (metis sorted_wrt_append)

lemma dropWhile_kills_after:
  fixes xs :: "(nat \<times> nat \<times> ts) list"
  assumes "sorted_wrt (\<lambda>(p, f, _) (p', f', _). f \<le> p') xs" and "\<forall>(p, f, tf) \<in> set xs. p < f"
    and "(p, f, tf) \<in> set (dropWhile (\<lambda>(p, f, tf). f \<le> j) xs)"
  shows "j < f"
  using assms
proof (induct xs)
  case (Cons x xs)
  obtain p0 f0 tf0 where x: "x = (p0, f0, tf0)" by (cases x) auto
  show ?case
  proof (cases "f0 \<le> j")
    case True
    then show ?thesis using Cons by (simp add: x)
  next
    case False
    then have "(p, f, tf) = x \<or> (p, f, tf) \<in> set xs" using Cons(4) by (simp add: x)
    then show ?thesis
    proof (elim disjE)
      assume "(p, f, tf) = x"
      then show ?thesis using False by (simp add: x)
    next
      assume m: "(p, f, tf) \<in> set xs"
      have "f0 \<le> p" using Cons(2) m by (auto simp: x)
      moreover have "p < f" using Cons(3) m by auto
      ultimately show ?thesis using False by simp
    qed
  qed
qed simp

lemma Nil_eq_dropWhile_conv: "([] = dropWhile P xs) = (\<forall>x \<in> set xs. P x)"
  by (metis dropWhile_eq_Nil_conv)

lemma kq_prune: "kq (eraux_prune i K X) v =
    (if v \<in> X then dropWhile (\<lambda>(p, f, tf). f \<le> Suc i) (kq K v) else kq K v)"
  by (auto simp: eraux_prune_def kq_def kqq_def Let_def delete_set_lookup Mapping_lookup_upd_set
      dropWhile_queue_rep hd_queue_rep empty_queue_rep Nil_eq_dropWhile_conv
      split: option.splits list.splits
      simp del: dropWhile_queue.simps)

lemma front_dead_erdead:
  assumes "\<forall>(p, f, tf) \<in> set (kq K v). i < f \<and> p < f"
    and "sorted_wrt (\<lambda>(p, f, _) (p', f', _). f \<le> p') (kq K v)"
  shows "front_dead I i t (kqq K v) = erdead I (kq K v) i t"
proof (cases "kq K v")
  case (Cons x xs)
  obtain p f tf where x: "x = (p, f, tf)" by (cases x) auto
  have "\<not> p' \<le> i" if "(p', f', tf') \<in> set xs" for p' f' tf'
    using assms that by (fastforce simp: Cons x)
  then show ?thesis using assms
    by (auto simp: front_dead_def hd_queue_rep kq_def[symmetric] Cons x erdead_def)
qed (simp add: front_dead_def hd_queue_rep kq_def[symmetric] erdead_def)

lemma erel_pop:
  assumes R: "erel_list I cur oi n ((t, X) # ps) P K ((t', a1, a2) # L)"
  shows "Set.filter (\<lambda>v. \<not> front_dead I oi t (kqq K v)) X = a2 \<and>
    erel_list I cur (Suc oi) n ps P (eraux_prune oi K X) L"
proof -
  have len0: "length ((t, X) # ps) = length ((t', a1, a2) # L)"
    and on: "oi + length ((t', a1, a2) # L) = n"
    and E0: "\<forall>k < length ((t', a1, a2) # L). fst (((t, X) # ps) ! k) = fst (((t', a1, a2) # L) ! k) \<and>
       snd (snd (((t', a1, a2) # L) ! k)) = {v \<in> snd (((t, X) # ps) ! k).
         \<not> erdead I (kq K v) (oi + k) (fst (((t, X) # ps) ! k))} \<and>
       (memR I (cur - fst (((t, X) # ps) ! k)) \<longrightarrow>
         fst (snd (((t', a1, a2) # L) ! k)) = {v \<in> Mapping.keys P. the (Mapping.lookup P v) \<le> oi + k})"
    and Pv0: "\<forall>v p. Mapping.lookup P v = Some p \<longrightarrow> p < n \<and> (\<forall>(p', f, tf) \<in> set (kq K v). f \<le> p)"
    and Pl0: "(t, X) # ps \<noteq> [] \<longrightarrow> Mapping.keys P \<subseteq> snd (last ((t, X) # ps))"
    and Kv0: "\<forall>v. \<forall>(p, f, tf) \<in> set (kq K v). oi < f \<and> f \<le> n \<and> p < f \<and>
      v \<in> snd (((t, X) # ps) ! (f - Suc oi))"
    and Ks0: "\<forall>v. sorted_wrt (\<lambda>(p, f, _) (p', f', _). f \<le> p') (kq K v)"
    using R unfolding erel_list_def by - (elim conjE; assumption)+
  have len: "length ps = length L" using len0 by simp
  have Kv: "oi < f \<and> f \<le> n \<and> p < f \<and> v \<in> snd (((t, X) # ps) ! (f - Suc oi))"
    if "(p, f, tf) \<in> set (kq K v)" for v p f tf
    using Kv0 that by fast
  have Ks: "sorted_wrt (\<lambda>(p, f, _) (p', f', _). f \<le> p') (kq K v)" for v
    using Ks0 by blast
  have a2: "a2 = {v \<in> X. \<not> erdead I (kq K v) oi t}"
    using E0 by (auto dest: spec[of _ 0])
  have fd: "front_dead I oi t (kqq K v) = erdead I (kq K v) oi t" for v
    by (rule front_dead_erdead) (use Kv Ks in fast)+
  define K' where "K' = eraux_prune oi K X"
  have kK': "kq K' v = (if v \<in> X then dropWhile (\<lambda>(p, f, tf). f \<le> Suc oi) (kq K v) else kq K v)"
    for v by (simp add: K'_def kq_prune)
  have sub: "x \<in> set (kq K v)" if "x \<in> set (kq K' v)" for x v
    using that by (auto simp: kK' split: if_splits dest: set_dropWhileD)
  have after: "Suc oi < f" if "(p, f, tf) \<in> set (kq K' v)" for p f tf v
  proof (cases "v \<in> X")
    case True
    have "\<forall>(p, f, tf) \<in> set (kq K v). p < f" using Kv by fast
    moreover have "(p, f, tf) \<in> set (dropWhile (\<lambda>(p, f, tf). f \<le> Suc oi) (kq K v))"
      using that True by (simp add: kK')
    ultimately show ?thesis by (rule dropWhile_kills_after[OF Ks])
  next
    case False
    then have "(p, f, tf) \<in> set (kq K v)" using that by (simp add: kK')
    from Kv[OF this] False show ?thesis by (cases "f = Suc oi") auto
  qed
  have ed: "erdead I (kq K' v) i u = erdead I (kq K v) i u" if "Suc oi \<le> i" for v i u
    using that by (simp add: kK' erdead_dropWhile)
  have "erel_list I cur (Suc oi) n ps P K' L"
    unfolding erel_list_def
  proof (intro conjI allI impI)
    show "length ps = length L" by (rule len)
    show "Suc oi + length L = n" using on by simp
  next
    fix k assume k: "k < length L"
    have "Suc k < length ((t', a1, a2) # L)" using k by simp
    note e = E0[rule_format, OF this]
    show "fst (ps ! k) = fst (L ! k)" using e by simp
    show "snd (snd (L ! k)) = {v \<in> snd (ps ! k). \<not> erdead I (kq K' v) (Suc oi + k) (fst (ps ! k))}"
      using e by (simp add: ed)
    show "fst (snd (L ! k)) = {v \<in> Mapping.keys P. the (Mapping.lookup P v) \<le> Suc oi + k}"
      if "memR I (cur - fst (ps ! k))" using e that by simp
  next
    fix v p assume "Mapping.lookup P v = Some p"
    then show "p < n" "\<forall>(p', f, tf) \<in> set (kq K' v). f \<le> p" using Pv0 sub by fast+
  next
    assume "ps \<noteq> []"
    then show "Mapping.keys P \<subseteq> snd (last ps)" using Pl0 by simp
  next
    fix v
    show "\<forall>(p, f, tf) \<in> set (kq K' v). Suc oi < f \<and> f \<le> n \<and> p < f \<and> v \<in> snd (ps ! (f - Suc (Suc oi)))"
    proof (intro ballI, clarify)
      fix p f tf assume x: "(p, f, tf) \<in> set (kq K' v)"
      have a: "Suc oi < f" by (rule after[OF x])
      have "f - Suc oi = Suc (f - Suc (Suc oi))" using a by simp
      then show "Suc oi < f \<and> f \<le> n \<and> p < f \<and> v \<in> snd (ps ! (f - Suc (Suc oi)))"
        using Kv[OF sub[OF x]] a by simp
    qed
    show "sorted_wrt (\<lambda>(p, f, _) (p', f', _). f \<le> p') (kq K' v)"
      using Ks[of v] by (simp add: kK')
  qed
  moreover have "Set.filter (\<lambda>v. \<not> front_dead I oi t (kqq K v)) X = a2"
    by (auto simp: a2 fd)
  ultimately show ?thesis by (simp add: K'_def)
qed

lemma erel_pops:
  "erel_list I cur oi n (xs @ ps) P K (L1 @ L2) \<Longrightarrow> length xs = length L1 \<Longrightarrow>
   eraux_pops I oi K xs = (ys, K') \<Longrightarrow>
   ys = map (\<lambda>(t, a1, a2). a2) L1 \<and> erel_list I cur (oi + length xs) n ps P K' L2"
proof (induct xs arbitrary: oi K L1 ys K')
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain t X where x: "x = (t, X)" by (cases x)
  obtain l L1' where L1: "L1 = l # L1'" using Cons(3) by (cases L1) auto
  obtain t' a1 a2 where l: "l = (t', a1, a2)" by (cases l)
  have pop: "Set.filter (\<lambda>v. \<not> front_dead I oi t (kqq K v)) X = a2 \<and>
      erel_list I cur (Suc oi) n (xs @ ps) P (eraux_prune oi K X) (L1' @ L2)"
    by (rule erel_pop) (use Cons(2) in \<open>simp add: x L1 l\<close>)
  obtain ys' K'' where rec: "eraux_pops I (Suc oi) (eraux_prune oi K X) xs = (ys', K'')"
    by fastforce
  have ih: "ys' = map (\<lambda>(t, a1, a2). a2) L1' \<and> erel_list I cur (Suc oi + length xs) n ps P K'' L2"
    by (rule Cons(1)[OF pop[THEN conjunct2] _ rec]) (use Cons(3) in \<open>simp add: L1\<close>)
  show ?case using Cons(4) pop ih rec by (simp add: x L1 l Let_def)
qed

lemma eval_until_takeWhile: "eval_until I nt L =
  (map (\<lambda>(t, a1, a2). a2) (takeWhile (\<lambda>x. \<not> memR I (nt - fst x)) L),
   dropWhile (\<lambda>x. \<not> memR I (nt - fst x)) L)"
  by (induct I nt L rule: eval_until.induct) (auto simp: Let_def split: prod.splits)

lemma erel_eval:
  assumes rel: "erel I aux L" and e: "eraux_eval I nt aux = (ys, aux')"
  shows "fst (eval_until I nt L) = ys \<and> erel I aux' (snd (eval_until I nt L)) \<and> fst aux' = fst aux"
proof -
  obtain cur oi n pend P K where aux: "aux = (cur, oi, n, pend, P, K)" by (cases aux) auto
  define ps where "ps = linearize pend"
  define Q :: "ts \<Rightarrow> bool" where "Q = (\<lambda>t. \<not> memR I (nt - t))"
  have R: "erel_list I cur oi n ps P K L" using rel by (simp add: erel_def aux ps_def)
  have len: "length ps = length L" using R by (simp add: erel_list_def)
  have mf: "map fst ps = map fst L"
    using R by (intro nth_equalityI) (auto simp: erel_list_def)
  have qe: "(\<lambda>(t, _). \<not> memR I (nt - t)) = Q \<circ> fst" by (auto simp: Q_def fun_eq_iff)
  have qe': "(\<lambda>x. \<not> memR I (nt - fst x)) = Q \<circ> fst" by (auto simp: Q_def fun_eq_iff)
  define xs where "xs = takeWhile (Q \<circ> fst) ps"
  have td: "takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) pend =
      (dropWhile_queue (Q \<circ> fst) pend, xs)"
    by (simp add: prod_eq_iff takedropWhile_queue_fst takedropWhile_queue_snd qe xs_def ps_def
      del: takedropWhile_queue.simps dropWhile_queue.simps)
  obtain ys0 K' where p: "eraux_pops I oi K xs = (ys0, K')" by fastforce
  have e': "ys = ys0 \<and> aux' = (cur, oi + length xs, n, dropWhile_queue (Q \<circ> fst) pend, P, K')"
    using e by (simp add: eraux_eval_def aux td p Let_def
      del: takedropWhile_queue.simps dropWhile_queue.simps)
  have lx: "length xs = length (takeWhile (Q \<circ> fst) L)"
    using arg_cong[OF mf, of "\<lambda>xs. length (takeWhile Q xs)"] by (simp add: takeWhile_map xs_def)
  have "erel_list I cur oi n (xs @ dropWhile (Q \<circ> fst) ps) P K
      (takeWhile (Q \<circ> fst) L @ dropWhile (Q \<circ> fst) L)"
    using R by (simp add: xs_def)
  from erel_pops[OF this lx p]
  have "ys0 = map (\<lambda>(t, a1, a2). a2) (takeWhile (Q \<circ> fst) L) \<and>
      erel_list I cur (oi + length xs) n (dropWhile (Q \<circ> fst) ps) P K' (dropWhile (Q \<circ> fst) L)" .
  then show ?thesis
    using e' by (simp add: eval_until_takeWhile qe' erel_def dropWhile_queue_rep ps_def[symmetric] aux
      del: takedropWhile_queue.simps dropWhile_queue.simps)
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

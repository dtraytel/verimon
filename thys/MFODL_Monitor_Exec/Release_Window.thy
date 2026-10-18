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
  leaves, and that entry contains the tuple.  Most runs end right after they start, and such a
  run reaches only the entry it started at, which is the last one; its kill is taken out of that
  entry's table directly instead of being queued.  For the same reason, pruning looks only at the
  tuples whose first kill is due.

  The state is the timestamp of the last point, the index of the oldest pending point, the index
  of the next one, the pending points' timestamps and right-operand tables, the run starts and
  the kills.
\<close>

text \<open>The table of the last pending point is changed in place.\<close>

fun map_last_t :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "map_last_t g ([], []) = ([], [])"
| "map_last_t g (fs, l # ls) = (fs, g l # ls)"
| "map_last_t g (f # fs, []) = (f # fs, [])"

lift_definition map_last_queue :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is map_last_t
  by (auto simp: queue_invariant_def split: list.splits elim!: map_last_t.elims)

lemma map_last_queue_rep: "linearize (map_last_queue g q) =
    (if linearize q = [] then [] else butlast (linearize q) @ [g (last (linearize q))])"
  by transfer (auto simp: queue_invariant_def butlast_append split: list.splits elim!: map_last_t.elims)

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
         D = W - r;
         S = Set.filter (\<lambda>v. the (Mapping.lookup P v) = n - 1) D;
         pend' = map_last_queue (\<lambda>(tz, Xl).
           if memR (args_ivl args) (nt - tz) then (tz, Xl - S) else (tz, Xl)) pend;
         K' = (if oi = n then K
           else upd_set K (\<lambda>v. append_queue (the (Mapping.lookup P v), n, nt) (kqq K v)) (D - S));
         P' = upd_set (Mapping.filter (\<lambda>v _. v \<in> W') P) (\<lambda>_. n) (W' - W)
     in (nt, oi, Suc n, append_queue (nt, r) pend', P', K'))"

definition front_dead :: "\<I> \<Rightarrow> nat \<Rightarrow> ts \<Rightarrow> (nat \<times> nat \<times> ts) queue \<Rightarrow> bool" where
  "front_dead I i t q = (case hd_queue q of None \<Rightarrow> False
     | Some (p, f, tf) \<Rightarrow> p \<le> i \<and> memR I (tf - t))"

definition eraux_prune :: "nat \<Rightarrow> ('b list, (nat \<times> nat \<times> ts) queue) mapping \<Rightarrow> 'b list set \<Rightarrow>
    ('b list, (nat \<times> nat \<times> ts) queue) mapping" where
  "eraux_prune i K X = (let
     S = Set.filter (\<lambda>v. case hd_queue (kqq K v) of None \<Rightarrow> False
       | Some (p, f, tf) \<Rightarrow> f \<le> Suc i) X;
     K1 = upd_set K (\<lambda>v. dropWhile_queue (\<lambda>(p, f, tf). f \<le> Suc i) (kqq K v)) S
   in mapping_delete_set K1 (Set.filter (\<lambda>v. hd_queue (kqq K1 v) = None) S))"

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
  ends after the oldest pending point and before the next one, at a point that holds the tuple, and
  a tuple's kills are ordered.
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
     (\<forall>v. \<forall>(p, f, tf) \<in> set (kq K v). oi < f \<and> f < n \<and> p < f \<and> v \<in> snd (ps ! (f - Suc oi))) \<and>
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
  define D where "D = W - r"
  define S where "S = Set.filter (\<lambda>v. the (Mapping.lookup P v) = n - 1) D"
  define pend1 where "pend1 = map_last_queue (\<lambda>(tz, Xl).
    if memR I (nt - tz) then (tz, Xl - S) else (tz, Xl)) pend"
  define K' where "K' = (if oi = n then K
    else upd_set K (\<lambda>v. append_queue (the (Mapping.lookup P v), n, nt) (kqq K v)) (D - S))"
  define P' where "P' = upd_set (Mapping.filter (\<lambda>v _. v \<in> W') P) (\<lambda>_. n) (W' - W)"
  have upd: "eraux_update args msk l r nt aux = (nt, oi, Suc n, append_queue (nt, r) pend1, P', K')"
    unfolding aux eraux_update_def Let_def W_def W'_def D_def S_def pend1_def K'_def P'_def I
    by simp
  have R: "erel_list I cur oi n ps P K L" using rel by (simp add: erel_def aux ps_def)
  have cur: "cur \<le> nt" using le by (simp add: aux)
  have len: "length ps = length L" and on: "oi + length L = n"
    and E0: "\<forall>k < length L. fst (ps ! k) = fst (L ! k) \<and>
       snd (snd (L ! k)) = {v \<in> snd (ps ! k). \<not> erdead I (kq K v) (oi + k) (fst (ps ! k))} \<and>
       (memR I (cur - fst (ps ! k)) \<longrightarrow>
         fst (snd (L ! k)) = {v \<in> Mapping.keys P. the (Mapping.lookup P v) \<le> oi + k})"
    and Pv0: "\<forall>v p. Mapping.lookup P v = Some p \<longrightarrow> p < n \<and> (\<forall>(p', f, tf) \<in> set (kq K v). f \<le> p)"
    and Pl0: "ps \<noteq> [] \<longrightarrow> Mapping.keys P \<subseteq> snd (last ps)"
    and Kv0: "\<forall>v. \<forall>(p, f, tf) \<in> set (kq K v). oi < f \<and> f < n \<and> p < f \<and> v \<in> snd (ps ! (f - Suc oi))"
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
  have PW: "the (Mapping.lookup P v) < n" if "v \<in> W" for v
    using that Pv unfolding W_def by (auto dest: Mapping.in_keysD)
  have Pl: "Mapping.keys P \<subseteq> snd (last ps)" if "ps \<noteq> []"
    using Pl0 that by blast
  have Kv: "oi < f \<and> f < n \<and> p < f \<and> v \<in> snd (ps ! (f - Suc oi))" if "(p, f, tf) \<in> set (kq K v)"
    for v p f tf
    using Kv0 that by fast
  define md where "md \<longleftrightarrow> oi \<noteq> n \<and> memR I (nt - fst (last ps))"
  define ps1 where "ps1 = (if md then butlast ps @ [(fst (last ps), snd (last ps) - S)] else ps)"
  have lp1: "linearize pend1 = ps1"
  proof (cases "oi = n")
    case True
    then have e: "ps = []" using len on by simp
    then show ?thesis using True by (simp add: pend1_def ps1_def md_def map_last_queue_rep ps_def[symmetric])
  next
    case False
    then have ne: "ps \<noteq> []" using len on by auto
    obtain tz Xl where tX: "last ps = (tz, Xl)" by fastforce
    show ?thesis using False ne tX
      by (auto simp: pend1_def ps1_def md_def map_last_queue_rep ps_def[symmetric] append_butlast_last_id)
  qed
  have len1: "length ps1 = length ps"
    using len on by (auto simp: ps1_def md_def)
  have p1: "fst (ps1 ! k) = fst (ps ! k) \<and>
      snd (ps1 ! k) = (if md \<and> oi + k = n - 1 then snd (ps ! k) - S else snd (ps ! k))"
    if "k < length ps" for k
  proof (cases "md")
    case True
    then have ne: "ps \<noteq> []" using len on by (auto simp: md_def)
    show ?thesis
    proof (cases "k = length ps - 1")
      case True
      have "oi + k = n - 1" using True ne on len by (cases ps) auto
      moreover have "ps1 ! k = (fst (last ps), snd (last ps) - S)"
        using True ne \<open>md\<close> by (simp add: ps1_def nth_append)
      moreover have "last ps = ps ! k" using True ne by (simp add: last_conv_nth)
      ultimately show ?thesis using \<open>md\<close> by simp
    next
      case False
      have k: "k < length (butlast ps)" using False that by simp
      have "oi + k \<noteq> n - 1" using False that on len by arith
      moreover have "ps1 ! k = ps ! k"
        using k \<open>md\<close> by (simp add: ps1_def nth_append nth_butlast)
      ultimately show ?thesis by simp
    qed
  qed (simp add: ps1_def)
  have lP': "Mapping.lookup P' v = (if v \<in> W' then (if v \<in> W then Mapping.lookup P v else Some n)
      else None)" for v
    by (auto simp: P'_def W_def Mapping_lookup_upd_set Mapping.lookup_filter keys_is_none_rep
        split: option.splits)
  have kP': "Mapping.keys P' = W'"
    by (auto simp: keys_is_none_rep lP' W_def split: if_splits)
  have kK': "kq K' v = (if oi \<noteq> n \<and> v \<in> D - S
      then kq K v @ [(the (Mapping.lookup P v), n, nt)] else kq K v)" for v
    by (auto simp: K'_def kq_def kqq_def Mapping_lookup_upd_set append_queue_rep)
  define L' where "L' = eupdate_release args msk l r nt L"
  define ps' where "ps' = ps1 @ [(nt, r)]"
  have ed: "erdead I (kq K' v) i t \<longleftrightarrow> erdead I (kq K v) i t \<or>
      (oi \<noteq> n \<and> v \<in> D - S \<and> the (Mapping.lookup P v) \<le> i \<and> memR I (nt - t))"
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
    have kp: "k < length ps" using True len by simp
    have t: "fst (ps ! k) = t"
      and a2: "a2 = {v \<in> snd (ps ! k). \<not> erdead I (kq K v) (oi + k) t}"
      and a1: "memR I (cur - t) \<Longrightarrow> a1 = {v \<in> W. the (Mapping.lookup P v) \<le> oi + k}"
      using E[OF True] Lk by (auto simp: W_def)
    have i: "oi + k < n" and nn: "oi \<noteq> n" using True on by simp_all
    have pk: "ps' ! k = ps1 ! k" using kp len1 by (simp add: ps'_def nth_append)
    have lastk: "fst (last ps) = t" if "oi + k = n - 1"
    proof -
      have "k = length ps - 1" using that kp on len by arith
      moreover have "ps \<noteq> []" using kp by auto
      ultimately show ?thesis using t by (simp add: last_conv_nth)
    qed
    have md_iff: "(md \<and> oi + k = n - 1) \<longleftrightarrow> (oi + k = n - 1 \<and> memR I (nt - t))"
      using nn lastk by (auto simp: md_def)
    have X1: "snd (ps1 ! k) = (if oi + k = n - 1 \<and> memR I (nt - t) then snd (ps ! k) - S
        else snd (ps ! k))"
      using p1[OF kp] md_iff by simp
    show ?thesis
    proof (cases "memR I (nt - t)")
      case True2: True
      have mc: "memR I (cur - t)" by (rule memR_antimono[OF True2 diff_le_mono[OF cur]])
      have L'k: "L' ! k = (t, esemi msk (\<not> args_pos args) (a1 \<inter> r) l, a2 - (a1 - r))"
        using True True2 Lk by (simp add: L'_def eupdate_release_nth I)
      have "a2 - (a1 - r) = {v \<in> snd (ps1 ! k). \<not> erdead I (kq K' v) (oi + k) t}"
      proof (cases "oi + k = n - 1")
        case True3: True
        have "{v \<in> W. the (Mapping.lookup P v) \<le> oi + k} = W" using PW True3 by fastforce
        then show ?thesis unfolding a2 a1[OF mc] ed[OF i] X1 using nn True2 True3
          by (auto simp: D_def S_def)
      next
        case False3: False
        have "the (Mapping.lookup P v) \<le> oi + k \<Longrightarrow> v \<notin> S" for v
          using False3 i by (auto simp: S_def)
        then show ?thesis unfolding a2 a1[OF mc] ed[OF i] X1 using nn True2 False3
          by (auto simp: D_def)
      qed
      moreover have "esemi msk (\<not> args_pos args) (a1 \<inter> r) l =
          {v \<in> Mapping.keys P'. the (Mapping.lookup P' v) \<le> oi + k}"
        unfolding esemi_Int a1[OF mc] kP' W'_def[symmetric] using i
        by (auto simp: lP')
      ultimately show ?thesis using L'k pk t p1[OF kp] by simp
    next
      case False2: False
      have L'k: "L' ! k = (t, a1, a2)"
        using True False2 Lk by (simp add: L'_def eupdate_release_nth I)
      have "a2 = {v \<in> snd (ps1 ! k). \<not> erdead I (kq K' v) (oi + k) t}"
        unfolding a2 ed[OF i] X1 using False2 by auto
      then show ?thesis using L'k pk t p1[OF kp] False2 by simp
    qed
  next
    case False
    then have kl: "k = length L" using k by simp
    have pk: "ps' ! k = (nt, r)" using kl len len1 by (simp add: ps'_def nth_append)
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
    have "v \<notin> D - S" using v(1) esemi_sub[of msk _ r l] by (auto simp: W'_def D_def)
    then show ?thesis using Pv[OF v(2)] by (simp add: kK')
  next
    case False
    then have "p = n" using that by (auto simp: lP' split: if_splits)
    then show ?thesis using Kv False by (fastforce simp: kK' D_def)
  qed
  have Pl': "Mapping.keys P' \<subseteq> snd (last ps')"
    using esemi_sub[of msk _ r l] by (simp add: kP' W'_def ps'_def)
  have Kv': "oi < f \<and> f < Suc n \<and> p < f \<and> v \<in> snd (ps' ! (f - Suc oi))"
    if "(p, f, tf) \<in> set (kq K' v)" for v p f tf
  proof (cases "(p, f, tf) \<in> set (kq K v)")
    case True
    have j: "f - Suc oi < length ps" and nl: "oi + (f - Suc oi) \<noteq> n - 1"
      using Kv[OF True] on len by arith+
    then show ?thesis using Kv[OF True] p1[OF j] len1 by (simp add: ps'_def nth_append)
  next
    case False
    then have new: "oi \<noteq> n" "v \<in> D - S" "p = the (Mapping.lookup P v)" "f = n"
      using that by (auto simp: kK' split: if_splits)
    have ne: "ps \<noteq> []" using new(1) on len by auto
    have vW: "v \<in> W" using new(2) by (simp add: D_def)
    have j: "n - Suc oi < length ps" and jl: "oi + (n - Suc oi) = n - 1" "n - Suc oi = length ps - 1"
      using new(1) on len by arith+
    have "ps' ! (f - Suc oi) = ps1 ! (n - Suc oi)" using j len1 new(4) by (simp add: ps'_def nth_append)
    moreover have "v \<in> snd (ps ! (n - Suc oi))"
      using Pl[OF ne] vW jl(2) ne by (auto simp: W_def last_conv_nth)
    ultimately show ?thesis using new PW[OF vW] p1[OF j] on len by auto
  qed
  have Ks': "sorted_wrt (\<lambda>(p, f, _) (p', f', _). f \<le> p') (kq K' v)" for v
  proof (cases "oi \<noteq> n \<and> v \<in> D - S")
    case True
    obtain q where q: "Mapping.lookup P v = Some q"
      using True unfolding D_def W_def by (auto dest: Mapping.in_keysD)
    show ?thesis using True Ks[of v] Pv[OF q] by (auto simp: kK' sorted_wrt_append q)
  qed (auto simp: kK' Ks)
  have "erel_list I nt oi (Suc n) ps' P' K' L'"
    unfolding erel_list_def
    using entries Pv' Pl' Kv' Ks' len len1 on by (simp add: L'_def ps'_def; blast)
  then show ?thesis
    by (simp add: upd erel_def append_queue_rep lp1 L'_def ps'_def)
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
proof -
  define S where "S = Set.filter (\<lambda>v. case hd_queue (kqq K v) of None \<Rightarrow> False
    | Some (p, f, tf) \<Rightarrow> f \<le> Suc i) X"
  define K1 where "K1 = upd_set K (\<lambda>v. dropWhile_queue (\<lambda>(p, f, tf). f \<le> Suc i) (kqq K v)) S"
  have pr: "eraux_prune i K X = mapping_delete_set K1 (Set.filter (\<lambda>v. hd_queue (kqq K1 v) = None) S)"
    by (simp add: eraux_prune_def Let_def S_def K1_def)
  have l1: "Mapping.lookup K1 v = (if v \<in> S
      then Some (dropWhile_queue (\<lambda>(p, f, tf). f \<le> Suc i) (kqq K v)) else Mapping.lookup K v)"
    by (simp add: K1_def Mapping_lookup_upd_set)
  have mS: "v \<in> S \<longleftrightarrow> v \<in> X \<and> (case kq K v of [] \<Rightarrow> False | (p, f, tf) # _ \<Rightarrow> f \<le> Suc i)"
    by (auto simp: S_def kq_def hd_queue_rep split: list.splits)
  show ?thesis
  proof (cases "v \<in> S")
    case True
    define q' where "q' = dropWhile_queue (\<lambda>(p, f, tf). f \<le> Suc i) (kqq K v)"
    have k1: "kqq K1 v = q'" by (simp add: kqq_def l1 True q'_def del: dropWhile_queue.simps)
    have lq: "linearize q' = dropWhile (\<lambda>(p, f, tf). f \<le> Suc i) (kq K v)"
      by (simp add: q'_def dropWhile_queue_rep kq_def del: dropWhile_queue.simps)
    have "kq (eraux_prune i K X) v = linearize q'"
    proof (cases "hd_queue q' = None")
      case True
      then have "linearize q' = []" by (simp add: hd_queue_rep split: list.splits)
      then show ?thesis using True \<open>v \<in> S\<close>
        by (simp add: pr delete_set_lookup kq_def kqq_def k1[unfolded kqq_def] empty_queue_rep)
    next
      case False
      have "Mapping.lookup K1 v = Some q'" using \<open>v \<in> S\<close> by (simp add: l1 q'_def del: dropWhile_queue.simps)
      then show ?thesis using False k1
        by (auto simp: pr delete_set_lookup kq_def kqq_def simp del: dropWhile_queue.simps)
    qed
    then show ?thesis using lq True mS by simp
  next
    case False
    have "kq (eraux_prune i K X) v = kq K v"
      using False by (simp add: pr delete_set_lookup kq_def kqq_def l1)
    moreover have "dropWhile (\<lambda>(p, f, tf). f \<le> Suc i) (kq K v) = kq K v" if "v \<in> X"
      using False mS that by (auto split: list.splits)
    ultimately show ?thesis by simp
  qed
qed

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
    and Kv0: "\<forall>v. \<forall>(p, f, tf) \<in> set (kq K v). oi < f \<and> f < n \<and> p < f \<and>
      v \<in> snd (((t, X) # ps) ! (f - Suc oi))"
    and Ks0: "\<forall>v. sorted_wrt (\<lambda>(p, f, _) (p', f', _). f \<le> p') (kq K v)"
    using R unfolding erel_list_def by - (elim conjE; assumption)+
  have len: "length ps = length L" using len0 by simp
  have Kv: "oi < f \<and> f < n \<and> p < f \<and> v \<in> snd (((t, X) # ps) ! (f - Suc oi))"
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
    show "\<forall>(p, f, tf) \<in> set (kq K' v). Suc oi < f \<and> f < n \<and> p < f \<and> v \<in> snd (ps ! (f - Suc (Suc oi)))"
    proof (intro ballI, clarify)
      fix p f tf assume x: "(p, f, tf) \<in> set (kq K' v)"
      have a: "Suc oi < f" by (rule after[OF x])
      have "f - Suc oi = Suc (f - Suc (Suc oi))" using a by simp
      then show "Suc oi < f \<and> f < n \<and> p < f \<and> v \<in> snd (ps ! (f - Suc (Suc oi)))"
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

(*<*)
theory Deque
  imports Main
begin
(*>*)

section \<open>Deques with constant-time access at both ends\<close>

text \<open>
  A deque is a front list and a reversed back list together with their lengths. It replaces
  the time-point-indexed mappings of the Until structure in the monitor's refinement (theory
  @{text Optimized_Until_Deque}), whose operation @{text add_new} the remarks below refer to.
\<close>

datatype 'a dq = Dq (dq_f: "'a list") (dq_b: "'a list") (dq_nf: nat) (dq_nb: nat)

definition dq_list :: "'a dq \<Rightarrow> 'a list" where
  "dq_list d = dq_f d @ rev (dq_b d)"

definition dq_inv :: "'a dq \<Rightarrow> bool" where
  "dq_inv d \<longleftrightarrow> dq_nf d = length (dq_f d) \<and> dq_nb d = length (dq_b d)"

definition dq_empty :: "'a dq" where
  "dq_empty = Dq [] [] 0 0"

definition dq_len :: "'a dq \<Rightarrow> nat" where
  "dq_len d = dq_nf d + dq_nb d"

text \<open>
  The front list is empty only for the empty deque: @{text dq_push} builds the front when it
  is empty, and @{text dq_tl} normalises after removing the head. Otherwise an access to the
  oldest entry (the common case in @{text add_new}) would walk the whole back list.
\<close>

definition dq_push :: "'a \<Rightarrow> 'a dq \<Rightarrow> 'a dq" where
  "dq_push x d = (if dq_f d = [] then Dq (rev (x # dq_b d)) [] (dq_nb d + 1) 0
     else Dq (dq_f d) (x # dq_b d) (dq_nf d) (dq_nb d + 1))"

text \<open>
  When the front list is exhausted, only the older half of the back list is moved to the
  front, so that the newest entries stay at the head of the back list: the entries accessed
  by @{text add_new} are the newest ones, and a walk of the whole window is avoided.
\<close>

definition dq_norm :: "'a dq \<Rightarrow> 'a dq" where
  "dq_norm d = (if dq_f d = [] then (let h = dq_nb d div 2 in
     Dq (rev (drop h (dq_b d))) (take h (dq_b d)) (dq_nb d - h) h) else d)"

definition dq_tl :: "'a dq \<Rightarrow> 'a dq" where
  "dq_tl d = (let d' = dq_norm d in dq_norm (Dq (tl (dq_f d')) (dq_b d') (dq_nf d' - 1) (dq_nb d')))"

definition dq_nth :: "'a dq \<Rightarrow> nat \<Rightarrow> 'a" where
  "dq_nth d k = (if k < dq_nf d then dq_f d ! k else dq_b d ! (dq_nb d - 1 - (k - dq_nf d)))"

definition dq_upd :: "'a dq \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a dq" where
  "dq_upd d k x = (if k < dq_nf d then Dq ((dq_f d)[k := x]) (dq_b d) (dq_nf d) (dq_nb d)
     else Dq (dq_f d) ((dq_b d)[dq_nb d - 1 - (k - dq_nf d) := x]) (dq_nf d) (dq_nb d))"

lemma dq_inv_empty[simp]: "dq_inv dq_empty"
  by (simp add: dq_inv_def dq_empty_def)

lemma dq_list_empty[simp]: "dq_list dq_empty = []"
  by (simp add: dq_list_def dq_empty_def)

lemma dq_inv_push[simp]: "dq_inv d \<Longrightarrow> dq_inv (dq_push x d)"
  by (auto simp add: dq_inv_def dq_push_def)

lemma dq_list_push[simp]: "dq_list (dq_push x d) = dq_list d @ [x]"
  by (auto simp add: dq_list_def dq_push_def)

lemma dq_inv_norm[simp]:
  assumes inv: "dq_inv d"
  shows "dq_inv (dq_norm d)"
proof (cases "dq_f d = []")
  case True
  have nb: "dq_nb d = length (dq_b d)" using inv unfolding dq_inv_def by simp
  have "min (length (dq_b d) div 2) (length (dq_b d)) = length (dq_b d) div 2"
    by (rule min_absorb1) (rule div_le_dividend)
  then show ?thesis using True unfolding dq_norm_def dq_inv_def Let_def nb by simp
next
  case False
  then show ?thesis using inv by (simp add: dq_norm_def)
qed

lemma dq_list_norm[simp]: "dq_list (dq_norm d) = dq_list d"
proof (cases "dq_f d = []")
  case True
  have "rev (drop h (dq_b d)) @ rev (take h (dq_b d)) = rev (dq_b d)" for h
    by (metis append_take_drop_id rev_append)
  then show ?thesis using True by (simp add: dq_list_def dq_norm_def Let_def)
qed (simp add: dq_list_def dq_norm_def)

lemma dq_f_norm:
  assumes "dq_inv d" "dq_list d \<noteq> []"
  shows "dq_f (dq_norm d) \<noteq> []"
proof (cases "dq_f d = []")
  case True
  then have "dq_b d \<noteq> []" using assms(2) by (simp add: dq_list_def)
  then have "0 < length (dq_b d)" by simp
  then have "length (dq_b d) div 2 < length (dq_b d)" by presburger
  then show ?thesis using True assms(1) by (simp add: dq_norm_def dq_inv_def Let_def)
qed (simp add: dq_norm_def)

lemma dq_inv_tl[simp]:
  assumes inv: "dq_inv d"
  shows "dq_inv (dq_tl d)"
proof -
  have "dq_inv (Dq (tl (dq_f (dq_norm d))) (dq_b (dq_norm d)) (dq_nf (dq_norm d) - 1) (dq_nb (dq_norm d)))"
    using dq_inv_norm[OF inv] unfolding dq_inv_def by simp
  then show ?thesis unfolding dq_tl_def Let_def by (rule dq_inv_norm)
qed

lemma dq_list_tl[simp]:
  assumes inv: "dq_inv d"
  shows "dq_list (dq_tl d) = tl (dq_list d)"
proof -
  have *: "dq_list (dq_tl d) = tl (dq_f (dq_norm d)) @ rev (dq_b (dq_norm d))"
    unfolding dq_tl_def Let_def dq_list_norm by (simp add: dq_list_def)
  show ?thesis
  proof (cases "dq_list d = []")
    case True
    then have "dq_f (dq_norm d) = []" "dq_b (dq_norm d) = []" using dq_list_norm[of d] by (auto simp: dq_list_def)
    then show ?thesis using True * by simp
  next
    case False
    have "dq_list (dq_tl d) = tl (dq_f (dq_norm d) @ rev (dq_b (dq_norm d)))"
      using dq_f_norm[OF inv False] * by simp
    then show ?thesis using dq_list_norm[of d] by (simp add: dq_list_def)
  qed
qed

lemma dq_inv_upd[simp]: "dq_inv d \<Longrightarrow> dq_inv (dq_upd d k x)"
  by (auto simp add: dq_inv_def dq_upd_def)

definition dq_of_list :: "'a list \<Rightarrow> 'a dq" where
  "dq_of_list xs = Dq xs [] (length xs) 0"

lemma dq_inv_of_list[simp]: "dq_inv (dq_of_list xs)"
  by (simp add: dq_inv_def dq_of_list_def)

lemma dq_list_of_list[simp]: "dq_list (dq_of_list xs) = xs"
  by (simp add: dq_list_def dq_of_list_def)

lemma dq_len_list: "dq_inv d \<Longrightarrow> dq_len d = length (dq_list d)"
  by (simp add: dq_inv_def dq_len_def dq_list_def)

lemma dq_nth: "dq_inv d \<Longrightarrow> k < dq_len d \<Longrightarrow> dq_nth d k = dq_list d ! k"
  by (auto simp add: dq_inv_def dq_nth_def dq_len_def dq_list_def nth_append rev_nth)

lemma dq_list_upd: "dq_inv d \<Longrightarrow> k < dq_len d \<Longrightarrow> dq_list (dq_upd d k x) = (dq_list d)[k := x]"
  by (auto simp add: dq_inv_def dq_upd_def dq_len_def dq_list_def list_update_append rev_update)

lemma dq_len_tl: "dq_inv d \<Longrightarrow> dq_len (dq_tl d) = dq_len d - 1"
  by (simp add: dq_len_list)

lemma dq_len_upd: "dq_inv d \<Longrightarrow> k < dq_len d \<Longrightarrow> dq_len (dq_upd d k x) = dq_len d"
  by (simp add: dq_len_list dq_list_upd)

lemma dq_len_push: "dq_inv d \<Longrightarrow> dq_len (dq_push x d) = dq_len d + 1"
  by (simp add: dq_len_list)

lemma dq_nth_tl_upd:
  assumes "dq_inv d" "i < dq_len d" "Suc k < dq_len d"
  shows "dq_nth (dq_tl (dq_upd d i X)) k = (dq_list d)[i := X] ! Suc k"
proof -
  have inv1: "dq_inv (dq_upd d i X)" using assms by simp
  have len1: "dq_len (dq_upd d i X) = dq_len d" using assms by (simp add: dq_len_upd)
  have inv2: "dq_inv (dq_tl (dq_upd d i X))" using inv1 by simp
  have len2: "dq_len (dq_tl (dq_upd d i X)) = dq_len d - 1" using inv1 len1 by (simp add: dq_len_tl)
  have "dq_nth (dq_tl (dq_upd d i X)) k = dq_list (dq_tl (dq_upd d i X)) ! k"
    using inv2 len2 assms(3) by (intro dq_nth) auto
  also have "\<dots> = tl (dq_list (dq_upd d i X)) ! k" using inv1 by simp
  also have "\<dots> = tl ((dq_list d)[i := X]) ! k" using assms by (simp add: dq_list_upd)
  also have "\<dots> = (dq_list d)[i := X] ! Suc k" using assms by (intro nth_tl) (simp add: dq_len_list)
  finally show ?thesis .
qed

text \<open>
  The same entry, reached the other way round: dropping the head first and then reading and
  writing at index 0. @{const dq_norm} guarantees that the front list of a non-empty deque is
  non-empty, so index 0 is the head of the front list and both the read and the write are
  constant time, whereas index 1 of the deque before the head is dropped falls into the back
  list whenever the front list holds exactly one element, and is then reached by walking the
  back list to its far end.
\<close>

lemma tl_list_update_1: "tl (xs[Suc 0 := X]) = (tl xs)[0 := X]"
  by (cases xs) auto

lemma dq_nth_upd_tl:
  assumes "dq_inv d" "Suc 0 < dq_len d" "Suc k < dq_len d"
  shows "dq_nth (dq_upd (dq_tl d) 0 X) k = (dq_list d)[Suc 0 := X] ! Suc k"
proof -
  have inv1: "dq_inv (dq_tl d)" using assms(1) by simp
  have len1: "dq_len (dq_tl d) = dq_len d - 1" using assms(1) by (simp add: dq_len_tl)
  have k1: "k < dq_len (dq_tl d)" using assms(3) len1 by simp
  have z1: "0 < dq_len (dq_tl d)" using assms(2) len1 by simp
  have inv2: "dq_inv (dq_upd (dq_tl d) 0 X)" using inv1 by simp
  have len2: "dq_len (dq_upd (dq_tl d) 0 X) = dq_len (dq_tl d)"
    using inv1 z1 by (simp add: dq_len_upd)
  have "dq_nth (dq_upd (dq_tl d) 0 X) k = dq_list (dq_upd (dq_tl d) 0 X) ! k"
    using inv2 len2 k1 by (intro dq_nth) auto
  also have "\<dots> = (dq_list (dq_tl d))[0 := X] ! k" using inv1 z1 by (simp add: dq_list_upd)
  also have "\<dots> = (tl (dq_list d))[0 := X] ! k" using assms(1) by simp
  also have "\<dots> = tl ((dq_list d)[Suc 0 := X]) ! k" by (simp add: tl_list_update_1)
  also have "\<dots> = (dq_list d)[Suc 0 := X] ! Suc k"
    using assms by (intro nth_tl) (simp add: dq_len_list)
  finally show ?thesis .
qed

lemma dq_nth_tl_0:
  assumes "dq_inv d" "Suc 0 < dq_len d"
  shows "dq_nth (dq_tl d) 0 = dq_nth d 1"
proof -
  have inv1: "dq_inv (dq_tl d)" using assms(1) by simp
  have len1: "dq_len (dq_tl d) = dq_len d - 1" using assms(1) by (simp add: dq_len_tl)
  have "dq_nth (dq_tl d) 0 = dq_list (dq_tl d) ! 0"
    using inv1 len1 assms(2) by (intro dq_nth) auto
  also have "\<dots> = tl (dq_list d) ! 0" using assms(1) by simp
  also have "\<dots> = dq_list d ! Suc 0"
    using assms by (intro nth_tl) (simp add: dq_len_list)
  also have "\<dots> = dq_nth d 1" using assms by (simp add: dq_nth)
  finally show ?thesis .
qed

(*<*)
end
(*>*)

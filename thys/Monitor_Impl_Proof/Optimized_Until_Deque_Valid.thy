(*<*)
theory Optimized_Until_Deque_Valid
  imports "Monitor_Impl.Optimized_Until_Deque" Optimized_Agg_Temporal_Valid
begin
(*>*)

section \<open>Correctness of the deque-based Until structure\<close>

subsection \<open>Deques related to mappings\<close>

lemma rel_a2_lookup: "rel_a2 tp len d m \<Longrightarrow> k \<le> len \<Longrightarrow> Mapping.lookup m (tp - len + k) = Some (dq_nth d k)"
  by (simp add: rel_a2_def)

lemma rel_a2_lookup0: "rel_a2 tp len d m \<Longrightarrow> Mapping.lookup m (tp - len) = Some (dq_nth d 0)"
  using rel_a2_lookup[of tp len d m 0] by simp

lemma rel_a2_lookup1: "rel_a2 tp len d m \<Longrightarrow> 1 \<le> len \<Longrightarrow> Mapping.lookup m (tp - len + 1) = Some (dq_nth d 1)"
  using rel_a2_lookup[of tp len d m 1] by simp

lemma rel_a2_step:
  assumes "rel_a2 tp len d m" "1 \<le> len" "len \<le> tp"
  shows "rel_a2 tp (len - 1) (dq_tl (dq_upd d 1 X)) (Mapping.delete (tp - len) (Mapping.update (tp - len + 1) X m))"
proof -
  have inv: "dq_inv d" and dlen: "dq_len d = len + 1" and keys: "Mapping.keys m = {tp - len..tp}"
    and look: "\<And>k. k \<le> len \<Longrightarrow> Mapping.lookup m (tp - len + k) = Some (dq_nth d k)"
    using assms(1) by (auto simp: rel_a2_def)
  have len_list: "length (dq_list d) = len + 1"
    using inv dlen by (simp add: dq_len_list)
  have inv': "dq_inv (dq_tl (dq_upd d 1 X))" using inv by simp
  have len': "dq_len (dq_tl (dq_upd d 1 X)) = len" using inv dlen assms(2) by (simp add: dq_len_tl dq_len_upd)
  have nth': "dq_nth (dq_tl (dq_upd d 1 X)) k = (dq_list d)[1 := X] ! Suc k" if "k < len" for k
    using that inv dlen assms(2) by (intro dq_nth_tl_upd) auto
  show ?thesis
    unfolding rel_a2_def
  proof (intro conjI allI impI)
    show "dq_inv (dq_tl (dq_upd d 1 X))" by (rule inv')
    show "dq_len (dq_tl (dq_upd d 1 X)) = len - 1 + 1" using len' assms(2) by simp
    show "Mapping.keys (Mapping.delete (tp - len) (Mapping.update (tp - len + 1) X m)) = {tp - (len - 1)..tp}"
      using assms(2,3) by (auto simp: keys)
    fix k assume k: "k \<le> len - 1"
    then have klen: "k < len" using assms(2) by simp
    show "Mapping.lookup (Mapping.delete (tp - len) (Mapping.update (tp - len + 1) X m)) (tp - (len - 1) + k) =
      Some (dq_nth (dq_tl (dq_upd d 1 X)) k)"
    proof (cases k)
      case 0
      have e: "tp - (len - 1) + k = tp - len + 1" using 0 assms(2,3) by simp
      have nthX: "dq_nth (dq_tl (dq_upd d 1 X)) k = X"
        unfolding nth'[OF klen] using 0 len_list assms(2) by simp
      show ?thesis
        unfolding e nthX by simp
    next
      case (Suc k')
      have e: "tp - (len - 1) + k = tp - len + (k' + 2)" using Suc assms(2,3) by simp
      have nth2: "dq_nth (dq_tl (dq_upd d 1 X)) k = dq_nth d (k' + 2)"
        unfolding nth'[OF klen] using inv dlen Suc klen by (simp add: dq_nth)
      show ?thesis
        unfolding e nth2 using look[of "k' + 2"] klen Suc
        by simp
    qed
  qed
qed

lemma rel_tstp_step:
  assumes "rel_tstp tp len d m" "1 \<le> len" "len \<le> tp"
  shows "rel_tstp tp (len - 1) (dq_tl d) (Mapping.delete (tp - len) m)"
proof -
  have inv: "dq_inv d" and dlen: "dq_len d = len" and keys: "Mapping.keys m = {tp - len..<tp}"
    and look: "\<And>k. k < len \<Longrightarrow> Mapping.lookup m (tp - len + k) = Some (dq_nth d k)"
    using assms(1) by (auto simp: rel_tstp_def)
  show ?thesis
    unfolding rel_tstp_def
  proof (intro conjI allI impI)
    show "dq_inv (dq_tl d)" using inv by simp
    show "dq_len (dq_tl d) = len - 1" using inv dlen by (simp add: dq_len_tl)
    show "Mapping.keys (Mapping.delete (tp - len) m) = {tp - (len - 1)..<tp}" using assms(2,3) by (auto simp: keys)
    fix k assume k: "k < len - 1"
    have "tp - (len - 1) + k = tp - len + (k + 1)" using assms(2,3) by simp
    then show "Mapping.lookup (Mapping.delete (tp - len) m) (tp - (len - 1) + k) = Some (dq_nth (dq_tl d) k)"
      using k assms(2,3) look[of "k + 1"] inv dlen
      by (auto simp: dq_nth dq_len_tl nth_tl dq_len_list)
  qed
qed

lemma rel_a2_push:
  assumes "rel_a2 tp len d m" "len \<le> tp"
  shows "rel_a2 (tp + 1) (len + 1) (dq_push X d) (Mapping.update (tp + 1) X m)"
proof -
  have inv: "dq_inv d" and dlen: "dq_len d = len + 1" and keys: "Mapping.keys m = {tp - len..tp}"
    and look: "\<And>k. k \<le> len \<Longrightarrow> Mapping.lookup m (tp - len + k) = Some (dq_nth d k)"
    using assms(1) by (auto simp: rel_a2_def)
  have len_list: "length (dq_list d) = len + 1" using inv dlen by (simp add: dq_len_list)
  show ?thesis
    unfolding rel_a2_def
  proof (intro conjI allI impI)
    show "dq_inv (dq_push X d)" using inv by simp
    show "dq_len (dq_push X d) = len + 1 + 1" using inv dlen by (simp add: dq_len_push)
    show "Mapping.keys (Mapping.update (tp + 1) X m) = {tp + 1 - (len + 1)..tp + 1}" using assms(2) by (auto simp: keys)
    fix k assume k: "k \<le> len + 1"
    show "Mapping.lookup (Mapping.update (tp + 1) X m) (tp + 1 - (len + 1) + k) = Some (dq_nth (dq_push X d) k)"
      using k look[of k] inv dlen assms(2)
      by (auto simp: Mapping.lookup_update' dq_nth dq_len_push nth_append len_list)
  qed
qed

lemma rel_tstp_push:
  assumes "rel_tstp tp len d m" "len \<le> tp"
  shows "rel_tstp (tp + 1) (len + 1) (dq_push x d) (Mapping.update tp x m)"
proof -
  have inv: "dq_inv d" and dlen: "dq_len d = len" and keys: "Mapping.keys m = {tp - len..<tp}"
    and look: "\<And>k. k < len \<Longrightarrow> Mapping.lookup m (tp - len + k) = Some (dq_nth d k)"
    using assms(1) by (auto simp: rel_tstp_def)
  have len_list: "length (dq_list d) = len" using inv dlen by (simp add: dq_len_list)
  show ?thesis
    unfolding rel_tstp_def
  proof (intro conjI allI impI)
    show "dq_inv (dq_push x d)" using inv by simp
    show "dq_len (dq_push x d) = len + 1" using inv dlen by (simp add: dq_len_push)
    show "Mapping.keys (Mapping.update tp x m) = {tp + 1 - (len + 1)..<tp + 1}" using assms(2) by (auto simp: keys)
    fix k assume k: "k < len + 1"
    show "Mapping.lookup (Mapping.update tp x m) (tp + 1 - (len + 1) + k) = Some (dq_nth (dq_push x d) k)"
      using k look[of k] inv dlen assms(2)
      by (auto simp: Mapping.lookup_update' dq_nth dq_len_push nth_append len_list)
  qed
qed

text \<open>@{const rel_a2} sees a deque only through @{const dq_inv}, @{const dq_len} and
  @{const dq_nth}, so updating the entry behind the head before or after dropping the head is
  the same.\<close>

lemma rel_a2_step_tl:
  assumes "rel_a2 tp len d m" "1 \<le> len" "len \<le> tp"
  shows "rel_a2 tp (len - 1) (dq_upd (dq_tl d) 0 X) (Mapping.delete (tp - len) (Mapping.update (tp - len + 1) X m))"
proof -
  have inv: "dq_inv d" and dlen: "dq_len d = len + 1" and keys: "Mapping.keys m = {tp - len..tp}"
    and look: "\<And>k. k \<le> len \<Longrightarrow> Mapping.lookup m (tp - len + k) = Some (dq_nth d k)"
    using assms(1) by (auto simp: rel_a2_def)
  have len_list: "length (dq_list d) = len + 1"
    using inv dlen by (simp add: dq_len_list)
  have invtl: "dq_inv (dq_tl d)" using inv by simp
  have lentl: "dq_len (dq_tl d) = len" using inv dlen by (simp add: dq_len_tl)
  have inv': "dq_inv (dq_upd (dq_tl d) 0 X)" using invtl by simp
  have len': "dq_len (dq_upd (dq_tl d) 0 X) = len"
    using invtl lentl assms(2) by (simp add: dq_len_upd)
  have nth': "dq_nth (dq_upd (dq_tl d) 0 X) k = (dq_list d)[Suc 0 := X] ! Suc k" if "k < len" for k
    using that inv dlen assms(2) by (intro dq_nth_upd_tl) auto
  show ?thesis
    unfolding rel_a2_def
  proof (intro conjI allI impI)
    show "dq_inv (dq_upd (dq_tl d) 0 X)" by (rule inv')
    show "dq_len (dq_upd (dq_tl d) 0 X) = len - 1 + 1" using len' assms(2) by simp
    show "Mapping.keys (Mapping.delete (tp - len) (Mapping.update (tp - len + 1) X m)) = {tp - (len - 1)..tp}"
      using assms(2,3) by (auto simp: keys)
    fix k assume k: "k \<le> len - 1"
    then have klen: "k < len" using assms(2) by simp
    show "Mapping.lookup (Mapping.delete (tp - len) (Mapping.update (tp - len + 1) X m)) (tp - (len - 1) + k) =
      Some (dq_nth (dq_upd (dq_tl d) 0 X) k)"
    proof (cases k)
      case 0
      have e: "tp - (len - 1) + k = tp - len + 1" using 0 assms(2,3) by simp
      have nthX: "dq_nth (dq_upd (dq_tl d) 0 X) k = X"
        unfolding nth'[OF klen] using 0 len_list assms(2) by simp
      show ?thesis
        unfolding e nthX by simp
    next
      case (Suc k')
      have e: "tp - (len - 1) + k = tp - len + (k' + 2)" using Suc assms(2,3) by simp
      have nth2: "dq_nth (dq_upd (dq_tl d) 0 X) k = dq_nth d (k' + 2)"
        unfolding nth'[OF klen] using inv dlen Suc klen by (simp add: dq_nth)
      show ?thesis
        unfolding e nth2 using look[of "k' + 2"] klen Suc by simp
    qed
  qed
qed

lemma rel_a2_step_tl':
  assumes "rel_a2 tp len d m" "1 \<le> len" "len \<le> tp"
  shows "rel_a2 tp (len - 1) (dq_upd (dq_tl d) 0 (if len = 1 then E else C))
    (Mapping.delete (tp - len) (if len = 1 then Mapping.update tp E m else Mapping.update (tp - len + 1) C m))"
proof (cases "len = 1")
  case True
  have eq: "tp - len + 1 = tp" using True assms(3) by simp
  show ?thesis using True rel_a2_step_tl[OF assms, of E, unfolded eq] by simp
next
  case False
  then show ?thesis using rel_a2_step_tl[OF assms, of C] by simp
qed

subsection \<open>Simulation of evaluation\<close>

lemma eval_step_sim:
  assumes rel: "rel_uaux d a" and valid: "valid_mmuaux' args cur dt a auxlist" and tss: "lin_ts_mmuaux a = ts # tss''"
  shows "rel_uaux (eval_step_dq args d) (eval_step_mmuaux args a)"
proof -
  obtain tp tss tables len result a1_map a2_map tstp_map "done" where a:
    "a = (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done)"
    by (cases a) auto
  obtain a2_dq tstp_dq where d: "d = (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done)"
    using rel unfolding a by (cases d) auto
  have ra2: "rel_a2 tp len a2_dq a2_map" and rt: "rel_tstp tp len tstp_dq tstp_map" and lentp: "len \<le> tp"
    using rel unfolding a d by auto
  have lin: "linearize tss = ts # tss''" using tss unfolding a by simp
  have len1: "1 \<le> len"
    using valid lin unfolding a valid_mmuaux'.simps by (metis One_nat_def Suc_le_eq length_greater_0_conv list.simps(3))
  obtain ts0 tss0 where hd: "safe_hd tss = (Some ts0, tss0)"
    using safe_hd_rep[of tss] lin by (cases "safe_hd tss") (auto split: option.splits)
  have m0: "Mapping.lookup a2_map (tp - len) = Some (dq_nth a2_dq 0)" by (rule rel_a2_lookup0[OF ra2])
  have inv: "dq_inv a2_dq" and dlen: "dq_len a2_dq = len + 1"
    using ra2 by (auto simp: rel_a2_def)
  have gt1: "Suc 0 < dq_len a2_dq" using dlen len1 by simp
  have m1: "Mapping.lookup a2_map (tp - len + 1) = Some (dq_nth (dq_tl a2_dq) 0)"
    using rel_a2_lookup1[OF ra2 len1] dq_nth_tl_0[OF inv gt1] by simp
  have ra2': "rel_a2 tp (len - 1) (dq_upd (dq_tl a2_dq) 0 (if len = 1 then Mapping.empty else C))
    (Mapping.delete (tp - len) (if len = 1 then Mapping.update tp Mapping.empty a2_map else Mapping.update (tp - len + 1) C a2_map))" for C
    by (rule rel_a2_step_tl'[OF ra2 len1 lentp])
  have rt': "rel_tstp tp (len - 1) (dq_tl tstp_dq) (Mapping.delete (tp - len) tstp_map)"
    by (rule rel_tstp_step[OF rt len1 lentp])
  show ?thesis
    unfolding a d eval_step_dq.simps eval_step_mmuaux.simps hd m0 m1 prod.case option.case Let_def
    using ra2' rt' lentp
    by (auto split: prod.splits)
qed

lemma foldl_eval_step_sim:
  assumes "rel_uaux d a" "valid_mmuaux' args cur dt a auxlist" "lin_ts_mmuaux a = xs @ ys"
    "\<And>t. t \<in> set xs \<Longrightarrow> \<not> memR (args_ivl args) (dt - t)"
  shows "rel_uaux (foldl (\<lambda>aux _. eval_step_dq args aux) d xs) (foldl (\<lambda>aux _. eval_step_mmuaux args aux) a xs)"
  using assms
proof (induction xs arbitrary: d a)
  case (Cons x xs)
  have step: "rel_uaux (eval_step_dq args d) (eval_step_mmuaux args a)"
    using eval_step_sim[OF Cons.prems(1,2)] Cons.prems(3) by simp
  have valid': "valid_mmuaux' args cur dt (eval_step_mmuaux args a) auxlist"
    "lin_ts_mmuaux (eval_step_mmuaux args a) = xs @ ys"
    using valid_eval_step_mmuaux'[OF Cons.prems(2), of x "xs @ ys"] Cons.prems(3,4) by auto
  show ?case
    using Cons.IH[OF step valid'] Cons.prems(4) by simp
qed simp

lemma shift_sim:
  assumes rel: "rel_uaux d a" and valid: "valid_mmuaux' args cur cur a auxlist" and nt: "nt \<ge> cur"
  shows "rel_uaux (shift_dq args nt d) (shift_mmuaux args nt a)"
proof -
  obtain tp tss tables len result a1_map a2_map tstp_map "done" where a:
    "a = (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done)"
    by (cases a) auto
  obtain a2_dq tstp_dq where d: "d = (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done)"
    using rel unfolding a by (cases d) auto
  define P where "P = (\<lambda>t. \<not> memR (args_ivl args) (nt - t))"
  define tss_queue where "tss_queue = fst (takeWhile_queue P tss)"
  define tss' where "tss' = snd (takeWhile_queue P tss)"
  have tq: "takeWhile_queue P tss = (tss_queue, tss')" by (simp add: tss_queue_def tss'_def)
  let ?a = "(tp, tss', tables, len, result, a1_map, a2_map, tstp_map, done)"
  let ?d = "(tp, tss', tables, len, result, a1_map, a2_dq, tstp_dq, done)"
  have lin': "linearize tss' = linearize tss" unfolding tss'_def by (rule takeWhile_queue_rep_snd)
  have valid_nt: "valid_mmuaux' args cur nt a auxlist" using valid_mmuaux'_mono[OF valid nt] .
  have valid': "valid_mmuaux' args cur nt ?a auxlist"
    using valid_nt unfolding a valid_mmuaux'.simps lin' .
  have rel': "rel_uaux ?d ?a" using rel unfolding a d by simp
  have lin_q: "linearize tss_queue = takeWhile P (linearize tss)" unfolding tss_queue_def by (rule takeWhile_queue_rep_fst)
  have split: "lin_ts_mmuaux ?a = linearize tss_queue @ dropWhile P (linearize tss)"
    by (simp add: lin' lin_q)
  have mem: "\<And>t. t \<in> set (linearize tss_queue) \<Longrightarrow> \<not> memR (args_ivl args) (nt - t)"
    unfolding lin_q P_def by (auto dest: set_takeWhileD)
  show ?thesis
    unfolding a d shift_dq.simps shift_mmuaux.simps P_def[symmetric] tq prod.case Let_def
    by (rule foldl_eval_step_sim[OF rel' valid' split mem])
qed

lemma eval_sim:
  assumes rel: "rel_uaux d a" and valid: "valid_mmuaux args cur a auxlist" and nt: "nt \<ge> cur"
  shows "fst (eval_dq args nt d) = fst (eval_mmuaux' args nt a)"
    "rel_uaux (snd (eval_dq args nt d)) (snd (eval_mmuaux' args nt a))"
proof -
  have rel': "rel_uaux (shift_dq args nt d) (shift_mmuaux args nt a)"
    using shift_sim[OF rel _ nt] valid unfolding valid_mmuaux_def by blast
  obtain tp tss tables len result a1_map a2_map tstp_map "done" where a:
    "shift_mmuaux args nt a = (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done)"
    by (cases "shift_mmuaux args nt a") auto
  obtain a2_dq tstp_dq where d: "shift_dq args nt d = (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done)"
    using rel' unfolding a by (cases "shift_dq args nt d") auto
  show "fst (eval_dq args nt d) = fst (eval_mmuaux' args nt a)"
    "rel_uaux (snd (eval_dq args nt d)) (snd (eval_mmuaux' args nt a))"
    using rel' unfolding eval_dq.simps eval_mmuaux'.simps a d by auto
qed

lemma init_sim: "rel_uaux (init_dq args) (init_mmuaux args)"
  unfolding init_dq_def init_mmuaux_def rel_uaux.simps rel_a2_def rel_tstp_def
  by (auto simp: dq_nth dq_len_list Mapping.lookup_update' dq_len_push)

lemma length_sim: "rel_uaux d a \<Longrightarrow> length_dq args d = length_mmuaux args a"
  by (cases d; cases a) auto

subsection \<open>Nested update on the deque\<close>

lemma upd_nested_dq_Nil[simp]: "upd_nested_dq base d f [] dq = dq"
  by (simp add: upd_nested_dq_def)

lemma upd_nested_dq_Cons: "upd_nested_dq base d f (x # xs) dq = upd_nested_step_dq base d f x (upd_nested_dq base d f xs dq)"
  by (simp add: upd_nested_dq_def)

lemma dq_inv_nested_step[simp]: "dq_inv dq \<Longrightarrow> dq_inv (upd_nested_step_dq base d f x dq)"
  by (auto simp: upd_nested_step_dq_def split: prod.splits)

lemma dq_inv_upd_nested_dq[simp]: "dq_inv dq \<Longrightarrow> dq_inv (upd_nested_dq base d f xs dq)"
  by (induction xs) (auto simp: upd_nested_dq_Cons)

lemma dq_len_nested_step: "dq_inv dq \<Longrightarrow> dq_len (upd_nested_step_dq base d f x dq) = dq_len dq"
  by (auto simp: upd_nested_step_dq_def dq_len_upd split: prod.splits)

lemma dq_nth_nested_step:
  assumes "dq_inv dq" "i < dq_len dq"
  shows "dq_nth (upd_nested_step_dq base d f (k, k') dq) i =
    (if k = base + i then (case Mapping.lookup (dq_nth dq i) k' of Some v \<Rightarrow> Mapping.update k' (f v) (dq_nth dq i)
       | None \<Rightarrow> Mapping.update k' d (dq_nth dq i)) else dq_nth dq i)"
proof -
  have len: "length (dq_list dq) = dq_len dq" using assms(1) by (simp add: dq_len_list)
  show ?thesis
    using assms unfolding upd_nested_step_dq_def prod.case Let_def
    by (auto simp: dq_nth dq_len_upd dq_list_upd nth_list_update len)
qed

lemma dq_len_upd_nested_dq: "dq_inv dq \<Longrightarrow> dq_len (upd_nested_dq base d f xs dq) = dq_len dq"
  by (induction xs) (auto simp: upd_nested_dq_Cons dq_len_nested_step)

lemma dq_nth_upd_nested_dq:
  assumes idem: "d = f d" "\<And>x. f (f x) = f x" and inv: "dq_inv dq" and i: "i < dq_len dq"
  shows "dq_nth (upd_nested_dq base d f xs dq) i = upd_set' (dq_nth dq i) d f {b. (base + i, b) \<in> set xs}"
proof (induction xs)
  case (Cons x xs)
  obtain k k' where x: "x = (k, k')" by (cases x)
  have inv': "dq_inv (upd_nested_dq base d f xs dq)" using inv by simp
  have i': "i < dq_len (upd_nested_dq base d f xs dq)" using i inv by (simp add: dq_len_upd_nested_dq)
  note ins = upd_set'_insert_dq[where d = d and f = f, OF idem]
  show ?case
  proof (cases "k = base + i")
    case True
    have seteq: "{b. (base + i, b) \<in> Set.insert (k, k') (set xs)} = Set.insert k' {b. (base + i, b) \<in> set xs}" using True by auto
    show ?thesis
      unfolding upd_nested_dq_Cons x dq_nth_nested_step[OF inv' i'] Cons.IH list.set(2) seteq ins Let_def
      using True by simp
  next
    case False
    have seteq: "{b. (base + i, b) \<in> Set.insert (k, k') (set xs)} = {b. (base + i, b) \<in> set xs}" using False by auto
    show ?thesis
      unfolding upd_nested_dq_Cons x dq_nth_nested_step[OF inv' i'] Cons.IH list.set(2) seteq
      using False by simp
  qed
qed simp

lemma rel_a2_upd_nested:
  assumes "rel_a2 tp len dq m" and idem: "d = f d" "\<And>x. f (f x) = f x" and rng: "fst ` set xs \<subseteq> {tp - len..tp}"
  shows "rel_a2 tp len (upd_nested_dq (tp - len) d f xs dq) (upd_nested m d f (set xs))"
proof -
  have inv: "dq_inv dq" and dlen: "dq_len dq = len + 1" and keys: "Mapping.keys m = {tp - len..tp}"
    and look: "\<And>k. k \<le> len \<Longrightarrow> Mapping.lookup m (tp - len + k) = Some (dq_nth dq k)"
    using assms(1) by (auto simp: rel_a2_def)
  note nth = dq_nth_upd_nested_dq[where d = d and f = f, OF idem inv]
  show ?thesis
    unfolding rel_a2_def
  proof (intro conjI allI impI)
    show "dq_inv (upd_nested_dq (tp - len) d f xs dq)" using inv by simp
    show "dq_len (upd_nested_dq (tp - len) d f xs dq) = len + 1" using inv dlen by (simp add: dq_len_upd_nested_dq)
    show "Mapping.keys (upd_nested m d f (set xs)) = {tp - len..tp}" using rng by (auto simp: upd_nested_keys keys)
    fix k assume k: "k \<le> len"
    show "Mapping.lookup (upd_nested m d f (set xs)) (tp - len + k) = Some (dq_nth (upd_nested_dq (tp - len) d f xs dq) k)"
      using look[OF k] k dlen by (simp add: upd_nested_lookup nth)
  qed
qed

subsection \<open>Conversions for infinite operand tables\<close>

lemma rel_a2_det:
  assumes "rel_a2 tp len dq m"
  shows "a2_of_dq tp len dq = m"
proof (rule mapping_eqI)
  fix t
  have keys: "Mapping.keys m = {tp - len..tp}" and look: "\<And>k. k \<le> len \<Longrightarrow> Mapping.lookup m (tp - len + k) = Some (dq_nth dq k)"
    using assms by (auto simp: rel_a2_def)
  show "Mapping.lookup (a2_of_dq tp len dq) t = Mapping.lookup m t"
  proof (cases "tp - len \<le> t \<and> t \<le> tp")
    case True
    have k: "t - (tp - len) \<le> len" using True by arith
    have eq: "tp - len + (t - (tp - len)) = t" using True by simp
    show ?thesis using look[OF k] True unfolding a2_of_dq_def lookup_tabulate_upt eq by simp
  next
    case False
    have "t \<notin> Mapping.keys m" using False keys by auto
    then have "Mapping.lookup m t = None" using Mapping_keys_intro[of m t] by blast
    then show ?thesis using False unfolding a2_of_dq_def lookup_tabulate_upt by (simp add: less_Suc_eq_le)
  qed
qed

lemma rel_tstp_det:
  assumes "rel_tstp tp len dq m"
  shows "tstp_of_dq tp len dq = m"
proof (rule mapping_eqI)
  fix t
  have keys: "Mapping.keys m = {tp - len..<tp}" and look: "\<And>k. k < len \<Longrightarrow> Mapping.lookup m (tp - len + k) = Some (dq_nth dq k)"
    using assms by (auto simp: rel_tstp_def)
  show "Mapping.lookup (tstp_of_dq tp len dq) t = Mapping.lookup m t"
  proof (cases "tp - len \<le> t \<and> t < tp")
    case True
    have k: "t - (tp - len) < len" using True by arith
    have eq: "tp - len + (t - (tp - len)) = t" using True by simp
    show ?thesis using look[OF k] True unfolding tstp_of_dq_def lookup_tabulate_upt eq by simp
  next
    case False
    have "t \<notin> Mapping.keys m" using False keys by auto
    then have "Mapping.lookup m t = None" using Mapping_keys_intro[of m t] by blast
    then show ?thesis using False unfolding tstp_of_dq_def lookup_tabulate_upt by simp
  qed
qed

lemma rel_uaux_det: "rel_uaux d a \<Longrightarrow> uaux_of_dq d = a"
  by (cases d; cases a) (auto simp: rel_a2_det rel_tstp_det)

lemma rel_a2_of:
  assumes keys: "Mapping.keys m = {tp - len..tp}" and lentp: "len \<le> tp"
  shows "rel_a2 tp len (dq_of_a2 tp len m) m"
  unfolding rel_a2_def
proof (intro conjI allI impI)
  fix k assume k: "k \<le> len"
  have "tp - len + k \<in> Mapping.keys m" using k lentp keys by auto
  then obtain v where v: "Mapping.lookup m (tp - len + k) = Some v" by (auto dest: Mapping.in_keysD)
  have nth: "map (\<lambda>k. the (Mapping.lookup m (tp - len + k))) [0..<len + 1] ! k = the (Mapping.lookup m (tp - len + k))"
    using k by (subst nth_map_upt) auto
  have inv: "dq_inv (dq_of_a2 tp len m)" by (simp add: dq_of_a2_def)
  have klen: "k < dq_len (dq_of_a2 tp len m)" using k by (simp add: dq_of_a2_def dq_len_list)
  show "Mapping.lookup m (tp - len + k) = Some (dq_nth (dq_of_a2 tp len m) k)"
    unfolding dq_nth[OF inv klen] unfolding dq_of_a2_def dq_list_of_list nth by (simp add: v)
qed (auto simp: dq_of_a2_def dq_len_list keys)

lemma rel_tstp_of:
  assumes keys: "Mapping.keys m = {tp - len..<tp}" and lentp: "len \<le> tp"
  shows "rel_tstp tp len (dq_of_tstp tp len m) m"
  unfolding rel_tstp_def
proof (intro conjI allI impI)
  fix k assume k: "k < len"
  have "tp - len + k \<in> Mapping.keys m" using k lentp keys by auto
  then obtain v where v: "Mapping.lookup m (tp - len + k) = Some v" by (auto dest: Mapping.in_keysD)
  have nth: "map (\<lambda>k. the (Mapping.lookup m (tp - len + k))) [0..<len] ! k = the (Mapping.lookup m (tp - len + k))"
    using k by (subst nth_map_upt) auto
  show "Mapping.lookup m (tp - len + k) = Some (dq_nth (dq_of_tstp tp len m) k)"
    using k v unfolding dq_of_tstp_def by (subst dq_nth) (auto simp: dq_len_list nth)
qed (auto simp: dq_of_tstp_def dq_len_list keys)

lemma valid_mmuaux'_facts:
  assumes "valid_mmuaux' args cur dt (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done) auxlist"
  shows "len \<le> tp" "Mapping.keys a2_map = {tp - len..tp}" "Mapping.keys tstp_map = {tp - len..<tp}"
    "\<And>as tp'. Mapping.lookup a1_map as = Some tp' \<Longrightarrow> tp' < tp"
proof -
  show lentp: "len \<le> tp" using assms unfolding valid_mmuaux'.simps by (elim conjE)
  show "Mapping.keys a2_map = {tp - len..tp}" using assms unfolding valid_mmuaux'.simps by (elim conjE)
  have "Mapping.keys tstp_map = (if len > 0 then {tp - len..tp - 1} else {})"
    using assms unfolding valid_mmuaux'.simps by (elim conjE)
  then show "Mapping.keys tstp_map = {tp - len..<tp}" using lentp by auto
  have a1: "\<forall>xs \<in> Mapping.keys a1_map. case Mapping.lookup a1_map xs of Some tp' \<Rightarrow> tp' < tp"
    using assms unfolding valid_mmuaux'.simps by (elim conjE)
  fix as tp' assume l: "Mapping.lookup a1_map as = Some tp'"
  have "as \<in> Mapping.keys a1_map" using l by (intro Mapping_keys_intro) simp
  then show "tp' < tp" using a1 l by auto
qed

lemma rel_uaux_of:
  assumes "valid_mmuaux' args cur dt a auxlist"
  shows "rel_uaux (dq_of_uaux a) a"
proof -
  obtain tp tss tables len result a1_map a2_map tstp_map "done" where a:
    "a = (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done)"
    by (cases a) auto
  note facts = valid_mmuaux'_facts[OF assms[unfolded a]]
  show ?thesis
    unfolding a dq_of_uaux.simps rel_uaux.simps
    using rel_a2_of[OF facts(2,1)] rel_tstp_of[OF facts(3,1)] facts(1) by simp
qed

subsection \<open>Adding a new time point\<close>

lemma set_until_pairs_list: "set (until_pairs_list a1_map L R pos tp len inz as) =
  until_cand a1_map L R pos tp len as \<union> (if inz then {(tp, as)} else {})"
  by (auto simp: until_pairs_list_def until_cand_def split: option.splits)

lemma until_elem_step_dq_foldr: "until_elem_step_dq a1_map L R pos tp len inz P d as acc =
  foldr (until_step_dq P d (tp - len)) (until_pairs_list a1_map L R pos tp len inz as) acc"
  by (auto simp: until_elem_step_dq_def until_pairs_list_def split: option.splits)

lemma foldr_until_step_dq:
  "foldr (until_step_dq P d t0) ps (tbl, a2, res) =
    (tbl \<union> snd ` set (filter (\<lambda>p. P (fst p)) ps),
     upd_nested_dq t0 d (max_tstp d) (filter (\<lambda>p. P (fst p)) ps) a2,
     res \<union> snd ` set (filter (\<lambda>p. P (fst p) \<and> fst p = t0) ps))"
  by (induction ps) (auto simp: until_step_dq_def upd_nested_dq_Cons)

lemma fold_until_elem_step_dq:
  "fold (until_elem_step_dq a1_map L R pos tp len inz P d) xs acc =
    foldr (until_step_dq P d (tp - len)) (concat (map (until_pairs_list a1_map L R pos tp len inz) (rev xs))) acc"
proof -
  have "foldr (until_elem_step_dq a1_map L R pos tp len inz P d) ys acc =
    foldr (until_step_dq P d (tp - len)) (concat (map (until_pairs_list a1_map L R pos tp len inz) ys)) acc" for ys
    by (induction ys arbitrary: acc) (simp_all add: until_elem_step_dq_foldr)
  from this[of "rev xs"] show ?thesis by (simp add: foldr_conv_fold)
qed

lemma set_concat_until_pairs_list:
  "set (concat (map (until_pairs_list a1_map L R pos tp len inz) xs)) =
    \<Union>(until_cand a1_map L R pos tp len ` set xs) \<union> (if inz then {tp} \<times> set xs else {})"
  by (cases inz) (auto simp: set_until_pairs_list)

lemma set_csorted_list_of_set_etuple: "finite (X :: event_data table) \<Longrightarrow> set (csorted_list_of_set X) = X"
  using ID_ccompare_etuple_dq by (subst csorted_list_of_set_split) auto

lemma add_new_sim:
  assumes rel: "rel_uaux d a" and valid: "valid_mmuaux args cur a auxlist" and nt: "nt \<ge> cur"
    and tabs: "table (args_L args) rel1" "table (args_R args) rel2"
  shows "rel_uaux (add_new_dq args rel1 rel2 nt d) (add_new_mmuaux args rel1 rel2 nt a)"
proof (cases "finite rel2")
  case False
  have "valid_mmuaux' args nt nt (add_new_mmuaux args rel1 rel2 nt a) (update_until args rel1 rel2 nt auxlist)"
    using valid_add_new_mmuaux[OF valid tabs nt] unfolding valid_mmuaux_def .
  then show ?thesis
    unfolding add_new_dq_def using False rel_uaux_det[OF rel] by (simp add: rel_uaux_of)
next
  case True
  have valid0: "valid_mmuaux' args cur cur a auxlist" using valid unfolding valid_mmuaux_def .
  have rel': "rel_uaux (shift_dq args nt d) (shift_mmuaux args nt a)" by (rule shift_sim[OF rel valid0 nt])
  have valid': "valid_mmuaux' args cur nt (shift_mmuaux args nt a) auxlist"
    using valid_shift_mmuaux'[OF valid0 nt] by simp
  obtain tp tss tables len result a1_map a2_map tstp_map "done" where a:
    "shift_mmuaux args nt a = (tp, tss, tables, len, result, a1_map, a2_map, tstp_map, done)"
    by (cases "shift_mmuaux args nt a") auto
  obtain a2_dq tstp_dq where d: "shift_dq args nt d = (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, done)"
    using rel' unfolding a by (cases "shift_dq args nt d") auto
  have ra2: "rel_a2 tp len a2_dq a2_map" and rt: "rel_tstp tp len tstp_dq tstp_map" and lentp: "len \<le> tp"
    using rel' unfolding a d by auto
  note a1 = valid_mmuaux'_facts(4)[OF valid'[unfolded a]]
  define I where "I = args_ivl args"
  define pos where "pos = args_pos args"
  define inz where "inz = memL I 0"
  define new_tstp where "new_tstp = (if inz then Inr tp else Inl nt :: ts + tp)"
  define tstp_map' where "tstp_map' = Mapping.update tp nt tstp_map"
  define tstp_dq' where "tstp_dq' = dq_push nt tstp_dq"
  define P where "P = (\<lambda>t. memL I (nt - dq_nth tstp_dq' (t - (tp - len))))"
  define a1_map' where "a1_map' = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1)"
  define xs where "xs = csorted_list_of_set rel2"
  have set_xs: "set xs = rel2" unfolding xs_def by (rule set_csorted_list_of_set_etuple[OF True])
  define ps where "ps = concat (map (until_pairs_list a1_map (args_L args) (args_R args) pos tp len inz) (rev xs))"
  define tmp0 where "tmp0 = \<Union>(until_cand a1_map (args_L args) (args_R args) pos tp len ` rel2) \<union> (if inz then {tp} \<times> rel2 else {})"
  have set_ps: "set ps = tmp0" unfolding ps_def tmp0_def set_concat_until_pairs_list set_rev set_xs ..
  define qs where "qs = filter (\<lambda>p. P (fst p)) ps"
  define tmp where "tmp = Set.filter (\<lambda>p. P (fst p)) tmp0"
  have set_qs: "set qs = tmp" unfolding qs_def tmp_def set_ps[symmetric] by auto
  have rt': "rel_tstp (tp + 1) (len + 1) tstp_dq' tstp_map'"
    unfolding tstp_dq'_def tstp_map'_def by (rule rel_tstp_push[OF rt lentp])
  have look_tstp: "\<And>t. tp - len \<le> t \<Longrightarrow> t \<le> tp \<Longrightarrow> Mapping.lookup tstp_map' t = Some (dq_nth tstp_dq' (t - (tp - len)))"
  proof -
    fix t assume t: "tp - len \<le> t" "t \<le> tp"
    have "t - (tp - len) < len + 1" using t lentp by arith
    moreover have "tp + 1 - (len + 1) + (t - (tp - len)) = t" using t lentp by arith
    ultimately show "Mapping.lookup tstp_map' t = Some (dq_nth tstp_dq' (t - (tp - len)))"
      using rt' unfolding rel_tstp_def by metis
  qed
  have rng_cand: "\<And>t as x. (t, as) \<in> until_cand a1_map (args_L args) (args_R args) pos tp len x \<Longrightarrow> tp - len \<le> t \<and> t \<le> tp"
  proof -
    fix t as x assume mem: "(t, as) \<in> until_cand a1_map (args_L args) (args_R args) pos tp len x"
    show "tp - len \<le> t \<and> t \<le> tp"
    proof (cases "Mapping.lookup a1_map (restrict (args_L args) (args_R args) x)")
      case None
      then show ?thesis using mem unfolding until_cand_def by (auto split: if_splits)
    next
      case (Some tp')
      then show ?thesis using mem a1[OF Some] unfolding until_cand_def by (auto split: if_splits)
    qed
  qed
  have rng0: "\<And>t as. (t, as) \<in> tmp0 \<Longrightarrow> tp - len \<le> t \<and> t \<le> tp"
    unfolding tmp0_def using rng_cand by (auto split: if_splits)
  have tmp_eq: "Set.filter (\<lambda>(t, as). case Mapping.lookup tstp_map' t of Some ts \<Rightarrow> memL I (nt - ts)) tmp0 = tmp"
    unfolding tmp_def P_def using rng0 look_tstp by (auto split: prod.splits)
  have res_eq: "set (filter (\<lambda>p. P (fst p) \<and> fst p = tp - len) ps) = Set.filter (\<lambda>(t, x). t = tp - len) tmp"
    unfolding tmp_def set_ps[symmetric] by (auto simp: split_beta)
  have fold_eq: "fold (until_elem_step_dq a1_map (args_L args) (args_R args) pos tp len inz P new_tstp) xs ({}, a2_dq, result) =
    (snd ` tmp, upd_nested_dq (tp - len) new_tstp (max_tstp new_tstp) qs a2_dq,
     result \<union> snd ` Set.filter (\<lambda>(t, x). t = tp - len) tmp)"
    unfolding fold_until_elem_step_dq foldr_until_step_dq ps_def[symmetric] qs_def[symmetric] set_qs res_eq by simp
  have rng_qs: "fst ` set qs \<subseteq> {tp - len..tp}"
    unfolding set_qs tmp_def by (auto dest!: rng0)
  have ra2': "rel_a2 (tp + 1) (len + 1)
    (dq_push Mapping.empty (upd_nested_dq (tp - len) new_tstp (max_tstp new_tstp) qs a2_dq))
    (Mapping.update (tp + 1) Mapping.empty (upd_nested a2_map new_tstp (max_tstp new_tstp) tmp))"
    using rel_a2_push[OF rel_a2_upd_nested[where d = new_tstp and f = "max_tstp new_tstp",
      OF ra2 max_tstp_d_d[symmetric] max_tstp_idem' rng_qs] lentp]
    unfolding set_qs .
  have cand_eta: "(\<lambda>as. case Mapping.lookup a1_map (restrict (args_L args) (args_R args) as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) = until_cand a1_map (args_L args) (args_R args) pos tp len"
    by (simp add: fun_eq_iff until_cand_def)
  have dq_eq: "add_new_dq args rel1 rel2 nt d = (tp + 1, append_queue nt tss, append_queue (snd ` tmp, new_tstp) tables,
    len + 1, result \<union> snd ` Set.filter (\<lambda>(t, x). t = tp - len) tmp, a1_map',
    dq_push Mapping.empty (upd_nested_dq (tp - len) new_tstp (max_tstp new_tstp) qs a2_dq), tstp_dq', done)"
    unfolding add_new_dq_def if_P[OF True] d Let_def prod.case
    unfolding I_def[symmetric] pos_def[symmetric] inz_def[symmetric] new_tstp_def[symmetric] tstp_dq'_def[symmetric]
      xs_def[symmetric] P_def[symmetric] a1_map'_def[symmetric]
    unfolding fold_eq prod.case ..
  have mm_eq: "add_new_mmuaux args rel1 rel2 nt a = (tp + 1, append_queue nt tss, append_queue (snd ` tmp, new_tstp) tables,
    len + 1, result \<union> snd ` Set.filter (\<lambda>(t, x). t = tp - len) tmp, a1_map',
    Mapping.update (tp + 1) Mapping.empty (upd_nested a2_map new_tstp (max_tstp new_tstp) tmp), tstp_map', done)"
    unfolding add_new_mmuaux_def a Let_def prod.case
    unfolding I_def[symmetric] pos_def[symmetric] inz_def[symmetric] new_tstp_def[symmetric] tstp_map'_def[symmetric]
      cand_eta tmp0_def[symmetric] tmp_eq a1_map'_def[symmetric] ..
  show ?thesis
    unfolding dq_eq mm_eq rel_uaux.simps using ra2' rt' lentp by simp
qed

subsection \<open>Combined structure\<close>

lemma valid_init_muaux_dq:
  assumes LR: "set L \<subseteq> set R" "distinct L" "distinct R"
  shows "valid_muaux_dq (init_args I n L R pos aggargs) 0 (init_muaux_dq (init_args I n L R pos aggargs)) []"
proof (cases "args_agg (init_args I n L R pos aggargs) = None")
  case True
  show ?thesis unfolding init_muaux_dq_def if_P[OF True] valid_muaux_dq.simps
    using init_sim valid_init_mmuaux[OF LR] by blast
next
  case False
  show ?thesis unfolding init_muaux_dq_def if_not_P[OF False] valid_muaux_dq.simps
    by (rule valid_init_mmauaux[OF LR])
qed

lemma valid_add_new_muaux_dq:
  assumes "valid_muaux_dq args cur aux auxlist" "table (args_L args) rel1"
    "table (args_R args) rel2" "nt \<ge> cur"
  shows "valid_muaux_dq args nt (add_new_muaux_dq args rel1 rel2 nt aux) (update_until args rel1 rel2 nt auxlist)"
proof (cases aux)
  case (MU_dq d)
  obtain a where rel: "rel_uaux d a" and valid: "valid_mmuaux args cur a auxlist" using assms(1) unfolding MU_dq by auto
  show ?thesis unfolding MU_dq add_new_muaux_dq.simps valid_muaux_dq.simps
    using add_new_sim[OF rel valid assms(4) assms(2,3)] valid_add_new_mmuaux[OF valid assms(2,3,4)] by blast
next
  case (MU_agg a)
  obtain m x where a: "a = (m, x)" by (cases a)
  show ?thesis
    using valid_add_new_mmauaux[OF assms(1)[unfolded MU_agg a valid_muaux_dq.simps] assms(2,3,4)]
    unfolding MU_agg a by simp
qed

lemma valid_length_muaux_dq:
  assumes "valid_muaux_dq args cur aux auxlist"
  shows "length_muaux_dq args aux = length auxlist"
proof (cases aux)
  case (MU_dq d)
  obtain a where rel: "rel_uaux d a" and valid: "valid_mmuaux args cur a auxlist" using assms unfolding MU_dq by auto
  show ?thesis unfolding MU_dq length_muaux_dq.simps length_sim[OF rel] by (rule valid_length_mmuaux[OF valid])
next
  case (MU_agg a)
  then show ?thesis using assms by (cases a) (auto simp: valid_length_mmauaux)
qed

lemma valid_eval_muaux_dq:
  assumes "valid_muaux_dq args cur aux auxlist" "nt \<ge> cur"
    "eval_muaux_dq args nt aux = (res, aux')" "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "valid_muaux_dq args cur aux' auxlist' \<and> res = map (eval_args_agg args) res'"
proof (cases aux)
  case (MU_dq d)
  obtain a where rel: "rel_uaux d a" and valid: "valid_mmuaux args cur a auxlist" using assms(1) unfolding MU_dq by auto
  have ev: "res = fst (eval_dq args nt d)" "aux' = MU_dq (snd (eval_dq args nt d))"
    using assms(3) unfolding MU_dq by (auto split: prod.splits)
  have "valid_mmuaux args cur (snd (eval_mmuaux' args nt a)) auxlist' \<and> fst (eval_mmuaux' args nt a) = map (eval_args_agg args) res'"
    by (rule valid_eval_mmuaux'[OF valid assms(2) _ assms(4)]) simp
  then show ?thesis unfolding ev valid_muaux_dq.simps
    using eval_sim[OF rel valid assms(2)] by (intro conjI exI[of _ "snd (eval_mmuaux' args nt a)"]) auto
next
  case (MU_agg a)
  obtain m x where a: "a = (m, x)" by (cases a)
  obtain a' where ev: "eval_mmauaux' args nt a = (res, a')" "aux' = MU_agg a'"
    using assms(3) unfolding MU_agg by (auto split: prod.splits)
  show ?thesis
    using valid_eval_mmauaux[OF assms(1)[unfolded MU_agg a valid_muaux_dq.simps] assms(2) ev(1)[unfolded a] assms(4)]
    unfolding ev(2) by simp
qed

interpretation dq_muaux: muaux valid_muaux_dq init_muaux_dq add_new_muaux_dq length_muaux_dq eval_muaux_dq
  using valid_init_muaux_dq valid_add_new_muaux_dq valid_length_muaux_dq valid_eval_muaux_dq
  by unfold_locales auto

(*<*)
end
(*>*)

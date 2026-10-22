(*<*)
theory Until_Gen_Proof
  imports "Monitor_Exec.Until_Gen" Frame_Aux_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma dq_nth_s_in: "k < dq_len d \<Longrightarrow> dq_nth_s d k z = dq_nth d k"
  by (simp add: dq_nth_s_def)

lemma dq_hd_s_nth: "dq_inv d \<Longrightarrow> 0 < dq_len d \<Longrightarrow> dq_hd_s d z = dq_nth d 0"
  by (auto simp: dq_hd_s_def dq_nth_def dq_inv_def dq_len_def last_conv_nth hd_conv_nth
      split: list.splits)

lemma dq_nth_l_in: "dq_inv d \<Longrightarrow> k < dq_len d \<Longrightarrow> dq_nth_l d k z = dq_nth d k"
  by (auto simp: dq_nth_l_def dq_nth_def dq_inv_def dq_len_def Let_def)

lemma nth_def_eq: "nth_def xs k z = (if k < length xs then xs ! k else z)"
  by (induct xs k z rule: nth_def.induct) auto

lemma gupd_nested_step_dq_eq:
  assumes inv: "dq_inv dq"
  shows "gupd_nested_step_dq base d f x dq = upd_nested_step_dq base d f x dq"
proof -
  obtain k k' where x: "x = (k, k')" by (cases x)
  show ?thesis
  proof (cases "base \<le> k \<and> k - base < dq_len dq")
    case True
    then have "dq_nth_l dq (k - base) Mapping.empty = dq_nth dq (k - base)"
      using inv by (simp add: dq_nth_l_in)
    then show ?thesis unfolding gupd_nested_step_dq_def upd_nested_step_dq_def x Let_def
      by (simp split: option.splits)
  next
    case False
    then show ?thesis unfolding gupd_nested_step_dq_def upd_nested_step_dq_def x by auto
  qed
qed

lemma ushape_fix_res[simp]: "ushape (fix_res d) = ushape d"
  and ulen_fix_res[simp]: "ulen (fix_res d) = ulen d"
  and utp_fix_res[simp]: "utp (fix_res d) = utp d"
  and ua1_fix_res[simp]: "ua1 (fix_res d) = ua1 d"
  and glength_fix_res[simp]: "glength_dq args (fix_res d) = glength_dq args d"
  by (induct d rule: fix_res.induct, simp)+

lemma dq_hd_s_list: "dq_inv d \<Longrightarrow> 0 < dq_len d \<Longrightarrow> dq_hd_s d z = hd (dq_list d)"
  by (simp add: dq_hd_s_nth dq_nth dq_len_list hd_conv_nth)

lemma dq_hd_s_push: "dq_inv d \<Longrightarrow> 0 < dq_len d \<Longrightarrow> dq_hd_s (dq_push x d) z = dq_hd_s d z"
  by (simp add: dq_hd_s_list dq_len_push dq_len_list)

lemma dq_hd_s_upd0: "dq_inv d \<Longrightarrow> 0 < dq_len d \<Longrightarrow> dq_hd_s (dq_upd d 0 x) z = x"
  by (simp add: dq_hd_s_list dq_len_upd dq_list_upd dq_len_list hd_conv_nth)

lemma dq_hd_s_upd_pos:
  "dq_inv d \<Longrightarrow> 0 < k \<Longrightarrow> k < dq_len d \<Longrightarrow> dq_hd_s (dq_upd d k x) z = dq_hd_s d z"
  using dq_hd_s_list[of "dq_upd d k x" z] dq_hd_s_list[of d z]
  by (cases "dq_list d"; cases k) (auto simp: dq_len_upd dq_list_upd dq_len_list)

lemma geval_step_dq_eq:
  assumes ag: "args_agg args = None"
    and sh: "ushape (d :: event_data mmuaux_dq)" and l: "1 \<le> ulen d"
  shows "fix_res (geval_step_dq args d) = eval_step_dq args (fix_res d)"
    and "ushape (geval_step_dq args d)" and "ulen (geval_step_dq args d) = ulen d - 1"
    and "utp (geval_step_dq args d) = utp d" and "ua1 (geval_step_dq args d) = ua1 d"
proof -
  obtain tp tss tables len result a1_map a2_dq tstp_dq dn
    where d: "d = (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases d rule: mmuaux_dq_cases)
  have inv: "dq_inv a2_dq" and la2: "dq_len a2_dq = len + 1" and invt: "dq_inv tstp_dq"
    and lt: "dq_len tstp_dq = len" and ls: "length (linearize tss) = len"
    using sh unfolding d by simp_all
  have len: "1 \<le> len" using l unfolding d by simp
  have n0: "dq_hd_s a2_dq z = dq_nth a2_dq 0" for z :: "(event_data tuple, ts + tp) mapping"
    by (simp add: dq_hd_s_nth[OF inv] la2)
  have n1: "dq_hd_s (dq_tl a2_dq) z = dq_nth (dq_tl a2_dq) 0"
    for z :: "(event_data tuple, ts + tp) mapping"
    using len by (simp add: dq_hd_s_nth[OF dq_inv_tl[OF inv]] dq_len_tl[OF inv] la2)
  have u0: "dq_hd_s (dq_upd (dq_tl a2_dq) 0 X) z = X"
    for X z :: "(event_data tuple, ts + tp) mapping"
    using len by (simp add: dq_hd_s_upd0[OF dq_inv_tl[OF inv]] dq_len_tl[OF inv] la2)
  obtain h tss1 where sh1: "safe_hd tss = (h, tss1)" by (cases "safe_hd tss")
  have ne: "linearize tss \<noteq> []" using ls len by auto
  obtain t where h: "h = Some t" using safe_hd_rep[OF sh1] ne by (cases h) auto
  have l1: "linearize tss1 = linearize tss" using safe_hd_rep[OF sh1] by simp
  obtain h2 tss2 where sh2: "safe_hd (tl_queue tss1) = (h2, tss2)"
    by (cases "safe_hd (tl_queue tss1)")
  have l2: "linearize tss2 = tl (linearize tss)"
    using safe_hd_rep[OF sh2] by (simp add: tl_queue_rep l1)
  show "fix_res (geval_step_dq args d) = eval_step_dq args (fix_res d)"
    unfolding d fix_res.simps using len
    by (simp add: sh1 h Let_def n0 n1 u0 eval_args_agg_def ag split: prod.splits option.splits)
  have "ushape (geval_step_dq args d) \<and> ulen (geval_step_dq args d) = ulen d - 1 \<and>
      utp (geval_step_dq args d) = utp d \<and> ua1 (geval_step_dq args d) = ua1 d"
    unfolding d using inv la2 invt lt ls len l2
    by (cases h2)
      (simp_all add: sh1 h sh2 Let_def dq_len_tl dq_len_upd
        split: prod.splits)
  then show "ushape (geval_step_dq args d)" "ulen (geval_step_dq args d) = ulen d - 1"
    "utp (geval_step_dq args d) = utp d" "ua1 (geval_step_dq args d) = ua1 d" by simp_all
qed

lemma foldl_geval_step_dq_eq:
  assumes ag: "args_agg args = None"
    and sh: "ushape (d :: event_data mmuaux_dq)" and l: "length xs \<le> ulen d"
  shows "fix_res (foldl (\<lambda>aux _. geval_step_dq args aux) d xs)
       = foldl (\<lambda>aux _. eval_step_dq args aux) (fix_res d) xs \<and>
     ushape (foldl (\<lambda>aux _. geval_step_dq args aux) d xs) \<and>
     ulen (foldl (\<lambda>aux _. geval_step_dq args aux) d xs) = ulen d - length xs \<and>
     utp (foldl (\<lambda>aux _. geval_step_dq args aux) d xs) = utp d \<and>
     ua1 (foldl (\<lambda>aux _. geval_step_dq args aux) d xs) = ua1 d"
  using sh l
proof (induct xs arbitrary: d)
  case (Cons x xs)
  note step = geval_step_dq_eq[OF ag Cons.prems(1)]
  have l1: "1 \<le> ulen d" using Cons.prems(2) by simp
  have "length xs \<le> ulen (geval_step_dq args d)" using Cons.prems(2) step(3)[OF l1] by simp
  from Cons.hyps[OF step(2)[OF l1] this] show ?case
    using step(1)[OF l1] step(3)[OF l1] step(4)[OF l1] step(5)[OF l1] by simp
qed simp

lemma gshift_dq_eq:
  assumes ag: "args_agg args = None" and sh: "ushape (d :: event_data mmuaux_dq)"
  shows "fix_res (gshift_dq args nt d) = shift_dq args nt (fix_res d)"
    and "ushape (gshift_dq args nt d)" and "utp (gshift_dq args nt d) = utp d"
    and "ua1 (gshift_dq args nt d) = ua1 d"
proof -
  obtain tp tss tables len result a1_map a2_dq tstp_dq dn
    where d: "d = (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases d rule: mmuaux_dq_cases)
  obtain tq tss' where tw: "takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss = (tq, tss')"
    by (cases "takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss")
  have ltq: "length (linearize tq) \<le> length (linearize tss)"
    using takeWhile_queue_rep_fst[of "\<lambda>t. \<not> memR (args_ivl args) (nt - t)" tss]
    unfolding tw by (simp add: length_takeWhile_le)
  have lts: "linearize tss' = linearize tss"
    using takeWhile_queue_rep_snd[of "\<lambda>t. \<not> memR (args_ivl args) (nt - t)" tss]
    unfolding tw by simp
  let ?s = "(tp, tss', tables, len, result, a1_map, a2_dq, tstp_dq, dn)"
  have sh': "ushape ?s" using sh unfolding d by (simp add: lts)
  have l: "length (linearize tq) \<le> ulen ?s" using ltq sh unfolding d by simp
  note f = foldl_geval_step_dq_eq[OF ag sh' l]
  have g: "gshift_dq args nt d = foldl (\<lambda>aux _. geval_step_dq args aux) ?s (linearize tq)"
    and s: "shift_dq args nt (fix_res d)
      = foldl (\<lambda>aux _. eval_step_dq args aux) (fix_res ?s) (linearize tq)"
    unfolding d gshift_dq.simps shift_dq.simps fix_res.simps tw by (simp_all add: Let_def)
  show "fix_res (gshift_dq args nt d) = shift_dq args nt (fix_res d)" unfolding g s using f by simp
  show "ushape (gshift_dq args nt d)" "utp (gshift_dq args nt d) = utp d"
    "ua1 (gshift_dq args nt d) = ua1 d" unfolding g using f unfolding d by simp_all
qed

lemma geval_dq_eq:
  assumes "args_agg args = None" and "ushape (d :: event_data mmuaux_dq)"
  shows "fst (geval_dq args nt d) = fst (eval_dq args nt (fix_res d))"
    and "fix_res (snd (geval_dq args nt d)) = snd (eval_dq args nt (fix_res d))"
  using gshift_dq_eq(1)[OF assms, of nt, symmetric]
  by (cases "gshift_dq args nt d" rule: mmuaux_dq_cases; simp)+

lemma dq_len_upd_nested_step_dq:
  "dq_inv dq \<Longrightarrow> dq_len (upd_nested_step_dq base d f x dq) = dq_len dq"
  by (auto simp: upd_nested_step_dq_def Let_def dq_len_upd split: prod.splits)

lemma keys_hd_upd_nested_step_dq:
  assumes inv: "dq_inv dq" and l: "0 < dq_len dq"
  shows "Mapping.keys (dq_hd_s (upd_nested_step_dq t0 d f (k, k') dq) Mapping.empty)
    = (if k = t0 then Set.insert k' (Mapping.keys (dq_hd_s dq Mapping.empty))
       else Mapping.keys (dq_hd_s dq Mapping.empty))"
  using inv l
  by (auto simp: upd_nested_step_dq_def Let_def dq_hd_s_upd0 dq_hd_s_upd_pos dq_hd_s_nth
      split: option.splits)

lemma until_step_dq_lift:
  assumes P: "P (fst p) = P' (fst p)" and q: "qacc n acc"
  shows "until_step_dq P' d t0 (p :: nat \<times> event_data tuple) (lift_acc acc)
      = lift_acc (guntil_step_dq P d t0 p acc)"
    and "qacc n (guntil_step_dq P d t0 p acc)"
proof -
  obtain tbl a2 where acc: "acc = (tbl, a2)" by (cases acc)
  obtain k k' where p: "p = (k, k')" by (cases p)
  have inv: "dq_inv a2" and l: "0 < dq_len a2" and ln: "dq_len a2 = n"
    using q unfolding acc qacc_def by simp_all
  show "until_step_dq P' d t0 p (lift_acc acc) = lift_acc (guntil_step_dq P d t0 p acc)"
    using P unfolding acc p
    by (simp add: lift_acc_def until_step_dq_def guntil_step_dq_def gupd_nested_step_dq_eq[OF inv]
        keys_hd_upd_nested_step_dq[OF inv l])
  show "qacc n (guntil_step_dq P d t0 p acc)"
    using inv l ln q unfolding acc p
    by (simp add: qacc_def guntil_step_dq_def gupd_nested_step_dq_eq[OF inv]
        dq_len_upd_nested_step_dq)
qed

lemma euntil_elem_step_dq_lift:
  assumes P: "\<And>t. t \<le> tp \<Longrightarrow> P t = P' t"
    and a1: "\<And>k v. Mapping.lookup a1_map k = Some v \<Longrightarrow> v < tp"
    and q: "qacc n acc"
  shows "euntil_elem_step_dq a1_map msk pos tp len inz P' d (as :: event_data tuple) (lift_acc acc)
       = lift_acc (guntil_elem_step_dq a1_map msk pos tp len inz P d as acc)"
    and "qacc n (guntil_elem_step_dq a1_map msk pos tp len inz P d as acc)"
proof -
  have s1: "fst p \<le> tp \<Longrightarrow> qacc n acc \<Longrightarrow>
      until_step_dq P' d (tp - len) p (lift_acc acc) = lift_acc (guntil_step_dq P d (tp - len) p acc)"
    for p :: "nat \<times> event_data tuple" and acc using until_step_dq_lift(1) P by blast
  have s2: "qacc n acc \<Longrightarrow> qacc n (guntil_step_dq P d (tp - len) p acc)"
    for p :: "nat \<times> event_data tuple" and acc
    by (rule until_step_dq_lift(2)[OF refl])
  show "euntil_elem_step_dq a1_map msk pos tp len inz P' d as (lift_acc acc)
       = lift_acc (guntil_elem_step_dq a1_map msk pos tp len inz P d as acc)"
    unfolding guntil_elem_step_dq_def euntil_elem_step_dq_def Let_def
    by (auto simp: s1 s2 q Suc_le_eq dest!: a1 split: option.splits)
  show "qacc n (guntil_elem_step_dq a1_map msk pos tp len inz P d as acc)"
    unfolding guntil_elem_step_dq_def Let_def by (auto simp: s2 q split: option.splits)
qed

lemma fold_euntil_elem_step_dq_lift:
  assumes P: "\<And>t. t \<le> tp \<Longrightarrow> P t = P' t"
    and a1: "\<And>k v. Mapping.lookup a1_map k = Some v \<Longrightarrow> v < tp"
  shows "qacc n acc \<Longrightarrow>
    fold (euntil_elem_step_dq a1_map msk pos tp len inz P' d) (xs :: event_data tuple list)
      (lift_acc acc)
    = lift_acc (fold (guntil_elem_step_dq a1_map msk pos tp len inz P d) xs acc) \<and>
    qacc n (fold (guntil_elem_step_dq a1_map msk pos tp len inz P d) xs acc)"
proof (induct xs arbitrary: acc)
  case (Cons a xs)
  note e = euntil_elem_step_dq_lift[OF P a1 Cons.prems,
      where msk = msk and pos = pos and len = len and inz = inz and d = d and as = a]
  show ?case using Cons.hyps[OF e(2)] e(1) by simp
qed simp

lemma gadd_new_dq_eq:
  assumes ag: "args_agg args = None" and sh: "ushape (d :: event_data mmuaux_dq)"
    and a1: "\<And>k v. Mapping.lookup (ua1 d) k = Some v \<Longrightarrow> v < utp d"
  shows "fix_res (gadd_new_dq args msk rel1 rel2 nt d) = eadd_new_dq args msk rel1 rel2 nt (fix_res d)"
    and "ushape (gadd_new_dq args msk rel1 rel2 nt d)"
proof -
  obtain tp tss tables len result a1_map a2_dq tstp_dq dn
    where s: "gshift_dq args nt d = (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases "gshift_dq args nt d" rule: mmuaux_dq_cases)
  note sh' = gshift_dq_eq[OF ag sh, of nt]
  have fs: "shift_dq args nt (fix_res d) = (tp, tss, tables, len,
      Mapping.keys (dq_hd_s a2_dq Mapping.empty), a1_map, a2_dq, tstp_dq, dn)"
    using sh'(1) unfolding s by simp
  have invt: "dq_inv tstp_dq" and lt: "dq_len tstp_dq = len" and inva: "dq_inv a2_dq"
    and la: "dq_len a2_dq = len + 1" and lts: "length (linearize tss) = len"
    using sh'(2) unfolding s by simp_all
  have tp: "tp = utp d" and a1m: "a1_map = ua1 d" using sh'(3) sh'(4) unfolding s by simp_all
  define Pg where "Pg = (\<lambda>t. memL (args_ivl args) (nt - dq_nth_s (dq_push nt tstp_dq) (t - (tp - len)) 0))"
  define Pk where "Pk = (\<lambda>t. memL (args_ivl args) (nt - dq_nth (dq_push nt tstp_dq) (t - (tp - len))))"
  have P: "\<And>t. t \<le> tp \<Longrightarrow> Pg t = Pk t"
    by (simp add: Pg_def Pk_def dq_nth_s_in dq_len_push[OF invt] lt)
  have a1': "\<And>k v. Mapping.lookup a1_map k = Some v \<Longrightarrow> v < tp"
    using a1 unfolding tp a1m .
  define nts where "nts = (if memL (args_ivl args) 0 then Inr tp else Inl nt)"
  define g where "g = guntil_elem_step_dq a1_map msk (args_pos args) tp len
    (memL (args_ivl args) 0) Pg nts"
  obtain tbl a2' where f: "fold g (csl rel2) ({}, a2_dq) = (tbl, a2')"
    by (cases "fold g (csl rel2) ({}, a2_dq)")
  have q0: "qacc (len + 1) ({}, a2_dq)" using inva la by (simp add: qacc_def)
  have fl: "fold (euntil_elem_step_dq a1_map msk (args_pos args) tp len (memL (args_ivl args) 0) Pk
      nts) (csl rel2) (lift_acc ({}, a2_dq)) = lift_acc (tbl, a2') \<and> qacc (len + 1) (tbl, a2')"
    using fold_euntil_elem_step_dq_lift[where P = Pg and P' = Pk and a1_map = a1_map and tp = tp,
      OF P a1' q0, where msk = msk and pos = "args_pos args" and len = len
      and inz = "memL (args_ivl args) 0" and d = nts and xs = "csl rel2"]
    unfolding g_def[symmetric] f .
  have q1: "dq_inv a2'" "0 < dq_len a2'" "dq_len a2' = len + 1"
    using fl by (simp_all add: qacc_def)
  have fd: "fold (euntil_elem_step_dq a1_map msk (args_pos args) tp len (memL (args_ivl args) 0) Pk
      nts) (csl rel2) ({}, a2_dq, Mapping.keys (dq_hd_s a2_dq Mapping.empty))
    = (tbl, a2', Mapping.keys (dq_hd_s a2' Mapping.empty))"
    using conjunct1[OF fl] unfolding lift_acc_def fst_conv snd_conv .
  have ga: "gadd_new_dq args msk rel1 rel2 nt d = (tp + 1, append_queue nt tss,
      append_queue (tbl, nts) tables, len + 1,
      result, if args_pos args then Mapping.filter (\<lambda>as _. as \<in> rel1)
        (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1,
      dq_push Mapping.empty a2', dq_push nt tstp_dq, dn)"
    unfolding gadd_new_dq_def s Let_def using f unfolding g_def Pg_def nts_def
    by (simp split: prod.splits)
  show "fix_res (gadd_new_dq args msk rel1 rel2 nt d) = eadd_new_dq args msk rel1 rel2 nt (fix_res d)"
    unfolding ga eadd_new_dq_def fs Let_def using fd unfolding Pk_def nts_def
    by (simp add: dq_hd_s_push[OF q1(1,2)] split: prod.splits)
  show "ushape (gadd_new_dq args msk rel1 rel2 nt d)"
    unfolding ga using q1 invt lt lts by (simp add: dq_len_push append_queue_rep)
qed

lemma evalid_muaux_ushape:
  assumes v: "evalid_muaux args msk cur d auxlist"
  shows "ushape d" and "\<And>k v. Mapping.lookup (ua1 d) k = Some v \<Longrightarrow> v < utp d"
proof -
  obtain tp tss tables len result a1_map a2_dq tstp_dq dn
    where d: "d = (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases d rule: mmuaux_dq_cases)
  obtain a where rel: "rel_uaux d a" and va: "valid_mmuaux args cur a auxlist"
    using v by (auto simp: evalid_muaux_def)
  obtain tp' tss' tables' len' result' a1' a2m tstpm dn'
    where a: "a = (tp', tss', tables', len', result', a1', a2m, tstpm, dn')"
    by (cases a) auto
  have eqs: "tp' = tp" "tss' = tss" "len' = len" "a1' = a1_map"
    and ra2: "rel_a2 tp len a2_dq a2m" and rt: "rel_tstp tp len tstp_dq tstpm"
    using rel unfolding d a by simp_all
  have lts: "length (linearize tss) = len"
    and a1b: "\<forall>xs \<in> Mapping.keys a1_map. case Mapping.lookup a1_map xs of Some tp' \<Rightarrow> tp' < tp"
    using va unfolding a valid_mmuaux_def eqs by simp_all
  show "ushape d" unfolding d using ra2 rt lts by (simp add: rel_a2_def rel_tstp_def)
  fix k v assume kv: "Mapping.lookup (ua1 d) k = Some v"
  have k: "Mapping.lookup a1_map k = Some v" using kv unfolding d by simp
  then have mem: "k \<in> Mapping.keys a1_map" by (simp add: Mapping.keys_is_none_rep)
  from bspec[OF a1b mem] show "v < utp d" unfolding k d by simp
qed

lemma euaux'_ushape:
  assumes "euaux' kL cL kR cR args cur d auxlist"
  shows "ushape d" and "\<And>k v. Mapping.lookup (ua1 d) k = Some v \<Longrightarrow> v < utp d"
  using evalid_muaux_ushape assms unfolding euaux'_def by blast+

(*<*)
end
(*>*)

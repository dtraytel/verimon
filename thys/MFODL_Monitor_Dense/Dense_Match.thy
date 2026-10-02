(*<*)
theory Dense_Match
  imports Dense_Produces
begin
(*>*)

section \<open>Discharging @{const produces} for the regular-expression nodes\<close>

text \<open>
  The two match nodes need a toolkit of their own: the kernel's derivative operations on marked
  regular expressions.  That their results are tables over the node's columns is proved in
  @{theory MFODL_Monitor_Dense.Dense_Aux} (@{thm [source] table_eps_lax},
  @{thm [source] table_reps_strict}, @{thm [source] table_rdelta} and their left analogues), for
  atoms described by @{const wf_atoms}; the strict epsilons borrow the kernel's own
  @{thm [source] qtable_r\<epsilon>_strict}, since @{const r\<epsilon>_strict} returns the unit table at a
  @{term "Regex.Skip 0"}, which is a table over the node's columns only because the safety
  condition forces those columns to be empty there.  What is left is finiteness, which is purely
  structural: every one of the operations builds unions and joins of the operand tables.
\<close>

lemma finite_reorder: "finite X \<Longrightarrow> finite (reorder cs ds X)"
  by (simp add: reorder_def)

lemma finite_eps_lax:
  assumes ops: "\<forall>i < length \<phi>s. finite (\<phi>s ! i)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> finite guard \<Longrightarrow> finite (\<epsilon>_lax cs dss guard \<phi>s mr)"
  using ops by (induct mr) (auto simp: finite_join empty_table_def)

lemma finite_reps_strict:
  assumes ops: "\<forall>i < length \<phi>s. finite (\<phi>s ! i)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> finite (r\<epsilon>_strict cs dss \<phi>s mr)"
proof (induct mr)
  case (MTimes r s)
  then show ?case by (auto intro!: finite_eps_lax[OF ops])
qed (use ops in \<open>auto simp: empty_table_def unit_table_def finite_reorder\<close>)

lemma finite_leps_strict:
  assumes ops: "\<forall>i < length \<phi>s. finite (\<phi>s ! i)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> finite (l\<epsilon>_strict cs dss \<phi>s mr)"
proof (induct mr)
  case (MTimes r s)
  then show ?case by (auto intro!: finite_eps_lax[OF ops])
qed (use ops in \<open>auto simp: empty_table_def unit_table_def finite_reorder\<close>)

lemma finite_rdelta:
  assumes ops: "\<forall>i < length \<phi>s. finite (\<phi>s ! i)" and X: "\<And>ms. finite (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> finite (r\<delta> cs dss \<kappa> X \<phi>s mr)"
proof (induct mr arbitrary: \<kappa>)
  case (MTimes r s)
  then show ?case by (auto intro!: finite_eps_lax[OF ops])
qed (use X in \<open>auto simp: empty_table_def split: nat.splits\<close>)

lemma finite_ldelta:
  assumes ops: "\<forall>i < length \<phi>s. finite (\<phi>s ! i)" and X: "\<And>ms. finite (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> finite (l\<delta> cs dss \<kappa> X \<phi>s mr)"
proof (induct mr arbitrary: \<kappa>)
  case (MTimes r s)
  then show ?case by (auto intro!: finite_eps_lax[OF ops])
qed (use X in \<open>auto simp: empty_table_def split: nat.splits\<close>)

text \<open>The table lemmas of @{theory MFODL_Monitor_Dense.Dense_Aux} ask for dense column lists of
  the atoms, which play no role here; the ascending order of each atom's variables will do.\<close>

definition acss :: "ty Formula.formula list \<Rightarrow> cols list" where
  "acss \<psi>s = map (\<lambda>\<psi>. sorted_list_of_set (Formula.fv \<psi>)) \<psi>s"

lemma wf_atoms_acss:
  assumes ops: "list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel) \<psi>s rels"
    and sub: "\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> set ks"
  shows "wf_atoms ks (map Formula.fv_list \<psi>s) (acss \<psi>s) rels"
  using ops sub by (auto simp: wf_atoms_def acss_def list_all2_conv_all_nth dframe_def)

lemma ftable_mrtabulate:
  assumes d: "distinct mrs" and f: "\<And>ms. ms \<in> set mrs \<Longrightarrow> ftable ks (f ms)"
  shows "ftable ks (lookup (mrtabulate mrs f) ms)"
  using f by (simp add: lookup_tabulate[OF d])

lemma ftable_foldr_Un_lookup:
  "\<forall>(t, rel) \<in> set aux. ftable ks (lookup rel ms) \<Longrightarrow>
     ftable ks (foldr (\<union>) [lookup rel ms. (t, rel) \<leftarrow> aux, P t] {})"
  by (induct aux) (auto simp: table_def split: if_splits)

subsection \<open>The past-match node\<close>

text \<open>
  The past-match structure keeps, per timestamp, a mapping from the derivatives of the node's
  marked regular expression to tables.  Its invariant is that every one of those tables is a
  finite table over the node's columns, which one update preserves: each entry's new mapping is
  tabulated from a right derivative of the old one and, at the current timestamp, the strict
  right epsilon.  The node's output is the union of the mappings' values at the node's own
  expression over the part of the window the interval admits.
\<close>

definition maux_inv :: "cols \<Rightarrow> event_data mr\<delta>aux \<Rightarrow> bool" where
  "maux_inv ks aux \<longleftrightarrow> (\<forall>(t, rel) \<in> set aux. \<forall>ms. ftable ks (lookup rel ms))"

lemma maux_inv_map:
  "(\<And>t rel ns. (t, rel) \<in> set aux \<Longrightarrow> ftable ks (lookup (F t rel) ns)) \<Longrightarrow>
     maux_inv ks [(t, F t rel). (t, rel) \<leftarrow> aux, P t]"
  by (induct aux) (auto simp: maux_inv_def split: if_splits)

lemma maux_inv_cons_case:
  assumes x: "maux_inv ks xs" and r: "\<And>ns. ftable ks (lookup rel0 ns)"
  shows "maux_inv ks (case xs of [] \<Rightarrow> [(nt, rel0)]
     | x # xs' \<Rightarrow> (if fst x = nt then x # xs' else (nt, rel0) # x # xs'))"
  using assms by (cases xs) (auto simp: maux_inv_def)

lemma maux_inv_update:
  fixes \<psi>s :: "ty Formula.formula list" and rels :: "event_data table list"
  assumes inv: "maux_inv ks aux"
    and sr: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<psi>s)"
    and ok: "ok (length \<psi>s) mr" and A: "set ks = fv_regex (from_mregex mr \<psi>s)"
    and dks: "distinct ks" and d: "distinct mrs" and mrs: "set mrs = RPDs mr"
    and ops: "list_all2 (\<lambda>\<psi> rel. ftable (Formula.fv_list \<psi>) rel) \<psi>s rels"
    and sub: "\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> set ks"
    and e: "update_matchP ks (map Formula.fv_list \<psi>s) I mr mrs rels nt aux = (z, aux')"
  shows "ftable ks z \<and> maux_inv ks aux'"
proof -
  let ?kss = "map Formula.fv_list \<psi>s"
  have lr: "length \<psi>s = length rels" using ops by (simp add: list_all2_lengthD)
  have opt: "list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel) \<psi>s rels"
    using ops by (rule list_all2_mono) simp
  have fr: "\<forall>i < length rels. finite (rels ! i)"
    using ops lr by (auto simp: list_all2_conv_all_nth)
  have wfa: "wf_atoms ks ?kss (acss \<psi>s) rels" by (rule wf_atoms_acss[OF opt sub])
  have okr: "\<And>ms. ms \<in> set mrs \<Longrightarrow> ok (length rels) ms"
    using RPDs_ok[OF ok] mrs lr by auto
  have eps: "\<And>ms. ms \<in> set mrs \<Longrightarrow> ftable ks (r\<epsilon>_strict ks ?kss rels ms)"
  proof -
    fix ms assume "ms \<in> set mrs"
    then have ms: "ms \<in> RPDs mr" using mrs by simp
    have "table ks (r\<epsilon>_strict ks ?kss rels ms)"
      by (rule table_reps_strict[OF RPDs_safe[OF sr ms] RPDs_ok[OF ok ms]
          trans[OF A RPDs_safe_fv_regex[OF sr ms, symmetric]] dks opt])
    moreover have "finite (r\<epsilon>_strict ks ?kss rels ms)"
      by (rule finite_reps_strict[OF fr]) (use okr \<open>ms \<in> set mrs\<close> in simp)
    ultimately show "ftable ks (r\<epsilon>_strict ks ?kss rels ms)" by simp
  qed
  have key: "\<And>t rel ms. (t, rel) \<in> set aux \<Longrightarrow> ms \<in> set mrs \<Longrightarrow>
      ftable ks (r\<delta> ks ?kss id rel rels ms \<union> (if t = nt then r\<epsilon>_strict ks ?kss rels ms else {}))"
  proof -
    fix t rel ms
    assume m: "(t, rel) \<in> set aux" and mm: "ms \<in> set mrs"
    have x: "\<And>ns. ftable ks (lookup rel ns)" using inv m unfolding maux_inv_def by auto
    have r: "ftable ks (r\<delta> ks ?kss id rel rels ms)"
      using table_rdelta[OF wfa, of rel] finite_rdelta[OF fr, of rel] x okr[OF mm] by simp
    show "ftable ks (r\<delta> ks ?kss id rel rels ms \<union> (if t = nt then r\<epsilon>_strict ks ?kss rels ms else {}))"
      using r eps[OF mm] by (auto simp: table_def)
  qed
  have hf: "\<And>t rel ns. (t, rel) \<in> set aux \<Longrightarrow>
      ftable ks (lookup (mrtabulate mrs (\<lambda>ms. r\<delta> ks ?kss id rel rels ms \<union>
        (if t = nt then r\<epsilon>_strict ks ?kss rels ms else {}))) ns)"
    by (rule ftable_mrtabulate[OF d]) (use key in blast)
  have hn: "\<And>ns. ftable ks (lookup (mrtabulate mrs (r\<epsilon>_strict ks ?kss rels)) ns)"
    by (rule ftable_mrtabulate[OF d]) (use eps in blast)
  obtain aux2 where a2: "aux2 = (case [(t, mrtabulate mrs (\<lambda>ms. r\<delta> ks ?kss id rel rels ms \<union>
        (if t = nt then r\<epsilon>_strict ks ?kss rels ms else {}))). (t, rel) \<leftarrow> aux, memR I (nt - t)] of
      [] \<Rightarrow> [(nt, mrtabulate mrs (r\<epsilon>_strict ks ?kss rels))]
    | x # aux' \<Rightarrow> (if fst x = nt then x # aux'
                   else (nt, mrtabulate mrs (r\<epsilon>_strict ks ?kss rels)) # x # aux'))" by blast
  have zz: "z = foldr (\<union>) [lookup rel mr. (t, rel) \<leftarrow> aux2, memL I (nt - t)] {}"
    and aa: "aux' = aux2" using e unfolding a2 update_matchP_def Let_def by auto
  have hfl: "maux_inv ks [(t, mrtabulate mrs (\<lambda>ms. r\<delta> ks ?kss id rel rels ms \<union>
        (if t = nt then r\<epsilon>_strict ks ?kss rels ms else {}))). (t, rel) \<leftarrow> aux, memR I (nt - t)]"
    by (rule maux_inv_map) (use hf in blast)
  have h2: "maux_inv ks aux2" unfolding a2
    by (rule maux_inv_cons_case[OF hfl hn])
  have "ftable ks z" unfolding zz
    by (rule ftable_foldr_Un_lookup) (use h2 in \<open>auto simp: maux_inv_def\<close>)
  then show ?thesis using h2 aa by simp
qed

lemma mbufnt_take_out:
  "mbufnt_take f z buf t0 ts = (w, buf', t', ts') \<Longrightarrow> length Ss = length buf \<Longrightarrow>
   (\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i) \<Longrightarrow>
   (\<And>as t u. length as = length Ss \<Longrightarrow> (\<forall>i < length Ss. as ! i \<in> Ss ! i) \<Longrightarrow> Q u \<Longrightarrow>
      Q (f as t u)) \<Longrightarrow>
   Q z \<Longrightarrow>
   Q w \<and> length buf' = length buf \<and> (\<forall>i < length buf'. set (buf' ! i) \<subseteq> Ss ! i)"
proof (induct f z buf t0 ts arbitrary: w buf' t' ts' rule: mbufnt_take.induct)
  case (1 f z buf t0 ts)
  note IH = 1(1) and E = 1(2) and L = 1(3) and SUB = 1(4) and ST = 1(5) and QZ = 1(6)
  show ?case
  proof (cases "[] \<in> set buf \<or> ts = []")
    case True
    then show ?thesis using E L SUB QZ by simp
  next
    case False
    then have ne: "\<And>i. i < length buf \<Longrightarrow> buf ! i \<noteq> []" by (auto simp: in_set_conv_nth)
    have las: "length (map hd buf) = length Ss" using L by simp
    have has: "\<forall>i < length Ss. map hd buf ! i \<in> Ss ! i"
    proof (intro allI impI)
      fix i assume i: "i < length Ss"
      then have ib: "i < length buf" using L by simp
      have "hd (buf ! i) \<in> set (buf ! i)" using ne[OF ib] by simp
      then show "map hd buf ! i \<in> Ss ! i" using SUB ib by auto
    qed
    have q: "Q (f (map hd buf) (hd ts) z)" by (rule ST[OF las has QZ])
    have lt: "length Ss = length (map tl buf)" using L by simp
    have st: "\<forall>i < length (map tl buf). set (map tl buf ! i) \<subseteq> Ss ! i"
      using SUB L by (auto dest: set_tl_sub[THEN subsetD])
    have e: "mbufnt_take f (f (map hd buf) (hd ts) z) (map tl buf) (hd ts) (tl ts)
        = (w, buf', t', ts')" using E False by simp
    show ?thesis using IH[OF False e lt st ST q] L by simp
  qed
qed

lemma produces_MMatchP:
  fixes \<psi>s :: "ty Formula.formula list"
  defines "dss \<equiv> map Formula.fv_list \<psi>s"
  assumes sr: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<psi>s)"
    and ok: "ok (length \<psi>s) mr" and A: "set ks = fv_regex (from_mregex mr \<psi>s)"
    and dks: "distinct ks" and d: "distinct mrs" and mrs: "set mrs = RPDs mr"
    and fvsub: "\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> set ks"
    and lL: "length L = length \<psi>s"
    and pL: "\<forall>i < length \<psi>s. produces n (dss ! i) tw (L ! i)"
    and lb: "length buf = length \<psi>s"
    and pb: "\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (buf ! i)"
    and ax: "maux_inv ks aux"
  shows "produces n ks tw (MMatchP I ks dss mr mrs L buf nts aux)"
proof (rule producesI[where X = "\<lambda>n' ks' u \<Phi>. n' = n \<and> ks' = ks \<and>
    (\<exists>M bf ns ay. \<Phi> = MMatchP I ks dss mr mrs M bf ns ay \<and>
       length M = length \<psi>s \<and> (\<forall>i < length \<psi>s. produces n (dss ! i) u (M ! i)) \<and>
       length bf = length \<psi>s \<and> (\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (bf ! i)) \<and>
       maux_inv ks ay)"])
  show "n = n \<and> ks = ks \<and> (\<exists>M bf ns ay.
      MMatchP I ks dss mr mrs L buf nts aux = MMatchP I ks dss mr mrs M bf ns ay \<and>
      length M = length \<psi>s \<and> (\<forall>i < length \<psi>s. produces n (dss ! i) tw (M ! i)) \<and>
      length bf = length \<psi>s \<and> (\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (bf ! i)) \<and>
      maux_inv ks ay)"
    using lL pL lb pb ax by blast
next
  fix n' ks' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> ks' = ks \<and> (\<exists>M bf ns ay. \<Phi> = MMatchP I ks dss mr mrs M bf ns ay \<and>
       length M = length \<psi>s \<and> (\<forall>i < length \<psi>s. produces n (dss ! i) u (M ! i)) \<and>
       length bf = length \<psi>s \<and> (\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (bf ! i)) \<and>
       maux_inv ks ay)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>v \<in> set ts. u \<le> v"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain M bf ns ay where Phi: "\<Phi> = MMatchP I ks dss mr mrs M bf ns ay"
    and lM: "length M = length \<psi>s"
    and pM: "\<forall>i < length \<psi>s. produces n (dss ! i) u (M ! i)"
    and lbf: "length bf = length \<psi>s"
    and pbf: "\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (bf ! i)"
    and ay: "maux_inv ks ay" by blast
  have ldss: "length dss = length \<psi>s" by (simp add: dss_def)
  define Ss :: "event_data table set list" where "Ss = map (\<lambda>k. {Y. ftable k Y}) dss"
  define g where "g = (\<lambda>rels t (zs :: event_data table list, ax).
    let (z, ax) = update_matchP ks dss I mr mrs rels t ax in (zs @ [z], ax))"
  define Q where "Q = (\<lambda>pr :: event_data table list \<times> event_data mr\<delta>aux.
    list_all (ftable ks) (fst pr) \<and> maux_inv ks (snd pr))"
  define R where "R = map (meval j n ts db) M"
  define bf1 where "bf1 = mbufn_add (map fst R) bf"
  have lSs: "length Ss = length \<psi>s" by (simp add: Ss_def ldss)
  have lR: "length R = length \<psi>s" using lM by (simp add: R_def)
  have tR: "\<And>i. i < length \<psi>s \<Longrightarrow> list_all (ftable (dss ! i)) (fst (R ! i))"
  proof -
    fix i assume i: "i < length \<psi>s"
    obtain as \<chi>' where ei: "meval j n ts db (M ! i) = (as, \<chi>')"
      by (cases "meval j n ts db (M ! i)")
    have "list_all (ftable (dss ! i)) as"
      by (rule produces_tables[OF _ w sts mts ei]) (use pM i in blast)
    then show "list_all (ftable (dss ! i)) (fst (R ! i))"
      using ei i lM by (simp add: R_def)
  qed
  have nR: "\<And>i. i < length \<psi>s \<Longrightarrow> produces n (dss ! i) (dnext u ts) (snd (R ! i))"
  proof -
    fix i assume i: "i < length \<psi>s"
    obtain as \<chi>' where ei: "meval j n ts db (M ! i) = (as, \<chi>')"
      by (cases "meval j n ts db (M ! i)")
    have "produces n (dss ! i) (dnext u ts) \<chi>'"
      by (rule produces_next[OF _ w sts mts ei]) (use pM i in blast)
    then show "produces n (dss ! i) (dnext u ts) (snd (R ! i))"
      using ei i lM by (simp add: R_def)
  qed
  have lb1: "length bf1 = length \<psi>s" using lbf lR by (simp add: bf1_def)
  have sub1: "\<forall>i < length bf1. set (bf1 ! i) \<subseteq> Ss ! i"
  proof (intro allI impI)
    fix i assume i: "i < length bf1"
    then have ic: "i < length \<psi>s" using lb1 by simp
    have "bf1 ! i = bf ! i @ fst (R ! i)" using ic lbf lR by (simp add: bf1_def)
    then show "set (bf1 ! i) \<subseteq> Ss ! i"
      using pbf tR[OF ic] ic ldss by (auto simp: Ss_def list_all_iff)
  qed
  have st: "\<And>as t p. length as = length Ss \<Longrightarrow> (\<forall>i < length Ss. as ! i \<in> Ss ! i) \<Longrightarrow>
      Q p \<Longrightarrow> Q (g as t p)"
  proof -
    fix as :: "event_data table list" and t
      and p :: "event_data table list \<times> event_data mr\<delta>aux"
    assume la: "length as = length Ss" and ha: "\<forall>i < length Ss. as ! i \<in> Ss ! i"
      and qp: "Q p"
    have las: "length \<psi>s = length as" using la lSs by simp
    have ops: "list_all2 (\<lambda>\<psi> rel. ftable (Formula.fv_list \<psi>) rel) \<psi>s as"
      using ha lSs las by (auto simp: list_all2_conv_all_nth Ss_def dss_def)
    obtain zz ay' where eu: "update_matchP ks dss I mr mrs as t (snd p) = (zz, ay')"
      by (cases "update_matchP ks dss I mr mrs as t (snd p)")
    have "ftable ks zz \<and> maux_inv ks ay'"
      by (rule maux_inv_update[OF _ sr ok A dks d mrs ops fvsub eu[unfolded dss_def]])
        (use qp in \<open>simp add: Q_def\<close>)
    then show "Q (g as t p)" using qp eu by (cases p) (auto simp: Q_def g_def)
  qed
  obtain zs ay1 bf2 t2 ns2 where e2:
    "mbufnt_take g ([], ay) bf1 0 (ns @ ts) = ((zs, ay1), bf2, t2, ns2)"
    by (cases "mbufnt_take g ([], ay) bf1 0 (ns @ ts)") auto
  have q0: "Q ([], ay)" using ay by (simp add: Q_def)
  have out: "Q (zs, ay1) \<and> length bf2 = length bf1 \<and>
      (\<forall>i < length bf2. set (bf2 ! i) \<subseteq> Ss ! i)"
    by (rule mbufnt_take_out[where Q = Q and f = g and Ss = Ss, OF e2 _ sub1 st q0])
      (use lSs lb1 in simp)
  have m: "meval j n ts db (MMatchP I ks dss mr mrs M bf ns ay)
      = (zs, MMatchP I ks dss mr mrs (map snd R) bf2 ns2 ay1)"
    using e2 unfolding R_def bf1_def g_def
    by (simp add: map_split_alt Let_def del: mbufnt_take.simps)
  have x: "xs = zs" and f: "\<Phi>' = MMatchP I ks dss mr mrs (map snd R) bf2 ns2 ay1"
    using e X Phi m by simp_all
  have tz: "list_all (ftable ks) zs" using out by (simp add: Q_def)
  have ay1: "maux_inv ks ay1" using out by (simp add: Q_def)
  have lM': "length (map snd R) = length \<psi>s" using lR by simp
  have pM': "\<forall>i < length \<psi>s. produces n (dss ! i) (dnext u ts) (map snd R ! i)"
    using nR lR by simp
  have lbf2: "length bf2 = length \<psi>s" using out lb1 by simp
  have pbf2: "\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (bf2 ! i)"
    using out lbf2 ldss by (auto simp: Ss_def list_all_iff subset_eq)
  show "list_all (ftable ks') xs \<and>
      ((n' = n \<and> ks' = ks \<and> (\<exists>M bf ns ay. \<Phi>' = MMatchP I ks dss mr mrs M bf ns ay \<and>
         length M = length \<psi>s \<and> (\<forall>i < length \<psi>s. produces n (dss ! i) (dnext u ts) (M ! i)) \<and>
         length bf = length \<psi>s \<and> (\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (bf ! i)) \<and>
         maux_inv ks ay)) \<or>
       produces n' ks' (dnext u ts) \<Phi>')"
    using X tz ay1 lM' pM' lbf2 pbf2 by (auto simp: x f)
qed

subsection \<open>The future-match node\<close>

text \<open>
  The future-match structure keeps, per timestamp, the operand tables it was given together
  with the table accumulated for that timestamp so far; the mapping is threaded through the
  fold rather than stored.  So the invariant has to record the operands too -- the fold reads
  them back to take a left derivative -- and the accumulated table is the one the node
  eventually emits.
\<close>

definition mfaux_inv :: "cols \<Rightarrow> ty Formula.formula list \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> bool" where
  "mfaux_inv ks \<psi>s aux \<longleftrightarrow> (\<forall>(t, rels, rel) \<in> set aux.
     list_all2 (\<lambda>\<psi> r. ftable (Formula.fv_list \<psi>) r) \<psi>s rels \<and> ftable ks rel)"

lemma mfaux_inv_step:
  fixes \<psi>s :: "ty Formula.formula list"
  assumes inv: "mfaux_inv ks \<psi>s aux" and Y: "\<And>ms. ftable ks (lookup X ms)"
    and ok: "ok (length \<psi>s) mr" and d: "distinct mrs" and mrs: "set mrs = LPDs mr"
    and fvsub: "\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> set ks"
    and e: "foldr (update_matchF_step ks (map Formula.fv_list \<psi>s) I mr mrs nt) aux (aux0, X)
      = (aux1, X1)"
    and inv0: "mfaux_inv ks \<psi>s aux0"
  shows "mfaux_inv ks \<psi>s aux1 \<and> (\<forall>ms. ftable ks (lookup X1 ms))"
  using inv e inv0
proof (induct aux arbitrary: aux1 X1)
  case Nil
  then show ?case using Y by simp
next
  case (Cons a aux)
  let ?kss = "map Formula.fv_list \<psi>s"
  obtain t rels rel where a: "a = (t, rels, rel)" by (cases a)
  have i1: "mfaux_inv ks \<psi>s aux" using Cons(2) a by (simp add: mfaux_inv_def)
  have or1: "list_all2 (\<lambda>\<psi> r. ftable (Formula.fv_list \<psi>) r) \<psi>s rels"
    and tr1: "ftable ks rel" using Cons(2) a by (auto simp: mfaux_inv_def)
  obtain aux2 X2 where e2: "foldr (update_matchF_step ks ?kss I mr mrs nt) aux (aux0, X)
      = (aux2, X2)"
    by (cases "foldr (update_matchF_step ks ?kss I mr mrs nt) aux (aux0, X)")
  have h: "mfaux_inv ks \<psi>s aux2 \<and> (\<forall>ms. ftable ks (lookup X2 ms))"
    by (rule Cons(1)[OF i1 e2 Cons(4)])
  have i2: "mfaux_inv ks \<psi>s aux2" using h by simp
  have hx: "\<And>ms. ftable ks (lookup X2 ms)" using h by simp
  have lr: "length \<psi>s = length rels" using or1 by (simp add: list_all2_lengthD)
  have opt: "list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel) \<psi>s rels"
    using or1 by (rule list_all2_mono) simp
  have fr: "\<forall>i < length rels. finite (rels ! i)"
    using or1 lr by (auto simp: list_all2_conv_all_nth)
  have wfa: "wf_atoms ks ?kss (acss \<psi>s) rels" by (rule wf_atoms_acss[OF opt fvsub])
  have okl: "\<And>ms. ms \<in> set mrs \<Longrightarrow> ok (length rels) ms"
    using LPDs_ok[OF ok] mrs lr by auto
  have hy: "\<And>ms. ftable ks (lookup (mrtabulate mrs (l\<delta> ks ?kss id X2 rels)) ms)"
    by (rule ftable_mrtabulate[OF d])
      (use table_ldelta[OF wfa, of X2] finite_ldelta[OF fr, of X2] hx okl in auto)
  have res: "aux1 = (t, rels, if mem I (nt - t) then rel \<union> lookup (mrtabulate mrs
        (l\<delta> ks ?kss id X2 rels)) mr else rel) # aux2"
      and resX: "X1 = mrtabulate mrs (l\<delta> ks ?kss id X2 rels)"
    using Cons(3) e2 a by (auto simp: update_matchF_step_def Let_def)
  have "ftable ks (if mem I (nt - t) then rel \<union> lookup (mrtabulate mrs
      (l\<delta> ks ?kss id X2 rels)) mr else rel)"
    using tr1 hy[of mr] by (auto simp: table_def)
  then show ?case using i2 or1 hy unfolding res resX by (simp add: mfaux_inv_def)
qed

lemma mfaux_inv_update:
  fixes \<psi>s :: "ty Formula.formula list" and rels :: "event_data table list"
  assumes inv: "mfaux_inv ks \<psi>s aux"
    and sr: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<psi>s)"
    and ok: "ok (length \<psi>s) mr" and A: "set ks = fv_regex (from_mregex mr \<psi>s)"
    and dks: "distinct ks" and d: "distinct mrs" and mrs: "set mrs = LPDs mr"
    and ops: "list_all2 (\<lambda>\<psi> rel. ftable (Formula.fv_list \<psi>) rel) \<psi>s rels"
    and fvsub: "\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> set ks"
  shows "mfaux_inv ks \<psi>s (update_matchF ks (map Formula.fv_list \<psi>s) I mr mrs rels nt aux)"
proof -
  let ?kss = "map Formula.fv_list \<psi>s"
  have lr: "length \<psi>s = length rels" using ops by (simp add: list_all2_lengthD)
  have opt: "list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel) \<psi>s rels"
    using ops by (rule list_all2_mono) simp
  have fr: "\<forall>i < length rels. finite (rels ! i)"
    using ops lr by (auto simp: list_all2_conv_all_nth)
  have eps: "\<And>ms. ms \<in> set mrs \<Longrightarrow> ftable ks (l\<epsilon>_strict ks ?kss rels ms)"
  proof -
    fix ms assume msm: "ms \<in> set mrs"
    then have ms: "ms \<in> LPDs mr" using mrs by simp
    have "table ks (l\<epsilon>_strict ks ?kss rels ms)"
      by (rule table_leps_strict[OF LPDs_safe[OF sr ms] LPDs_ok[OF ok ms]
          trans[OF A LPDs_safe_fv_regex[OF sr ms, symmetric]] dks opt])
    moreover have "finite (l\<epsilon>_strict ks ?kss rels ms)"
      by (rule finite_leps_strict[OF fr]) (use LPDs_ok[OF ok ms] lr in simp)
    ultimately show "ftable ks (l\<epsilon>_strict ks ?kss rels ms)" by simp
  qed
  have hx: "\<And>ms. ftable ks (lookup (mrtabulate mrs (l\<epsilon>_strict ks ?kss rels)) ms)"
    by (rule ftable_mrtabulate[OF d]) (use eps in blast)
  have i0: "mfaux_inv ks \<psi>s [(nt, rels, if memL I 0
      then lookup (mrtabulate mrs (l\<epsilon>_strict ks ?kss rels)) mr else empty_table)]"
    using ops hx by (simp add: mfaux_inv_def)
  obtain aux1 X1 where e: "foldr (update_matchF_step ks ?kss I mr mrs nt) aux
      ([(nt, rels, if memL I 0 then lookup (mrtabulate mrs (l\<epsilon>_strict ks ?kss rels)) mr
         else empty_table)], mrtabulate mrs (l\<epsilon>_strict ks ?kss rels)) = (aux1, X1)"
    by (cases "foldr (update_matchF_step ks ?kss I mr mrs nt) aux
      ([(nt, rels, if memL I 0 then lookup (mrtabulate mrs (l\<epsilon>_strict ks ?kss rels)) mr
         else empty_table)], mrtabulate mrs (l\<epsilon>_strict ks ?kss rels))")
  have "mfaux_inv ks \<psi>s aux1 \<and> (\<forall>ms. ftable ks (lookup X1 ms))"
    by (rule mfaux_inv_step[OF inv hx ok d mrs fvsub e i0])
  then show ?thesis using e
    by (simp add: update_matchF_def update_matchF_base_def Let_def)
qed

lemma eval_matchF_ftable:
  fixes \<psi>s :: "ty Formula.formula list"
  shows "eval_matchF I mr nt aux = (res, aux') \<Longrightarrow> mfaux_inv ks \<psi>s aux \<Longrightarrow>
    list_all (ftable ks) res \<and> mfaux_inv ks \<psi>s aux'"
  by (induct I mr nt aux arbitrary: res aux' rule: eval_matchF.induct)
    (auto simp: mfaux_inv_def split: if_splits prod.splits)

lemma produces_MMatchF:
  fixes \<psi>s :: "ty Formula.formula list"
  defines "dss \<equiv> map Formula.fv_list \<psi>s"
  assumes sr: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<psi>s)"
    and ok: "ok (length \<psi>s) mr" and A: "set ks = fv_regex (from_mregex mr \<psi>s)"
    and dks: "distinct ks" and d: "distinct mrs" and mrs: "set mrs = LPDs mr"
    and fvsub: "\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> set ks"
    and lL: "length L = length \<psi>s"
    and pL: "\<forall>i < length \<psi>s. produces n (dss ! i) tw (L ! i)"
    and lb: "length buf = length \<psi>s"
    and pb: "\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (buf ! i)"
    and ax: "mfaux_inv ks \<psi>s aux"
  shows "produces n ks tw (MMatchF I ks dss mr mrs L buf nts t aux)"
proof (rule producesI[where X = "\<lambda>n' ks' u \<Phi>. n' = n \<and> ks' = ks \<and>
    (\<exists>M bf ns tt ay. \<Phi> = MMatchF I ks dss mr mrs M bf ns tt ay \<and>
       length M = length \<psi>s \<and> (\<forall>i < length \<psi>s. produces n (dss ! i) u (M ! i)) \<and>
       length bf = length \<psi>s \<and> (\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (bf ! i)) \<and>
       mfaux_inv ks \<psi>s ay)"])
  show "n = n \<and> ks = ks \<and> (\<exists>M bf ns tt ay.
      MMatchF I ks dss mr mrs L buf nts t aux = MMatchF I ks dss mr mrs M bf ns tt ay \<and>
      length M = length \<psi>s \<and> (\<forall>i < length \<psi>s. produces n (dss ! i) tw (M ! i)) \<and>
      length bf = length \<psi>s \<and> (\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (bf ! i)) \<and>
      mfaux_inv ks \<psi>s ay)"
    using lL pL lb pb ax by blast
next
  fix n' ks' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> ks' = ks \<and> (\<exists>M bf ns tt ay. \<Phi> = MMatchF I ks dss mr mrs M bf ns tt ay \<and>
       length M = length \<psi>s \<and> (\<forall>i < length \<psi>s. produces n (dss ! i) u (M ! i)) \<and>
       length bf = length \<psi>s \<and> (\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (bf ! i)) \<and>
       mfaux_inv ks \<psi>s ay)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>v \<in> set ts. u \<le> v"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain M bf ns tt ay where Phi: "\<Phi> = MMatchF I ks dss mr mrs M bf ns tt ay"
    and lM: "length M = length \<psi>s"
    and pM: "\<forall>i < length \<psi>s. produces n (dss ! i) u (M ! i)"
    and lbf: "length bf = length \<psi>s"
    and pbf: "\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (bf ! i)"
    and ay: "mfaux_inv ks \<psi>s ay" by blast
  have ldss: "length dss = length \<psi>s" by (simp add: dss_def)
  define Ss :: "event_data table set list" where "Ss = map (\<lambda>k. {Y. ftable k Y}) dss"
  define Q where "Q = (\<lambda>ax :: event_data ml\<delta>aux. mfaux_inv ks \<psi>s ax)"
  define R where "R = map (meval j n ts db) M"
  define bf1 where "bf1 = mbufn_add (map fst R) bf"
  have lSs: "length Ss = length \<psi>s" by (simp add: Ss_def ldss)
  have lR: "length R = length \<psi>s" using lM by (simp add: R_def)
  have tR: "\<And>i. i < length \<psi>s \<Longrightarrow> list_all (ftable (dss ! i)) (fst (R ! i))"
  proof -
    fix i assume i: "i < length \<psi>s"
    obtain as \<chi>' where ei: "meval j n ts db (M ! i) = (as, \<chi>')"
      by (cases "meval j n ts db (M ! i)")
    have "list_all (ftable (dss ! i)) as"
      by (rule produces_tables[OF _ w sts mts ei]) (use pM i in blast)
    then show "list_all (ftable (dss ! i)) (fst (R ! i))"
      using ei i lM by (simp add: R_def)
  qed
  have nR: "\<And>i. i < length \<psi>s \<Longrightarrow> produces n (dss ! i) (dnext u ts) (snd (R ! i))"
  proof -
    fix i assume i: "i < length \<psi>s"
    obtain as \<chi>' where ei: "meval j n ts db (M ! i) = (as, \<chi>')"
      by (cases "meval j n ts db (M ! i)")
    have "produces n (dss ! i) (dnext u ts) \<chi>'"
      by (rule produces_next[OF _ w sts mts ei]) (use pM i in blast)
    then show "produces n (dss ! i) (dnext u ts) (snd (R ! i))"
      using ei i lM by (simp add: R_def)
  qed
  have lb1: "length bf1 = length \<psi>s" using lbf lR by (simp add: bf1_def)
  have sub1: "\<forall>i < length bf1. set (bf1 ! i) \<subseteq> Ss ! i"
  proof (intro allI impI)
    fix i assume i: "i < length bf1"
    then have ic: "i < length \<psi>s" using lb1 by simp
    have "bf1 ! i = bf ! i @ fst (R ! i)" using ic lbf lR by (simp add: bf1_def)
    then show "set (bf1 ! i) \<subseteq> Ss ! i"
      using pbf tR[OF ic] ic ldss by (auto simp: Ss_def list_all_iff)
  qed
  have st: "\<And>as v p. length as = length Ss \<Longrightarrow> (\<forall>i < length Ss. as ! i \<in> Ss ! i) \<Longrightarrow>
      Q p \<Longrightarrow> Q (update_matchF ks dss I mr mrs as v p)"
  proof -
    fix as :: "event_data table list" and v and p :: "event_data ml\<delta>aux"
    assume la: "length as = length Ss" and ha: "\<forall>i < length Ss. as ! i \<in> Ss ! i"
      and qp: "Q p"
    have las: "length \<psi>s = length as" using la lSs by simp
    have ops: "list_all2 (\<lambda>\<psi> rel. ftable (Formula.fv_list \<psi>) rel) \<psi>s as"
      using ha lSs las by (auto simp: list_all2_conv_all_nth Ss_def dss_def)
    show "Q (update_matchF ks dss I mr mrs as v p)" unfolding Q_def dss_def
      by (rule mfaux_inv_update[OF _ sr ok A dks d mrs ops fvsub]) (use qp in \<open>simp add: Q_def\<close>)
  qed
  obtain ay1 bf2 nt ns2 where e2:
    "mbufnt_take (update_matchF ks dss I mr mrs) ay bf1 tt (ns @ ts) = (ay1, bf2, nt, ns2)"
    by (cases "mbufnt_take (update_matchF ks dss I mr mrs) ay bf1 tt (ns @ ts)") auto
  have out: "Q ay1 \<and> length bf2 = length bf1 \<and> (\<forall>i < length bf2. set (bf2 ! i) \<subseteq> Ss ! i)"
    by (rule mbufnt_take_out[where Q = Q and f = "update_matchF ks dss I mr mrs" and Ss = Ss,
        OF e2 _ sub1 st]) (use lSs lb1 ay in \<open>simp_all add: Q_def\<close>)
  obtain zs ay2 where e3: "eval_matchF I mr nt ay1 = (zs, ay2)"
    by (cases "eval_matchF I mr nt ay1")
  have ev: "list_all (ftable ks) zs \<and> mfaux_inv ks \<psi>s ay2"
    by (rule eval_matchF_ftable[OF e3]) (use out in \<open>simp add: Q_def\<close>)
  have m: "meval j n ts db (MMatchF I ks dss mr mrs M bf ns tt ay)
      = (zs, MMatchF I ks dss mr mrs (map snd R) bf2 ns2 nt ay2)"
    using e2 e3 unfolding R_def bf1_def
    by (simp add: map_split_alt Let_def del: mbufnt_take.simps eval_matchF.simps)
  have x: "xs = zs" and f: "\<Phi>' = MMatchF I ks dss mr mrs (map snd R) bf2 ns2 nt ay2"
    using e X Phi m by simp_all
  have lM': "length (map snd R) = length \<psi>s" using lR by simp
  have pM': "\<forall>i < length \<psi>s. produces n (dss ! i) (dnext u ts) (map snd R ! i)"
    using nR lR by simp
  have lbf2: "length bf2 = length \<psi>s" using out lb1 by simp
  have pbf2: "\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (bf2 ! i)"
    using out lbf2 ldss by (auto simp: Ss_def list_all_iff subset_eq)
  show "list_all (ftable ks') xs \<and>
      ((n' = n \<and> ks' = ks \<and> (\<exists>M bf ns tt ay. \<Phi>' = MMatchF I ks dss mr mrs M bf ns tt ay \<and>
         length M = length \<psi>s \<and> (\<forall>i < length \<psi>s. produces n (dss ! i) (dnext u ts) (M ! i)) \<and>
         length bf = length \<psi>s \<and> (\<forall>i < length \<psi>s. list_all (ftable (dss ! i)) (bf ! i)) \<and>
         mfaux_inv ks \<psi>s ay)) \<or>
       produces n' ks' (dnext u ts) \<Phi>')"
    using X ev lM' pM' lbf2 pbf2 by (auto simp: x f)
qed

(*<*)
end
(*>*)

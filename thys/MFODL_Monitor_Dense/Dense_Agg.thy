(*<*)
theory Dense_Agg
  imports Dense_Let
begin
(*>*)

section \<open>The aggregated temporal nodes\<close>

text \<open>
  @{thm [source] produces_MSince} and @{thm [source] produces_MUntil} were proved for
  @{term "args_agg args = None"}, the shape a plain \<open>Since\<close> or \<open>Until\<close> is
  initialised with.  The kernel also fuses an aggregation into these two nodes: for
  \<open>Agg y \<omega> tys f (Since \<phi> I \<psi>)\<close> it builds a single @{const mformula.MSince}
  whose @{term args} carry @{term "Some aggargs"}, and the node then evaluates its operands at
  the inner frame @{term "length tys + n"} while emitting tables at the outer frame @{term n}.
  Without this section a criterion for the kernel's initial state could not cover such a formula.

  Only one step of each proof looks at the aggregation: the node's output is
  @{const result_mmasaux} for Since and @{const eval_args_agg} of the evaluated window for Until,
  and in both cases everything before that step is about the auxiliary structure, which does not
  change.  So each proof is generalised over what the output step is asked to deliver -- a
  parameter \<open>Res\<close>, respectively a frame @{term "(nr, Ar)"} -- and the two
  instances follow, the aggregated one from @{thm [source] ftable_eval_agg}, which the
  @{const mformula.MAgg} node already needed.
\<close>

subsection \<open>The Since node, over an arbitrary output frame\<close>

lemma eval_since_ftable_gen:
  fixes args :: args
  assumes an: "args_n args = n"
    and aL: "args_L args = L" and aR: "args_R args = R" and sub: "L \<subseteq> R"
    and res: "\<And>cur' aux'' al. valid_mmasaux args cur' aux'' al \<Longrightarrow>
      (\<forall>(v, rel) \<in> set al. ftable n R rel) \<Longrightarrow> Res (result_mmasaux args aux'')"
  shows "meval_since args rs buf aux = (zs, buf', aux') \<Longrightarrow>
    saux_inv args n L R u buf aux \<Longrightarrow> list_all Res rs \<Longrightarrow>
    list_all Res zs \<and> saux_inv args n L R u buf' aux'"
proof (induction rs buf aux arbitrary: zs buf' aux'
    taking: args rule: default_maux.eval_since.induct)
  case (1 rs x xs t tss skew aux)
  note E = 1(1) and R = 1(2) and Q = 1(3)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist" and cu: "cur \<le> u"
    and wa: "\<forall>(t, rel) \<in> set auxlist. ftable n R rel"
    and lx: "list_all (ftable n L) (x # xs)"
    and st: "sorted (t # tss)" and ct: "\<forall>v \<in> set (t # tss). cur \<le> v \<and> v \<le> u"
    using R by (rule saux_invE)
  have tx: "ftable n L x" using lx by simp
  have ctu: "cur \<le> t" using ct by simp
  show ?case
  proof (cases "skew \<or> memL (args_ivl args) 0")
    case True
    show ?thesis using E R Q True by (auto simp: list_all_iff)
  next
    case False
    let ?wa = "gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)"
    let ?al = "map (\<lambda>(v, rel). (v, join rel (args_pos args) x))
        (filter (\<lambda>(v, rel). memR (args_ivl args) (t - v)) auxlist)"
    have vw': "valid_mmasaux args t ?wa ?al"
      by (rule default_mmasaux.valid_join_msaux
          [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu]]) (use tx an aL in simp)
    have wa': "\<forall>(v, rel) \<in> set ?al. ftable n R rel"
      by (rule fauxlist_join[OF sub tx]) (use wa in auto)
    have EW: "meval_since args rs (x # xs, [], t # tss, skew) aux
        = (rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa)"
      using False by (simp add: Let_def)
    have EE: "(rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa) = (zs, buf', aux')"
      by (rule trans[OF EW[symmetric] E])
    have tr: "Res (result_mmasaux args ?wa)" by (rule res[OF vw' wa'])
    have R': "saux_inv args n L R u (xs, [], tss, True) ?wa"
      by (rule saux_invI[OF vw' _ wa']) (use lx st ct in auto)
    show ?thesis using EE Q tr R' by auto
  qed
next
  case (2 rs xs y ys tss aux)
  note IH = 2(1) and E = 2(2) and R = 2(3) and Q = 2(4)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist" and cu: "cur \<le> u"
    and wa: "\<forall>(t, rel) \<in> set auxlist. ftable n R rel"
    and lx: "list_all (ftable n L) xs" and ly: "list_all (ftable n R) (y # ys)"
    and st: "sorted tss" and ct: "\<forall>v \<in> set tss. cur \<le> v \<and> v \<le> u"
    using R by (rule saux_invE)
  have ty: "ftable n R y" using ly by simp
  let ?al = "case auxlist of [] \<Rightarrow> [(cur, y)]
      | ((v, w) # r) \<Rightarrow> if v = cur then (v, w \<union> y) # r else (cur, y) # auxlist"
  have vw': "valid_mmasaux args cur (add_new_table_mmasaux args y aux) ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vw]) (use ty an aR in simp)
  have wa': "\<forall>(v, rel) \<in> set ?al. ftable n R rel"
    by (rule fauxlist_add_new_table[OF wa ty])
  have E': "meval_since args rs (xs, ys, tss, False) (add_new_table_mmasaux args y aux)
      = (zs, buf', aux')" using E by simp
  have R': "saux_inv args n L R u (xs, ys, tss, False) (add_new_table_mmasaux args y aux)"
    by (rule saux_invI[OF vw' cu wa']) (use lx ly st ct in auto)
  show ?case by (rule IH[OF E' R' Q])
next
  case (3 rs x xs y ys t tss aux)
  note IH = 3(1) and E = 3(2) and R = 3(3) and Q = 3(4)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist" and cu: "cur \<le> u"
    and wa: "\<forall>(v, rel) \<in> set auxlist. ftable n R rel"
    and lx: "list_all (ftable n L) (x # xs)" and ly: "list_all (ftable n R) (y # ys)"
    and st: "sorted (t # tss)" and ct: "\<forall>v \<in> set (t # tss). cur \<le> v \<and> v \<le> u"
    using R by (rule saux_invE)
  have tx: "ftable n L x" using lx by simp
  have ty: "ftable n R y" using ly by simp
  have ctu: "cur \<le> t" using ct by simp
  let ?jl = "map (\<lambda>(v, rel). (v, join rel (args_pos args) x))
      (filter (\<lambda>(v, rel). memR (args_ivl args) (t - v)) auxlist)"
  let ?al = "case ?jl of [] \<Rightarrow> [(t, y)]
      | ((v, w) # r) \<Rightarrow> if v = t then (v, w \<union> y) # r else (t, y) # ?jl"
  let ?wa = "add_new_table_mmasaux args y
      (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux))"
  have vwj: "valid_mmasaux args t (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)) ?jl"
    by (rule default_mmasaux.valid_join_msaux
        [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu]]) (use tx an aL in simp)
  have wj: "\<forall>(v, rel) \<in> set ?jl. ftable n R rel"
    by (rule fauxlist_join[OF sub tx]) (use wa in auto)
  have vw': "valid_mmasaux args t ?wa ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vwj]) (use ty an aR in simp)
  have wa': "\<forall>(v, rel) \<in> set ?al. ftable n R rel"
    by (rule fauxlist_add_new_table[OF wj ty])
  have tr: "Res (result_mmasaux args ?wa)" by (rule res[OF vw' wa'])
  have E': "meval_since args (result_mmasaux args ?wa # rs) (xs, ys, tss, False) ?wa
      = (zs, buf', aux')" using E by (simp add: Let_def)
  have R': "saux_inv args n L R u (xs, ys, tss, False) ?wa"
    by (rule saux_invI[OF vw' _ wa']) (use lx ly st ct in auto)
  have Q': "list_all Res (result_mmasaux args ?wa # rs)" using tr Q by simp
  show ?case by (rule IH[OF refl E' R' Q'])
qed auto

lemma produces_MSince_gen:
  fixes args :: args
  assumes p1: "produces n L tw \<phi>" and p2: "produces n R tw \<psi>"
    and r: "saux_inv args n L R tw buf aux"
    and an: "args_n args = n"
    and aL: "args_L args = L" and aR: "args_R args = R" and sub: "L \<subseteq> R"
    and res: "\<And>cur' aux'' al. valid_mmasaux args cur' aux'' al \<Longrightarrow>
      (\<forall>(v, rel) \<in> set al. ftable n R rel) \<Longrightarrow> ftable nr Ar (result_mmasaux args aux'')"
  shows "produces nr Ar tw (mformula.MSince args \<phi> \<psi> buf aux)"
proof (rule producesI[where X = "\<lambda>n' A' u \<Phi>. n' = nr \<and> A' = Ar \<and>
    (\<exists>\<chi> \<eta> bf ax. \<Phi> = mformula.MSince args \<chi> \<eta> bf ax \<and>
       produces n L u \<chi> \<and> produces n R u \<eta> \<and> saux_inv args n L R u bf ax)"])
  show "nr = nr \<and> Ar = Ar \<and> (\<exists>\<chi> \<eta> bf ax. mformula.MSince args \<phi> \<psi> buf aux
      = mformula.MSince args \<chi> \<eta> bf ax \<and> produces n L tw \<chi> \<and> produces n R tw \<eta> \<and>
      saux_inv args n L R tw bf ax)"
    using p1 p2 r by blast
next
  fix n' A' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = nr \<and> A' = Ar \<and> (\<exists>\<chi> \<eta> bf ax. \<Phi> = mformula.MSince args \<chi> \<eta> bf ax \<and>
      produces n L u \<chi> \<and> produces n R u \<eta> \<and> saux_inv args n L R u bf ax)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. u \<le> t"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> \<eta> bf ax where Phi: "\<Phi> = mformula.MSince args \<chi> \<eta> bf ax"
    and pc: "produces n L u \<chi>" and pe: "produces n R u \<eta>"
    and inv: "saux_inv args n L R u bf ax" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  obtain bs \<eta>' where e2: "meval j n ts db \<eta> = (bs, \<eta>')" by (cases "meval j n ts db \<eta>")
  obtain zs bf' ax' where e3: "meval_since args [] (mbuf2S_add as bs ts bf) ax = (zs, bf', ax')"
    by (cases "meval_since args [] (mbuf2S_add as bs ts bf) ax")
  have x: "xs = zs" and f: "\<Phi>' = mformula.MSince args \<chi>' \<eta>' bf' ax'"
    using e X Phi e1 e2 e3 an by simp_all
  have ta: "list_all (ftable n L) as" by (rule produces_tables[OF pc w sts mts e1])
  have tb: "list_all (ftable n R) bs" by (rule produces_tables[OF pe w sts mts e2])
  have add: "saux_inv args n L R (dnext u ts) (mbuf2S_add as bs ts bf) ax"
    by (rule saux_inv_add[OF inv ta tb sts mts])
  have nil: "list_all (\<lambda>X. table nr Ar X \<and> finite X) []" by simp
  have step: "list_all (ftable nr Ar) zs \<and> saux_inv args n L R (dnext u ts) bf' ax'"
    by (rule eval_since_ftable_gen[where Res = "\<lambda>X. table nr Ar X \<and> finite X",
          OF an aL aR sub res e3 add nil])
  show "list_all (ftable n' A') xs \<and>
      ((n' = nr \<and> A' = Ar \<and>
          (\<exists>\<chi> \<eta> bf ax. \<Phi>' = mformula.MSince args \<chi> \<eta> bf ax \<and>
             produces n L (dnext u ts) \<chi> \<and> produces n R (dnext u ts) \<eta> \<and>
             saux_inv args n L R (dnext u ts) bf ax)) \<or>
       produces n' A' (dnext u ts) \<Phi>')"
    using X step produces_next[OF pc w sts mts e1] produces_next[OF pe w sts mts e2]
    by (auto simp: x f)
qed

subsection \<open>The aggregated output of the two structures\<close>

lemma ftable_result_mmasaux_agg:
  assumes v: "valid_mmasaux args cur aux auxlist"
    and w: "\<forall>(t, rel) \<in> set auxlist. ftable n R rel"
    and agg: "args_agg args = Some aggargs"
    and ty: "n = length (aggargs_tys aggargs) + nr"
    and an': "aggargs_n aggargs = nr" and y: "aggargs_y aggargs < nr"
    and g0: "aggargs_g0 aggargs \<Longrightarrow> R \<subseteq> {0..<length (aggargs_tys aggargs)}"
  shows "ftable nr (Set.insert (aggargs_y aggargs)
      ((\<lambda>i. i - length (aggargs_tys aggargs))
        ` (R - {0..<length (aggargs_tys aggargs)}))) (result_mmasaux args aux)"
proof -
  have f: "ftable n R (foldr (\<union>)
      [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
    by (rule ftable_foldr_Un[OF w])
  have e: "result_mmasaux args aux = eval_aggargs aggargs
      (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
    using default_mmasaux.valid_result_msaux[OF v] by (simp add: eval_args_agg_def agg)
  show ?thesis unfolding e eval_aggargs_def an'
    by (rule ftable_eval_agg[OF _ _ y g0]) (use f ty in auto)
qed

lemma ftable_eval_args_agg:
  assumes agg: "args_agg args = Some aggargs"
    and ty: "n = length (aggargs_tys aggargs) + nr"
    and an': "aggargs_n aggargs = nr" and y: "aggargs_y aggargs < nr"
    and g0: "aggargs_g0 aggargs \<Longrightarrow> R \<subseteq> {0..<length (aggargs_tys aggargs)}"
    and f: "ftable n R X"
  shows "ftable nr (Set.insert (aggargs_y aggargs)
      ((\<lambda>i. i - length (aggargs_tys aggargs))
        ` (R - {0..<length (aggargs_tys aggargs)}))) (eval_args_agg args X)"
proof -
  have e: "eval_args_agg args X = eval_agg nr (aggargs_g0 aggargs) (aggargs_y aggargs)
      (aggargs_\<omega> aggargs) (aggargs_tys aggargs) (aggargs_f aggargs) X"
    by (simp add: eval_args_agg_def agg eval_aggargs_def an')
  show ?thesis unfolding e
    by (rule ftable_eval_agg[OF _ _ y g0]) (use f ty in auto)
qed

lemma produces_MSince_agg:
  fixes args :: args
  assumes p1: "produces n L tw \<phi>" and p2: "produces n R tw \<psi>"
    and r: "saux_inv args n L R tw buf aux"
    and an: "args_n args = n"
    and aL: "args_L args = L" and aR: "args_R args = R" and sub: "L \<subseteq> R"
    and agg: "args_agg args = Some aggargs"
    and ty: "n = length (aggargs_tys aggargs) + nr"
    and an': "aggargs_n aggargs = nr" and y: "aggargs_y aggargs < nr"
    and g0: "aggargs_g0 aggargs \<Longrightarrow> R \<subseteq> {0..<length (aggargs_tys aggargs)}"
  shows "produces nr (Set.insert (aggargs_y aggargs)
      ((\<lambda>i. i - length (aggargs_tys aggargs))
        ` (R - {0..<length (aggargs_tys aggargs)}))) tw (mformula.MSince args \<phi> \<psi> buf aux)"
proof (rule produces_MSince_gen[OF p1 p2 r an aL aR sub])
  fix cur' aux'' al
  assume "valid_mmasaux args cur' aux'' al"
    and "\<forall>(v, rel) \<in> set al. ftable n R rel"
  then show "ftable nr (Set.insert (aggargs_y aggargs)
      ((\<lambda>i. i - length (aggargs_tys aggargs))
        ` (R - {0..<length (aggargs_tys aggargs)}))) (result_mmasaux args aux'')"
    by (rule ftable_result_mmasaux_agg[OF _ _ agg ty an' y g0])
qed

subsection \<open>The Until node, over an arbitrary output frame\<close>

lemma uaux_inv_eval_gen:
  assumes v: "uaux_inv args n L R cur aux" and nt: "cur \<le> nt"
    and res: "\<And>X. ftable n R X \<Longrightarrow> ftable nr Ar (eval_args_agg args X)"
    and we: "eval_muaux_dq args nt aux = (zs, aux')"
  shows "list_all (ftable nr Ar) zs \<and> uaux_inv args n L R cur aux'"
proof -
  obtain auxlist where vw: "valid_muaux_dq args cur aux auxlist"
    and wf: "\<forall>(t, a1, a2) \<in> set auxlist. ftable n L a1 \<and> ftable n R a2"
    using v unfolding uaux_inv_def by blast
  obtain resl auxlist' where eu: "eval_until (args_ivl args) nt auxlist = (resl, auxlist')"
    by (cases "eval_until (args_ivl args) nt auxlist")
  have w: "valid_muaux_dq args cur aux' auxlist' \<and> zs = map (eval_args_agg args) resl"
    by (rule valid_eval_muaux_dq[OF vw nt we eu])
  have u: "list_all (ftable n R) resl \<and>
      (\<forall>(t, a1, a2) \<in> set auxlist'. ftable n L a1 \<and> ftable n R a2)"
    by (rule eval_until_ftable[OF eu wf])
  have zs: "zs = map (eval_args_agg args) resl" using w by simp
  have lz: "list_all (ftable nr Ar) zs" unfolding zs list_all_iff
  proof
    fix X assume "X \<in> set (map (eval_args_agg args) resl)"
    then obtain Y where Y: "Y \<in> set resl" and X: "X = eval_args_agg args Y" by auto
    have "ftable n R Y" using u Y by (simp add: list_all_iff)
    then show "ftable nr Ar X" unfolding X by (rule res)
  qed
  have iv: "uaux_inv args n L R cur aux'" using w u unfolding uaux_inv_def by blast
  show ?thesis using lz iv by simp
qed

lemma until_step_ftable_gen:
  fixes args :: args
  assumes sub: "L \<subseteq> R" and an: "args_n args = n"
    and aL: "args_L args = L" and aR: "args_R args = R"
    and res: "\<And>X. ftable n R X \<Longrightarrow> ftable nr Ar (eval_args_agg args X)"
    and rel: "until_inv args n L R u t aux buf nts"
    and ta: "list_all (ftable n L) as" and tb: "list_all (ftable n R) bs"
    and s: "sorted tss" and bnd: "\<forall>v \<in> set tss. u \<le> v"
    and we: "mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add as bs buf) t (nts @ tss)
      = (aux1, buf1, nt, nts1)"
    and wev: "eval_muaux_dq args nt aux1 = (zs, aux2)"
  shows "list_all (ftable nr Ar) zs \<and> until_inv args n L R (dnext u tss) nt aux2 buf1 nts1"
proof -
  obtain cur where vr: "uaux_inv args n L R cur aux" and ct: "cur \<le> t" and ttw: "t \<le> u"
    and lu: "list_all (ftable n L) (fst buf)"
    and lv: "list_all (ftable n R) (snd buf)"
    and sn: "sorted nts" and cn: "\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> u"
    using rel unfolding until_inv_def by blast
  obtain b1 b2 where bfs: "buf1 = (b1, b2)" by (cases buf1)
  define us where "us = fst buf @ as"
  define vs where "vs = snd buf @ bs"
  have ma: "mbuf2_add as bs buf = (us, vs)" by (cases buf) (simp add: us_def vs_def)
  have lus: "list_all (ftable n L) us" using lu ta by (simp add: us_def)
  have lvs: "list_all (ftable n R) vs" using lv tb by (simp add: vs_def)
  have step: "\<And>a b v w z. a \<in> set us \<Longrightarrow> b \<in> set vs \<Longrightarrow>
      uaux_inv args n L R w z \<Longrightarrow> w \<le> v \<Longrightarrow>
      uaux_inv args n L R v (add_new_muaux_dq args a b v z)"
    using lus lvs by (intro uaux_inv_step[OF _ sub an aL aR]) (auto simp: list_all_iff)
  have sts: "sorted (nts @ tss)"
    using sn s cn bnd by (fastforce simp: sorted_append intro: order_trans)
  have cts: "\<forall>v \<in> set (nts @ tss). cur \<le> v" using cn bnd ct ttw by fastforce
  have tdn: "t \<le> dnext u tss" using ttw dnext_ge[OF bnd] by simp
  have bound: "\<forall>v \<in> set (nts @ tss). v \<le> dnext u tss"
    using cn dnext_ge[OF bnd] dnext_bound[OF s] by fastforce
  have we': "mbuf2t_take (add_new_muaux_dq args) aux (us, vs) t (nts @ tss)
      = (aux1, (b1, b2), nt, nts1)" using we unfolding ma bfs by simp
  have Rr: "(\<exists>v. uaux_inv args n L R v aux1 \<and> v \<le> nt \<and> (\<forall>w \<in> set nts1. v \<le> w)) \<and>
      sorted nts1 \<and> (nt = t \<or> nt \<in> set (nts @ tss)) \<and> set nts1 \<subseteq> set (nts @ tss)"
    by (rule mbuf2t_take_inv[OF step vr ct sts cts we'])
  obtain v where vu: "uaux_inv args n L R v aux1" and unt: "v \<le> nt"
    and un: "\<forall>w \<in> set nts1. v \<le> w" using Rr by blast
  have sn1: "sorted nts1" and sub1: "set nts1 \<subseteq> set (nts @ tss)" using Rr by blast+
  have ntdn: "nt \<le> dnext u tss" using Rr tdn bound by blast
  have ev: "list_all (ftable nr Ar) zs \<and> uaux_inv args n L R v aux2"
    by (rule uaux_inv_eval_gen[OF vu unt res wev])
  have sb: "set b1 \<subseteq> set us \<and> set b2 \<subseteq> set vs" by (rule mbuf2t_take_sub[OF we'])
  have lb1: "list_all (ftable n L) b1" using sb lus by (auto simp: list_all_iff)
  have lb2: "list_all (ftable n R) b2" using sb lvs by (auto simp: list_all_iff)
  have "uaux_inv args n L R v aux2 \<and> v \<le> nt \<and> nt \<le> dnext u tss \<and>
      list_all (ftable n L) (fst buf1) \<and> list_all (ftable n R) (snd buf1) \<and>
      sorted nts1 \<and> (\<forall>w \<in> set nts1. v \<le> w \<and> w \<le> dnext u tss)"
    using ev unt ntdn lb1 lb2 sn1 un sub1 bound bfs by auto
  then have "until_inv args n L R (dnext u tss) nt aux2 buf1 nts1"
    unfolding until_inv_def by blast
  then show ?thesis using ev by simp
qed

lemma produces_MUntil_gen:
  fixes args :: args
  assumes p1: "produces n L tw \<phi>" and p2: "produces n R tw \<psi>"
    and r: "until_inv args n L R tw t aux buf nts"
    and an: "args_n args = n"
    and aL: "args_L args = L" and aR: "args_R args = R" and sub: "L \<subseteq> R"
    and res: "\<And>X. ftable n R X \<Longrightarrow> ftable nr Ar (eval_args_agg args X)"
  shows "produces nr Ar tw (mformula.MUntil args \<phi> \<psi> buf nts t aux)"
proof (rule producesI[where X = "\<lambda>n' A' u \<Phi>. n' = nr \<and> A' = Ar \<and>
    (\<exists>\<chi> \<eta> bf ns tt ax. \<Phi> = mformula.MUntil args \<chi> \<eta> bf ns tt ax \<and>
       produces n L u \<chi> \<and> produces n R u \<eta> \<and>
       until_inv args n L R u tt ax bf ns)"])
  show "nr = nr \<and> Ar = Ar \<and> (\<exists>\<chi> \<eta> bf ns tt ax.
      mformula.MUntil args \<phi> \<psi> buf nts t aux = mformula.MUntil args \<chi> \<eta> bf ns tt ax \<and>
      produces n L tw \<chi> \<and> produces n R tw \<eta> \<and> until_inv args n L R tw tt ax bf ns)"
    using p1 p2 r by blast
next
  fix n' A' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = nr \<and> A' = Ar \<and> (\<exists>\<chi> \<eta> bf ns tt ax.
      \<Phi> = mformula.MUntil args \<chi> \<eta> bf ns tt ax \<and>
      produces n L u \<chi> \<and> produces n R u \<eta> \<and> until_inv args n L R u tt ax bf ns)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>v \<in> set ts. u \<le> v"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<chi> \<eta> bf ns tt ax where Phi: "\<Phi> = mformula.MUntil args \<chi> \<eta> bf ns tt ax"
    and pc: "produces n L u \<chi>" and pe: "produces n R u \<eta>"
    and inv: "until_inv args n L R u tt ax bf ns" by blast
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  obtain bs \<eta>' where e2: "meval j n ts db \<eta> = (bs, \<eta>')" by (cases "meval j n ts db \<eta>")
  obtain ax1 bf1 nt ns1 where e3:
    "mbuf2t_take (add_new_muaux_dq args) ax (mbuf2_add as bs bf) tt (ns @ ts)
       = (ax1, bf1, nt, ns1)"
    by (cases "mbuf2t_take (add_new_muaux_dq args) ax (mbuf2_add as bs bf) tt (ns @ ts)")
      auto
  obtain zs ax2 where e4: "eval_muaux_dq args nt ax1 = (zs, ax2)"
    by (cases "eval_muaux_dq args nt ax1")
  have x: "xs = zs" and f: "\<Phi>' = mformula.MUntil args \<chi>' \<eta>' bf1 ns1 nt ax2"
    using e X Phi e1 e2 e3 e4 an by simp_all
  have ta: "list_all (ftable n L) as" by (rule produces_tables[OF pc w sts mts e1])
  have tb: "list_all (ftable n R) bs" by (rule produces_tables[OF pe w sts mts e2])
  have step: "list_all (ftable nr Ar) zs \<and>
      until_inv args n L R (dnext u ts) nt ax2 bf1 ns1"
    by (rule until_step_ftable_gen[OF sub an aL aR res inv ta tb sts mts e3 e4])
  show "list_all (ftable n' A') xs \<and>
      ((n' = nr \<and> A' = Ar \<and>
          (\<exists>\<chi> \<eta> bf ns tt ax. \<Phi>' = mformula.MUntil args \<chi> \<eta> bf ns tt ax \<and>
             produces n L (dnext u ts) \<chi> \<and> produces n R (dnext u ts) \<eta> \<and>
             until_inv args n L R (dnext u ts) tt ax bf ns)) \<or>
       produces n' A' (dnext u ts) \<Phi>')"
    using X step produces_next[OF pc w sts mts e1] produces_next[OF pe w sts mts e2]
    by (auto simp: x f)
qed

lemma produces_MUntil_agg:
  fixes args :: args
  assumes p1: "produces n L tw \<phi>" and p2: "produces n R tw \<psi>"
    and r: "until_inv args n L R tw t aux buf nts"
    and an: "args_n args = n"
    and aL: "args_L args = L" and aR: "args_R args = R" and sub: "L \<subseteq> R"
    and agg: "args_agg args = Some aggargs"
    and ty: "n = length (aggargs_tys aggargs) + nr"
    and an': "aggargs_n aggargs = nr" and y: "aggargs_y aggargs < nr"
    and g0: "aggargs_g0 aggargs \<Longrightarrow> R \<subseteq> {0..<length (aggargs_tys aggargs)}"
  shows "produces nr (Set.insert (aggargs_y aggargs)
      ((\<lambda>i. i - length (aggargs_tys aggargs))
        ` (R - {0..<length (aggargs_tys aggargs)}))) tw
      (mformula.MUntil args \<phi> \<psi> buf nts t aux)"
  by (rule produces_MUntil_gen[OF p1 p2 r an aL aR sub
        ftable_eval_args_agg[OF agg ty an' y g0]])

subsection \<open>Triggers whose interval does not contain zero\<close>

text \<open>
  The node lemma for a fused conjunction with a trigger on the right assumed that the trigger's
  interval contains zero, because only then does the trigger structure always report the right
  operand's column set.  When the interval does not contain zero, a safe trigger has the same
  free variables on both sides, and the structure reports either that column set or, on an empty
  window, the empty one together with the unit table.  Either way the reported column set is
  contained in the right operand's, which is all the following join needs: the join is against a
  table over a subset of the conjunction's columns, so the result is still a table over them.
  The lemmas below are the corresponding weakenings, with the fixed column set @{term R} in the
  buffer invariant replaced by a bound.
\<close>

lemma taux_inv_step_weak:
  fixes args :: args
  assumes v: "taux_inv args n L R u aux"
    and an: "args_n args = n" and aL: "args_L args = L" and aR: "args_R args = R"
    and wkc: "mem (args_ivl args) 0 \<or> (args_pos args \<and> L = R)"
    and t1: "ftable n L a" and t2: "ftable n R b" and ut: "u \<le> t"
  shows "taux_inv args n L R t (update_mmtaux args t a b aux) \<and>
     ftable n (fst (result_mmtaux args (update_mmtaux args t a b aux)))
       (snd (result_mmtaux args (update_mmtaux args t a b aux))) \<and>
     fst (result_mmtaux args (update_mmtaux args t a b aux)) \<subseteq> R"
proof -
  obtain auxlist where vw: "valid_mmtaux args u aux auxlist"
    and wf: "\<forall>(v, l, r) \<in> set auxlist. ftable n L l \<and> ftable n R r"
    using v unfolding taux_inv_def by blast
  define al where "al = filter (\<lambda>(v, _). memR (args_ivl args) (t - v)) auxlist @ [(t, a, b)]"
  have vw': "valid_mmtaux args t (update_mmtaux args t a b aux) al"
    unfolding al_def by (rule valid_update_mmtaux[OF ut _ _ vw]) (use t1 t2 an aL aR in simp_all)
  have wf': "\<forall>(v, l, r) \<in> set al. ftable n L l \<and> ftable n R r"
    using wf t1 t2 unfolding al_def by auto
  have ne: "al \<noteq> []" by (simp add: al_def)
  have lst: "fst (last al) = t" by (simp add: al_def)
  have ftr: "ftable n (fst (trigger_results args t al)) (snd (trigger_results args t al)) \<and>
      fst (trigger_results args t al) \<subseteq> R"
    by (rule ftable_trigger_results_weak[OF wf' ne lst an aL aR wkc])
  have res: "result_mmtaux args (update_mmtaux args t a b aux) = trigger_results args t al"
    by (rule valid_result_mmtaux[OF vw'])
  have "taux_inv args n L R t (update_mmtaux args t a b aux)"
    unfolding taux_inv_def using vw' wf' by blast
  then show ?thesis using ftr unfolding res by simp
qed

lemma trigger_pairs_step_weak:
  fixes args :: args
  assumes an: "args_n args = n" and aL: "args_L args = L" and aR: "args_R args = R"
    and wkc: "mem (args_ivl args) 0 \<or> (args_pos args \<and> L = R)"
    and rel: "trigger_inv args n L R u aux buf nts"
    and ta: "list_all (ftable n L) as" and tb: "list_all (ftable n R) bs"
    and s: "sorted tss" and bnd: "\<forall>v \<in> set tss. u \<le> v"
    and we: "mbuf2T_take (\<lambda>r1 r2 t (zs, aux).
        let aux = update_mmtaux args t r1 r2 aux; (fv_z, z) = result_mmtaux args aux
        in (zs @ [(fv_z, z)], aux)) ([], aux) (mbuf2_add as bs buf) (nts @ tss)
      = ((zs, aux1), buf1, nts1)"
  shows "list_all (\<lambda>p. fst p \<subseteq> R \<and> ftable n (fst p) (snd p)) zs \<and>
     trigger_inv args n L R (dnext u tss) aux1 buf1 nts1"
proof -
  obtain cur where vr: "taux_inv args n L R cur aux" and ct: "cur \<le> u"
    and lu: "list_all (ftable n L) (fst buf)"
    and lv: "list_all (ftable n R) (snd buf)"
    and sn: "sorted nts" and cn: "\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> u"
    using rel unfolding trigger_inv_def by blast
  obtain b1 b2 where bfs: "buf1 = (b1, b2)" by (cases buf1)
  define us where "us = fst buf @ as"
  define vs where "vs = snd buf @ bs"
  define g where "g = (\<lambda>r1 r2 t (zs :: (nat set \<times> event_data table) list, ax).
    let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
    in (zs @ [(fv_z, z)], ax))"
  define Q where "Q = (\<lambda>v (pr :: (nat set \<times> event_data table) list \<times> event_data mmtaux).
    list_all (\<lambda>p. fst p \<subseteq> R \<and> ftable n (fst p) (snd p)) (fst pr) \<and>
      taux_inv args n L R v (snd pr))"
  have ma: "mbuf2_add as bs buf = (us, vs)" by (cases buf) (simp add: us_def vs_def)
  have lus: "list_all (ftable n L) us" using lu ta by (simp add: us_def)
  have lvs: "list_all (ftable n R) vs" using lv tb by (simp add: vs_def)
  have step: "\<And>a b v w z. a \<in> set us \<Longrightarrow> b \<in> set vs \<Longrightarrow> Q w z \<Longrightarrow> w \<le> v \<Longrightarrow>
      Q v (g a b v z)"
  proof -
    fix a b v w and z :: "(nat set \<times> event_data table) list \<times> event_data mmtaux"
    assume au: "a \<in> set us" and bv: "b \<in> set vs" and q: "Q w z" and wv: "w \<le> v"
    have t1: "ftable n L a" using au lus by (simp add: list_all_iff)
    have t2: "ftable n R b" using bv lvs by (simp add: list_all_iff)
    have "taux_inv args n L R v (update_mmtaux args v a b (snd z)) \<and>
        ftable n (fst (result_mmtaux args (update_mmtaux args v a b (snd z))))
          (snd (result_mmtaux args (update_mmtaux args v a b (snd z)))) \<and>
        fst (result_mmtaux args (update_mmtaux args v a b (snd z))) \<subseteq> R"
      by (rule taux_inv_step_weak[OF _ an aL aR wkc t1 t2 wv]) (use q in \<open>simp add: Q_def\<close>)
    then show "Q v (g a b v z)" using q
      by (cases z) (auto simp: Q_def g_def Let_def split: prod.splits)
  qed
  have sts: "sorted (nts @ tss)"
    using sn s cn bnd by (fastforce simp: sorted_append intro: order_trans)
  have cts: "\<forall>v \<in> set (nts @ tss). cur \<le> v" using cn bnd ct by fastforce
  have bound: "\<forall>v \<in> set (nts @ tss). v \<le> dnext u tss"
    using cn dnext_ge[OF bnd] dnext_bound[OF s] by fastforce
  have cdn: "cur \<le> dnext u tss" using ct dnext_ge[OF bnd] by simp
  have q0: "Q cur ([], aux)" using vr by (simp add: Q_def)
  have we': "mbuf2T_take g ([], aux) (us, vs) (nts @ tss) = ((zs, aux1), (b1, b2), nts1)"
    using we unfolding ma bfs g_def by simp
  have Rr: "(\<exists>v. Q v (zs, aux1) \<and> v \<le> dnext u tss \<and> (\<forall>w \<in> set nts1. v \<le> w)) \<and>
      sorted nts1 \<and> set nts1 \<subseteq> set (nts @ tss) \<and> set b1 \<subseteq> set us \<and> set b2 \<subseteq> set vs"
    by (rule mbuf2T_take_inv[where Q = Q and f = g and xs = us and ys = vs,
        OF step q0 sts cts bound cdn we'])
  obtain v where qv: "Q v (zs, aux1)" and vb: "v \<le> dnext u tss"
    and un: "\<forall>w \<in> set nts1. v \<le> w" using Rr by blast
  have sn1: "sorted nts1" and sb1: "set b1 \<subseteq> set us" and sb2: "set b2 \<subseteq> set vs"
    and sub1: "set nts1 \<subseteq> set (nts @ tss)" using Rr by blast+
  have lb1: "list_all (ftable n L) b1" using sb1 lus by (auto simp: list_all_iff)
  have lb2: "list_all (ftable n R) b2" using sb2 lvs by (auto simp: list_all_iff)
  have tz: "list_all (\<lambda>p. fst p \<subseteq> R \<and> ftable n (fst p) (snd p)) zs"
    using qv by (simp add: Q_def)
  have "taux_inv args n L R v aux1 \<and> v \<le> dnext u tss \<and>
      list_all (ftable n L) (fst buf1) \<and> list_all (ftable n R) (snd buf1) \<and>
      sorted nts1 \<and> (\<forall>w \<in> set nts1. v \<le> w \<and> w \<le> dnext u tss)"
    using qv vb lb1 lb2 sn1 un sub1 bound bfs by (auto simp: Q_def)
  then have "trigger_inv args n L R (dnext u tss) aux1 buf1 nts1"
    unfolding trigger_inv_def by blast
  then show ?thesis using tz by simp
qed

lemma produces_MAndTrigger_weak:
  fixes args :: args
  assumes pa: "produces n A tw \<alpha>" and p1: "produces n L tw \<phi>" and p2: "produces n R tw \<psi>"
    and r: "trigger_inv args n L R tw aux buf2 nts"
    and b1a: "list_all (ftable n A) (fst buf1)"
    and b1b: "list_all (\<lambda>p. fst p \<subseteq> R \<and> ftable n (fst p) (snd p)) (snd buf1)"
    and an: "args_n args = n" and aL: "args_L args = L" and aR: "args_R args = R"
    and wkc: "mem (args_ivl args) 0 \<or> (args_pos args \<and> L = R)" and sub: "R \<subseteq> A"
  shows "produces n A tw (mformula.MAndTrigger A \<alpha> buf1 args \<phi> \<psi> buf2 nts aux)"
proof (rule producesI[where X = "\<lambda>n' A' u \<Phi>. n' = n \<and> A' = A \<and>
    (\<exists>\<alpha>' \<chi> \<eta> c1 c2 ns ax. \<Phi> = mformula.MAndTrigger A \<alpha>' c1 args \<chi> \<eta> c2 ns ax \<and>
       produces n A u \<alpha>' \<and> produces n L u \<chi> \<and> produces n R u \<eta> \<and>
       trigger_inv args n L R u ax c2 ns \<and>
       list_all (ftable n A) (fst c1) \<and>
       list_all (\<lambda>p. fst p \<subseteq> R \<and> ftable n (fst p) (snd p)) (snd c1))"])
  show "n = n \<and> A = A \<and> (\<exists>\<alpha>' \<chi> \<eta> c1 c2 ns ax.
      mformula.MAndTrigger A \<alpha> buf1 args \<phi> \<psi> buf2 nts aux
        = mformula.MAndTrigger A \<alpha>' c1 args \<chi> \<eta> c2 ns ax \<and>
      produces n A tw \<alpha>' \<and> produces n L tw \<chi> \<and> produces n R tw \<eta> \<and>
      trigger_inv args n L R tw ax c2 ns \<and> list_all (ftable n A) (fst c1) \<and>
      list_all (\<lambda>p. fst p \<subseteq> R \<and> ftable n (fst p) (snd p)) (snd c1))"
    using pa p1 p2 r b1a b1b by blast
next
  fix n' A' u \<Phi> j ts db xs \<Phi>'
  assume X: "n' = n \<and> A' = A \<and>
      (\<exists>\<alpha>' \<chi> \<eta> c1 c2 ns ax. \<Phi> = mformula.MAndTrigger A \<alpha>' c1 args \<chi> \<eta> c2 ns ax \<and>
         produces n A u \<alpha>' \<and> produces n L u \<chi> \<and> produces n R u \<eta> \<and>
         trigger_inv args n L R u ax c2 ns \<and> list_all (ftable n A) (fst c1) \<and>
         list_all (\<lambda>p. fst p \<subseteq> R \<and> ftable n (fst p) (snd p)) (snd c1))"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>v \<in> set ts. u \<le> v"
    and e: "meval j n' ts db \<Phi> = (xs, \<Phi>')"
  from X obtain \<alpha>' \<chi> \<eta> c1 c2 ns ax
    where Phi: "\<Phi> = mformula.MAndTrigger A \<alpha>' c1 args \<chi> \<eta> c2 ns ax"
      and pal: "produces n A u \<alpha>'" and pc: "produces n L u \<chi>" and pe: "produces n R u \<eta>"
      and inv: "trigger_inv args n L R u ax c2 ns"
      and lc1: "list_all (ftable n A) (fst c1)"
      and lc2: "list_all (\<lambda>p. fst p \<subseteq> R \<and> ftable n (fst p) (snd p)) (snd c1)" by blast
  obtain aas \<alpha>2 where e0: "meval j n ts db \<alpha>' = (aas, \<alpha>2)"
    by (cases "meval j n ts db \<alpha>'")
  obtain as \<chi>' where e1: "meval j n ts db \<chi> = (as, \<chi>')" by (cases "meval j n ts db \<chi>")
  obtain bs \<eta>' where e2: "meval j n ts db \<eta> = (bs, \<eta>')" by (cases "meval j n ts db \<eta>")
  obtain zt ax1 d2 ns1 where e3: "mbuf2T_take (\<lambda>r1 r2 t (zs, aux).
      let aux = update_mmtaux args t r1 r2 aux; (fv_z, z) = result_mmtaux args aux
      in (zs @ [(fv_z, z)], aux)) ([], ax) (mbuf2_add as bs c2) (ns @ ts)
        = ((zt, ax1), d2, ns1)"
    by (cases "mbuf2T_take (\<lambda>r1 r2 t (zs, aux).
      let aux = update_mmtaux args t r1 r2 aux; (fv_z, z) = result_mmtaux args aux
      in (zs @ [(fv_z, z)], aux)) ([], ax) (mbuf2_add as bs c2) (ns @ ts)") auto
  obtain zs d1 where e4: "mbuf2_take (\<lambda>r1 (V, r2). bin_join n A r1 True V r2)
      (mbuf2_add aas zt c1) = (zs, d1)"
    by (cases "mbuf2_take (\<lambda>r1 (V, r2). bin_join n A r1 True V r2)
      (mbuf2_add aas zt c1)")
  have x: "xs = zs" and f: "\<Phi>' = mformula.MAndTrigger A \<alpha>2 d1 args \<chi>' \<eta>' d2 ns1 ax1"
    using e X Phi e0 e1 e2 e3 e4 by (simp_all del: bin_join.simps)
  have taa: "list_all (ftable n A) aas" by (rule produces_tables[OF pal w sts mts e0])
  have ta: "list_all (ftable n L) as" by (rule produces_tables[OF pc w sts mts e1])
  have tb: "list_all (ftable n R) bs" by (rule produces_tables[OF pe w sts mts e2])
  have tstep: "list_all (\<lambda>p. fst p \<subseteq> R \<and> ftable n (fst p) (snd p)) zt \<and>
      trigger_inv args n L R (dnext u ts) ax1 d2 ns1"
    by (rule trigger_pairs_step_weak[OF an aL aR wkc inv ta tb sts mts e3])
  have add: "mbuf2_add aas zt c1 = (fst c1 @ aas, snd c1 @ zt)" by (cases c1) simp
  have la: "list_all (ftable n A) (fst c1 @ aas)" using lc1 taa by simp
  have lb: "list_all (\<lambda>p. fst p \<subseteq> R \<and> ftable n (fst p) (snd p)) (snd c1 @ zt)"
    using lc2 tstep by simp
  have e4': "mbuf2_take (\<lambda>r1 (V, r2). bin_join n A r1 True V r2)
      (fst c1 @ aas, snd c1 @ zt) = (zs, d1)" using e4 unfolding add by simp
  have jt: "\<And>a p. a \<in> set (fst c1 @ aas) \<Longrightarrow> p \<in> set (snd c1 @ zt) \<Longrightarrow>
      ftable n A ((\<lambda>r1 (V, r2). bin_join n A r1 True V r2) a p)"
  proof -
    fix a and p :: "nat set \<times> event_data table"
    assume ma: "a \<in> set (fst c1 @ aas)" and mp: "p \<in> set (snd c1 @ zt)"
    have tA: "ftable n A a" using ma la by (simp add: list_all_iff)
    have pR: "fst p \<subseteq> R" and tR: "ftable n (fst p) (snd p)"
      using mp lb by (auto simp: list_all_iff)
    have sA: "fst p \<subseteq> A" using pR sub by simp
    have "ftable n A (bin_join n A a True (fst p) (snd p))"
      by (rule ftable_bin_join[OF tA tR]) (use sA in auto)
    then show "ftable n A ((\<lambda>r1 (V, r2). bin_join n A r1 True V r2) a p)"
      by (cases p) simp
  qed
  have tz: "list_all (ftable n A) zs"
    by (rule mbuf2_take_out[where P = "\<lambda>X :: event_data table. table n A X \<and> finite X"
        and f = "\<lambda>r1 (V, r2). bin_join n A r1 True V r2", OF e4' jt])
  have sb: "set (fst d1) \<subseteq> set (fst c1 @ aas) \<and> set (snd d1) \<subseteq> set (snd c1 @ zt)"
  proof -
    obtain dd1 dd2 where d: "d1 = (dd1, dd2)" by (cases d1)
    have "mbuf2_take (\<lambda>r1 (V, r2). bin_join n A r1 True V r2)
        (fst c1 @ aas, snd c1 @ zt) = (zs, dd1, dd2)" using e4' d by simp
    from mbuf2_take_sub[OF this] show ?thesis using d by simp
  qed
  have ld1: "list_all (ftable n A) (fst d1)" using sb la by (auto simp: list_all_iff)
  have ld2: "list_all (\<lambda>p. fst p \<subseteq> R \<and> ftable n (fst p) (snd p)) (snd d1)"
    using sb lb by (auto simp: list_all_iff)
  show "list_all (ftable n' A') xs \<and>
      ((n' = n \<and> A' = A \<and>
          (\<exists>\<alpha>' \<chi> \<eta> c1 c2 ns ax. \<Phi>' = mformula.MAndTrigger A \<alpha>' c1 args \<chi> \<eta> c2 ns ax \<and>
             produces n A (dnext u ts) \<alpha>' \<and> produces n L (dnext u ts) \<chi> \<and>
             produces n R (dnext u ts) \<eta> \<and>
             trigger_inv args n L R (dnext u ts) ax c2 ns \<and>
             list_all (ftable n A) (fst c1) \<and>
             list_all (\<lambda>p. fst p \<subseteq> R \<and> ftable n (fst p) (snd p)) (snd c1))) \<or>
       produces n' A' (dnext u ts) \<Phi>')"
    using X tz tstep ld1 ld2 produces_next[OF pal w sts mts e0]
      produces_next[OF pc w sts mts e1] produces_next[OF pe w sts mts e2]
    by (auto simp: x f)
qed

(*<*)
end
(*>*)

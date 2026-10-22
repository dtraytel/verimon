(*<*)
theory Abstract_Monitor
  imports Trace Table
begin
(*>*)

section \<open>Abstract monitors and slicing\<close>

subsection \<open>First-order specifications\<close>

text \<open>A specification is abstracted to its free variables and its satisfaction relation over
  traces, valuations and time-points, restricted to a set of traces.\<close>

locale fo_spec =
  fixes
    nfv :: nat and cols :: "nat list" and
    traces :: "'a trace set" and
    sat :: "'a trace \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> bool"
  assumes
    distinct_cols: "distinct cols" and
    fv_less_nfv: "x \<in> set cols \<Longrightarrow> x < nfv" and
    sat_fv_cong: "\<sigma> \<in> traces \<Longrightarrow> (\<And>x. x \<in> set cols \<Longrightarrow> v!x = v'!x) \<Longrightarrow> sat \<sigma> v i = sat \<sigma> v' i"
begin

definition verdicts :: "'a trace \<Rightarrow> (nat \<times> 'b tuple) set" where
  "verdicts \<sigma> = {(i, v). wf_tuple cols v \<and> sat \<sigma> (val nfv cols v) i}"

definition prefixes :: "'a prefix set" where
  "prefixes = {\<pi>. \<exists>\<sigma> \<in> traces. prefix_of \<pi> \<sigma>}"

lemma prefix_of_trace[simp, intro]: "\<sigma> \<in> traces \<Longrightarrow> prefix_of \<pi> \<sigma> \<Longrightarrow> \<pi> \<in> prefixes"
  by (auto simp: prefixes_def)

lemma prefixes_closed[simp, intro]: "\<pi>' \<in> prefixes \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> \<pi> \<in> prefixes"
  using prefix_of_antimono by (auto simp: prefixes_def)

end

text \<open>Monitors see only finite prefixes; co-safety ensures that every satisfaction is witnessed
  by one.\<close>

locale cosafety_fo_spec = fo_spec +
  assumes cosafety_lr: "\<sigma> \<in> traces \<Longrightarrow> sat \<sigma> v i \<Longrightarrow>
    \<exists>\<pi>. prefix_of \<pi> \<sigma> \<and> (\<forall>\<sigma>' \<in> traces. prefix_of \<pi> \<sigma>' \<longrightarrow> sat \<sigma>' v i)"
begin

lemma cosafety: "\<sigma> \<in> traces \<Longrightarrow>
  sat \<sigma> v i \<longleftrightarrow> (\<exists>\<pi>. prefix_of \<pi> \<sigma> \<and> (\<forall>\<sigma>' \<in> traces. prefix_of \<pi> \<sigma>' \<longrightarrow> sat \<sigma>' v i))"
  using cosafety_lr by blast

end

subsection \<open>Monitor functions\<close>

locale monitor = fo_spec +
  fixes M :: "'a prefix \<Rightarrow> (nat \<times> 'b tuple) set"
  assumes
    mono_monitor: "\<pi>' \<in> prefixes \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> M \<pi> \<subseteq> M \<pi>'" and
    wf_monitor: "\<pi> \<in> prefixes \<Longrightarrow> (i, v) \<in> M \<pi> \<Longrightarrow> wf_tuple cols v" and
    sound_monitor: "\<sigma> \<in> traces \<Longrightarrow> (i, v) \<in> M \<pi> \<Longrightarrow> prefix_of \<pi> \<sigma> \<Longrightarrow> sat \<sigma> (val nfv cols v) i" and
    complete_monitor: "\<sigma> \<in> traces \<Longrightarrow> prefix_of \<pi> \<sigma> \<Longrightarrow> wf_tuple cols v \<Longrightarrow>
      (\<And>\<sigma>'. \<sigma>' \<in> traces \<Longrightarrow> prefix_of \<pi> \<sigma>' \<Longrightarrow> sat \<sigma>' (val nfv cols v) i) \<Longrightarrow>
      \<exists>\<pi>'. prefix_of \<pi>' \<sigma> \<and> (i, v) \<in> M \<pi>'"

text \<open>On a co-safety specification, a monitor outputs exactly the satisfactions in the limit.\<close>

abbreviation (in monitor) "M_limit \<sigma> \<equiv> \<Union>{M \<pi> | \<pi>. prefix_of \<pi> \<sigma>}"

locale cosafety_monitor = cosafety_fo_spec + monitor
begin

lemma M_limit_eq:
  assumes "\<sigma> \<in> traces"
  shows "M_limit \<sigma> = verdicts \<sigma>"
proof
  show "\<Union>{M \<pi> | \<pi>. prefix_of \<pi> \<sigma>} \<subseteq> verdicts \<sigma>"
    using assms wf_monitor sound_monitor by (auto simp: verdicts_def)
next
  show "\<Union>{M \<pi> | \<pi>. prefix_of \<pi> \<sigma>} \<supseteq> verdicts \<sigma>"
    unfolding verdicts_def
  proof safe
    fix i v
    assume "wf_tuple cols v" and "sat \<sigma> (val nfv cols v) i"
    then obtain \<pi> where "prefix_of \<pi> \<sigma> \<and> (\<forall>\<sigma>'\<in>traces. prefix_of \<pi> \<sigma>' \<longrightarrow> sat \<sigma>' (val nfv cols v) i)"
      using assms cosafety_lr by blast
    with \<open>wf_tuple cols v\<close> obtain \<pi>' where "prefix_of \<pi>' \<sigma> \<and> (i, v) \<in> M \<pi>'"
      using assms complete_monitor by blast
    then show "(i, v) \<in> \<Union>{M \<pi> | \<pi>. prefix_of \<pi> \<sigma>}"
      by blast
  qed
qed

end

subsection \<open>Monitors defined by progress\<close>

text \<open>A monitor that outputs verdicts in order of time-points is determined by its progress: the
  time-point up to which all verdicts are computed.\<close>

locale progress = fo_spec _ _ _ sat for sat :: "'a trace \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> bool" +
  fixes progress :: "'a prefix \<Rightarrow> nat"
  assumes
    progress_mono: "\<pi>' \<in> prefixes \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> progress \<pi> \<le> progress \<pi>'" and
    ex_progress_ge: "\<sigma> \<in> traces \<Longrightarrow> \<exists>\<pi>. prefix_of \<pi> \<sigma> \<and> x \<le> progress \<pi>" and
    progress_sat_cong: "\<sigma> \<in> traces \<Longrightarrow> prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of \<pi> \<sigma>' \<Longrightarrow> i < progress \<pi> \<Longrightarrow>
      sat \<sigma> v i \<longleftrightarrow> sat \<sigma>' v i"
    \<comment> \<open>not needed for a monitor, but implies co-safety\<close>
begin

definition M :: "'a prefix \<Rightarrow> (nat \<times> 'b tuple) set" where
  "M \<pi> = {(i, v). i < progress \<pi> \<and> wf_tuple cols v \<and>
    (\<forall>\<sigma> \<in> traces. prefix_of \<pi> \<sigma> \<longrightarrow> sat \<sigma> (val nfv cols v) i)}"

definition Mt :: "'a prefix \<Rightarrow> (nat \<times> nat \<times> 'b tuple) set" where
  "Mt \<pi> = (\<lambda>(i, v). (i, pts \<pi> ! i, v)) ` M \<pi>"

lemma M_alt: "\<pi> \<in> prefixes \<Longrightarrow> M \<pi> = {(i, v). i < progress \<pi> \<and> wf_tuple cols v \<and>
    (\<exists>\<sigma> \<in> traces. prefix_of \<pi> \<sigma> \<and> sat \<sigma> (val nfv cols v) i)}"
  using ex_prefix_of[of \<pi>]
  by (auto simp: prefixes_def M_def cong: progress_sat_cong)

end

sublocale progress \<subseteq> cosafety_monitor _ _ _ _ M
proof
  fix i v and \<sigma> :: "'a trace"
  assume "\<sigma> \<in> traces" and "sat \<sigma> v i"
  moreover obtain \<pi> where *: "prefix_of \<pi> \<sigma>" "i < progress \<pi>"
    using \<open>\<sigma> \<in> traces\<close> ex_progress_ge by (auto simp: less_eq_Suc_le)
  ultimately have "sat \<sigma>' v i" if "prefix_of \<pi> \<sigma>'" for \<sigma>'
    using \<open>\<sigma> \<in> traces\<close> that progress_sat_cong by blast
  with * show "\<exists>\<pi>. prefix_of \<pi> \<sigma> \<and> (\<forall>\<sigma>' \<in> traces. prefix_of \<pi> \<sigma>' \<longrightarrow> sat \<sigma>' v i)"
    by blast
next
  fix \<pi> \<pi>' :: "'a prefix"
  assume "\<pi>' \<in> prefixes" and "\<pi> \<le> \<pi>'"
  then show "M \<pi> \<subseteq> M \<pi>'"
    by (auto simp: M_def intro: progress_mono prefix_of_antimono
        elim: order.strict_trans2)
next
  fix i v \<pi>
  assume "\<pi> \<in> prefixes" and "(i, v) \<in> M \<pi>"
  then show "wf_tuple cols v"
    by (simp add: M_def)
next
  fix i v \<pi> and \<sigma> :: "'a trace"
  assume "\<sigma> \<in> traces" and "(i, v) \<in> M \<pi>" and "prefix_of \<pi> \<sigma>"
  then show "sat \<sigma> (val nfv cols v) i"
    by (simp add: M_def)
next
  fix i v \<pi> and \<sigma> :: "'a trace"
  assume *: "\<sigma> \<in> traces" "prefix_of \<pi> \<sigma>" "wf_tuple cols v"
    "\<And>\<sigma>'. \<sigma>' \<in> traces \<Longrightarrow> prefix_of \<pi> \<sigma>' \<Longrightarrow> sat \<sigma>' (val nfv cols v) i"
  show "\<exists>\<pi>'. prefix_of \<pi>' \<sigma> \<and> (i, v) \<in> M \<pi>'"
  proof (cases "i < progress \<pi>")
    case True
    with * show ?thesis by (auto simp: M_def)
  next
    case False
    obtain \<pi>' where **: "prefix_of \<pi>' \<sigma> \<and> i < progress \<pi>'"
      using \<open>\<sigma> \<in> traces\<close> ex_progress_ge by (auto simp: less_eq_Suc_le)
    then have "\<pi> \<le> \<pi>'"
      using \<open>\<sigma> \<in> traces\<close> \<open>prefix_of \<pi> \<sigma>\<close> prefix_of_imp_linear False progress_mono
      by (blast intro: order.strict_trans2)
    with * ** show ?thesis
      by (auto simp: M_def intro: prefix_of_antimono)
  qed
qed

subsection \<open>Sliceable specifications\<close>

text \<open>A sliceable specification can be evaluated on the events relevant to a set of valuations.\<close>

locale abstract_slicer =
  fixes relevant_events :: "'b list set \<Rightarrow> 'a set"
begin

abbreviation slice :: "'b list set \<Rightarrow> 'a set trace \<Rightarrow> 'a set trace" where
  "slice S \<equiv> map_\<Gamma> (\<lambda>D. D \<inter> relevant_events S)"

abbreviation pslice :: "'b list set \<Rightarrow> 'a set prefix \<Rightarrow> 'a set prefix" where
  "pslice S \<equiv> pmap_\<Gamma> (\<lambda>D. D \<inter> relevant_events S)"

lemma prefix_of_psliceI: "prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of (pslice S \<pi>) (slice S \<sigma>)"
  by (transfer fixing: S) auto

lemma plen_pslice[simp]: "plen (pslice S \<pi>) = plen \<pi>"
  by (transfer fixing: S) simp

lemma pslice_pnil[simp]: "pslice S pnil = pnil"
  by (transfer fixing: S) simp

lemma last_ts_pslice[simp]: "last_ts (pslice S \<pi>) = last_ts \<pi>"
  by (transfer fixing: S) (simp add: last_map case_prod_beta split: list.split)

abbreviation verdict_filter :: "'b list set \<Rightarrow> nat list \<Rightarrow> (nat \<times> 'b tuple) set \<Rightarrow> (nat \<times> 'b tuple) set" where
  "verdict_filter S cs V \<equiv> {(i, v) \<in> V. mem_restr S cs v}"

end

locale sliceable_fo_spec = fo_spec _ _ _ sat + abstract_slicer relevant_events
  for relevant_events :: "'b list set \<Rightarrow> 'a set" and sat :: "'a set trace \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> bool" +
  assumes
    slice_closed[simp, intro]: "\<sigma> \<in> traces \<Longrightarrow> slice S \<sigma> \<in> traces" and
    sliceable: "\<sigma> \<in> traces \<Longrightarrow> v \<in> S \<Longrightarrow> sat (slice S \<sigma>) v i \<longleftrightarrow> sat \<sigma> v i"
begin

lemma pslice_closed[simp, intro]: "\<pi> \<in> prefixes \<Longrightarrow> pslice S \<pi> \<in> prefixes"
  using prefix_of_pmap_\<Gamma> by (fastforce simp: prefixes_def)

lemma sat_slice_val:
  assumes "\<sigma> \<in> traces" "mem_restr S cols v"
  shows "sat (slice S \<sigma>) (val nfv cols v) i \<longleftrightarrow> sat \<sigma> (val nfv cols v) i"
proof -
  obtain w where w: "w \<in> S" "\<forall>c\<in>set cols. c < length w \<and> w ! c = tup_get cols v c"
    using assms(2) distinct_cols by (auto elim: mem_restrE)
  have eq: "val nfv cols v ! x = w ! x" if "x \<in> set cols" for x
    using w(2) that fv_less_nfv[OF that] by simp
  have "sat (slice S \<sigma>) (val nfv cols v) i \<longleftrightarrow> sat (slice S \<sigma>) w i"
    using eq by (intro sat_fv_cong) (simp_all add: assms(1))
  also have "\<dots> \<longleftrightarrow> sat \<sigma> w i"
    by (rule sliceable[OF assms(1) w(1)])
  also have "\<dots> \<longleftrightarrow> sat \<sigma> (val nfv cols v) i"
    using eq by (intro sat_fv_cong[symmetric]) (simp_all add: assms(1))
  finally show ?thesis .
qed

lemma mem_restr_val:
  assumes "wf_tuple cols v" "val nfv cols v \<in> S"
  shows "mem_restr S cols v"
  using assms fv_less_nfv by (intro mem_restrI[OF distinct_cols assms(2,1)]) auto

lemma union_verdicts_slice:
  assumes part: "\<And>v. length v = nfv \<Longrightarrow> v \<in> \<Union>\<S>"
    and trace: "\<sigma> \<in> traces"
  shows "\<Union>((\<lambda>S. verdict_filter S cols (verdicts (slice S \<sigma>))) ` \<S>) = verdicts \<sigma>"
proof safe
  fix S i and v :: "'b tuple"
  assume "(i, v) \<in> verdicts (slice S \<sigma>)" "mem_restr S cols v"
  then show "(i, v) \<in> verdicts \<sigma>"
    using sat_slice_val[OF trace] by (auto simp: verdicts_def)
next
  fix i and v :: "'b tuple"
  assume "(i, v) \<in> verdicts \<sigma>"
  then have tuple: "wf_tuple cols v" and sat: "sat \<sigma> (val nfv cols v) i"
    by (auto simp: verdicts_def)
  obtain S where "S \<in> \<S>" and "val nfv cols v \<in> S"
    using part[of "val nfv cols v"] by auto
  then have "mem_restr S cols v"
    using mem_restr_val[OF tuple] by blast
  then have "(i, v) \<in> verdicts (slice S \<sigma>)"
    using tuple sat sat_slice_val[OF trace] by (simp add: verdicts_def)
  then show "(i, v) \<in> (\<Union>S\<in>\<S>. verdict_filter S cols (verdicts (slice S \<sigma>)))"
    using \<open>S \<in> \<S>\<close> \<open>mem_restr S cols v\<close> by blast
qed

end

subsection \<open>Sliceable monitors\<close>

text \<open>Unlike for specifications, slicing must not change when a verdict is output.\<close>

locale sliceable_monitor = monitor _ _ _ sat M + abstract_slicer relevant_events
  for relevant_events :: "'b list set \<Rightarrow> 'a set" and sat :: "'a set trace \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> bool" and M +
  assumes sliceable_M: "\<pi> \<in> prefixes \<Longrightarrow> mem_restr S cols v \<Longrightarrow> (i, v) \<in> M (pslice S \<pi>) \<longleftrightarrow> (i, v) \<in> M \<pi>"
begin

lemma union_M_pslice:
  assumes part: "\<And>v. length v = nfv \<Longrightarrow> v \<in> \<Union>\<S>"
    and prefix: "\<pi> \<in> prefixes"
  shows "\<Union>((\<lambda>S. verdict_filter S cols (M (pslice S \<pi>))) ` \<S>) = M \<pi>"
proof safe
  fix S i and v :: "'b tuple"
  assume "mem_restr S cols v" and "(i, v) \<in> M (pslice S \<pi>)"
  then show "(i, v) \<in> M \<pi>" using sliceable_M prefix by blast
next
  fix i and v :: "'b tuple"
  assume "(i, v) \<in> M \<pi>"
  then have tuple: "wf_tuple cols v"
    using prefix wf_monitor by blast
  obtain S where "S \<in> \<S>" and "val nfv cols v \<in> S"
    using part[of "val nfv cols v"] by auto
  then have "mem_restr S cols v"
    using tuple fv_less_nfv by (intro mem_restrI[OF distinct_cols]) auto
  then have "(i, v) \<in> M (pslice S \<pi>)"
    using \<open>(i, v) \<in> M \<pi>\<close> sliceable_M prefix by blast
  then show "(i, v) \<in> (\<Union>S\<in>\<S>. verdict_filter S cols (M (pslice S \<pi>)))"
    using \<open>S \<in> \<S>\<close> \<open>mem_restr S cols v\<close> by blast
qed

end

text \<open>If the specification is sliceable and the progress depends only on time-stamps, the monitor
  is sliceable.\<close>

locale timed_progress = progress +
  assumes progress_time_conv: "\<pi> \<in> prefixes \<Longrightarrow> \<pi>' \<in> prefixes \<Longrightarrow>
    pts \<pi> = pts \<pi>' \<Longrightarrow> progress \<pi> = progress \<pi>'"

locale sliceable_timed_progress = sliceable_fo_spec + timed_progress
begin

lemma progress_pslice[simp]: "\<pi> \<in> prefixes \<Longrightarrow> progress (pslice S \<pi>) = progress \<pi>"
  by (simp cong: progress_time_conv)

end

sublocale sliceable_timed_progress \<subseteq> sliceable_monitor _ _ _ _ _ M
proof
  fix S :: "'b list set" and v i \<pi>
  assume *: "\<pi> \<in> prefixes" "mem_restr S cols v"
  show "(i, v) \<in> M (pslice S \<pi>) \<longleftrightarrow> (i, v) \<in> M \<pi>" (is "?L \<longleftrightarrow> ?R")
  proof
    assume ?L
    then have i: "i < progress \<pi>" and tuple: "wf_tuple cols v"
      and sat: "\<And>\<sigma>. \<sigma> \<in> traces \<Longrightarrow> prefix_of (pslice S \<pi>) \<sigma> \<Longrightarrow> sat \<sigma> (val nfv cols v) i"
      using *(1) by (auto simp: M_def)
    have "sat \<sigma> (val nfv cols v) i" if "\<sigma> \<in> traces" "prefix_of \<pi> \<sigma>" for \<sigma>
      using sat[of "slice S \<sigma>"] that prefix_of_psliceI sat_slice_val[OF that(1) *(2)] by blast
    with i tuple show ?R
      by (simp add: M_def)
  next
    assume ?R
    then have i: "i < progress \<pi>" and tuple: "wf_tuple cols v"
      and sat: "\<exists>\<sigma> \<in> traces. prefix_of \<pi> \<sigma> \<and> sat \<sigma> (val nfv cols v) i"
      using *(1) by (auto simp: M_alt)
    then obtain \<sigma> where "\<sigma> \<in> traces" "prefix_of \<pi> \<sigma>" "sat \<sigma> (val nfv cols v) i"
      by blast
    then have "slice S \<sigma> \<in> traces" "prefix_of (pslice S \<pi>) (slice S \<sigma>)"
      "sat (slice S \<sigma>) (val nfv cols v) i"
      using prefix_of_psliceI sat_slice_val[OF _ *(2)] by auto
    with i tuple *(1) show ?L
      by (auto simp: M_alt)
  qed
qed

(*<*)
end
(*>*)

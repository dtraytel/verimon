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


subsection \<open>The summaries\<close>

abbreviation efold :: "'b esum list \<Rightarrow> 'b esum option" where
  "efold \<equiv> sw_fold ecomp"

definition eout :: "'b esum \<Rightarrow> 'b list set \<times> 'b list set" where
  "eout x = (fst x, fst x \<union> snd x)"

definition edisj :: "'b esum \<Rightarrow> bool" where
  "edisj x \<longleftrightarrow> fst x \<inter> snd x = {}"

text \<open>An entry the list updates is the composition of its summary with the new point's.\<close>

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

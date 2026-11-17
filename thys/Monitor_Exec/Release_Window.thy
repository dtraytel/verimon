(*<*)
theory Release_Window
  imports Exec_Since "Monitor_Data_Structures.Sliding_Window_Agg"
begin
(*>*)

section \<open>Release structure\<close>

subsection \<open>Auxiliary list over short tuples\<close>

definition eupdate_release :: "args \<Rightarrow> bool list \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> ts \<Rightarrow>
    (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow> (ts \<times> 'b list set \<times> 'b list set) list" where
  "eupdate_release args msk rel1 rel2 nt aux =
    map (\<lambda>(t, a1, a2). if memR (args_ivl args) (nt - t)
      then (t, esemi msk (\<not> args_pos args) (a1 \<inter> rel2) rel1, a2 - (a1 - rel2))
      else (t, a1, a2)) aux @
    [(nt, esemi msk (\<not> args_pos args) rel2 rel1, rel2)]"

subsection \<open>Sliding window of summaries\<close>

text \<open>
  Over a stretch of points a tuple is pending, released or dead; summaries of stretches compose
  associatively, so the list becomes a sliding window aggregation with bounded work per step.
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

abbreviation efold :: "'b esum list \<Rightarrow> 'b esum option" where
  "efold \<equiv> sw_fold ecomp"

definition eout :: "'b esum \<Rightarrow> 'b list set \<times> 'b list set" where
  "eout x = (fst x, fst x \<union> snd x)"

definition edisj :: "'b esum \<Rightarrow> bool" where
  "edisj x \<longleftrightarrow> fst x \<inter> snd x = {}"

subsection \<open>Refinement relations\<close>

text \<open>An entry's pending and alive tuples are read off the summary from its point to the last.\<close>

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

lemma fst_eraux_update[simp]: "fst (eraux_update args msk l r nt aux) = nt"
  by (simp add: eraux_update_def Let_def split: prod.splits)

lemma length_eupdate_release[simp]: "length (eupdate_release args msk l r nt L) = Suc (length L)"
  by (simp add: eupdate_release_def)

text \<open>The structure accepts only timestamps at or after its own, so the node's relation bounds the
  kernel's timestamps by the node's bound.\<close>

definition erelease_rel :: "cols \<Rightarrow> cols \<Rightarrow> \<I> \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow> event_data muaux \<Rightarrow>
    event_data eraux \<Rightarrow> ts list \<Rightarrow> bool" where
  "erelease_rel kR cR I tw t aux daux nts \<longleftrightarrow>
     (\<forall>(u, a1, a2) \<in> set aux. table kR a1 \<and> table kR a2) \<and>
     erel I daux (eauxlist3 kR cR kR cR aux) \<and> fst daux \<le> t \<and> t \<le> tw \<and>
     sorted nts \<and> (\<forall>u \<in> set nts. fst daux \<le> u \<and> u \<le> tw)"

(*<*)
end
(*>*)

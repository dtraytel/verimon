(*<*)
theory Trigger_Window
  imports Until_Gen "Monitor_DS.Sliding_Window_Agg" Release_Window
begin
(*>*)



section \<open>The trigger structure\<close>

text \<open>A table is used throughout with the two properties every theorem about the executable
  representation needs of it: it is well formed over its columns, and it is finite.\<close>

abbreviation (input) ftable :: "nat list \<Rightarrow> 'a table \<Rightarrow> bool" where
  "ftable A X \<equiv> table A X \<and> finite X"

subsection \<open>The interval side condition\<close>

text \<open>
  The executable trigger structure below answers for the kernel's auxiliary list under the side
  condition @{term tok} on the operand frames: the standalone trigger meets it by its interval
  containing zero, the fused And-Trigger by its two operand frames agreeing and its left operand
  being positive.  Without zero in the interval the time points that are not yet in it contribute
  their left tables to the read, which is a table only when the left operand has the node's
  columns.
\<close>

definition tok :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> bool" where
  "tok cR cL args \<longleftrightarrow> mem (args_ivl args) 0 \<or> (cL = cR \<and> args_pos args)"

subsection \<open>The structure as a sliding window\<close>

text \<open>
  A tuple satisfies the trigger at the current time-point if at every time-point in the interval
  the right operand held, or the left operand held at some later time-point.  Over a stretch of
  time-points the tuples that pass every in-interval point of it fall into those that can still
  fail on an earlier point (no point of the stretch satisfies the left operand) and those that
  cannot (some point does).  These are the release's summaries read backwards in time: a stretch
  is summarised by the two sets, a single point by the right operand's tuples split by the left
  operand, and two stretches compose by @{const ecomp} with the later one first.  The read is the
  union of the two sets of the summary of the whole window.

  The window is a two-list queue over this monoid (theory @{text Sliding_Window_Agg}), so every
  point is composed a bounded number of times.  When the interval does not contain zero, the
  newest points are not yet in the interval; they only contribute the tuples that satisfy the left
  operand, which under the side condition @{const tok} are the left tables themselves.  They are
  kept in a second two-list queue over union, from which they move to the first queue once they
  enter the interval.  The pending points' union is added to the read.
\<close>

definition tcomp :: "'b esum \<Rightarrow> 'b esum \<Rightarrow> 'b esum" where
  "tcomp x y = ecomp y x"

type_synonym 'b twaux = "bool list \<times> (ts, 'b list set \<times> 'b list set, 'b list set) swag \<times>
  (ts, 'b esum, 'b esum) swag"

definition tw_init :: "args \<Rightarrow> bool list \<Rightarrow> 'b twaux" where
  "tw_init args msk = (msk, sw_empty, sw_empty)"

definition tw_push :: "args \<Rightarrow> bool list \<Rightarrow> ts \<Rightarrow> (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow>
    (ts, 'b esum, 'b esum) swag \<Rightarrow> (ts, 'b esum, 'b esum) swag" where
  "tw_push args msk nt mv W = fold (\<lambda>(t, l, r) W. if memR (args_ivl args) (nt - t)
     then sw_push tcomp id t (esum_of args msk l r) W else W) mv W"

definition tw_update :: "args \<Rightarrow> ts \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> 'b twaux \<Rightarrow> 'b twaux" where
  "tw_update args nt l r ax = (case ax of (msk, P, W) \<Rightarrow>
     let W1 = snd (sw_pop tcomp id (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) W) in
     if mem (args_ivl args) 0 then (msk, P, sw_push tcomp id nt (esum_of args msk l r) W1)
     else (case sw_pop (\<union>) fst (\<lambda>t. memL (args_ivl args) (nt - t)) (sw_push (\<union>) fst nt (l, r) P) of
       (mv, P') \<Rightarrow> (msk, P', tw_push args msk nt mv W1)))"

definition tw_result :: "'b twaux \<Rightarrow> 'b list set" where
  "tw_result ax = (case ax of (msk, P, W) \<Rightarrow>
     (case sw_query tcomp W of None \<Rightarrow> {} | Some s \<Rightarrow> eunion s) \<union>
     (case sw_query (\<union>) P of None \<Rightarrow> {} | Some u \<Rightarrow> u))"

definition tw_empty :: "'b twaux \<Rightarrow> bool" where
  "tw_empty ax = sw_null (snd (snd ax))"

definition tphi :: "args \<Rightarrow> bool list \<Rightarrow> 'b list set \<Rightarrow> 'b list \<Rightarrow> bool" where
  "tphi args msk l x \<longleftrightarrow> (eproj msk x \<in> l) = args_pos args"

fun tT :: "args \<Rightarrow> bool list \<Rightarrow> ('b list set \<times> 'b list set) list \<Rightarrow> 'b list \<Rightarrow> bool" where
  "tT args msk [] x = True"
| "tT args msk ((l, r) # es) x =
     ((x \<in> r \<or> (\<exists>e \<in> set es. tphi args msk (fst e) x)) \<and> tT args msk es x)"

subsection \<open>The list a structure stands for\<close>

definition tent :: "args \<Rightarrow> bool list \<Rightarrow> ts \<times> 'b list set \<times> 'b list set \<Rightarrow> ts \<times> 'b esum" where
  "tent args msk x = (fst x, esum_of args msk (fst (snd x)) (snd (snd x)))"

definition trel :: "args \<Rightarrow> bool list \<Rightarrow> ts \<Rightarrow> 'b twaux \<Rightarrow> (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow>
    bool" where
  "trel args msk cur ax D \<longleftrightarrow> fst ax = msk \<and> List.sorted (map fst D) \<and>
     (\<forall>x \<in> set D. fst x \<le> cur \<and> memR (args_ivl args) (cur - fst x)) \<and>
     sw_rel (\<union>) fst (fst (snd ax)) (filter (\<lambda>x. \<not> memL (args_ivl args) (cur - fst x)) D) \<and>
     sw_rel tcomp id (snd (snd ax))
       (map (tent args msk) (filter (\<lambda>x. memL (args_ivl args) (cur - fst x)) D))"

subsection \<open>The trigger node's structure\<close>

definition etw :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> event_data twaux \<Rightarrow>
    event_data mtaux \<Rightarrow> bool" where
  "etw kL cL kR cR args cur daux auxlist \<longleftrightarrow>
     (\<forall>(t, l, r) \<in> set auxlist. table kL l \<and> table kR r) \<and> tok cR cL args \<and>
     trel (eargs cR cL args) (emsk cR cL) cur daux (eauxlist3 kL cL kR cR auxlist)"

end
(*>*)

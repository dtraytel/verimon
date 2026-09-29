(*<*)
theory Kernel_Code
  imports "MFODL_Monitor_Devel.Monomorphic_Code" "MFODL_Monitor_Devel.RBT_set_opt"
    "MFODL_Monitor_Devel.Monitor_Impl"
begin
(*>*)

section \<open>Code setup for the kernel's export\<close>

text \<open>
  The code equations the kernel of @{theory MFODL_Monitor_Devel.Monitor_Impl} needs to be
  exported, and those that keep its tables red-black trees.  They belong in
  @{theory MFODL_Monitor_Devel.Monitor_Impl} and @{theory MFODL_Monitor_Devel.Monomorphic_Code}
  and are collected here until those theories are next rebuilt.
\<close>

subsection \<open>The initial state\<close>

text \<open>The initial state is computed by @{const minit0} itself.  It builds its temporal nodes
  through the locales' @{text init_since}, @{text init_until}, @{text init_trigger} and
  @{text init_and_trigger}, whose definitions hold only under the locales' assumptions; the
  interpretations' instances of them are unfolded into the code instead.  The fused
  And-Trigger's is unfolded into the equations of @{const minit0} directly, where the
  preprocessor does not reach it.\<close>

declare default_mmasaux.init_since_def[code_unfold] dq_muaux.init_until_def[code_unfold]
  verimon_maux.init_trigger_def[code_unfold]

lemmas minit0_code_simps = default_maux.minit0.simps[unfolded verimon_maux.init_and_trigger_def]

declare [[code drop: minit0]]
declare minit0_code_simps[code]

subsection \<open>The probe of the joins\<close>

text \<open>@{theory MFODL_Monitor_Devel.Monomorphic_Code} replaces the probe of the joins over red-black
  trees by @{const probe_step_key}, which computes the join key once; the probe over other sets
  goes through it too.\<close>

declare probe_step_key[symmetric, code]

subsection \<open>Matching a predicate's table\<close>

text \<open>The match of a predicate's table against the atom's terms is an image followed by
  @{const Option.these}, which the generated code ran through the generic set operations: the
  intermediate set is one of functions, which have no order, so the result was not a tree.  On
  a tree it is one fold that inserts the matches.\<close>

definition match_table :: "Formula.trm list \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "match_table tms X = tabulate_match (pred_cols tms) ` Option.these (match tms ` X)"

lemma match_table_unfold[code_unfold]:
  "tabulate_match (pred_cols tms) ` Option.these (match tms ` X) = match_table tms X"
  by (simp add: match_table_def)

lemma image_these_image: "h ` Option.these (u ` A) = Option.these ((\<lambda>x. map_option h (u x)) ` A)"
  by (force simp: Option.these_def image_iff)

lemma these_image_fold:
  "fold (\<lambda>x acc. case u x of None \<Rightarrow> acc | Some f \<Rightarrow> Set.insert (h f) acc) xs A
   = A \<union> Option.these ((\<lambda>x. map_option h (u x)) ` set xs)"
  by (induct xs arbitrary: A) (auto split: option.splits)

lemma match_table_rbt[code]:
  "match_table tms (RBT_set t) = (let cs = pred_cols tms in
     RBT_Set2.fold (\<lambda>x acc. case match tms x of None \<Rightarrow> acc
       | Some f \<Rightarrow> Set.insert (tabulate_match cs f) acc) t {})"
proof -
  have i: "ID CCOMPARE(event_data list) \<noteq> None"
    by (simp add: ID_ccompare_etuple)
  show ?thesis
    unfolding match_table_def RBT_set_conv_keys[OF i] RBT_Set2.fold_conv_fold_keys' Let_def
      these_image_fold image_these_image by (simp add: RBT_Set2.keys.rep_eq)
qed

lemma match_table_other[code]:
  "match_table tms (DList_set d) = tabulate_match (pred_cols tms) ` Option.these (match tms ` DList_set d)"
  "match_table tms (Set_Monad xs) = tabulate_match (pred_cols tms) ` Option.these (match tms ` Set_Monad xs)"
  "match_table tms (Collect_set P) = tabulate_match (pred_cols tms) ` Option.these (match tms ` Collect_set P)"
  "match_table tms (Complement Q) = tabulate_match (pred_cols tms) ` Option.these (match tms ` Complement Q)"
  by (simp_all add: match_table_def)

(*<*)
end
(*>*)

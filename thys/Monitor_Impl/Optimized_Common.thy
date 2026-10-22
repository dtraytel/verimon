(*<*)
theory Optimized_Common
  imports "Monitor_Data_Structures.Queue" "Monitor_Algorithm.Monitor" Wf_Table
begin
(*>*)

section \<open>Notions shared by optimized structures\<close>

fun upd_set_keys where "upd_set_keys Z (t, X) (m, Y) = (upd_set m (\<lambda>_. t) (Z X t), Y \<union> Z X t)"

declare upd_set_keys.simps[simp del]

definition ts_tuple_rel_f :: "('b \<Rightarrow> 'a table) \<Rightarrow> (ts \<times> 'b) set \<Rightarrow> (ts \<times> 'a tuple) set" where
  "ts_tuple_rel_f f ys = {(t, as). \<exists>X. as \<in> (f X) \<and> (t, X) \<in> ys}"

abbreviation "ts_tuple_rel ys \<equiv> ts_tuple_rel_f id ys"

definition valid_tuple :: "(('a tuple, ts) mapping) \<Rightarrow> (ts \<times> 'a tuple) \<Rightarrow> bool" where
  "valid_tuple tuple_since = (\<lambda>(t, as). case Mapping.lookup tuple_since as of None \<Rightarrow> False
  | Some t' \<Rightarrow> t \<ge> t')"

definition safe_max :: "'a :: linorder set \<Rightarrow> 'a option" where
  "safe_max X = (if X = {} then None else Some (Max X))"

definition newest_tuple_in_mapping :: "
  ('b \<Rightarrow> 'a table) \<Rightarrow>
  (ts \<times> 'b) queue \<Rightarrow>
  (('a tuple, ts) mapping) \<Rightarrow>
  ((ts \<times> 'a tuple) \<Rightarrow> bool) \<Rightarrow>
  bool"
  where
  "newest_tuple_in_mapping entry_to_db data_in tuple_in P = (\<forall>tuple.
    \<comment> \<open>iff something is present in the mapping then the value corresponds
       to the maximum timestamp of a db containing the tuple\<close>
    Mapping.lookup tuple_in tuple =
    safe_max (
      fst ` {
       tas \<in> ts_tuple_rel_f entry_to_db (set (linearize data_in)).
       P tas \<and> tuple = snd tas
      }
    )
  )"

declare Map_To_Mapping.map_apply_def[simp]

end
(*>*)

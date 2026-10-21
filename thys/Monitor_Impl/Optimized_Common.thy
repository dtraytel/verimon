(*<*)
theory Optimized_Common
  imports "Monitor_DS.Queue" "MFODL_Monitor.Monitor" Wf_Table
begin
(*>*)

definition mapping_delete_set :: "('a, 'b) mapping \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" where
  "mapping_delete_set m X = Mapping.filter (join_filter_cond False X) m"

lift_definition upd_set :: "('a, 'b) mapping \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m f X a. if a \<in> X then Some (f a) else m a" .

fun upd_set_keys where "upd_set_keys Z (t, X) (m, Y) = (upd_set m (\<lambda>_. t) (Z X t), Y \<union> Z X t)"

declare upd_set_keys.simps[simp del]

abbreviation "filter_cond X' ts t' \<equiv> (\<lambda>as _. \<not> (as \<in> X' \<and> Mapping.lookup ts as = Some t'))"
abbreviation "filter_cond' X' ts t' \<equiv> (\<lambda>as. \<not> (as \<in> X' \<and> Mapping.lookup ts as = Some t'))"

fun filter_set where "filter_set (t, X) (m, Y) =
  (let m' = Mapping.filter (filter_cond X m t) m in (m', Y \<union> (Mapping.keys m - Mapping.keys m')))"

declare filter_set.simps[simp del]

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

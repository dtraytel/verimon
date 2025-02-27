theory VeriMon
imports Correctness Rewriting
begin

context maux begin

definition "prepare_verimon rw sig \<phi> =
(case type_check sig \<phi> of Inl err \<Rightarrow> Inl err
| Inr \<phi> \<Rightarrow>
(if mmonitorable_exec \<phi> then Inr \<phi> else
(if rw then
let n\<phi> = normalize \<phi> in
if mmonitorable_exec n\<phi> then Inr n\<phi> else
let r\<phi> = rrewrite n\<phi> in
if mmonitorable_exec r\<phi> then Inr r\<phi> else Inl STR ''not monitorable''
else Inl STR ''not monitorable'')))"

definition "minit_verimon rw sig \<phi> = map_sum id minit (prepare_verimon rw sig \<phi>)"

end

locale actually_verimon = maux +
  fixes rw sig \<phi>
  assumes "\<not> sum.isl (prepare_verimon rw sig \<phi>)"
begin

term type_check
find_theorems check
thm check_sound_proven

interpretation verimon: verimon "projr (prepare_verimon rw sig \<phi>)" "map_option (map convert_tysym) o sig"
  apply standard
  subgoal sorry
  subgoal (*TODO*) sorry
  done
thm verimon.sound_monitor

end

context verimon begin
thm mono_monitor sound_monitor complete_monitor sliceable_M
end
end
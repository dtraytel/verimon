(*<*)
theory IEval_Proof
  imports "Monitor_Exec.IEval" Eval_Proof IWindow_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma dabs_update[simp]: "dabs (Mapping.update k xs db) = Mapping.update k (map iset xs) (dabs db)"
  by (rule mapping_eqI) (simp add: lookup_dabs Mapping.lookup_update')

lemma dabs_demb[simp]: "dabs (demb db) = db"
  by (rule mapping_eqI) (simp add: lookup_dabs demb_def Mapping.lookup_map_values option.map_comp
      comp_def option.map_ident)

lemma map_zip_inv:
  "length Q = length L \<Longrightarrow> (\<And>q x. (q, x) \<in> set (zip Q L) \<Longrightarrow> g (f q x) = x) \<Longrightarrow>
    map g (map (\<lambda>(q, x). f q x) (zip Q L)) = L"
  by (induct Q L rule: list_induct2) auto

lemma eabs_eemb[simp]: "eabs (eemb ix rq \<phi>) = \<phi>"
proof (induct ix rq \<phi> rule: eemb.induct)
  case (13 ix rq ps ns Ld dbuf)
  have "map eabs (map (\<lambda>(q, \<phi>). eemb ix q \<phi>) (zip (eands_req ps (length Ld)) Ld)) = Ld"
    by (rule map_zip_inv) (auto intro: 13)
  then show ?case by simp
qed (auto simp: comp_def intro!: map_idI)

end

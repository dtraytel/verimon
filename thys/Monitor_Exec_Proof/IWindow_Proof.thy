(*<*)
theory IWindow_Proof
  imports "Monitor_Exec.IWindow" Window_Dispatch_Proof ITable_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma ims_abs_add_new_table_msaux:
  "ims_abs (ieadd_new_table_msaux args X a) = eadd_new_table_msaux args X (ims_abs a)"
  by (cases a rule: iemsaux_cases) (simp add: Let_def)

lemma iuw_extend_abs:
  "uw_extend args ts0 win rest bend (icnt_abs cc) =
     (case iuw_extend args ts0 win rest bend cc of (w, r, b, c) \<Rightarrow> (w, r, b, icnt_abs c))"
proof (induct args ts0 win rest bend cc rule: iuw_extend.induct)
  case (1 args ts0 win rest bend cc)
  show ?case
    by (subst uw_extend.simps, subst iuw_extend.simps)
      (use 1 in \<open>auto simp: icnt_abs_add split: prod.splits option.splits\<close>)
qed

lemma iuw_abs_step: "iuw_abs (iuw_step args ts0 aux) = uw_step args ts0 (iuw_abs aux)"
proof -
  obtain nts win rest len bend cc dn where a: "aux = (nts, win, rest, len, bend, cc, dn)"
    by (cases aux) auto
  obtain win1 rest1 bend1 cc1 where x: "iuw_extend args ts0 win rest bend cc = (win1, rest1, bend1, cc1)"
    by (cases "iuw_extend args ts0 win rest bend cc") auto
  have u: "uw_extend args ts0 win rest bend (icnt_abs cc) = (win1, rest1, bend1, icnt_abs cc1)"
    by (simp add: iuw_extend_abs x)
  obtain eo w' where h: "safe_hd win1 = (eo, w')" by (cases "safe_hd win1")
  show ?thesis
    by (cases eo) (simp_all add: a x u h iuw_abs_def iuw_step_def uw_step_def Let_def icnt_abs_del)
qed

lemma iuw_abs_shift: "iuw_abs (iuw_shift args nt aux) = uw_shift args nt (iuw_abs aux)"
proof (induct args nt aux rule: iuw_shift.induct)
  case (1 args nt aux)
  obtain nts win rest len bend cc dn where a: "aux = (nts, win, rest, len, bend, cc, dn)"
    by (cases aux) auto
  obtain to nts' where h: "safe_hd nts = (to, nts')" by (cases "safe_hd nts")
  show ?case
  proof (cases to)
    case None
    then show ?thesis
      by (subst iuw_shift.simps, subst uw_shift.simps) (simp add: a h)
  next
    case (Some ts0)
    show ?thesis
    proof (cases "memR (args_ivl args) (nt - ts0) \<or> len = 0")
      case True
      then show ?thesis using Some
        by (subst iuw_shift.simps, subst uw_shift.simps) (simp add: a h)
    next
      case False
      note IH = 1[OF a[symmetric] refl refl refl refl refl h[symmetric] Some False]
      show ?thesis using Some False IH[unfolded iuw_abs_step]
        by (subst iuw_shift.simps, subst uw_shift.simps)
          (simp add: a h)
    qed
  qed
qed

lemma iuw_abs_add_new: "iuw_abs (iuw_add_new args rel1 rel2 nt aux) = uw_add_new args rel1 rel2 nt (iuw_abs aux)"
  using iuw_abs_shift[of args nt aux]
  by (auto simp: iuw_add_new_def uw_add_new_def iuw_abs_def Let_def split: prod.splits)

lemma iuw_eval_abs: "iuw_eval args nt aux = (zs, aux') \<Longrightarrow>
    uw_eval args nt (iuw_abs aux) = (map iset zs, iuw_abs aux')"
  using iuw_abs_shift[of args nt aux]
  by (auto simp: iuw_eval_def uw_eval_def iuw_abs_def rev_map split: prod.splits)

lemma riud_add_new: "udux_add_new args msk rel1 rel2 nt (riud d) = riud (iudux_add_new args msk rel1 rel2 nt d)"
  by (cases d) (simp_all add: iuw_abs_add_new)

end
(*>*)

theory Lexer imports Grammar begin

(*The names the proofs were written with; they are gone from the library since Isabelle 2024.*)
lemmas list_all_simps = list_all_Cons_iff list_all_Nil_iff

(*LexerState as a datatype.*)
datatype LexerState = 
  INITIAL | 
  QUOTED_STRING string |
  SIMPLE_STRING string | 
  LINE_COMMENT

(*Case: INITIAL*)
fun nextTokenInit :: "char \<Rightarrow> (TokenType list \<times> LexerState) option" where 
  "nextTokenInit c = (case c of 
  CHR '' '' \<Rightarrow> Some ([], INITIAL) |
  CHR 0x09 \<Rightarrow> Some ([], INITIAL) |
  CHR 0x0a \<Rightarrow> Some ([], INITIAL) |
  CHR 0x0D \<Rightarrow> Some ([], INITIAL) |
  CHR ''@'' \<Rightarrow> Some ([AT], INITIAL) | 
  CHR ''('' \<Rightarrow> Some ([LEFT_PAREN], INITIAL) |
  CHR '')'' \<Rightarrow> Some ([RIGHT_PAREN], INITIAL) |
  CHR ''<'' \<Rightarrow> Some ([LEFT_ANGLE], INITIAL) |
  CHR ''>'' \<Rightarrow> Some ([RIGHT_ANGLE], INITIAL) |
  CHR '','' \<Rightarrow> Some ([COMMA], INITIAL) |
  CHR '';'' \<Rightarrow> Some ([SEMICOLON], INITIAL) |
  CHR ''#'' \<Rightarrow> Some ([], LINE_COMMENT) |
  CHR ''\"'' \<Rightarrow> Some ([], (QUOTED_STRING '''')) |
  c \<Rightarrow> If (isSimpleChar c) (Some ([], (SIMPLE_STRING [c]))) None
)"

(*Q: So in the char after char way, we do not need an atEnd()?*)
fun nextToken :: "char \<Rightarrow> LexerState \<Rightarrow> (TokenType list \<times> LexerState) option" where
  "nextToken c INITIAL = nextTokenInit c" |
  "nextToken c (SIMPLE_STRING s) =
  (if (isSimpleChar c) 
  then (Some ([], (SIMPLE_STRING (c#s))))
  else (case (nextTokenInit c) of 
    None \<Rightarrow> None | 
    Some (xs, ls) \<Rightarrow> Some ((STRING (rev s)#xs) ,ls)))" |
  "nextToken c (QUOTED_STRING s) = (if c = CHR ''\"'' then 
  Some ([STRING (rev s)], INITIAL) else
  Some ([], QUOTED_STRING (c#s)))" |
  "nextToken c LINE_COMMENT = (if (isLineCommentEnd c)
  then (Some ([], INITIAL))
  else (Some ([], LINE_COMMENT)))"

fun LexerStepCaller :: "char list \<Rightarrow> (TokenType list \<times> LexerState) \<Rightarrow> (TokenType list \<times> LexerState) option" where
  "LexerStepCaller [] ttl = Some ttl" |
  "LexerStepCaller (x#xs) (ttl, ls) = (case (nextToken x ls) of
  Some (ttl', ls') \<Rightarrow> LexerStepCaller xs ((ttl @ ttl'), ls') |
  None \<Rightarrow> None
)"

value "LexerStepCaller ''this is a list of simple strings '' ([], INITIAL)"

(*INVARIANTS and PROOFS*)

lemma nextTokenInitSplit [consumes 1, case_names WS AT LP RP LA RA CO SC LC QS SS]: 
  assumes "nextTokenInit c = Some (ts, ls)"
  obtains 
    "isWhiteSpace c" "ts = []" "ls = INITIAL" | 
    "c = CHR ''@''" "ts = [AT]" "ls = INITIAL" | 
    "c = CHR ''(''" "ts = [LEFT_PAREN]" "ls = INITIAL" | 
    "c = CHR '')''" "ts = [RIGHT_PAREN]" "ls = INITIAL" | 
    "c = CHR ''<''" "ts = [LEFT_ANGLE]" "ls = INITIAL" | 
    "c = CHR ''>''" "ts = [RIGHT_ANGLE]" "ls = INITIAL" | 
    "c = CHR '',''" "ts = [COMMA]" "ls = INITIAL" | 
    "c = CHR '';''" "ts = [SEMICOLON]" "ls = INITIAL" | 
    "c = CHR ''#''" "ts = []" "ls = LINE_COMMENT" | 
    "c = CHR ''\"''" "ts = []" "ls = QUOTED_STRING ''''" | 
    "isSimpleChar c" "ts = []" "ls = SIMPLE_STRING [c]"
  using assms
  by (auto simp add: isWhiteSpace.simps split: char.splits bool.splits if_splits)

lemma isSimpleChar_nextTokenInit:
  assumes "isSimpleChar c"
  shows "nextTokenInit c = Some ([], SIMPLE_STRING [c])"
proof -
  from assms have "c \<noteq> CHR '' '' \<and> c \<noteq> CHR 0x09 \<and> c \<noteq> CHR 0x0a \<and> c \<noteq> CHR 0x0D \<and>
    c \<noteq> CHR ''@'' \<and> c \<noteq> CHR ''('' \<and> c \<noteq> CHR '')'' \<and> c \<noteq> CHR ''<'' \<and> c \<noteq> CHR ''>'' \<and>
    c \<noteq> CHR '','' \<and> c \<noteq> CHR '';'' \<and> c \<noteq> CHR ''#'' \<and> c \<noteq> CHR ''\"''"
    by auto
  then have "nextTokenInit c = (if isSimpleChar c then (Some ([], (SIMPLE_STRING [c]))) else None)"
    by (simp del: isSimpleChar.simps split: char.split bool.split split del: if_split cong: if_cong)
  with assms show ?thesis by simp
qed

inductive LexInv :: "string \<Rightarrow> LexerState \<Rightarrow> bool" where
  LexInv0 : "list_all isWhiteSpace s \<Longrightarrow> LexInv s INITIAL" |
  LexInvSS : "isSimpleString s \<Longrightarrow> LexInv s (SIMPLE_STRING (rev s))" | (*the "rev" is here because in the algo*)
  LexInvQS : "list_all (\<lambda>x. x \<noteq> CHR ''\"'') s \<Longrightarrow> LexInv ((CHR ''\"'')#s) (QUOTED_STRING (rev s))" |             (*we reverse the string until it is complete*)
  LexInvLC : "list_all (Not o isLineCommentEnd) s \<Longrightarrow> LexInv ((CHR ''#'')#s) (LINE_COMMENT)"

inductive LexInvHelper :: "string \<Rightarrow> LexerState \<Rightarrow> TokenType list \<Rightarrow> bool" where
  LexInvHelper2 : "Glex s1 ts \<Longrightarrow> LexInv s2 ls \<Longrightarrow> (s1 \<noteq> [] \<and> isSimpleChar (last s1) \<Longrightarrow> (\<not>isSimpleChar (hd s2) \<or> s2 = []) \<and> ls \<noteq> INITIAL) \<Longrightarrow> LexInvHelper (s1@s2) ls ts"

lemma GlexNilNil [simp]: "Glex [] []"
  apply(rule GlexWS)
  apply(auto intro: isWhiteString.intros)
  done

lemma LexInvNil : "LexInv [] INITIAL"
  by(rule LexInv0)
    (simp)

lemma LexInvInit : "LexInv s INITIAL \<Longrightarrow> list_all isWhiteSpace s"
  apply(cases pred : LexInv)
      apply(auto)
  done

lemma LexInvHelper0 [simp]: "LexInv s ls \<Longrightarrow> LexInvHelper s ls []"
  apply (rule LexInvHelper2[where ?s1.0 = "''''" and ?ts = "[]" , simplified])
  apply (simp)
  done

lemma LexInvHelper1 [simp]: "Glex s ts \<Longrightarrow> (s \<noteq> [] \<Longrightarrow> \<not> isSimpleChar (last s)) \<Longrightarrow> LexInvHelper s INITIAL ts"
  apply (rule LexInvHelper2[where ?s2.0 = "''''" and ?ls = "INITIAL", simplified append_Nil2])
    apply simp
   apply(rule LexInv0)
   apply auto
  done

lemma LexInvHelperInit [simp]: "LexInvHelper '''' INITIAL []"
  apply(rule LexInvHelper0)
  apply(rule LexInv0)
  apply simp
  done

lemma GlexNil0: "Glex [] [t] \<Longrightarrow> False"
  apply(cases rule: Glex.cases)
    apply(auto)
  apply(cases rule: GToken.cases)
           apply(auto)
  done

lemma GlexWSNil [simp] : "Glex s [] \<longleftrightarrow> isWhiteString s"
  apply(auto elim: Glex.cases intro: Glex.intros)
  done

lemma GTokenSSt: "isSimpleString s1 \<Longrightarrow> GToken s1 t \<Longrightarrow> t = STRING s1"
  apply(cases rule: GToken.cases)
  by(auto)

lemma GTokenNil [simp]: "\<not>GToken [] t"
  apply(auto elim: GToken.cases)
  done

lemma GlexNil: "Glex [] ts \<Longrightarrow> ts = []"
  apply(cases rule: Glex.cases)
    apply(auto)
  done

lemma GTokenSS: "GToken s t \<Longrightarrow> isSimpleChar(hd s) \<Longrightarrow> isSimpleString s"
  by(induction s t rule: GToken.induct)
    (auto)

lemma WShd: "isWhiteString s \<Longrightarrow> s = [] \<or> \<not>isSimpleChar (hd s)"
proof(induction s pred: isWhiteString)
  case (isWS0 s)
  then show ?case
    by(cases s)
      (auto simp add: isWhiteSpace.simps)
next
  case (isWS1 s c)
  then show ?case
    by(auto)
next
  case (isWS2 s1 s2)
  then show ?case
    apply(cases s1 type: list ; cases s2 type: list)
    by(auto)
qed

lemma GlexWSs2 : "Glex s1 ts \<Longrightarrow> isWhiteString s2 \<Longrightarrow> Glex (s1@s2) ts"
proof(induction s1 ts arbitrary: s2 rule: Glex.induct)
  case GWS: (GlexWS xs)
  then show ?case
    by (auto intro: GlexWS isWhiteString.intros)
next
  case GTK: (GlexTK s1' t s2' ts' w)
  then show ?case
    using GlexTK[where ?s2.0 = "(s2'@s2)" and ?w = w and ?s1.0 = s1' and ?t = t and ?ts = ts']
    apply(cases s2')
    by(auto simp add: WShd simp del: isSimpleChar.simps)
qed

lemma GlexTKRev [simp]: "Glex s1 ts \<Longrightarrow> GToken s2 t \<Longrightarrow> isWhiteString w \<Longrightarrow> (w = [] \<and> isSimpleString s2 \<Longrightarrow> s1 = [] \<or> \<not>isSimpleChar(last s1)) \<Longrightarrow> Glex (s1@w@s2) (ts@[t])"
proof(induction arbitrary: s2 t w rule: Glex.induct)
  case (GlexWS xs)
  then have "Glex ((xs @ w) @ s2 @ []) [t]"
    apply(intro GlexTK)
       apply(auto intro: isWhiteString.intros)
    done
  then show ?case by simp
next
  case GTK: (GlexTK s1 t' s2' ts w')
  then have "Glex (w' @ s1 @ (s2' @ w @ s2)) (t' # (ts @ [t]))"
    apply-apply(rule GlexTK)
       apply blast
      apply (metis Nil_is_append_conv last_appendR)
     apply blast
    apply(cases "s2' = []")
     apply(clarsimp simp del: isSimpleChar.simps)
     apply (metis GTokenSS WShd append_butlast_last_id hd_append list_all_append list_all_simps(1))
    by(auto)
  then show ?case by simp
qed

lemma GlexTKRevSS : "Glex s1 ts \<Longrightarrow> GToken s2 (STRING s2) \<Longrightarrow> GToken t t' \<Longrightarrow> \<not>isSimpleString t \<Longrightarrow> (isSimpleString s2 \<Longrightarrow> s1 = [] \<or> \<not>isSimpleChar(last s1)) \<Longrightarrow>  Glex ((s1 @ s2) @ t) ((ts @ [STRING s2]) @ [ t'])"
  apply(rule GlexTKRev[where w="[]", simplified])
     apply(rule GlexTKRev[where w="[]", simplified])
  by (auto intro: isWhiteString.intros)


(*------------------------------------------------------------------------------------------------------------------------------------------*)

lemma isWhiteSpace_not_simple: "isWhiteSpace c \<Longrightarrow> \<not> isSimpleChar c"
  by (induction c pred: isWhiteSpace) simp_all

lemma isLineCommentEnd_not_simple: "isLineCommentEnd c \<Longrightarrow> \<not> isSimpleChar c"
  by (induction c rule: isLineCommentEnd.induct) simp_all (* slow *)

lemma nextTokenSound: assumes "LexInvHelper s ls ts" and "nextToken c ls = Some (ts', ls')"
  shows "LexInvHelper (s@[c]) ls' (ts@ts')"
proof(cases ls)
  case INITIAL
  from assms (2, 1) show ?thesis unfolding INITIAL nextToken.simps
  proof (cases rule: nextTokenInitSplit)
    case WS
    with assms (1) show ?thesis 
    proof(cases)
      case L2:(LexInvHelper2 s1 s2)
      from L2 (3, 1, 2) INITIAL show ?thesis
      proof(cases rule: LexInv.cases)
        case LI0: LexInv0
        with WS L2 (1, 2, 4) show ?thesis
          using LexInvHelper2 [where ?s1.0 = s1 and ?s2.0 = "s2 @ [c]" and ?ts = ts and ?ls = ls'] 
          apply(cases s2)
          by(auto simp add: LexInv0 hd_append elim: isWhiteSpace.cases)
      qed auto
    qed
  next
    case AT  (*all cases after this inside the INITIAL case are just copy pasted*)
    with assms (1) show ?thesis
    proof(cases)
      case L2: (LexInvHelper2 s1 s2)
      with INITIAL have "list_all isWhiteSpace s2" by (simp add: LexInvInit)
      with L2 (2) show ?thesis unfolding L2 (1) AT
        by (auto intro: GToken.intros isWhiteString.intros LexInvHelper1 intro!: GlexTKRev)
    qed
  next
    case LP
    with assms (1) show ?thesis
    proof (cases)
      case L2: (LexInvHelper2 s1 s2)
      with INITIAL have "list_all isWhiteSpace s2" by (simp add: LexInvInit)
      with L2 (2) show ?thesis unfolding L2 (1) LP
        by (auto intro: GToken.intros isWhiteString.intros LexInvHelper1 intro!: GlexTKRev)
    qed
  next
    case RP
    with assms (1) show ?thesis
    proof (cases)
      case L2: (LexInvHelper2 s1 s2)
      with INITIAL have "list_all isWhiteSpace s2" by (simp add: LexInvInit)
      with L2 (2) show ?thesis unfolding L2 (1) RP
        by (auto intro: GToken.intros isWhiteString.intros LexInvHelper1 intro!: GlexTKRev)
    qed
  next
    case LA
    with assms (1) show ?thesis
    proof (cases)
      case L2: (LexInvHelper2 s1 s2)
      with INITIAL have "list_all isWhiteSpace s2" by (simp add: LexInvInit)
      with L2 (2) show ?thesis unfolding L2 (1) LA
        by (auto intro: GToken.intros isWhiteString.intros LexInvHelper1 intro!: GlexTKRev)
    qed
  next
    case RA
    with assms (1) show ?thesis
    proof(cases)
      case L2: (LexInvHelper2 s1 s2)
      with INITIAL have "list_all isWhiteSpace s2" by (simp add: LexInvInit)
      with L2 (2) show ?thesis unfolding L2 (1) RA
        by (auto intro: GToken.intros isWhiteString.intros LexInvHelper1 intro!: GlexTKRev)
    qed
  next
    case CO
    with assms (1) show ?thesis
    proof(cases)
      case L2: (LexInvHelper2 s1 s2)
      with INITIAL have "list_all isWhiteSpace s2" by (simp add: LexInvInit)
      with L2 (2) show ?thesis unfolding L2 (1) CO
        by (auto intro: GToken.intros isWhiteString.intros LexInvHelper1 intro!: GlexTKRev)
    qed
  next
    case SC
    with assms (1) show ?thesis
    proof(cases)
      case L2: (LexInvHelper2 s1 s2)
      with INITIAL have "list_all isWhiteSpace s2" by (simp add: LexInvInit)
      with L2 (2) show ?thesis unfolding L2 (1) SC
        by (auto intro: GToken.intros isWhiteString.intros LexInvHelper1 intro!: GlexTKRev)
    qed
  next
    case LC
    with assms (1) show ?thesis 
    proof(cases)
      case L2:(LexInvHelper2 s1 s2)
      from L2 (3, 1, 2) INITIAL show ?thesis
      proof(cases rule: LexInv.cases)
        case LI0: LexInv0
        with LC L2 (1, 2) show ?thesis
          using GlexWSs2 [where ?s1.0 = s1 and ?s2.0 = s2 and ?ts = ts] LexInvHelper2 [where ?s1.0 = "s1 @ s2" and ?s2.0 = "[c]" and ?ts = ts and ?ls = ls'] 
          by (auto simp add: LexInvLC [where ?s = "[]", simplified] isWhiteString.intros)
      qed auto
    qed
  next
    case QS
    from assms (1) show ?thesis
    proof(cases)
      case L2: (LexInvHelper2 s1 s2)
      from L2 (3, 1, 2) INITIAL show ?thesis
      proof(cases rule: LexInv.cases)
        case LI0: LexInv0
        with QS L2 (1, 2) show ?thesis unfolding INITIAL
          using GlexWSs2 [where ?s1.0 = s1 and ?s2.0 = s2 and ?ts = ts] LexInvHelper2 [where ?s1.0 = "s1 @ s2" and ?s2.0 = "[c]" and ?ts = ts and ?ls = ls'] 
          by (auto simp add: LexInvQS [where ?s = "[]", simplified] isWhiteString.intros)
      qed auto
    qed
  next
    case SS
    from assms (1) show ?thesis
    proof(cases)
      case L2: (LexInvHelper2 s1 s2)
      from L2 (3, 1, 2) INITIAL show ?thesis
      proof(cases rule: LexInv.cases)
        case LI0: LexInv0
        have isSimpleCharFalse: "\<not> isSimpleChar c \<Longrightarrow> \<not> isSimpleChar (hd [c])"
          by simp
        have isSimpleCharNotEmpty: "\<not> isSimpleChar (hd [c]) \<Longrightarrow> \<not> isSimpleChar (hd [c]) \<or> [c] = []"
          by simp
        have help1: "isSimpleChar c \<Longrightarrow> \<not> isSimpleChar (hd [c]) \<or> [c] = [] \<Longrightarrow> False"
          by simp
        from SS L2 LI0 show ?thesis
          apply(simp del: isSimpleChar.simps)
          apply(rule LexInvHelper2 [where ?s1.0 = "s1 @ s2" and ?s2.0 = "[c]" and ?ts = ts and ?ls = "SIMPLE_STRING [c]", simplified append_assoc])
          apply(simp del: isSimpleChar.simps add: GlexWSs2 isWS0)
           apply (simp del: isSimpleChar.simps add: LexInv.simps)
          apply(simp del: isSimpleChar.simps add: LexInv.simps)
          by (metis WShd hd_rev isWS0 last_append list_all_rev rev_is_Nil_conv)
      qed auto
    qed
  qed
next
  case QS: (QUOTED_STRING x2)
  then show ?thesis 
  proof (cases "c = CHR ''\"''")
    case True
    with QS assms show ?thesis
      by(force intro!: LexInvHelper1 GTokenQSt isWhiteString.intros intro: GlexTKRev [where ?w = "[]", simplified] elim!: LexInvHelper.cases LexInv.cases)
  next
    case False
    with QS assms show ?thesis
      apply(auto)
      apply(elim LexInvHelper.cases LexInv.cases)
         apply(simp_all)
      apply(rule LexInvHelper2)
      apply simp
      apply (smt (z3) LexInvQS list_all_rev list_all_simps(1) rev.simps(2) rev_swap)
      by simp
      (*apply (auto intro: LexInvQS [where ?s = "(_@[c])", simplified] elim!: LexInvHelper.cases LexInv.cases LexInvHelper2)
              apply (smt (z3) GlexNil LexInvHelper0 LexInvQS list_all_rev list_all_simps(1) rev.simps(2) rev_swap)
        sorry*)
  qed
next
  case SS: (SIMPLE_STRING x3)
  then show ?thesis
  proof(cases "isSimpleChar c")
    case True
    with assms SS show ?thesis
    proof(cases rule: LexInvHelper.cases)
      case L2: (LexInvHelper2 s1 s2)
      have S2: "rev x3 = s2"
        using L2(3) LexInv.simps SS by auto
      have LexInvStringNT : "isSimpleChar c \<Longrightarrow> LexInv (rev x3) (SIMPLE_STRING x3) \<Longrightarrow> nextToken c ls = Some (ts', ls') \<Longrightarrow> LexInv (rev x3 @ [c]) (SIMPLE_STRING (c # x3))"
        by (simp add: LexInv.simps)
      with L2 SS True assms S2 show ?thesis
        apply(simp del: isSimpleChar.simps add: eq_commute)
        apply(rule LexInvHelper2[where ?s1.0 = s1 and ?s2.0 = "rev x3 @ [c]" and ?ls = "SIMPLE_STRING (c # x3)" and ?ts = ts])
          apply(simp)
        apply(rule LexInvStringNT)
           apply(simp_all del: isSimpleChar.simps)
        by (metis LexInv.cases LexerState.distinct(3) Nil_is_rev_conv hd_append2 list.discI)
    qed
next
  case False
  {fix xs assume "nextTokenInit c = Some(xs, ls')" and TS': "ts' = STRING (rev x3) # xs" 
      and LS: "ls = SIMPLE_STRING x3"
    then have ?thesis
    proof (cases rule: nextTokenInitSplit)
      case WS
      with assms (1) show ?thesis 
      proof(cases)
        case L2:(LexInvHelper2 s1 s2)
        from L2 (3) SS show ?thesis
        proof(cases rule: LexInv.cases)
          case LISS: LexInvSS
          with TS' LS WS L2 (1, 2, 4) show ?thesis
            apply (simp flip: append_assoc eq_commute del: isSimpleChar.simps)
            apply (rule LexInvHelper1)
             apply (rule GlexWSs2)
              apply (rule GlexTKRev[where w="[]", simplified append_Nil])
                 apply assumption
                apply (rule GTokenSt)
                apply (simp add: eq_commute)
               apply (auto intro: isWhiteString.intros)[]
            subgoal by (cases s2) (auto simp del: isSimpleChar.simps)
             apply (rule isWS0)
             apply simp
            using isWhiteSpace_not_simple by simp
        qed auto
      qed
    next
      case AT
      with assms (1) show ?thesis
      proof(cases)
        case L2: (LexInvHelper2 s1 s2)
        from L2 (3) SS show ?thesis
        proof(cases rule: LexInv.cases)
          case LISS: LexInvSS
          have LexInvHelper2Custom: "Glex (s1 @ s2 @ ''@'') (ts @ [STRING (rev x3), AT]) \<Longrightarrow> LexInv [] INITIAL \<Longrightarrow> (s1 @ s2 @ ''@'' \<noteq> [] \<and> isSimpleChar (last (s1 @ s2 @ ''@'')) \<Longrightarrow> \<not> isSimpleChar (hd []) \<or> [] = []) \<Longrightarrow> LexInvHelper (s1 @ s2 @ ''@'') INITIAL (ts @ [STRING (rev x3), AT])"
            by auto
          have GlexCustom: "Glex ((s1 @ s2) @ [c]) ((ts @ [STRING s2]) @ [AT]) \<Longrightarrow> Glex (s1 @ s2 @ ''@'') (ts @ [STRING (rev x3), AT])"
            using LISS(1) SS local.AT(1) by auto
          from TS' AT L2 (1, 2, 4) show ?thesis
            apply(auto intro!: LexInvHelper2Custom simp add: LexInvNil simp del: isSimpleChar.simps)
            apply(rule GlexCustom)
            apply(rule GlexTKRevSS[where ?s1.0 = s1 and ?s2.0 = s2 and ?t = "[c]" and ?ts = ts and ?t' = "AT"])
                apply(simp)
               apply (simp add: GTokenSt LISS(2))
              apply (simp add: GToken.AT)
             apply (simp add: False)
            by (metis hd_Cons_tl list_all_simps(1))
        qed auto
      qed
    next
      case LP
      with assms (1) show ?thesis
      proof (cases)
        case L2: (LexInvHelper2 s1 s2)
        from L2 (3) SS show ?thesis
        proof(cases rule: LexInv.cases)
          case LISS: LexInvSS
          have LexInvHelper2Custom: "Glex (s1 @ s2 @ ''('') (ts @ [STRING (rev x3), LEFT_PAREN]) \<Longrightarrow> LexInv [] INITIAL \<Longrightarrow> (s1 @ s2 @ ''('' \<noteq> [] \<and> isSimpleChar (last (s1 @ s2 @ ''('')) \<Longrightarrow> \<not> isSimpleChar (hd []) \<or> [] = []) \<Longrightarrow> LexInvHelper (s1 @ s2 @ ''('') INITIAL (ts @ [STRING (rev x3), LEFT_PAREN])"
            by auto
          have GlexCustom: "Glex ((s1 @ s2) @ [c]) ((ts @ [STRING s2]) @ [LEFT_PAREN]) \<Longrightarrow> Glex (s1 @ s2 @ ''('') (ts @ [STRING (rev x3), LEFT_PAREN])"
            using LISS(1) SS local.LP(1) by auto
          from TS' LP L2 (1, 2, 4) show ?thesis
            apply(auto intro!: LexInvHelper2Custom simp add: LexInvNil simp del: isSimpleChar.simps)
            apply(rule GlexCustom)
            apply(rule GlexTKRevSS[where ?s1.0 = s1 and ?s2.0 = s2 and ?t = "[c]" and ?ts = ts and ?t' = "LEFT_PAREN"])
                apply(simp)
               apply (simp add: GTokenSt LISS(2))
              apply (simp add: GToken.LEFT_PAREN)
             apply (simp add: False)
            by (metis hd_Cons_tl list_all_simps(1))
        qed auto
      qed
    next
      case RP
      with assms (1) show ?thesis
      proof (cases)
        case L2: (LexInvHelper2 s1 s2)
        from L2 (3) SS show ?thesis
        proof(cases rule: LexInv.cases)
          case LISS: LexInvSS
          have LexInvHelper2Custom: "Glex (s1 @ s2 @ '')'') (ts @ [STRING (rev x3), RIGHT_PAREN]) \<Longrightarrow> LexInv [] INITIAL \<Longrightarrow> (s1 @ s2 @ '')'' \<noteq> [] \<and> isSimpleChar (last (s1 @ s2 @ '')'')) \<Longrightarrow> \<not> isSimpleChar (hd []) \<or> [] = []) \<Longrightarrow> LexInvHelper (s1 @ s2 @ '')'') INITIAL (ts @ [STRING (rev x3), RIGHT_PAREN])"
            by auto
          have GlexCustom: "Glex ((s1 @ s2) @ [c]) ((ts @ [STRING s2]) @ [RIGHT_PAREN]) \<Longrightarrow> Glex (s1 @ s2 @ '')'') (ts @ [STRING (rev x3), RIGHT_PAREN])"
            using LISS(1) SS local.RP(1) by auto
          from TS' RP L2 (1, 2, 4) show ?thesis
            apply(auto intro!: LexInvHelper2Custom simp add: LexInvNil simp del: isSimpleChar.simps)
            apply(rule GlexCustom)
            apply(rule GlexTKRevSS[where ?s1.0 = s1 and ?s2.0 = s2 and ?t = "[c]" and ?ts = ts and ?t' = "RIGHT_PAREN"])
                apply(simp)
               apply (simp add: GTokenSt LISS(2))
              apply (simp add: GToken.RIGHT_PAREN)
             apply (simp add: False)
            by (metis hd_Cons_tl list_all_simps(1))
        qed auto
      qed
    next
      case LA
      with assms (1) show ?thesis
      proof (cases)
        case L2: (LexInvHelper2 s1 s2)
        from L2 (3) SS show ?thesis
        proof(cases rule: LexInv.cases)
          case LISS: LexInvSS
          have LexInvHelper2Custom: "Glex (s1 @ s2 @ ''<'') (ts @ [STRING (rev x3), LEFT_ANGLE]) \<Longrightarrow> LexInv [] INITIAL \<Longrightarrow> (s1 @ s2 @ ''<'' \<noteq> [] \<and> isSimpleChar (last (s1 @ s2 @ ''<'')) \<Longrightarrow> \<not> isSimpleChar (hd []) \<or> [] = []) \<Longrightarrow> LexInvHelper (s1 @ s2 @ ''<'') INITIAL (ts @ [STRING (rev x3), LEFT_ANGLE])"
            by auto
          have GlexCustom: "Glex ((s1 @ s2) @ [c]) ((ts @ [STRING s2]) @ [LEFT_ANGLE]) \<Longrightarrow> Glex (s1 @ s2 @ ''<'') (ts @ [STRING (rev x3), LEFT_ANGLE])"
            using LISS(1) SS local.LA(1) by auto
          from TS' LA L2 (1, 2, 4) show ?thesis
            apply(auto intro!: LexInvHelper2Custom simp add: LexInvNil simp del: isSimpleChar.simps)
            apply(rule GlexCustom)
            apply(rule GlexTKRevSS[where ?s1.0 = s1 and ?s2.0 = s2 and ?t = "[c]" and ?ts = ts and ?t' = "LEFT_ANGLE"])
                apply(simp)
               apply (simp add: GTokenSt LISS(2))
              apply (simp add: GToken.LEFT_ANGLE)
             apply (simp add: False)
            by (metis hd_Cons_tl list_all_simps(1))
        qed auto
      qed
    next
      case RA
      with assms (1) show ?thesis
      proof (cases)
        case L2: (LexInvHelper2 s1 s2)
        from L2 (3) SS show ?thesis
        proof(cases rule: LexInv.cases)
          case LISS: LexInvSS
          have LexInvHelper2Custom: "Glex (s1 @ s2 @ ''>'') (ts @ [STRING (rev x3), RIGHT_ANGLE]) \<Longrightarrow> LexInv [] INITIAL \<Longrightarrow> (s1 @ s2 @ ''>'' \<noteq> [] \<and> isSimpleChar (last (s1 @ s2 @ ''>'')) \<Longrightarrow> \<not> isSimpleChar (hd []) \<or> [] = []) \<Longrightarrow> LexInvHelper (s1 @ s2 @ ''>'') INITIAL (ts @ [STRING (rev x3), RIGHT_ANGLE])"
            by auto
          have GlexCustom: "Glex ((s1 @ s2) @ [c]) ((ts @ [STRING s2]) @ [RIGHT_ANGLE]) \<Longrightarrow> Glex (s1 @ s2 @ ''>'') (ts @ [STRING (rev x3), RIGHT_ANGLE])"
            using LISS(1) SS local.RA(1) by auto
          from TS' RA L2 (1, 2, 4) show ?thesis
            apply(auto intro!: LexInvHelper2Custom simp add: LexInvNil simp del: isSimpleChar.simps)
            apply(rule GlexCustom)
            apply(rule GlexTKRevSS[where ?s1.0 = s1 and ?s2.0 = s2 and ?t = "[c]" and ?ts = ts and ?t' = "RIGHT_ANGLE"])
                apply(simp)
               apply (simp add: GTokenSt LISS(2))
              apply (simp add: GToken.RIGHT_ANGLE)
             apply (simp add: False)
            by (metis hd_Cons_tl list_all_simps(1))
        qed auto
      qed
    next
      case CO
      with assms (1) show ?thesis
      proof (cases)
        case L2: (LexInvHelper2 s1 s2)
        from L2 (3) SS show ?thesis
        proof(cases rule: LexInv.cases)
          case LISS: LexInvSS
          have LexInvHelper2Custom: "Glex (s1 @ s2 @ '','') (ts @ [STRING (rev x3), COMMA]) \<Longrightarrow> LexInv [] INITIAL \<Longrightarrow> (s1 @ s2 @ '','' \<noteq> [] \<and> isSimpleChar (last (s1 @ s2 @ '','')) \<Longrightarrow> \<not> isSimpleChar (hd []) \<or> [] = []) \<Longrightarrow> LexInvHelper (s1 @ s2 @ '','') INITIAL (ts @ [STRING (rev x3), COMMA])"
            by auto
          have GlexCustom: "Glex ((s1 @ s2) @ [c]) ((ts @ [STRING s2]) @ [COMMA]) \<Longrightarrow> Glex (s1 @ s2 @ '','') (ts @ [STRING (rev x3), COMMA])"
            using LISS(1) SS local.CO(1) by auto
          from TS' CO L2 (1, 2, 4) show ?thesis
            apply(auto intro!: LexInvHelper2Custom simp add: LexInvNil simp del: isSimpleChar.simps)
            apply(rule GlexCustom)
            apply(rule GlexTKRevSS[where ?s1.0 = s1 and ?s2.0 = s2 and ?t = "[c]" and ?ts = ts and ?t' = "COMMA"])
                apply(simp)
               apply (simp add: GTokenSt LISS(2))
              apply (simp add: GToken.COMMA)
             apply (simp add: False)
            by (metis hd_Cons_tl list_all_simps(1))
        qed auto
      qed
    next
      case SC
      with assms (1) show ?thesis
      proof (cases)
        case L2: (LexInvHelper2 s1 s2)
        from L2 (3) SS show ?thesis
        proof(cases rule: LexInv.cases)
          case LISS: LexInvSS
          have LexInvHelper2Custom: "Glex (s1 @ s2 @ '';'') (ts @ [STRING (rev x3), SEMICOLON]) \<Longrightarrow> LexInv [] INITIAL \<Longrightarrow> (s1 @ s2 @ '';'' \<noteq> [] \<and> isSimpleChar (last (s1 @ s2 @ '';'')) \<Longrightarrow> \<not> isSimpleChar (hd []) \<or> [] = []) \<Longrightarrow> LexInvHelper (s1 @ s2 @ '';'') INITIAL (ts @ [STRING (rev x3), SEMICOLON])"
            by auto
          have GlexCustom: "Glex ((s1 @ s2) @ [c]) ((ts @ [STRING s2]) @ [SEMICOLON]) \<Longrightarrow> Glex (s1 @ s2 @ '';'') (ts @ [STRING (rev x3), SEMICOLON])"
            using LISS(1) SS local.SC(1) by auto
          from TS' SC L2 (1, 2, 4) show ?thesis
            apply(auto intro!: LexInvHelper2Custom simp add: LexInvNil simp del: isSimpleChar.simps)
            apply(rule GlexCustom)
            apply(rule GlexTKRevSS[where ?s1.0 = s1 and ?s2.0 = s2 and ?t = "[c]" and ?ts = ts and ?t' = "SEMICOLON"])
                apply(simp)
               apply (simp add: GTokenSt LISS(2))
              apply (simp add: GToken.SEMICOLON)
             apply (simp add: False)
            by (metis hd_Cons_tl list_all_simps(1))
        qed auto
      qed
    next
      case LC
      with assms (1) show ?thesis 
      proof(cases)
        case L2:(LexInvHelper2 s1 s2)
        from L2 (3) SS show ?thesis
        proof(cases rule: LexInv.cases)
          case LISS: LexInvSS
          with LC L2 TS' SS show ?thesis thm GlexTKRev
            apply(simp del: isSimpleChar.simps)
            apply(rule LexInvHelper2[where ?s1.0 = "s1 @ s2" and ?s2.0 = "''#''" and ?ls = "LINE_COMMENT" and ?ts = "ts @ [STRING (rev x3)]", simplified])
             apply(simp add: eq_commute del: isSimpleChar.simps)
             apply(rule GlexTKRev[where ?w = "[]", simplified append_Nil])
                apply(simp)
               apply(rule GTokenSt)
               apply(simp add: eq_commute)
              apply(simp add: isWS0)
             apply (metis hd_Cons_tl list_all_simps(1))
            by (simp add: LexInv.simps)
          qed auto
      qed
    next
      case QS
      from assms (1) show ?thesis
      proof(cases)
        case L2: (LexInvHelper2 s1 s2)
        from L2 (3) SS show ?thesis
        proof(cases rule: LexInv.cases)
          case LISS: LexInvSS
          with QS L2 show ?thesis
            apply(simp del: isSimpleChar.simps)
            apply(rule LexInvHelper2[where ?s1.0 = "s1 @ s2" and ?s2.0 = "[CHR 0x22]" and ?ls = "QUOTED_STRING []" and ?ts = "ts @ ts'", simplified])
             apply (smt (verit, ccfv_threshold) GTokenSt GlexTKRev LexInvInit LexInvNil LexerState.inject(2) SS TS' isWS0 list.sel(1) list_all_simps(1) remdups_adj.elims rev_rev_ident self_append_conv2)
            by (simp add: LexInv.simps)
        qed auto
      qed
    next
      case SS':  SS
      then show ?thesis
        using False by auto
    qed}
  with assms(2, 1) show ?thesis unfolding SS nextToken.simps if_not_P [OF False] thm GTokenSt GlexNilNil GlexTKRev GlexWSNil LexInvHelper2 LexInvLC append.right_neutral append_assoc append_eq_append_conv2 list_all_simps(2) rev.simps(1) same_append_eq
    by(auto split: option.splits)
qed
next
  case LC: LINE_COMMENT
  then show ?thesis 
  proof (cases "isLineCommentEnd c")
    case True
    with LC assms show ?thesis
      apply(auto)
      apply(elim LexInvHelper.cases LexInv.cases)
         apply(simp_all)
      apply(rule LexInvHelper1)
       apply(rule GlexWSs2)
        apply(simp)
       apply(rule isWhiteString.intros(2))
      using isLineCommentEnd_not_simple apply simp_all
      done
  next
    case False
    with LC assms show ?thesis
      by(auto split: char.splits bool.splits dest!: GlexNil elim!: LexInvHelper.cases LexInv.cases simp add: LexInvHelper2 LexInvLC)
  qed
qed


(*
  Idea: We express the lexer's completeness using the auxiliary predicate lexRun.
  Intuitively, "lexRun ls s ts ls'" means that running the lexer from state ls
  on the input s is successful and yields the token list ts and new state ls'.
  (lexRun could alternatively be defined using LexerStepCaller.)
*)

inductive lexRun :: "LexerState \<Rightarrow> string \<Rightarrow> TokenType list \<Rightarrow> LexerState \<Rightarrow> bool" where
  "lexRun ls [] [] ls"
| "nextToken c ls = Some (ts, ls') \<Longrightarrow> lexRun ls' s ts' ls'' \<Longrightarrow> lexRun ls (c # s) (ts @ ts') ls''"

(*
  The completeness property is that "Glex s ts" implies "\<exists>ls. lexRun INITIAL s ts ls".
  This is naturally proved by induction over Glex (with some generalisation, see below).
  The advantage is that we can avoid LexInvHelper for this direction. As LexInvHelper
  is defined using Glex on a prefix of the string, it clashes with Glex's inductive
  definition, which is recursive on a suffix of the string.
*)

(* Helper lemmas *)
lemma lexRun_Some_Nil: "nextToken c ls = Some ([], ls') \<Longrightarrow> lexRun ls' s ts' ls'' \<Longrightarrow> lexRun ls (c # s) ts' ls''"
  using lexRun.intros(2)[where ts="[]"] by simp

lemma lexRun_singleton: "nextToken c ls = Some (ts, ls') \<Longrightarrow> lexRun ls [c] ts ls'"
  using lexRun.intros(2)[where ts'="[]"] by (simp add: lexRun.intros(1))

lemma lexRun_append: "lexRun ls s ts ls' \<Longrightarrow> lexRun ls' s' ts' ls'' \<Longrightarrow> lexRun ls (s@s') (ts@ts') ls''"
proof (induction ls s ts ls' pred: lexRun)
  case 1
  then show ?case by simp
next
  case (2 c ls ts ls' s ts')
  then show ?case by (simp add: lexRun.intros(2))
qed

lemma lexRun_append_char: "lexRun ls [c] ts ls'\<Longrightarrow> lexRun ls' s' ts' ls'' \<Longrightarrow> lexRun ls (c # s') (ts@ts') ls''"
  using lexRun_append by fastforce

lemma lexRun_append_Nil1: "lexRun ls s [] ls' \<Longrightarrow> lexRun ls' s' ts' ls'' \<Longrightarrow> lexRun ls (s@s') ts' ls''"
  using lexRun_append[where ts="[]"] by simp

lemma lexRun_append_Cons: "lexRun ls s [t] ls' \<Longrightarrow> lexRun ls' s' ts' ls'' \<Longrightarrow> lexRun ls (s@s') (t#ts') ls''"
  using lexRun_append[where ts="[t]"] by simp

lemma lexRun_QS_single: "a \<noteq> CHR 0x22 \<Longrightarrow> lexRun (QUOTED_STRING []) [a] [] (QUOTED_STRING [a])"
  apply(rule lexRun.intros(2)[where ?ls = "QUOTED_STRING []" and ?c = a and ?s = "[]" and ?ts = "[]" and ?ts' = "[]" and ?ls' = "QUOTED_STRING [a]" and ls'' = "QUOTED_STRING [a]", simplified append_Nil])
  by(auto simp add: lexRun.intros(1))

lemma lexRun_QS_double: "b \<noteq> CHR 0x22 \<Longrightarrow> lexRun (QUOTED_STRING [a]) [b] [] (QUOTED_STRING [b, a])"
  apply(rule lexRun.intros(2)[where ?ls = "QUOTED_STRING [a]" and ?c = b and ?s = "[]" and ?ts = "[]" and ?ts' = "[]" and ?ls' = "QUOTED_STRING [b, a]" and ls'' = "QUOTED_STRING [b, a]", simplified append_Nil])
  by (auto simp add: lexRun.intros(1))

lemma lexRun_Cons_QS: assumes "a \<noteq> CHR 0x22" and "lexRun (QUOTED_STRING [a]) s [] (QUOTED_STRING (rev s @ [a]))" 
  shows "lexRun (QUOTED_STRING []) (a # s) [] (QUOTED_STRING (rev s @ [a]))"
  apply(rule lexRun.intros(2)[where ?ls = "QUOTED_STRING []" and ?c = a and ?s = s and ?ts = "[]" and ?ts' = "[]" and ?ls' = "QUOTED_STRING [a]" and ls'' = "QUOTED_STRING (rev s @ [a])", simplified])
  by (simp_all add: assms)

lemma lexRun_QS: assumes "list_all (\<lambda>x. x \<noteq> CHR 0x22) s" 
  shows "lexRun INITIAL (CHR 0x22 # s @ [CHR 0x22]) [STRING s] INITIAL"
proof -
  have part1: "nextToken (CHR 0x22) INITIAL = Some ([], QUOTED_STRING [])"
    by (auto)
  moreover have part2: "lexRun (QUOTED_STRING list) s [] (QUOTED_STRING (rev s @ list))" for list
    using assms
  proof(induction s arbitrary: list)
    case Nil
    then show ?case 
      by (simp add: lexRun.intros)
  next
    case (Cons a s) thm Cons GTokenQSt lexRun.intros(2)
    then show ?case
      by(auto intro: lexRun_Some_Nil)
  qed
  moreover have part3: "lexRun (QUOTED_STRING (rev s)) ([CHR 0x22]) [STRING s] INITIAL"
    by (simp add: lexRun_singleton)
  from GlexTK assms show ?thesis
    using part1 part2[of "[]", simplified] part3 lexRun_Some_Nil lexRun_append_Nil1 by blast
qed

lemma lexRun_Cons_SS: assumes "isSimpleChar a" and "lexRun (SIMPLE_STRING [a]) s [] (SIMPLE_STRING (rev s @ [a]))" 
  shows "lexRun INITIAL (a # s) [] (SIMPLE_STRING (rev s @ [a]))" thm lexRun.intros(2)[where ?ls = "INITIAL" and ?c = a and ?s = s and ?ts = "[]" and ?ts' = "[]" and ?ls' = "SIMPLE_STRING [a]" and ls'' = "SIMPLE_STRING (rev s @ [a])", simplified append_Nil]
  apply(rule lexRun.intros(2)[where ?ls = "INITIAL" and ?c = a and ?s = s and ?ts = "[]" and ?ts' = "[]" and ?ls' = "SIMPLE_STRING [a]" and ls'' = "SIMPLE_STRING (rev s @ [a])", simplified append_Nil])
  apply (metis assms(1) isSimpleChar_nextTokenInit nextToken.simps(1))
  by(simp add: assms)

lemma lexRun_SS: assumes "isSimpleString s" shows "lexRun INITIAL s [] (SIMPLE_STRING (rev s))"
proof -
  obtain c s' where eq: "s = c # s'" and c: "isSimpleChar c" and s': "list_all isSimpleChar s'"
    by (metis assms list.exhaust list_all_simps(1))
  have "nextToken c INITIAL = Some ([], SIMPLE_STRING [c])"
    using c by (simp add: isSimpleChar_nextTokenInit del: nextTokenInit.simps)
  moreover have "lexRun (SIMPLE_STRING a) s' [] (SIMPLE_STRING (rev s' @ a))" for a
    using s'
  proof (induction s' arbitrary: a)
    case Nil
    then show ?case by (simp add: lexRun.intros(1))
  next
    case (Cons c' s')
    then show ?case
      by (auto simp del: isSimpleChar.simps intro: lexRun_Some_Nil)
  qed
  ultimately show ?thesis
    by (simp add: eq lexRun_Some_Nil)
qed

(*
  The next two lemmas are each needed in both Glex cases.
  See the main lemma Glex_lexRun for an explanation of the second one.
*)

lemma isWhiteString_lexRun: "isWhiteString s \<Longrightarrow> lexRun INITIAL s [] INITIAL"
proof (induction s pred: isWhiteString)
  case (isWS0 s)
  then show ?case
  proof (induction s)
    case Nil
    then show ?case by (auto intro: lexRun.intros)
  next
    case (Cons c s)
    moreover have "isWhiteSpace c" using Cons by simp
    then have "nextToken c INITIAL = Some ([], INITIAL)"
      by induction auto
    ultimately show ?case
      by (auto intro: lexRun_Some_Nil)
  qed
next
  case (isWS1 s c)
  have "nextToken (CHR ''#'') INITIAL = Some ([], LINE_COMMENT)" by simp
  moreover have "lexRun LINE_COMMENT (s @ [c]) [] INITIAL"
    using isWS1
  proof (induction s)
    case Nil
    then have "nextToken c LINE_COMMENT = Some ([], INITIAL)"
      by (auto)
    then show ?case
      by (auto intro: lexRun.intros(1) lexRun_Some_Nil)
  next
    case (Cons c' s)
    then have "nextToken c' LINE_COMMENT = Some ([], LINE_COMMENT)"
      by (auto split: char.split bool.split)
    with Cons show ?case by (simp add: lexRun_Some_Nil)
  qed
  ultimately show ?case by (simp add: lexRun_Some_Nil)
next
  case (isWS2 s1 s2)
  then show ?case
    by (auto simp add: lexRun_append_Nil1)
qed

lemma isWhiteString_lexRun_SIMPLE_STRING:
  "isWhiteString (c # s) \<Longrightarrow> \<not> isSimpleChar c \<Longrightarrow>
  lexRun (SIMPLE_STRING s') (c # s) [STRING (rev s')] INITIAL"
proof (induction "(c # s)" arbitrary: s pred: isWhiteString)
  case isWS0
  then have "isWhiteSpace c" by simp
  then have "nextTokenInit c = Some ([], INITIAL)"
    by induction auto
  then have "nextToken c (SIMPLE_STRING s') = Some ([STRING (rev s')], INITIAL)"
    by (simp add: isWS0(2) del: isSimpleChar.simps nextTokenInit.simps)
  moreover have "lexRun INITIAL s [] INITIAL"
    using isWS0(1) by (simp add: isWhiteString_lexRun isWhiteString.intros)
  ultimately show ?case by (rule lexRun.intros(2)[where ts'="[]", simplified])
next
  case (isWS1 w c')
  from isWS1 (1, 2) have "lexRun LINE_COMMENT (w @ [c']) [] INITIAL"
  proof (induction w)
    case Nil
    then show ?case 
      by(auto simp add: lexRun_Some_Nil lexRun.intros(1))
  next
    case (Cons a s)
    then show ?case 
      by (auto intro!: lexRun_Some_Nil split: char.splits bool.splits)
  qed
  then show ?case thm isWS1
    using isWS1 (3)[symmetric] isWS1 (4) lexRun_append_char [where ?ls' = "LINE_COMMENT" and ?ls'' = "INITIAL" and ?ts = "[STRING (rev s')]" and ?ts' = "[]" and ?c = c and ?ls = "SIMPLE_STRING s'" and ?s' = "w@[c']"]
    by (auto simp add: lexRun_singleton lexRun.intros(1))
next
  case (isWS2 s1 s2)
  then show ?case (* case distinction on s1? *)
  proof(cases s1 type: list)
    case Nil
    with isWS2 show ?thesis
      by simp
  next
    case (Cons a list)
    with isWS2 Cons have lR1: "lexRun (SIMPLE_STRING s') (a#list) [STRING (rev s')] INITIAL"
      by (auto)
    from isWS2 have lR2: "lexRun INITIAL s2 [] INITIAL" by (auto simp add: isWhiteString_lexRun)
    show ?thesis
      using lexRun_append[OF lR1 lR2] Cons isWS2 by simp
  qed
qed

lemma lexRun_SS_SS: "GToken (c#s1) t \<Longrightarrow> \<not>isSimpleChar c \<Longrightarrow> lexRun (SIMPLE_STRING s) (c#s1) [(STRING (rev s)), t] INITIAL \<or> lexRun (SIMPLE_STRING s) (c#s1) [STRING (rev s)] (SIMPLE_STRING (rev s1)) \<and> isSimpleString s1"
proof (induction "(c#s1)" t arbitrary: s pred: GToken)
  case AT
  then show ?case by(auto simp del: isSimpleChar.simps simp add: eq_commute intro: lexRun_singleton)
      (*apply-apply(rule disjI1)
    apply (simp del: isSimpleChar.simps)
    apply(rule lexRun_singleton )
    by (simp del: isSimpleChar.simps add: eq_commute)*)
next
  case LEFT_PAREN
  then show ?case by(auto simp del: isSimpleChar.simps simp add: eq_commute intro: lexRun_singleton)
next
  case RIGHT_PAREN
  then show ?case by(auto simp del: isSimpleChar.simps simp add: eq_commute intro: lexRun_singleton)
next
  case LEFT_ANGLE
  then show ?case by(auto simp del: isSimpleChar.simps simp add: eq_commute intro: lexRun_singleton)
next
  case RIGHT_ANGLE
  then show ?case by(auto simp del: isSimpleChar.simps simp add: eq_commute intro: lexRun_singleton)
next
  case COMMA
  then show ?case by(auto simp del: isSimpleChar.simps simp add: eq_commute intro: lexRun_singleton)
next
  case SEMICOLON
  then show ?case by(auto simp del: isSimpleChar.simps simp add: eq_commute intro: lexRun_singleton)
next
  case GTokenSt
  then show ?case
    apply-apply(rule disjI1)
    by (simp del: isSimpleChar.simps)
next
  case (GTokenQSt s')
  have part1: "nextToken (CHR 0x22) (SIMPLE_STRING s) = Some ([STRING (rev s)], QUOTED_STRING [])"
    by (auto)
  moreover have part2: "lexRun (QUOTED_STRING list) s' [] (QUOTED_STRING (rev s' @ list))" for list
    using GTokenQSt(1)
  proof(induction s' arbitrary: list)
    case Nil
    then show ?case 
      by (simp add: lexRun.intros)
  next
    case (Cons a s) thm Cons GTokenQSt lexRun.intros(2)
    then show ?case
      by(auto intro: lexRun_Some_Nil)
  qed
  moreover have part3: "lexRun (QUOTED_STRING (rev s')) ([CHR 0x22]) [STRING s'] INITIAL"
    by (simp add: lexRun_singleton)
  with GTokenQSt show ?case thm GTokenQSt(3)[simplified eq_commute]
    apply-apply(rule disjI1)
    apply(rule lexRun.intros(2)[where ?ls = "SIMPLE_STRING s" and ?c = c and ?s = s1 and ?ts = "[STRING (rev s)]" and ?ts' = "[STRING s']" and ?ls' = "QUOTED_STRING []" and ls'' = "INITIAL", simplified append_Nil append_Cons])
    using part1 apply simp
    apply(simp del: isSimpleChar.simps add: GTokenQSt(3)[simplified eq_commute])
    apply(rule lexRun_append_Nil1[where ?s = s' and s' = "[c]" and ?ts' = "[STRING s']" and ?ls = "QUOTED_STRING []" and ?ls' = "QUOTED_STRING (rev s')" and ?ls'' = "INITIAL"])
     apply (metis append_Nil2 part2)
    by(simp) (*uses part3*)
qed

lemma lexRun_INITIAL_SS: "GToken s1 t \<Longrightarrow> lexRun INITIAL s1 [t] INITIAL \<or> lexRun INITIAL s1 [] (SIMPLE_STRING (rev s1)) \<and> isSimpleString s1"
proof (induction s1 t pred: GToken)
  case AT
  show ?case by (auto intro: lexRun_singleton)
next
  case LEFT_PAREN
  show ?case by (auto intro: lexRun_singleton)
next
  case RIGHT_PAREN
  show ?case by (auto intro: lexRun_singleton)
next
  case LEFT_ANGLE
  show ?case by (auto intro: lexRun_singleton)
next
  case RIGHT_ANGLE
  show ?case by (auto intro: lexRun_singleton)
next
  case COMMA
  show ?case by (auto intro: lexRun_singleton)
next
  case SEMICOLON
  show ?case by (auto intro: lexRun_singleton)
next
  case (GTokenSt s)
  then show ?case
    using lexRun_SS by blast
next
  case (GTokenQSt s)
  then show ?case
    using lexRun_QS by blast
qed

(*
  The main completeness lemma.
  Note that the lexer sometimes begin reading a new token from a state other than
  INITIAL. This happens if the preceding token was a simple string. Therefore we
  must prove a more general form which includes a second goal for that case.
  The predicate tokenEndState propagates the information that there are two possible
  states after reading a token.
*)

lemma "isSimpleString s \<Longrightarrow> Glex s [STRING s]" thm GlexTK[where ?w = "[]" and ?s1.0 = s and ?s2.0 = "[]" and ?t = "STRING s" and ?ts = "[]", simplified]
  apply(rule GlexTK[where ?w = "[]" and ?s1.0 = s and ?s2.0 = "[]" and ?t = "STRING s" and ?ts = "[]", simplified])
  by (simp_all add: GTokenSt isWS0)

definition "tokenEndState ls = (ls = INITIAL \<or> (\<exists>s. ls = SIMPLE_STRING s))"


lemma Glex_lexRun: "Glex s ts \<Longrightarrow> lexRun INITIAL s ts INITIAL \<or>
  (\<exists>ts' s'. ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and>  lexRun INITIAL s ts' (SIMPLE_STRING (rev s')))" and
  "Glex s ts \<Longrightarrow> s = c # s0 \<Longrightarrow> \<not> isSimpleChar c \<Longrightarrow> lexRun (SIMPLE_STRING (rev s'')) s (STRING s'' # ts) INITIAL \<or> 
  (\<exists>ts' s'. ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and> lexRun (SIMPLE_STRING (rev s'')) s (STRING s'' # ts') (SIMPLE_STRING (rev s')))"
proof(induction s ts arbitrary: c s0 s'' rule: Glex.induct)
  case (GlexWS xs)
  {
    case 1
    with GlexWS show ?case
      by (simp add: isWhiteString_lexRun)
  next 
    case 2
    with GlexWS show ?case
      by (metis isWhiteString_lexRun_SIMPLE_STRING rev_rev_ident)
  }
next
  case (GlexTK s1 t s2 ts w)
  {
    case 1
    have part1: "lexRun INITIAL w [] INITIAL"
      using GlexTK isWhiteString_lexRun by simp
    have part2: "lexRun INITIAL s1 [t] INITIAL \<or> lexRun INITIAL s1 [] (SIMPLE_STRING (rev s1)) \<and> isSimpleString s1"
      using GlexTK(1) lexRun_INITIAL_SS by simp
    then show ?case
    proof
      assume "lexRun INITIAL s1 [t] INITIAL"
      then show ?thesis
        using part1 GlexTK.IH(1)
        by (smt (z3) append.assoc append_Nil2 lexRun_append rev_append rev_eq_Cons_iff rev_rev_ident)
    next
      assume INITIAL_SS: "lexRun INITIAL s1 [] (SIMPLE_STRING (rev s1)) \<and> isSimpleString s1"
      then have s2Info: "s2 = [] \<or> \<not> isSimpleChar (hd s2) \<and> s2 \<noteq> []"
        using GlexTK.hyps(4) by auto
      then show ?thesis
      proof
        assume s2Nil: "s2 = []"
        then have tsNil: "ts = []"
          using GlexNil GlexTK.hyps(2) by auto
        have "\<exists>ts' s'. t # ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and> lexRun INITIAL (w @ s1 @ s2) ts' (SIMPLE_STRING (rev s'))"
          using GTokenSSt GlexTK.hyps(1) INITIAL_SS lexRun_append_Nil1 part1 s2Nil tsNil by fastforce
        then show ?thesis
          by blast
      next
        assume s2hd: "\<not> isSimpleChar (hd s2) \<and> s2 \<noteq> []"
        then have "lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts) INITIAL \<or> (\<exists>ts' s'. ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and> lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts') (SIMPLE_STRING (rev s')))"
          apply(intro GlexTK(6)[where ?c = "(hd s2)" and ?s0.0 = "(tl s2)" and ?s'' = s1])
          by simp_all
        then show ?thesis
        proof
          assume assm_s2: "lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts) INITIAL"
          have tInfo: "t = (STRING s1)"
            by (simp add: GTokenSSt GlexTK.hyps(1) INITIAL_SS)
          then show ?thesis unfolding tInfo
            by (meson INITIAL_SS assm_s2 lexRun_append_Nil1 part1)
        next
          assume "\<exists>ts' s'. ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and> lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts') (SIMPLE_STRING (rev s'))"
          then show ?thesis (*why doesn't sledgehammer find a solution then I name the assm above?*)
            by (metis GTokenSSt GlexTK.hyps(1) INITIAL_SS append_butlast_last_id append_is_Nil_conv butlast.simps(2) butlast_snoc last.simps last_snoc lexRun_append_Nil1 list.discI part1)
        qed
      qed
    qed
  next
    case 2
    have w: "w = [] \<or> w \<noteq> [] \<and> c = (hd w)"
      by (metis "2.prems"(1) hd_append2 list.sel(1))
    then show ?case
    proof
      assume assm_w: "w = []"
      then have "lexRun  (SIMPLE_STRING (rev s'')) w []  (SIMPLE_STRING (rev s''))"
        by (simp add: lexRun.intros(1))
      from assm_w have cInfo: "c = (hd s1)"
        by (metis "2.prems"(1) GTokenNil GlexTK.hyps(1) hd_append list.sel(1))
      have s1Info: "lexRun (SIMPLE_STRING (rev s'')) (c # tl s1) [STRING s'', t] INITIAL \<or> lexRun (SIMPLE_STRING (rev s'')) (c # tl s1) [STRING s''] (SIMPLE_STRING (rev (tl s1))) \<and> isSimpleString (tl s1)"
        thm lexRun_SS_SS[where ?c = c and ?s1.0 = "tl s1" and ?s = "rev s''" and ?t = t, simplified rev_rev_ident]
        apply(rule lexRun_SS_SS[where ?c = c and ?s1.0 = "tl s1" and ?s = "rev s''" and ?t = t, simplified rev_rev_ident])
         apply (metis GTokenNil GlexTK.hyps(1) cInfo list.exhaust_sel)
        using "2.prems"(2) by auto
      from s1Info have "lexRun (SIMPLE_STRING (rev s'')) s1 [STRING s'', t] INITIAL \<or> lexRun (SIMPLE_STRING (rev s'')) s1 [STRING s''] (SIMPLE_STRING (rev (tl s1))) \<and> isSimpleString (tl s1)"
        by (metis GTokenNil GlexTK.hyps(1) cInfo hd_Cons_tl)
      then show ?thesis
      proof
        assume "lexRun (SIMPLE_STRING (rev s'')) s1 [STRING s'', t] INITIAL"
        then show ?thesis
          using GlexTK.IH(1) assm_w lexRun_append by fastforce
      next 
        assume SS_SS: "lexRun (SIMPLE_STRING (rev s'')) s1 [STRING s''] (SIMPLE_STRING (rev (tl s1)))  \<and> isSimpleString (tl s1)"
        then have s2Info: "s2 = [] \<or> \<not> isSimpleChar (hd s2) \<and> s2 \<noteq> []"
          by (smt (verit) GToken.simps GlexTK.hyps(1) GlexTK.hyps(4) list.sel(2) list.sel(3) list_all_append list_all_simps(1))
        then show ?thesis
        proof
          assume s2Nil: "s2 = []"
          then show ?thesis
            by (smt (verit) "2.prems"(1) "2.prems"(2) GToken.simps GlexTK.hyps(1) SS_SS assm_w list.sel(3) list_all_append list_all_simps(1) self_append_conv2)
        next
          assume "\<not> isSimpleChar (hd s2) \<and> s2 \<noteq> []"
          then show ?thesis
            by (smt (verit) "2.prems"(2) GToken.simps GlexTK.hyps(1) SS_SS cInfo list.collapse list.pred_inject(2) list.sel(1) list.sel(3) list_all_append)
        qed
      qed
    next
      assume cInfo: "w \<noteq> [] \<and> c = (hd w)"
      with GlexTK(3, 1, 2, 4, 5, 6) have part1: "lexRun (SIMPLE_STRING (rev s'')) w [STRING s''] INITIAL"
      proof(induction rule: isWhiteString.induct)
        case (isWS0 w')
        with cInfo have "isWhiteSpace (hd w')"
          by (metis list.exhaust_sel list.pred_inject(2))
        then have part1: "lexRun (SIMPLE_STRING (rev s'')) w' [STRING s''] INITIAL"
          by (metis "2.prems"(2) hd_Cons_tl isWS0.hyps isWS0.prems(6) isWhiteString.isWS0 isWhiteString_lexRun_SIMPLE_STRING rev_rev_ident)
        then have part2: "lexRun INITIAL s1 [t] INITIAL \<or> lexRun INITIAL s1 [] (SIMPLE_STRING (rev s1)) \<and> isSimpleString s1"
          using GlexTK(1) lexRun_INITIAL_SS
          by simp
        then show ?case
        proof
          assume assm_s1: "lexRun INITIAL s1 [t] INITIAL"
          then show ?thesis
            using part1 GlexTK.IH(1)
            by (smt (z3) append.assoc append_Nil2 lexRun_append rev_append rev_eq_Cons_iff rev_rev_ident)
        next
          assume INITIAL_SS: "lexRun INITIAL s1 [] (SIMPLE_STRING (rev s1)) \<and> isSimpleString s1"
          then have s2Info: "s2 = [] \<or> \<not> isSimpleChar (hd s2) \<and> s2 \<noteq> []"
            using GlexTK.hyps(4) by auto
          from s2Info show ?thesis
          proof
            assume s2Nil: "s2 = []"
            then have tsNil: "ts = []"
              using GlexNil GlexTK.hyps(2) by auto
            have "\<exists>ts' s'. t # ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and> lexRun INITIAL (w @ s1 @ s2) ts' (SIMPLE_STRING (rev s'))"
              using GTokenSSt GlexTK.hyps(3) INITIAL_SS isWS0.prems(1) isWhiteString_lexRun lexRun_append_Nil1 s2Nil tsNil by fastforce
            then show ?thesis
              by (simp add: part1)
          next
            assume s2hd: "\<not> isSimpleChar (hd s2) \<and> s2 \<noteq> []"
            then have "lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts) INITIAL \<or> (\<exists>ts' s'. ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and> lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts') (SIMPLE_STRING (rev s')))"
              apply(intro GlexTK(6)[where ?c = "(hd s2)" and ?s0.0 = "(tl s2)" and ?s'' = s1])
              by simp_all
            then show ?thesis
            proof
              assume assm_s2: "lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts) INITIAL"
              have tInfo: "t = (STRING s1)"
                by (simp add: GTokenSSt GlexTK.hyps(1) INITIAL_SS)
              then show ?thesis unfolding tInfo
                using INITIAL_SS assm_s2 lexRun_append_Cons lexRun_append_Nil1 part1 by blast
            next
              assume "\<exists>ts' s'. ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and> lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts') (SIMPLE_STRING (rev s'))"
              then show ?thesis
                by (smt (verit, ccfv_SIG) GTokenSSt INITIAL_SS append_assoc append_butlast_last_id append_is_Nil_conv butlast.simps(2) butlast_snoc isWS0.prems(1) last.simps last_snoc lexRun_append_Cons list.discI part1)
            qed
          qed
        qed
      next
        case (isWS1 w' c')
        with cInfo have "(hd w) = CHR ''#''"
          by (metis list.sel(1))
        have part1_1: "lexRun (SIMPLE_STRING (rev s'')) ''#'' [STRING s''] LINE_COMMENT"
          by(auto intro: lexRun_singleton[where ?c = "CHR ''#''" and ?ts = "[STRING s'']" and ?ls = "SIMPLE_STRING (rev s'')" and ?ls' = "LINE_COMMENT"])
        from isWS1(1) have part1_2: "lexRun LINE_COMMENT w' [] LINE_COMMENT"
        proof(induction w')
          case Nil
          then show ?case by(auto intro: lexRun.intros)
        next
          case (Cons a w'')
          have a_Info: "(Not \<circ> isLineCommentEnd) a"
            using Cons.prems by auto
          with Cons show ?case 
            by(auto intro: lexRun.intros(2)[where ?c = a and ?s = w'' and ?ts = "[]" and ?ts' = "[]" and ?ls = "LINE_COMMENT" and ?ls' = "LINE_COMMENT" and ?ls'' = "LINE_COMMENT", simplified append_Nil])
        qed
        from isWS1(2) have part1_3: "lexRun LINE_COMMENT [c'] [] INITIAL"
          by(auto intro: lexRun_singleton[where ?c = c' and ?ts = "[]" and ?ls = "LINE_COMMENT" and ?ls' = "INITIAL"])
        then have part1: "lexRun (SIMPLE_STRING (rev s'')) (CHR ''#'' # w' @ [c']) [STRING s''] INITIAL"
          using lexRun_append_Nil1 lexRun_append_char part1_1 part1_2 part1_3 by fastforce
        then have part2: "lexRun INITIAL s1 [t] INITIAL \<or> lexRun INITIAL s1 [] (SIMPLE_STRING (rev s1)) \<and> isSimpleString s1"
          using GlexTK(1) lexRun_INITIAL_SS
          by simp
        then show ?case
        proof
          assume assm_s1: "lexRun INITIAL s1 [t] INITIAL"
          then show ?thesis
            using part1 GlexTK.IH(1)
            by (smt (z3) append.assoc append_Nil2 lexRun_append rev_append rev_eq_Cons_iff rev_rev_ident)
        next
          assume INITIAL_SS: "lexRun INITIAL s1 [] (SIMPLE_STRING (rev s1)) \<and> isSimpleString s1"
          then have s2Info: "s2 = [] \<or> \<not> isSimpleChar (hd s2) \<and> s2 \<noteq> []"
            using GlexTK.hyps(4) by auto
          from s2Info show ?thesis
          proof
            assume s2Nil: "s2 = []"
            then have tsNil: "ts = []"
              using GlexNil GlexTK.hyps(2) by auto
            have "\<exists>ts' s'. t # ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and> lexRun INITIAL (w @ s1 @ s2) ts' (SIMPLE_STRING (rev s'))"
              using GTokenSSt GlexTK.hyps(3) INITIAL_SS isWS1.prems(1) isWhiteString_lexRun lexRun_append s2Nil tsNil by fastforce
            then show ?thesis
              by (simp add: part1)
          next
            assume s2hd: "\<not> isSimpleChar (hd s2) \<and> s2 \<noteq> []"
            then have "lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts) INITIAL \<or> (\<exists>ts' s'. ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and> lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts') (SIMPLE_STRING (rev s')))"
              apply(intro GlexTK(6)[where ?c = "(hd s2)" and ?s0.0 = "(tl s2)" and ?s'' = s1])
              by simp_all
            then show ?thesis
            proof
              assume assm_s2: "lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts) INITIAL"
              have tInfo: "t = (STRING s1)"
                by (simp add: GTokenSSt GlexTK.hyps(1) INITIAL_SS)
              then show ?thesis unfolding tInfo
                using INITIAL_SS assm_s2 lexRun_append_Cons lexRun_append_Nil1 part1 by blast
            next
              assume "\<exists>ts' s'. ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and> lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts') (SIMPLE_STRING (rev s'))"
              then show ?thesis
                by (smt (verit, ccfv_SIG) GTokenSSt INITIAL_SS append_assoc append_butlast_last_id append_is_Nil_conv butlast.simps(2) butlast_snoc isWS1.prems(1) last.simps last_snoc lexRun_append_Cons list.discI part1)
            qed
          qed
        qed
      next
        case (isWS2 s1' s2')
        have "s1' = [] \<or> s1' \<noteq> []"
          using isWS2.prems(1) by auto
        then show ?case
        proof
          assume s1'Nil: "s1' = []"
          then have "s2' \<noteq> []"
            using isWS2.prems(6) by auto
          then have "lexRun (SIMPLE_STRING (rev s'')) s2' [STRING s''] INITIAL"
          proof -
            have subpart_6_s2: "s1' @ s2' \<noteq> [] \<and> c = hd (s1' @ s2') \<Longrightarrow> s2' \<noteq> [] \<and> c = hd s2'"
              by (simp add: s1'Nil)
            with isWS2 show ?thesis
              apply(intro isWS2(4))
                     apply blast
                    apply blast
                   apply fastforce
                  apply blast
                 apply presburger
                by fastforce
          qed 
          then show ?thesis
            by (metis append.left_neutral s1'Nil)
        next
          assume s1'NotNil: "s1' \<noteq> []"
          then have "lexRun (SIMPLE_STRING (rev s'')) s1' [STRING s''] INITIAL"
          proof -
            from isWS2 show ?thesis
              apply(intro isWS2(3))
                   apply blast
                  apply blast
                 apply fastforce
                apply blast
               apply presburger
              by (metis hd_append2 s1'NotNil)
          qed
          moreover have "lexRun INITIAL s2' [] INITIAL"
            by (simp add: isWS2.hyps(2) isWhiteString_lexRun)
          ultimately show ?thesis
            using lexRun_append_Cons by auto
        qed
      qed
      have part2: "lexRun INITIAL s1 [t] INITIAL \<or> lexRun INITIAL s1 [] (SIMPLE_STRING (rev s1)) \<and> isSimpleString s1"
        using GlexTK(1) lexRun_INITIAL_SS by simp
      then show ?thesis
      proof
        assume "lexRun INITIAL s1 [t] INITIAL"
        then show ?thesis 
          using part1 GlexTK.IH(1)
          by (smt (z3) append.assoc append_Nil2 lexRun_append rev_append rev_eq_Cons_iff rev_rev_ident)
      next
        assume INITIAL_SS: "lexRun INITIAL s1 [] (SIMPLE_STRING (rev s1)) \<and> isSimpleString s1"
        then have s2Info: "s2 = [] \<or> \<not> isSimpleChar (hd s2) \<and> s2 \<noteq> []"
          using GlexTK.hyps(4) by auto
        then show ?thesis
        proof
          assume s2Nil: "s2 = []"
          then have tsNil: "ts = []"
            using GlexNil GlexTK.hyps(2) by auto
          have "\<exists>ts' s'. t # ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and> lexRun INITIAL (w @ s1 @ s2) ts' (SIMPLE_STRING (rev s'))"
            using GTokenSSt GlexTK.hyps(1) GlexTK.hyps(3) INITIAL_SS isWhiteString_lexRun lexRun_append_Nil1 s2Nil tsNil by fastforce
          then show ?thesis 
            by (metis GTokenSSt GlexTK.hyps(1) INITIAL_SS append.left_neutral append.right_neutral lexRun_append part1 s2Nil tsNil)
        next
          assume s2hd: "\<not> isSimpleChar (hd s2) \<and> s2 \<noteq> []"
          then have "lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts) INITIAL \<or> (\<exists>ts' s'. ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and> lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts') (SIMPLE_STRING (rev s')))"
            apply(intro GlexTK(6)[where ?c = "(hd s2)" and ?s0.0 = "(tl s2)" and ?s'' = s1])
            by simp_all
          then show ?thesis
          proof
            assume assm_s2: "lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts) INITIAL"
            have tInfo: "t = (STRING s1)"
              by (simp add: GTokenSSt GlexTK.hyps(1) INITIAL_SS)
            then show ?thesis unfolding tInfo
              by (meson INITIAL_SS assm_s2 lexRun_append_Cons lexRun_append_Nil1 part1)
          next
            assume "\<exists>ts' s'. ts = ts' @ [STRING s'] \<and> isSimpleString s' \<and> lexRun (SIMPLE_STRING (rev s1)) s2 (STRING s1 # ts') (SIMPLE_STRING (rev s'))"
            then show ?thesis
              by (smt (verit, ccfv_SIG) GTokenSSt GlexTK.hyps(1) INITIAL_SS append_assoc append_butlast_last_id append_is_Nil_conv butlast.simps(2) butlast_snoc last.simps last_snoc lexRun_append_Cons list.discI part1)
          qed
        qed
      qed
    qed
  }
qed

(* An idea for a stronger completeness property: *)

lemma lexRun_append1_conv:
  "lexRun ls (s@s') ts ls'' \<longleftrightarrow> (\<exists>ts' ts'' ls'. ts = ts' @ ts'' \<and> lexRun ls s ts' ls' \<and> lexRun ls' s' ts'' ls'')"
  (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then show ?B
    by (induction ls "s @ s'" ts ls'' arbitrary: s pred: lexRun)
      (auto simp add: Cons_eq_append_conv intro: lexRun.intros,
        meson append_eq_appendI lexRun.intros(2))
qed (auto intro!: lexRun_append)

lemma nextTokenComplete:
  assumes "Glex (s@s') ts"
  shows "\<exists>ts' ts'' ls. ts = ts' @ ts'' \<and> lexRun INITIAL s ts' ls"
  using Glex_lexRun[OF assms] apply (auto simp add: lexRun_append1_conv)
  by auto

end
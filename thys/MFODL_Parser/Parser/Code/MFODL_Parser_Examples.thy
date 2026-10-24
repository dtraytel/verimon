theory MFODL_Parser_Examples
  imports MFODL_Efficient_Lexer
begin

section \<open>Examples of the formula parser\<close>

text \<open>A separate session, so that the heap image of \<^session>\<open>MFODL_Parser\<close>, whose
  \<^theory_text>\<open>parser\<close> command takes long, does not depend on the examples.\<close>

subsection \<open>Examples\<close>

text \<open>One evaluation, since each compiles the parser's tables anew: precedences, terms and
  intervals, anonymous variables, aggregations, regular expressions, comments and errors.\<close>

lemma mfodl_examples:
  \<open>(parse_formula ''P(x) OR Q(x) AND R(x) SINCE S(x) SINCE [0,5] T(x)'' = Some
  (FSince dfintv (FOr (FPred (''P'', [TVar ''x''])) (FAnd (FPred (''Q'', [TVar ''x''])) (FPred (''R'', [TVar ''x'']))))
    (FSince (CBnd 0, CBnd 5) (FPred (''S'', [TVar ''x''])) (FPred (''T'', [TVar ''x'']))))) \<and>
   (parse_formula ''PREV P(x) AND NOT Q(x) SINCE R(x)'' = Some
  (FSince dfintv (FPrev dfintv (FAnd (FPred (''P'', [TVar ''x''])) (FNeg (FPred (''Q'', [TVar ''x''])))))
    (FPred (''R'', [TVar ''x''])))) \<and>
   (parse_formula ''A() AND LET P(x) = Q(x) IN P(x) SINCE B()'' = Some
  (FAnd (FPred (''A'', []))
    (FLet (''P'', [TVar ''x'']) (FPred (''Q'', [TVar ''x'']))
      (FSince dfintv (FPred (''P'', [TVar ''x''])) (FPred (''B'', [])))))) \<and>
   (parse_formula ''ONCE (1m, 2h] x > -y * 2 + 1'' = Some
  (FOnce (OBnd 60, CBnd 7200)
    (FLess (TPlus (TMult (TUMinus (TVar ''y'')) (TCst (CInt 2))) (TCst (CInt 1))) (TVar ''x'')))) \<and>
   (parse_formula ''P(_, x) OR Q(_)'' = Some
  (FOr (FExists [''_1''] (FPred (''P'', [TVar ''_1'', TVar ''x''])))
    (FExists [''_2''] (FPred (''Q'', [TVar ''_2'']))))) \<and>
   (parse_formula ''s <- SUM x; g P(g, x)'' = Some
  (FAggreg ''s'' ASum ''x'' [''g''] (FPred (''P'', [TVar ''g'', TVar ''x''])))) \<and>
   (parse_formula ''s <- SUM x; g P(g)'' = None) \<and>
   (parse_formula ''MATCHF [0,5] P(x) Q(x)? + .*'' = Some
  (FFrex (CBnd 0, CBnd 5)
    (RPlus (RConcat (RConcat (RTest (FPred (''P'', [TVar ''x'']))) wild) (RTest (FPred (''Q'', [TVar ''x'']))))
      (RStar wild)))) \<and>
   (parse_formula ''SOMETIMES (* a comment *) P() # another'' = Some (FEventually dfintv (FPred (''P'', [])))) \<and>
   (parse_formula ''P(x) AND'' = None) \<and>
   (parse_formula ''P(x) Q(x)'' = None)\<close>
  by eval

end

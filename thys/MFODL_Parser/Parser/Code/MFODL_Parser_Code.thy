theory MFODL_Parser_Code
  imports MFODL_Lexer_Code "HOL-Library.Code_Binary_Nat"
begin

text \<open>Examples, checked by evaluation. A separate session,
  so that the heap image of \<^session>\<open>MFODL_Parser\<close>, whose \<^theory_text>\<open>parser\<close>
  command takes long, does not depend on them.\<close>

section \<open>Code for the parser tables\<close>

text \<open>The parser's tables are binary tries; with binary naturals, a lookup
  follows the constructors of the index.\<close>

declare tlookup_binary [code]

section \<open>Examples\<close>

text \<open>
  Checked by a single evaluation, since each evaluation compiles the parser's
  tables anew:
  \<^item> \<open>AND\<close> binds tighter than \<open>OR\<close>, both tighter than \<open>SINCE\<close>, which is
    right associative;
  \<^item> a unary temporal operator absorbs the Boolean connectives to its right but not
    a binary temporal operator, and \<open>NOT\<close> binds tightest;
  \<^item> \<open>LET\<close> absorbs everything, also as the right operand of \<open>AND\<close>;
  \<^item> terms, intervals in time units, and \<open>>\<close> as a flipped \<open><\<close>;
  \<^item> anonymous arguments are numbered and existentially quantified;
  \<^item> the aggregated variable must be free in the aggregated formula;
  \<^item> a bare atom of a regular expression is a test followed by a step (\<open>MATCHF\<close>);
  \<^item> comments and synonyms of keywords; syntax errors.
\<close>

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

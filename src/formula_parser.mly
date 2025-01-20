/*
 * This file is part of MONPOLY.
 *
 * Copyright © 2011 Nokia Corporation and/or its subsidiary(-ies).
 * Contact:  Nokia Corporation (Debmalya Biswas: debmalya.biswas@nokia.com)
 *
 * Copyright (C) 2012 ETH Zurich.
 * Contact:  ETH Zurich (Eugen Zalinescu: eugen.zalinescu@inf.ethz.ch)
 *
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, version 2.1 of the
 * License.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library. If not, see
 * http://www.gnu.org/licenses/lgpl-2.1.html.
 *
 * As a special exception to the GNU Lesser General Public License,
 * you may link, statically or dynamically, a "work that uses the
 * Library" with a publicly distributed version of the Library to
 * produce an executable file containing portions of the Library, and
 * distribute that executable file under terms of your choice, without
 * any of the additional requirements listed in clause 6 of the GNU
 * Lesser General Public License. By "a publicly distributed version
 * of the Library", we mean either the unmodified Library as
 * distributed by Nokia, or a modified version of the Library that is
 * distributed under the conditions defined in clause 3 of the GNU
 * Lesser General Public License. This exception does not however
 * invalidate any other reasons why the executable file might be
 * covered by the GNU Lesser General Public License.
 */



%{
  open Predicate
  open MFOTL
  open Misc

  let f str =
    if Misc.debugging Dbg_parsing then
      Printf.eprintf "[Formula_parser] %s\t\n%!" str
    else
      ()

  let var_cnt = ref 0

  (* by default, the time unit is of 1 second *)
  let timeunits (n,c) =
    let d =
      match c with
      | 'd' -> 24 * 60 * 60
      | 'h' -> 60 * 60
      | 'm' -> 60
      | 's' -> 1
      | _ -> failwith "[Formula_parser.time_units] unrecognized time unit"
    in
    Z.of_int (d * n)

  let rec exists varlist f =
    match varlist with
    | [] -> failwith "[Formula_parser.exists] no variables"
    | vl -> Exists (vl, f)

  let rec forall varlist f =
    match varlist with
    | [] -> failwith "[Formula_parser.forall] no variables"
    | vl -> ForAll (vl, f)


  let dfintv = (MFOTL.CBnd Z.zero, MFOTL.Inf)

  let strip str =
    let len = String.length str in
    if str.[0] = '\"' && str.[len-1] = '\"' then
      String.sub str 1 (len-2)
    else
      str



  let check f = f

  let add_ex p =
    let args = Predicate.get_args p in
    let rec proc = function
      | [] -> []
      | (Var v) :: rest when v.[0] = '_' -> v :: (proc rest)
      | _ :: rest -> proc rest
    in
    let vl = proc args in
    let pred = Pred p in
    if vl <> [] then Exists (vl, pred) else pred

  let strip s =
    let len = String.length s in
    assert(s.[0] = '\"' && s.[len-1] = '\"');
    String.sub s 1 (len-2)
  
  let compile_regexp r =
    let len = String.length r in
    assert(r.[0] = 'r' && r.[1] = '\"' && r.[len-1] = '\"');
    let pattern = String.sub r 2 (len-3) in
    try
      f pattern;
      Regexp (pattern, Str.regexp pattern)
    with e ->
      let e_str = Printexc.to_string e in
      failwith (Printf.sprintf "[Formula_parser.compile_regexp] invalid regexp %s (%s)" r e_str)

  (* The rule is: var LARROW aggreg var SC varlist formula  *)
  let aggreg res_var op agg_var groupby_vars f =
    let free_vars = MFOTL.free_vars f in
    let msg b x =
      let kind = if b then "Aggregation" else "Group-by" in
      Printf.sprintf "[Formula_parser.aggreg] %s variable %s is not a free variable in the aggregated formula" kind x
    in
    if not (List.mem agg_var free_vars) then
      failwith (msg true agg_var)
    else
      begin
        List.iter (fun gby_var ->
          if not (List.mem gby_var free_vars) then
            failwith (msg false gby_var)
        ) groupby_vars;
        Aggreg ((TSymb (TAny, 0)),res_var, op, agg_var, groupby_vars, f)
      end

%}

%token FALSE TRUE
%token LPA RPA LSB RSB COM SC DOT QM LD LESSEQ EQ LESS GTR GTREQ STAR LARROW SUBSTRING MATCHES
%token PLUS MINUS SLASH MOD F2I I2F DAY_OF_MONTH MONTH YEAR FORMAT_DATE R2S S2R I2S S2I F2S S2F
%token <string> STR STR_CST REGEXP_CST
%token <Z.t> INT
%token <float> RAT
%token <int*char> TU
%token LET LETPAST IN NOT AND OR IMPL EQUIV EX FA
%token PREV NEXT EVENTUALLY ONCE ALWAYS PAST_ALWAYS SINCE TRIGGER UNTIL RELEASE BAR FREX PREX
%token CNT MIN MAX SUM AVG MED
%token END
%token EOF

/* REDUCE_CONCAT (lowest) is a general "prefer shift over an empty/optional
   production" marker. It tags (a) the regex concatenation/alternation reduce rules,
   so the inherent ambiguous "end the regex vs. start another atom" boundary resolves
   to shift (greedy); and (b) the empty `varlist` and empty `xopttermlist`
   productions, so a following group-by var / arithmetic term is shifted rather than
   committing to the empty list. In every case this is the choice ocamlyacc already
   made by default, now made explicit so the conflict is no longer reported. */
%nonassoc REDUCE_CONCAT
%nonassoc AGGREG
%nonassoc LET IN
%right SINCE TRIGGER UNTIL RELEASE
%nonassoc PREV NEXT EVENTUALLY ONCE ALWAYS PAST_ALWAYS 
%nonassoc EX FA
%left EQUIV
%right IMPL
%left OR
%left AND
%nonassoc LPA
%nonassoc NOT
%nonassoc BASE
%nonassoc QM
%nonassoc RPA


%nonassoc EQ LESSEQ LESS GTR GTREQ SUBSTRING MATCHES         /* comparisons, below arithmetic */
%left PLUS MINUS                                             /* lowest precedence */
%left STAR SLASH MOD                                         /* medium precedence */
%nonassoc UMINUS F2I I2F DAY_OF_MONTH MONTH YEAR FORMAT_DATE /* highest precedence */
/* Regex-atom-start terminals that otherwise have no precedence. Placing them above
   REDUCE_CONCAT makes "shift another atom" win over "end the regex" at the bare-
   formula juxtaposition boundary, matching the prior default-shift behaviour. */
%nonassoc FALSE TRUE LD STR STR_CST REGEXP_CST INT RAT DOT FREX PREX
%nonassoc LETPAST R2S S2R I2S S2I F2S S2F

%start formula
%type <MFOTL.formula> formula

%%


formula:
  | LPA formula RPA                 { f "f()"; $2 }
  | FALSE                           { f "FALSE"; Equal (Cst (Int Z.zero), Cst (Int Z.one)) }
  | TRUE                            { f "TRUE"; Equal (Cst (Int Z.zero), Cst (Int Z.zero)) }
  | predicate                       { f "f(pred)"; $1 }
  | LET predicate EQ formula IN formula
                                    { f "f(let)"; match $2 with
                                                  | Pred p -> Let (p,$4,$6)
                                                  | _ -> failwith "[formula_parser.mly] expected predicate"}
  | LETPAST predicate EQ formula IN formula
                                    { f "f(letpast)"; match $2 with
                                                  | Pred p -> LetPast (p,$4,$6)
                                                  | _ -> failwith "[formula_parser.mly] expected predicate"}
  | term EQ term                    { f "f(eq)"; check (Equal ($1,$3)) }
  | term LESSEQ term                { f "f(leq)"; check (LessEq ($1,$3)) }
  | term LESS term                  { f "f(less)"; check (Less ($1,$3)) }
  | term GTR term                   { f "f(gtr)"; check (Less ($3,$1)) }
  | term GTREQ term                 { f "f(geq)"; check (LessEq ($3,$1)) }
  | formula EQUIV formula           { f "f(<=>)"; Equiv ($1,$3) }
  | formula IMPL formula            { f "f(=>)"; Implies ($1,$3) }
  | formula OR formula              { f "f(or)"; Or ($1,$3) }
  | formula AND formula             { f "f(and)"; And ($1,$3) }
  | NOT formula                     { f "f(not)"; Neg ($2) }
  | EX varlist DOT formula %prec EX { f "f(ex)"; exists $2 $4 }
  | FA varlist DOT formula %prec FA { f "f(fa)"; forall $2 $4 }
  | var LARROW aggreg var formula %prec AGGREG  { f "f(agg1)"; aggreg $1 $3 $4 [] $5 }
  | var LARROW aggreg var SC varlist formula %prec AGGREG
                                    { f "f(agg2)"; aggreg $1 $3 $4 $6 $7 }
  | term SUBSTRING term             { f "f(substring)"; check (Substring ($1, $3)) }
  | term MATCHES term xopttermlist  { f "f(matches)"; check (Matches ($1, $3, $4)) }
  | PREV interval formula           { f "f(prev)"; Prev ($2,$3) }
  | PREV formula                    { f "f(prevdf)"; Prev (dfintv,$2) }
  | NEXT interval formula           { f "f(next)"; Next ($2,$3) }
  | NEXT formula                    { f "f(nextdf)"; Next (dfintv,$2) }
  | EVENTUALLY interval formula     { f "f(ev)"; Eventually ($2,$3) }
  | EVENTUALLY formula              { f "f(evdf)"; Eventually (dfintv,$2) }
  | ONCE interval formula           { f "f(once)"; Once ($2,$3) }
  | ONCE formula                    { f "f(oncedf)"; Once (dfintv,$2) }
  | ALWAYS interval formula         { f "f(always)"; Always ($2,$3) }
  | ALWAYS formula                  { f "f(alwaysdf)"; Always (dfintv,$2) }
  | PAST_ALWAYS interval formula    { f "f(palways)"; PastAlways ($2,$3) }
  | PAST_ALWAYS formula             { f "f(palwaysdf)"; PastAlways (dfintv,$2) }
  | formula SINCE interval formula  { f "f(since)"; Since ($3,$1,$4) }
  | formula SINCE formula           { f "f(sincedf)"; Since (dfintv,$1,$3) }
  | formula TRIGGER interval formula { f "f(triggerdf)"; Trigger ($3,$1,$4) }
  | formula TRIGGER formula         { f "f(triggerdf)"; Trigger (dfintv,$1,$3) }
  | formula UNTIL interval formula  { f "f(until)"; Until ($3,$1,$4) }
  | formula UNTIL formula           { f "f(untildf)"; Until (dfintv,$1,$3) }
  | formula RELEASE interval formula { f "f(releasedf)"; Release ($3,$1,$4) }
  | formula RELEASE formula         { f "f(releasedf)"; Release (dfintv,$1,$3) }

  | FREX interval fregex             { f "f(frexd)"; Frex ($2,$3) }
  | FREX fregex                      { f "f(frexdf)"; Frex (dfintv,$2) }
  | PREX interval pregex             { f "f(prexd)"; Prex ($2,$3) }
  | PREX pregex                      { f "f(prexdf)"; Prex (dfintv,$2) }

/* Stratified into alternation > concatenation > atom to remove the operator
   ambiguities of the old flat `fregex fregex | fregex PLUS fregex` grammar.
   Both levels are right-recursive to preserve the original right-associative
   parse of `a + b + c` and `a b c`. Concatenation now binds tighter than
   alternation (standard regex semantics): `a b + c` is `(a b) + c`. */
fregex:
  | fconcat PLUS fregex              { f "f(plus)"; Plus ($1, $3)}
  | fconcat %prec REDUCE_CONCAT      { $1 }

fconcat:
  | fatom fconcat                    { f "f(concat)"; Concat ($1,$2)}
  | fatom %prec REDUCE_CONCAT        { $1 }

fatom:
  | LPA fregex RPA                   { f "r()"; $2 }
  | DOT                              { f "f(wild)"; wild }
  | formula                          { f "f(fbase)"; Concat(Test ($1),wild)} %prec BASE
  | formula QM                       { f "f(test)"; Test ($1)}
  | fatom STAR                       { f "f(star)"; Star ($1)}

pregex:
  | pconcat PLUS pregex              { f "f(plus)"; Plus ($1, $3)}
  | pconcat %prec REDUCE_CONCAT      { $1 }

pconcat:
  | patom pconcat                    { f "f(concat)"; Concat ($1,$2)}
  | patom %prec REDUCE_CONCAT        { $1 }

patom:
  | LPA pregex RPA                   { f "r()"; $2 }
  | DOT                              { f "f(wild)"; wild }
  | formula                          { f "f(pbase)"; Concat(wild,Test ($1))} %prec BASE
  | formula QM                       { f "f(test)"; Test ($1)}
  | patom STAR                       { f "f(star)"; Star ($1)}


aggreg:
  | CNT                     { f "agg(cnt)"; Cnt }
  | MIN                     { f "agg(min)"; Min }
  | MAX                     { f "agg(max)"; Max }
  | SUM                     { f "agg(sum)"; Sum }
  | AVG                     { f "agg(avg)"; Avg }
  | MED                     { f "agg(med)"; Med }


interval:
  | lbound COM rbound       { f "interval"; ($1,$3) }

lbound:
  | LPA units               { f "opened lbound"; OBnd $2 }
  | LSB units               { f "closed lbound"; CBnd $2 }

rbound:
  | units RPA               { f "opened rbound"; OBnd $1 }
  | units RSB               { f "closed rbound"; CBnd $1 }
  | STAR RPA                { f "no bound(1)"; Inf }
  | STAR RSB                { f "no bound(2)"; Inf }

units:
  | TU                      { f "ts";  timeunits $1 }
  | INT                     { f "int"; $1 }


predicate:
  | pred LPA termlist RPA   { f "p()";
                              let p = Predicate.make_predicate ($1,$3) in
                              add_ex p
                            }

pred:
  | STR                     { f "pred"; $1 }


term:
  | term PLUS term            { f "term(plus)"; Plus ($1, $3) }
  | term MINUS term           { f "term(minus)"; Minus ($1, $3) }
  | term STAR term            { f "term(mult)"; Mult ($1, $3) }
  | term SLASH term           { f "term(div)"; Div ($1, $3) }
  | term MOD term             { f "term(mod)"; Mod ($1, $3) }
  | MINUS term %prec UMINUS   { f "term(uminus)"; UMinus $2 }
  | LPA term RPA              { f "term(paren)"; $2 }
  | F2I LPA term RPA          { f "term(f2i)"; F2i $3 }
  | I2F LPA term RPA          { f "term(i2f)"; I2f $3 }
  | DAY_OF_MONTH LPA term RPA { f "term(day_of_month)"; DayOfMonth $3 }
  | MONTH LPA term RPA        { f "term(month)"; Month $3 }
  | YEAR LPA term RPA         { f "term(year)"; Year $3 }
  | FORMAT_DATE LPA term RPA  { f "term(format_date)"; FormatDate $3 }
  | R2S LPA term RPA          { f "term(r2s)"; R2s $3 }
  | S2R LPA term RPA          { f "term(s2r)"; S2r $3 }
  | I2S LPA term RPA          { f "term(i2s)"; I2s $3 }
  | S2I LPA term RPA          { f "term(s2i)"; S2i $3 }
  | F2S LPA term RPA          { f "term(f2s)"; F2s $3 }
  | S2F LPA term RPA          { f "term(s2f)"; S2f $3 }
  | cst                       { f "term(cst)"; Cst $1 }
  | var                       { f "term(var)"; Var $1 }


cst:
  | INT                     { f "cst(int)"; Int $1 }
  | RAT                     { f "cst(rat)"; Float $1 }
  | STR_CST                 { f "cst(str)"; Str (strip $1) }
  | REGEXP_CST              { f "cst(regex)"; compile_regexp $1 }


termlist:
  | termarg COM termlist    { f "termlist(list)"; $1 :: $3 }
  | termarg                 { f "termlist(end)"; [$1] }
  |                         { f "termlist()"; [] }

/* A predicate argument is a term or the anonymous `_`, which becomes a fresh unnamed
   variable (existentially quantified by `add_ex`). `_` is handled here, not in `term`,
   so it is not a general term and does not collide with the optterm don't-care `_`. */
termarg:
  | term                    { f "termarg(term)"; $1 }
  | LD                      { f "termarg(_)"; incr var_cnt; Var ("_" ^ (string_of_int !var_cnt)) }

varlist:
  | varlist COM var         { f "varlist(list)"; $1 @ [$3] }
  | var                     { f "varlist(end)"; [$1] }
  |  %prec REDUCE_CONCAT    { f "varlist()"; [] }

xopttermlist:
  | LPA opttermlist RPA     { f "xopttermlist(list)"; $2 }
  |  %prec REDUCE_CONCAT    { f "xopttermlist()"; [] }

opttermlist:
  | opttermlist COM optterm { f "opttermlist(list)"; $1 @ [$3] }
  | optterm                 { f "opttermlist(end)"; [$1] }
  |                         { f "opttermlist()"; [] }

optterm:
  | LD                      { f "optterm(None)"; None }
  | term                    { f "optterm(Some)"; Some $1 }

/* A `var` is a named variable only. The anonymous `_` (LD) is NOT a general var/term:
   that is what previously made a lone `_` ambiguous in a MATCHES list (`optterm: LD`
   = don't-capture None vs `var: LD` = unnamed var, a reduce/reduce conflict). `_` is
   instead admitted only where it is meaningful: as an anonymous predicate argument
   (see `termarg`) and as the optterm don't-care marker (`optterm: LD`). */
var:
  | STR                     { f "var"; assert (String.length $1 > 0); $1 }

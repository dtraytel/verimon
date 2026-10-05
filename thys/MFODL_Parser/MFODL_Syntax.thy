theory MFODL_Syntax
  imports Main
begin

section \<open>Surface syntax of MFODL formulas\<close>

text \<open>
  The abstract syntax produced by MonPoly's formula parser
  (\<^verbatim>\<open>src/MFOTL.mli\<close> of MonPoly, \<^verbatim>\<open>src/predicate.mli\<close> of MonPoly), with named
  variables. Constructor names carry a prefix to avoid clashes with
  constants of \<^theory>\<open>Main\<close>. Numeric literals are kept as they are
  written: integers as \<^typ>\<open>int\<close> (MonPoly uses arbitrary precision
  integers), floating point numbers and regular expressions by their
  lexemes, since their interpretation (\<^verbatim>\<open>float_of_string\<close>,
  \<^verbatim>\<open>Str.regexp\<close>) is not part of the parser.
\<close>

datatype cst = CInt int | CStr string | CFloat string | CRegexp string

datatype trm =
    TVar string | TCst cst
  | TF2i trm | TI2f trm | TI2s trm | TS2i trm | TF2s trm | TS2f trm
  | TDayOfMonth trm | TMonth trm | TYear trm | TFormatDate trm | TR2s trm | TS2r trm
  | TPlus trm trm | TMinus trm trm | TUMinus trm | TMult trm trm | TDiv trm trm | TMod trm trm

datatype bound = OBnd int | CBnd int | BInf

type_synonym interval = \<open>bound \<times> bound\<close>

text \<open>The default interval \<open>[0, \<infinity>)\<close> of temporal operators written without one.\<close>

definition dfintv :: interval where
  \<open>dfintv = (CBnd 0, BInf)\<close>

datatype agg_op = ACnt | AMin | AMax | ASum | AAvg | AMed

type_synonym predicate = \<open>string \<times> trm list\<close>

datatype formula =
    FEqual trm trm | FLess trm trm | FLessEq trm trm | FSubstring trm trm
  | FMatches trm trm \<open>trm option list\<close>
  | FPred predicate
  | FLet predicate formula formula | FLetPast predicate formula formula
  | FFrz predicate formula formula
  | FNeg formula | FAnd formula formula | FOr formula formula
  | FImplies formula formula | FEquiv formula formula
  | FExists \<open>string list\<close> formula | FForAll \<open>string list\<close> formula
  | FAggreg string agg_op string \<open>string list\<close> formula
  | FPrev interval formula | FNext interval formula
  | FEventually interval formula | FOnce interval formula
  | FAlways interval formula | FPastAlways interval formula
  | FSince interval formula formula | FTrigger interval formula formula
  | FUntil interval formula formula | FRelease interval formula formula
  | FFrex interval regex | FPrex interval regex
and regex = RSkip nat | RTest formula | RConcat regex regex | RPlus regex regex | RStar regex

text \<open>\<^verbatim>\<open>MFOTL.wild\<close>, a single step.\<close>

definition wild :: regex where
  \<open>wild = RSkip 1\<close>

end

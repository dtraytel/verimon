(*<*)
theory CLI_Options
  imports "Log_Parser.Signature"
begin
(*>*)

section \<open>MonPoly's command line\<close>

text \<open>
  The verified monitor reads MonPoly's command line (\<^verbatim>\<open>src/main.ml\<close>): the same options,
  parsed as OCaml's @{text Arg.parse} parses them, with the same messages for unknown options,
  missing or wrong arguments, @{text "-help"}, and arguments that are not options. The options
  that concern MonPoly's own algorithm, or that MonPoly accepts and ignores, are accepted and
  ignored; @{text "-load"} and @{text "-combine"}, which resume or combine MonPoly's own monitor
  state, are refused.
\<close>

subsection \<open>The table of options\<close>

text \<open>The kind of argument an option takes: none, a string, an integer, or one of a list of
  symbols.\<close>

datatype okind = OFlag | OStr | OInt | OSym "string list"

definition tab :: string where
  "tab = [CHR 0x09]"

definition nl :: string where
  "nl = [CHR 0x0A]"

text \<open>MonPoly's options with their documentation, in MonPoly's order, as @{text "-help"} lists
  them.\<close>

definition opt_table :: "(string \<times> okind \<times> string) list" where
  "opt_table = [
    (''-sig'', OStr, tab @ tab @ ''Choose the signature file''),
    (''-formula'', OStr, tab @ ''Choose the formula file''),
    (''-negate'', OFlag, tab @ ''Analyze the negation of the input formula''),
    (''-log'', OStr, tab @ tab @ ''Choose the log file''),
    (''-version'', OFlag, tab @ ''Display the version (and exit)''),
    (''-debug'', OStr, tab @ ''Accepted and ignored by the verified monitor''),
    (''-verbose'', OFlag, tab @ ''Turn on verbose mode''),
    (''-check'', OFlag, tab @ ''Check if formula is monitorable (and exit)''),
    (''-no_rw'', OFlag, tab @ ''No formula rewrite''),
    (''-no_trigger'', OFlag, tab @ ''Accepted and ignored by the verified monitor''),
    (''-sigout'', OFlag, tab @ ''Show the output signature (and exit)''),
    (''-unix'', OFlag, tab @ ''Timestamps represent Unix time''),
    (''-mem'', OFlag, tab @ tab @ ''Show maximum memory usage on stderr''),
    (''-nonewlastts'', OFlag, tab @ ''Do not add a last maximal timestamp''),
    (''-nofilterrel'', OFlag, tab @ ''Disable filter_rel module''),
    (''-nofilteremptytp'', OFlag, tab @ ''Accepted and ignored by the verified monitor''),
    (''-stats'', OFlag, tab @ tab @ ''Accepted and ignored by the verified monitor''),
    (''-ignore_parse_errors'', OFlag, tab @ ''Ignore log parse errors''),
    (''-old_log_parser'', OFlag, tab @ ''Accepted and ignored: the verified monitor reads the log with the verified parser''),
    (''-verified_log_parser'', OFlag, tab @ ''Read the log with the verified parser (thys/Log_Parser; always)''),
    (''-stop_at_out_of_order_ts'', OFlag, tab @ ''Accepted and ignored: the verified monitor stops at an out-of-order timestamp''),
    (''-stop_at_first_viol'', OFlag, tab @ ''Stop at first encountered violation''),
    (''-load'', OStr, tab @ ''Not supported by the verified monitor''),
    (''-combine'', OStr, tab @ ''Not supported by the verified monitor''),
    (''-verified_parser'', OFlag, tab @ ''Parse the formula with the verified parser (thys/MFODL_Parser; always)''),
    (''-verified'', OFlag, tab @ ''Run the verified monitor (always)''),
    (''-dense'', OFlag, tab @ ''Deprecated, accepted and ignored''),
    (''-heap_maps'', OFlag, tab @ ''Deprecated, accepted and ignored''),
    (''-vdense'', OFlag, tab @ ''Deprecated, accepted and ignored''),
    (''-heap_join_min'', OInt, tab @ ''Deprecated, accepted and ignored''),
    (''-bulk_min'', OInt, tab @ ''Deprecated, accepted and ignored''),
    (''-heap_since'', OFlag, tab @ ''Deprecated, accepted and ignored''),
    (''-gc_space_overhead'', OInt, tab @ ''OCaml GC space_overhead in percent (default: 500); larger values trade memory for speed''),
    (''-gc_minor_heap'', OInt, tab @ ''OCaml GC minor_heap_size in words (default: 768k under OCaml 4, 4M under OCaml 5)''),
    (''-no_mw'', OFlag, tab @ ''No multi-way join''),
    (''-index'', OSym [''none'', ''unbounded'', ''all''], tab @ ''Which Since and Until windows keep indexed tables for the joins that probe them (default: unbounded)''),
    (''-generic_join'', OFlag, tab @ ''Deprecated, accepted and ignored''),
    (''-imperative_join'', OFlag, tab @ ''Deprecated, accepted and ignored''),
    (''-unfold_let'', OSym [''no'', ''full'', ''smart''], tab @ ''Accepted and ignored by the verified monitor''),
    (''-strcache'', OFlag, tab @ ''Accepted and ignored by the verified monitor''),
    (''-profile'', OStr, tab @ ''Accepted and ignored by the verified monitor'')]"

definition usage_string :: string where
  "usage_string = ''Usage: verimon -sig <file> -formula <file> [-negate] [-log <file>]'' @ nl @
     ''               [-help] [-version] [-verbose] [-no_rw] [-no_mw]'' @ nl @
     ''               [-check] [-sigout] [-unix] [-mem] [-nonewlastts] [-nofilterrel]'' @ nl @
     ''               [-ignore_parse_errors] [-stop_at_first_viol]''"

text \<open>@{text Arg.usage_string}: the usage, then a line per option, then @{text "-help"} and
  @{text "--help"}.\<close>

definition help_doc :: string where
  "help_doc = ''  Display this list of options''"

fun between :: "string \<Rightarrow> string list \<Rightarrow> string list" where
  "between s [] = []"
| "between s [x] = [x]"
| "between s (x # y # zs) = x # s # between s (y # zs)"

fun spec_line :: "string \<times> okind \<times> string \<Rightarrow> string" where
  "spec_line (k, OSym l, d) = ''  '' @ k @ '' {'' @ concat (between ''|'' l) @ ''}'' @ d @ nl"
| "spec_line (k, _, d) = (if d = [] then [] else ''  '' @ k @ '' '' @ d @ nl)"

definition arg_usage :: string where
  "arg_usage = usage_string @ nl @ concat (map spec_line opt_table) @
     spec_line (''-help'', OFlag, help_doc) @ spec_line (''--help'', OFlag, help_doc)"

subsection \<open>Parsing the arguments\<close>

text \<open>The options given, each with its argument (empty for a flag), latest first.\<close>

type_synonym opts = "(string \<times> string) list"

definition opt_lookup :: "string \<Rightarrow> okind option" where
  "opt_lookup k = map_option fst (map_of opt_table k)"

text \<open>@{text int_of_string} on the arguments of the integer options: decimal, with an optional
  sign.\<close>

definition is_int_arg :: "string \<Rightarrow> bool" where
  "is_int_arg s = (let d = (case s of CHR ''-'' # d \<Rightarrow> d | CHR ''+'' # d \<Rightarrow> d | _ \<Rightarrow> s) in
     d \<noteq> [] \<and> list_all (\<lambda>c. CHR ''0'' \<le> c \<and> c \<le> CHR ''9'') d)"

text \<open>The outcome: run with the options, or print a message and exit with a code. The messages
  are those of @{text Arg.parse}, with the program name as it was invoked; an argument that is not
  an option makes MonPoly print its usage and exit.\<close>

datatype args_result = ARun opts | AExit string string nat

definition arg_bad :: "string \<Rightarrow> string \<Rightarrow> args_result" where
  "arg_bad prog msg = AExit [] (prog @ '': '' @ msg @ ''.'' @ nl @ arg_usage) 2"

fun parse_args :: "string \<Rightarrow> string list \<Rightarrow> opts \<Rightarrow> args_result" where
  "parse_args prog [] acc = ARun acc"
| "parse_args prog (a # as) acc = (if a = ''-help'' \<or> a = ''--help'' then AExit arg_usage [] 0
     else (case opt_lookup a of
       None \<Rightarrow> (case a of CHR ''-'' # _ \<Rightarrow> arg_bad prog (''unknown option '' @ CHR 0x27 # a @ [CHR 0x27])
         | _ \<Rightarrow> AExit [] (usage_string @ nl) 2)
     | Some OFlag \<Rightarrow> parse_args prog as ((a, []) # acc)
     | Some k \<Rightarrow> (case as of
         [] \<Rightarrow> arg_bad prog (''option '' @ CHR 0x27 # a @ CHR 0x27 # '' needs an argument'')
       | b # bs \<Rightarrow> (case k of
           OInt \<Rightarrow> if is_int_arg b then parse_args prog bs ((a, b) # acc)
             else arg_bad prog (''wrong argument '' @ CHR 0x27 # b @ CHR 0x27 # ''; option '' @ CHR 0x27 # a @
               CHR 0x27 # '' expects an integer'')
         | OSym l \<Rightarrow> if b \<in> set l then parse_args prog bs ((a, b) # acc)
             else arg_bad prog (''wrong argument '' @ CHR 0x27 # b @ CHR 0x27 # ''; option '' @ CHR 0x27 # a @
               CHR 0x27 # '' expects one of: '' @ concat (between '' '' l))
         | _ \<Rightarrow> parse_args prog bs ((a, b) # acc)))))"

definition oflag :: "opts \<Rightarrow> string \<Rightarrow> bool" where
  "oflag os k \<longleftrightarrow> k \<in> fst ` set os"

text \<open>The argument of the last occurrence of a string option, or the empty string.\<close>

definition ostr :: "opts \<Rightarrow> string \<Rightarrow> string" where
  "ostr os k = (case map_of os k of Some v \<Rightarrow> v | None \<Rightarrow> [])"

definition oint :: "opts \<Rightarrow> string \<Rightarrow> int" where
  "oint os k = (case map_of os k of
     Some (CHR ''-'' # d) \<Rightarrow> - int (foldl (\<lambda>n c. 10 * n + (of_char c - 48)) 0 d)
   | Some (CHR ''+'' # d) \<Rightarrow> int (foldl (\<lambda>n c. 10 * n + (of_char c - 48)) 0 d)
   | Some d \<Rightarrow> int (foldl (\<lambda>n c. 10 * n + (of_char c - 48)) 0 d)
   | None \<Rightarrow> 0)"

subsection \<open>The configuration of a run\<close>

text \<open>What the options select. The driver reads the files and the log, and applies the settings of
  the OCaml runtime.\<close>

record config =
  c_sig :: string
  c_formula :: string
  c_log :: string
  c_negate :: bool
  c_verbose :: bool
  c_check :: bool
  c_rw :: bool
  c_mw :: bool
  c_index :: ipolicy
  c_sigout :: bool
  c_unix :: bool
  c_mem :: bool
  c_newlastts :: bool
  c_filter :: bool
  c_ignore_errors :: bool
  c_stop_first :: bool
  c_version :: bool
  c_gc_space_overhead :: int
  c_gc_minor_heap :: int

text \<open>The index policy (@{const ireq}): unbounded past windows unless @{text "-index"} says
  otherwise.\<close>

definition oindex :: "opts \<Rightarrow> ipolicy" where
  "oindex os = (case map_of os ''-index'' of
     Some s \<Rightarrow> if s = ''none'' then IxNone else if s = ''all'' then IxAll else IxUnbounded
   | None \<Rightarrow> IxUnbounded)"

definition config_of :: "opts \<Rightarrow> config" where
  "config_of os = \<lparr>c_sig = ostr os ''-sig'', c_formula = ostr os ''-formula'', c_log = ostr os ''-log'',
     c_negate = oflag os ''-negate'', c_verbose = oflag os ''-verbose'', c_check = oflag os ''-check'',
     c_rw = \<not> oflag os ''-no_rw'', c_mw = \<not> oflag os ''-no_mw'', c_index = oindex os,
     c_sigout = oflag os ''-sigout'',
     c_unix = oflag os ''-unix'', c_mem = oflag os ''-mem'', c_newlastts = \<not> oflag os ''-nonewlastts'',
     c_filter = \<not> oflag os ''-nofilterrel'', c_ignore_errors = oflag os ''-ignore_parse_errors'',
     c_stop_first = oflag os ''-stop_at_first_viol'', c_version = oflag os ''-version'',
     c_gc_space_overhead = oint os ''-gc_space_overhead'', c_gc_minor_heap = oint os ''-gc_minor_heap''\<rparr>"

text \<open>The command line: a configuration to run with, or a message (on standard output and on
  standard error) and an exit code. @{text "-load"} and @{text "-combine"} are refused, as MonPoly's
  verified kernel cannot resume or combine MonPoly's own states.\<close>

datatype command = CRun config | CExit string string nat

definition usage_exit :: command where
  "usage_exit = CExit [] (usage_string @ nl) 2"

definition parse_command :: "string \<Rightarrow> string list \<Rightarrow> command" where
  "parse_command prog args = (case parse_args prog args [] of
     AExit out e c \<Rightarrow> CExit out e c
   | ARun os \<Rightarrow> if oflag os ''-load'' \<or> oflag os ''-combine''
       then CExit [] (fatal_failure ''-load and -combine are not supported by the verified monitor'' @ nl) 2
       else CRun (config_of os))"

(*<*)
end
(*>*)

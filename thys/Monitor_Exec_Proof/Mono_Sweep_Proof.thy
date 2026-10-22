(*<*)
theory Mono_Sweep_Proof
  imports "Monitor_Exec.Mono_Sweep" Tuple_Code_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>
  @{theory Monitor_Impl.Monomorphic_Code} and @{theory MFODL_Monitor_Exec.Tuple_Code}
  monomorphise the operations of the inner loops -- the containers at @{typ "event_data list"}
  -- because those were what the profiles charged for.  What is left over is everything else:
  operations the generated code still reaches with a type class dictionary in hand, at types
  that are closed and known.  None of them is hot, so this section buys no measurable time; it
  is here because the exported code is meant to be monomorphic throughout, and a dictionary that
  survives is a dictionary someone has to reason about when reading the export.

  The remaining genericity divides into three kinds, and only the first is work:
  \<^item> \<^emph>\<open>Operations\<close> reached at one closed type -- the ones below.  Each gets a monomorphic copy
    whose code equations are the originals instantiated at that type, and a @{text code_unfold}
    rule that redirects the applied occurrences, exactly as in the two theories above.
  \<^item> \<^emph>\<open>Operations reached at several closed types\<close> -- one copy per type; the subset test and the
    treelists of the rank aggregations are the cases that occur.
  \<^item> \<^emph>\<open>Dictionary constructors\<close> (@{text ccompare_list}, @{text ceq_option}, @{text equal_prod},
    \<dots>).  These are not targets at all: they exist only to feed a generic consumer, and they
    disappear as the consumers above are specialised.  They are the majority of what a count of
    the dictionary-taking definitions in the export reports.
\<close>

end
(*>*)

(*<*)
theory Dense_RBT_Code
  imports Dense_Agg_Upkeep
begin
(*>*)

section \<open>The red-black trees' rebalancing, in code\<close>

text \<open>
  @{const RBT_Impl.balance} restores the colour invariant on the way back up from an insertion,
  at every level of every insertion into every tree the monitor keeps.  Its equations are
  sequential, and its last one, @{text "balance a s t b = Branch B a s t b"}, is what applies at
  almost every level.  The code generator completes the patterns of such a definition into
  disjoint nested ones, which replaces the variables @{text a} and @{text b} of that last equation
  by the constructors they were split into -- so the generated code rebuilds both subtrees from
  their fields, three blocks where one is needed.  A case expression with overlapping nested
  patterns has the same problem, for the same reason.

  The code equation below therefore inspects the arguments one level at a time, a node and then
  its colour, and never splits a variable that its right-hand side uses; the two sides that are
  checked for a red child, the left one only when it is red itself, are two small functions.
\<close>

definition bal_right :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "bal_right l k v r = (case r of
     RBT_Impl.Empty \<Rightarrow> Branch RBT_Impl.B l k v r
   | Branch cr b s t c \<Rightarrow> (case cr of
       RBT_Impl.B \<Rightarrow> Branch RBT_Impl.B l k v r
     | RBT_Impl.R \<Rightarrow>
       (let other = (case b of
            RBT_Impl.Empty \<Rightarrow> Branch RBT_Impl.B l k v r
          | Branch cb b1 s1 t1 c1 \<Rightarrow> (case cb of
              RBT_Impl.B \<Rightarrow> Branch RBT_Impl.B l k v r
            | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B l k v b1) s1 t1
                               (Branch RBT_Impl.B c1 s t c))) in
        case c of
          RBT_Impl.Empty \<Rightarrow> other
        | Branch cc c1 y z d \<Rightarrow> (case cc of
            RBT_Impl.B \<Rightarrow> other
          | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B l k v b) s t
                             (Branch RBT_Impl.B c1 y z d)))))"

definition bal_left :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow>
    ('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "bal_left a w x b l k v r = (case a of
     RBT_Impl.Empty \<Rightarrow> (case b of
         RBT_Impl.Empty \<Rightarrow> bal_right l k v r
       | Branch cb b1 s t c \<Rightarrow> (case cb of
           RBT_Impl.B \<Rightarrow> bal_right l k v r
         | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B a w x b1) s t (Branch RBT_Impl.B c k v r)))
   | Branch ca a1 w1 x1 b1 \<Rightarrow> (case ca of
       RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B a1 w1 x1 b1) w x (Branch RBT_Impl.B b k v r)
     | RBT_Impl.B \<Rightarrow> (case b of
         RBT_Impl.Empty \<Rightarrow> bal_right l k v r
       | Branch cb b2 s t c \<Rightarrow> (case cb of
           RBT_Impl.B \<Rightarrow> bal_right l k v r
         | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B a w x b2) s t
                            (Branch RBT_Impl.B c k v r)))))"

lemma balance_code[code]:
  "balance l k v r = (case l of
     RBT_Impl.Empty \<Rightarrow> bal_right l k v r
   | Branch cl a w x b \<Rightarrow> (case cl of
       RBT_Impl.B \<Rightarrow> bal_right l k v r
     | RBT_Impl.R \<Rightarrow> (case r of
         RBT_Impl.Empty \<Rightarrow> bal_left a w x b l k v r
       | Branch cr c y z d \<Rightarrow> (case cr of
           RBT_Impl.B \<Rightarrow> bal_left a w x b l k v r
         | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B a w x b) k v
                            (Branch RBT_Impl.B c y z d)))))"
  by (cases "(l, k, v, r)" rule: balance.cases)
    (simp_all add: bal_left_def bal_right_def Let_def split: color.split)

section \<open>The Since structure's deletions, through the specialised deletion\<close>

text \<open>@{theory MFODL_Monitor_Dense.Dense_Code_Opt} gives the deletion of a key set from the
  Since structure's timestamp mapping a code equation through the specialised deletion
  (@{thm [source] de_mapping_delete_set_nat_rbt}); the second pass of
  @{theory MFODL_Monitor_Dense.Dense_Mono_Sweep} made a second copy of the same operation at the
  same type from the generic equations, and its redirection is the one the code takes.  The copy
  gets the specialised deletion for the tree representation, and the generic equation for the
  others.\<close>

lemma edl_mapping_delete_set_code[code]:
  "edl_mapping_delete_set m (RBT_set rbt) = RBT_Set2.fold edl_delete_nat rbt m"
  "edl_mapping_delete_set m (DList_set dxs) = (if finite (DList_set dxs)
     then set_fold_cfi mapping_delete_set_cfi m (DList_set dxs)
     else Code.abort (STR ''mapping_delete_set: infinite'')
       (\<lambda>_. edl_mapping_delete_set m (DList_set dxs)))"
  "edl_mapping_delete_set m (Set_Monad xs) = (if finite (Set_Monad xs)
     then set_fold_cfi mapping_delete_set_cfi m (Set_Monad xs)
     else Code.abort (STR ''mapping_delete_set: infinite'')
       (\<lambda>_. edl_mapping_delete_set m (Set_Monad xs)))"
  "edl_mapping_delete_set m (Collect_set P) = (if finite (Collect_set P)
     then set_fold_cfi mapping_delete_set_cfi m (Collect_set P)
     else Code.abort (STR ''mapping_delete_set: infinite'')
       (\<lambda>_. edl_mapping_delete_set m (Collect_set P)))"
  "edl_mapping_delete_set m (Complement Q) = (if finite (Complement Q)
     then set_fold_cfi mapping_delete_set_cfi m (Complement Q)
     else Code.abort (STR ''mapping_delete_set: infinite'')
       (\<lambda>_. edl_mapping_delete_set m (Complement Q)))"
  unfolding edl_mapping_delete_set_def
    apply (rule de_mapping_delete_set_nat_rbt[unfolded de_mapping_delete_set_nat_def])
   apply (rule mapping_delete_set_code)+
  done
(*<*)
end
(*>*)

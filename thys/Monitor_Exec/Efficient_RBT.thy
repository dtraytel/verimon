(*<*)
theory Efficient_RBT
  imports Efficient_Map_Updates
begin
(*>*)



section \<open>Code for red-black trees\<close>

text \<open>The code equations inspect one level at a time and never split a variable that the
  right-hand side uses, so the generated code does not rebuild the subtrees it passes on.\<close>

subsection \<open>Rebalancing of insertions\<close>

text \<open>The fallback of @{text bal_right} is a function of its own, which the red case does not
  build.\<close>

definition bal_right_b :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow>
    ('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "bal_right_b l k v r b s t c = (case b of
     RBT_Impl.Empty \<Rightarrow> Branch RBT_Impl.B l k v r
   | Branch cb b1 s1 t1 c1 \<Rightarrow> (case cb of
       RBT_Impl.B \<Rightarrow> Branch RBT_Impl.B l k v r
     | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B l k v b1) s1 t1
                        (Branch RBT_Impl.B c1 s t c)))"

definition bal_right :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "bal_right l k v r = (case r of
     RBT_Impl.Empty \<Rightarrow> Branch RBT_Impl.B l k v r
   | Branch cr b s t c \<Rightarrow> (case cr of
       RBT_Impl.B \<Rightarrow> Branch RBT_Impl.B l k v r
     | RBT_Impl.R \<Rightarrow>
       (case c of
          RBT_Impl.Empty \<Rightarrow> bal_right_b l k v r b s t c
        | Branch cc c1 y z d \<Rightarrow> (case cc of
            RBT_Impl.B \<Rightarrow> bal_right_b l k v r b s t c
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
    (simp_all add: bal_left_def bal_right_def bal_right_b_def split: color.split)

subsection \<open>Rebalancing of deletions\<close>

definition bal_left_del :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "bal_left_del l k x r = (case r of
     RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
   | Branch cr a s y b \<Rightarrow> (case cr of
       RBT_Impl.B \<Rightarrow> balance l k x (Branch RBT_Impl.R a s y b)
     | RBT_Impl.R \<Rightarrow> (case a of
         RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
       | Branch ca a1 s1 y1 b1 \<Rightarrow> (case ca of
           RBT_Impl.B \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B l k x a1) s1 y1
                          (balance b1 s y (RBT_Impl.paint RBT_Impl.R b))
         | RBT_Impl.R \<Rightarrow> RBT_Impl.Empty))))"

lemma balance_left_code[code]:
  "balance_left l k x r = (case l of
     RBT_Impl.Empty \<Rightarrow> bal_left_del l k x r
   | Branch cl a k' x' b \<Rightarrow> (case cl of
       RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B a k' x' b) k x r
     | RBT_Impl.B \<Rightarrow> bal_left_del l k x r))"
  by (cases "(l, k, x, r)" rule: balance_left.cases) (simp_all add: bal_left_del_def)

definition bal_right_del :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "bal_right_del l k x r = (case l of
     RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
   | Branch cl a1 k1 x1 b1 \<Rightarrow> (case cl of
       RBT_Impl.B \<Rightarrow> balance (Branch RBT_Impl.R a1 k1 x1 b1) k x r
     | RBT_Impl.R \<Rightarrow> (case b1 of
         RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
       | Branch cb b2 s2 y2 c2 \<Rightarrow> (case cb of
           RBT_Impl.B \<Rightarrow> Branch RBT_Impl.R (balance (RBT_Impl.paint RBT_Impl.R a1) k1 x1 b2) s2 y2
                          (Branch RBT_Impl.B c2 k x r)
         | RBT_Impl.R \<Rightarrow> RBT_Impl.Empty))))"

lemma balance_right_code[code]:
  "balance_right l k x r = (case r of
     RBT_Impl.Empty \<Rightarrow> bal_right_del l k x r
   | Branch cr b s y c \<Rightarrow> (case cr of
       RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R l k x (Branch RBT_Impl.B b s y c)
     | RBT_Impl.B \<Rightarrow> bal_right_del l k x r))"
  by (cases "(l, k, x, r)" rule: balance_right.cases) (simp_all add: bal_right_del_def)

lemma combine_code[code]:
  "RBT_Impl.combine l r = (case l of
     RBT_Impl.Empty \<Rightarrow> r
   | Branch cl a k x b \<Rightarrow> (case r of
       RBT_Impl.Empty \<Rightarrow> l
     | Branch cr c s y d \<Rightarrow> (case cl of
         RBT_Impl.R \<Rightarrow> (case cr of
             RBT_Impl.R \<Rightarrow> (let bc = RBT_Impl.combine b c in case bc of
                 RBT_Impl.Empty \<Rightarrow> Branch RBT_Impl.R a k x (Branch RBT_Impl.R bc s y d)
               | Branch cbc b2 t z c2 \<Rightarrow> (case cbc of
                   RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.R a k x b2) t z
                                  (Branch RBT_Impl.R c2 s y d)
                 | RBT_Impl.B \<Rightarrow> Branch RBT_Impl.R a k x (Branch RBT_Impl.R bc s y d)))
           | RBT_Impl.B \<Rightarrow> Branch RBT_Impl.R a k x (RBT_Impl.combine b r))
       | RBT_Impl.B \<Rightarrow> (case cr of
             RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (RBT_Impl.combine l c) s y d
           | RBT_Impl.B \<Rightarrow> (let bc = RBT_Impl.combine b c in case bc of
                 RBT_Impl.Empty \<Rightarrow> balance_left a k x (Branch RBT_Impl.B bc s y d)
               | Branch cbc b2 t z c2 \<Rightarrow> (case cbc of
                   RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (Branch RBT_Impl.B a k x b2) t z
                                  (Branch RBT_Impl.B c2 s y d)
                 | RBT_Impl.B \<Rightarrow> balance_left a k x (Branch RBT_Impl.B bc s y d)))))))"
  by (cases "(l, r)" rule: RBT_Impl.combine.cases) (simp_all add: Let_def split: rbt.split color.split)

lemma ed_rbtc_del_from_left_code[code]:
  "ed_rbtc_del_from_left x a y s b = (case a of
     RBT_Impl.Empty \<Rightarrow> Branch RBT_Impl.R RBT_Impl.Empty y s b
   | Branch ca lt z v rt \<Rightarrow> (case ca of
       RBT_Impl.B \<Rightarrow> balance_left (ed_rbtc_del x a) y s b
     | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R (ed_rbtc_del x a) y s b))"
  by (cases a) (simp_all add: ed_rbtc_del_from_left_simps ed_rbtc_del_simps split: color.split)

lemma ed_rbtc_del_from_right_code[code]:
  "ed_rbtc_del_from_right x a y s b = (case b of
     RBT_Impl.Empty \<Rightarrow> Branch RBT_Impl.R a y s RBT_Impl.Empty
   | Branch cb lt z v rt \<Rightarrow> (case cb of
       RBT_Impl.B \<Rightarrow> balance_right a y s (ed_rbtc_del x b)
     | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.R a y s (ed_rbtc_del x b)))"
  by (cases b) (simp_all add: ed_rbtc_del_from_right_simps ed_rbtc_del_simps split: color.split)

lemma edl_rbtc_del_lk_fl_code[code]:
  "edl_rbtc_del_lk_fl x a y s b = (case a of
     RBT_Impl.Empty \<Rightarrow> (None, Branch RBT_Impl.R RBT_Impl.Empty y s b)
   | Branch ca lt z v rt \<Rightarrow> (case ca of
       RBT_Impl.B \<Rightarrow> (case edl_rbtc_del_lk x a of (ov, l') \<Rightarrow> (ov, balance_left l' y s b))
     | RBT_Impl.R \<Rightarrow> (case edl_rbtc_del_lk x a of (ov, a') \<Rightarrow> (ov, Branch RBT_Impl.R a' y s b))))"
  by (cases a) (simp_all add: edl_rbtc_del_lk_simps split: color.split)

lemma edl_rbtc_del_lk_fr_code[code]:
  "edl_rbtc_del_lk_fr x a y s b = (case b of
     RBT_Impl.Empty \<Rightarrow> (None, Branch RBT_Impl.R a y s RBT_Impl.Empty)
   | Branch cb lt z v rt \<Rightarrow> (case cb of
       RBT_Impl.B \<Rightarrow> (case edl_rbtc_del_lk x b of (ov, r') \<Rightarrow> (ov, balance_right a y s r'))
     | RBT_Impl.R \<Rightarrow> (case edl_rbtc_del_lk x b of (ov, b') \<Rightarrow> (ov, Branch RBT_Impl.R a y s b'))))"
  by (cases b) (simp_all add: edl_rbtc_del_lk_simps split: color.split)

text \<open>Painting leaves a root of the right colour as it is.\<close>

lemma paint_code[code]:
  "RBT_Impl.paint c t = (case t of
     RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
   | Branch c' l k v r \<Rightarrow> (case c of
       RBT_Impl.B \<Rightarrow> (case c' of RBT_Impl.B \<Rightarrow> t | RBT_Impl.R \<Rightarrow> Branch RBT_Impl.B l k v r)
     | RBT_Impl.R \<Rightarrow> (case c' of RBT_Impl.R \<Rightarrow> t | RBT_Impl.B \<Rightarrow> Branch RBT_Impl.R l k v r)))"
  by (cases t) (simp_all split: color.split)

subsection \<open>Key set deletion in Since\<close>

text \<open>The Since structure's deletion of a key set gets the specialised deletion on trees.\<close>

lemma edl_mapping_delete_set_code[code]:
  "edl_mapping_delete_set m (RBT_set rbt) = RBT_Set2.fold ed_delete_nat rbt m"
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
proof -
  show "edl_mapping_delete_set m (RBT_set rbt) = RBT_Set2.fold ed_delete_nat rbt m"
    by (simp add: edl_mapping_delete_set_def ed_delete_nat_def mapping_delete_set_RBT_code
        ID_ccompare_etuple ccomp_etuple)
qed (unfold edl_mapping_delete_set_def, (rule mapping_delete_set_code)+)

subsection \<open>Black heights compared without counting\<close>

text \<open>The joins compare black heights by descending two spines in lockstep (@{text bh_le_g}) or
  counting down one (@{text bh_lt_g}), without computing heights.\<close>

function bh_le_g :: "('a, 'b) rbt \<Rightarrow> ('c, 'd) rbt \<Rightarrow> bool" where
  "bh_le_g RBT_Impl.Empty t2 = True"
| "bh_le_g (Branch RBT_Impl.R l1 a1 b1 r1) t2 = bh_le_g l1 t2"
| "bh_le_g (Branch RBT_Impl.B l1 a1 b1 r1) RBT_Impl.Empty = False"
| "bh_le_g (Branch RBT_Impl.B l1 a1 b1 r1) (Branch RBT_Impl.R l2 a2 b2 r2) =
     bh_le_g (Branch RBT_Impl.B l1 a1 b1 r1) l2"
| "bh_le_g (Branch RBT_Impl.B l1 a1 b1 r1) (Branch RBT_Impl.B l2 a2 b2 r2) = bh_le_g l1 l2"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(t1, t2). size t1 + size t2)") auto

lemma bh_le_g_correct: "bh_le_g t1 t2 \<longleftrightarrow> bheight t1 \<le> bheight t2"
  by (induction t1 t2 rule: bh_le_g.induct) auto

fun bh_lt_g :: "integer \<Rightarrow> ('a, 'b) rbt \<Rightarrow> bool" where
  "bh_lt_g k RBT_Impl.Empty = (0 < k)"
| "bh_lt_g k (Branch RBT_Impl.R l a b r) = bh_lt_g k l"
| "bh_lt_g k (Branch RBT_Impl.B l a b r) = (if k \<le> 0 then False else bh_lt_g (k - 1) l)"

lemma bh_lt_g_correct: "bh_lt_g k t \<longleftrightarrow> integer_of_nat (bheight t) < k"
proof (induction k t rule: bh_lt_g.induct)
  case (3 k l a b r)
  show ?case
  proof (cases "k \<le> 0")
    case True
    have "k \<le> 0" by (rule True)
    also have "(0::integer) \<le> 1 + of_nat (bheight l)"
      by simp
    finally have "k \<le> 1 + of_nat (bheight l)" .
    then show ?thesis using True by (simp add: integer_of_nat_eq_of_nat not_less)
  next
    case False
    then show ?thesis using 3
      by (simp add: integer_of_nat_eq_of_nat less_diff_eq add.commute)
  qed
qed (auto simp: integer_of_nat_eq_of_nat)

text \<open>The union and intersection get back their defining equations, which use the two tests.\<close>

declare [[code drop: RBT_Impl.small_rbt RBT_Impl.flip_rbt RBT_Impl.rbt_joinL RBT_Impl.rbt_joinR
  RBT_Impl.rbt_join RBT_Comparator_Impl.rbt_comp_union_swap_rec
  RBT_Comparator_Impl.rbt_comp_inter_swap_rec]]

lemma small_rbt_bh_code[code]: "RBT_Impl.small_rbt t = bh_lt_g 4 t"
  by (simp add: RBT_Impl.small_rbt_def bh_lt_g_correct integer_of_nat_eq_of_nat)

lemma flip_rbt_bh_code[code]: "RBT_Impl.flip_rbt t1 t2 = (\<not> bh_le_g t1 t2)"
  by (simp add: RBT_Impl.flip_rbt_def bh_le_g_correct not_le)

lemma rbt_joinL_bh_code[code]: "RBT_Impl.rbt_joinL l a b r = (if bh_le_g r l
    then Branch RBT_Impl.R l a b r
    else case r of
      Branch RBT_Impl.B l' a' b' r' \<Rightarrow> rbt_baliL (RBT_Impl.rbt_joinL l a b l') a' b' r'
    | Branch RBT_Impl.R l' a' b' r' \<Rightarrow> Branch RBT_Impl.R (RBT_Impl.rbt_joinL l a b l') a' b' r')"
  by (subst RBT_Impl.rbt_joinL.simps) (simp add: bh_le_g_correct)

lemma rbt_joinR_bh_code[code]: "RBT_Impl.rbt_joinR l a b r = (if bh_le_g l r
    then Branch RBT_Impl.R l a b r
    else case l of
      Branch RBT_Impl.B l' a' b' r' \<Rightarrow> rbt_baliR l' a' b' (RBT_Impl.rbt_joinR r' a b r)
    | Branch RBT_Impl.R l' a' b' r' \<Rightarrow> Branch RBT_Impl.R l' a' b' (RBT_Impl.rbt_joinR r' a b r))"
  by (subst RBT_Impl.rbt_joinR.simps) (simp add: bh_le_g_correct)

lemma rbt_join_bh_code[code]: "RBT_Impl.rbt_join l a b r = (if \<not> bh_le_g l r
    then RBT_Impl.paint RBT_Impl.B (RBT_Impl.rbt_joinR l a b r)
    else if \<not> bh_le_g r l
    then RBT_Impl.paint RBT_Impl.B (RBT_Impl.rbt_joinL l a b r)
    else Branch RBT_Impl.B l a b r)"
  by (simp add: RBT_Impl.rbt_join_def bh_le_g_correct Let_def)

declare RBT_Comparator_Impl.rbt_comp_union_swap_rec.simps[code]
  RBT_Comparator_Impl.rbt_comp_inter_swap_rec.simps[code]

(*<*)
end
(*>*)

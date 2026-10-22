(*<*)
theory Sliding_Window_Agg
  imports Main
begin
(*>*)

section \<open>Two-stacks sliding-window aggregation\<close>

subsection \<open>Operations\<close>

text \<open>The front stores with each element the composition up to the front's end; the back stores
  the elements newest first with their total composition, and is flipped when the front runs out.\<close>

type_synonym ('t, 'e, 'a) swag = "('t \<times> 'e \<times> 'a) list \<times> ('t \<times> 'e) list \<times> 'a option"

definition sw_empty :: "('t, 'e, 'a) swag" where
  "sw_empty = ([], [], None)"

definition sw_comp :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
  "sw_comp f x y = (case y of None \<Rightarrow> x | Some y' \<Rightarrow> f x y')"

fun sw_fold :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a option" where
  "sw_fold f [] = None"
| "sw_fold f (x # xs) = Some (sw_comp f x (sw_fold f xs))"

definition sw_push :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'a) \<Rightarrow> 't \<Rightarrow> 'e \<Rightarrow> ('t, 'e, 'a) swag \<Rightarrow>
    ('t, 'e, 'a) swag" where
  "sw_push f g t e s = (case s of (fr, bk, B) \<Rightarrow>
     (fr, (t, e) # bk, Some (case B of None \<Rightarrow> g e | Some b \<Rightarrow> f b (g e))))"

definition sw_head :: "('t \<times> 'e \<times> 'a) list \<Rightarrow> 'a option" where
  "sw_head fr = (case fr of [] \<Rightarrow> None | (_, _, a) # _ \<Rightarrow> Some a)"

fun sw_flip :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'a) \<Rightarrow> ('t \<times> 'e) list \<Rightarrow> ('t \<times> 'e \<times> 'a) list \<Rightarrow>
    ('t \<times> 'e \<times> 'a) list" where
  "sw_flip f g [] fr = fr"
| "sw_flip f g ((t, e) # bk) fr = sw_flip f g bk ((t, e, sw_comp f (g e) (sw_head fr)) # fr)"

definition sw_strip :: "('t \<times> 'e \<times> 'a) list \<Rightarrow> ('t \<times> 'e) list" where
  "sw_strip fr = map (\<lambda>(t, e, _). (t, e)) fr"

text \<open>A leaving element carries its front summary and the back summary; composed, they summarise
  the queue from it to the end.\<close>

definition sw_tag :: "'a option \<Rightarrow> ('t \<times> 'e \<times> 'a) list \<Rightarrow> ('t \<times> 'e \<times> 'a \<times> 'a option) list" where
  "sw_tag B xs = map (\<lambda>(t, e, a). (t, e, a, B)) xs"

definition sw_strip4 :: "('t \<times> 'e \<times> 'a \<times> 'a option) list \<Rightarrow> ('t \<times> 'e) list" where
  "sw_strip4 ys = map (\<lambda>(t, e, _, _). (t, e)) ys"

definition sw_popx :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'a) \<Rightarrow> ('t \<Rightarrow> bool) \<Rightarrow> ('t, 'e, 'a) swag \<Rightarrow>
    ('t \<times> 'e \<times> 'a \<times> 'a option) list \<times> ('t, 'e, 'a) swag" where
  "sw_popx f g P s = (case s of (fr, bk, B) \<Rightarrow>
     (let ys = sw_tag B (takeWhile (\<lambda>(t, _). P t) fr); fr' = dropWhile (\<lambda>(t, _). P t) fr in
      case fr' of
        [] \<Rightarrow> (case bk of
            [] \<Rightarrow> (ys, ([], [], None))
          | _ \<Rightarrow> (let fl = sw_flip f g bk [] in
              (ys @ sw_tag None (takeWhile (\<lambda>(t, _). P t) fl),
               (dropWhile (\<lambda>(t, _). P t) fl, [], None))))
      | _ \<Rightarrow> (ys, (fr', bk, B))))"

definition sw_pop :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'a) \<Rightarrow> ('t \<Rightarrow> bool) \<Rightarrow> ('t, 'e, 'a) swag \<Rightarrow>
    ('t \<times> 'e) list \<times> ('t, 'e, 'a) swag" where
  "sw_pop f g P s = (case sw_popx f g P s of (ys, s') \<Rightarrow> (sw_strip4 ys, s'))"

definition sw_query :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('t, 'e, 'a) swag \<Rightarrow> 'a option" where
  "sw_query f s = (case s of (fr, bk, B) \<Rightarrow>
     (case fr of [] \<Rightarrow> B | (_, _, a) # _ \<Rightarrow> Some (sw_comp f a B)))"

definition sw_null :: "('t, 'e, 'a) swag \<Rightarrow> bool" where
  "sw_null s = (case s of (fr, bk, B) \<Rightarrow>
     (case fr of [] \<Rightarrow> (case bk of [] \<Rightarrow> True | _ \<Rightarrow> False) | _ \<Rightarrow> False))"

subsection \<open>Invariant and represented queue\<close>

definition sw_assoc :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "sw_assoc f \<longleftrightarrow> (\<forall>x y z. f (f x y) z = f x (f y z))"

definition sw_sfx :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'a) \<Rightarrow> ('t \<times> 'e \<times> 'a) list \<Rightarrow> bool" where
  "sw_sfx f g fr \<longleftrightarrow> (\<forall>i < length fr.
     Some (snd (snd (fr ! i))) = sw_fold f (map (g \<circ> snd) (drop i (sw_strip fr))))"

definition sw_rel :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('e \<Rightarrow> 'a) \<Rightarrow> ('t, 'e, 'a) swag \<Rightarrow> ('t \<times> 'e) list \<Rightarrow>
    bool" where
  "sw_rel f g s W \<longleftrightarrow> (case s of (fr, bk, B) \<Rightarrow>
     sw_strip fr @ rev bk = W \<and> sw_sfx f g fr \<and> B = sw_fold f (map (g \<circ> snd) (rev bk)))"

definition sw_comb :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "sw_comb f x y = (case x of None \<Rightarrow> y | Some x' \<Rightarrow> Some (sw_comp f x' y))"

lemma sw_comp_comb:
  "sw_assoc f \<Longrightarrow> sw_comp f (sw_comp f e X) Y = sw_comp f e (sw_comb f X Y)"
  by (cases X; cases Y) (simp_all add: sw_comp_def sw_comb_def sw_assoc_def)

lemma sw_fold_append:
  "sw_assoc f \<Longrightarrow> sw_fold f (xs @ ys) = sw_comb f (sw_fold f xs) (sw_fold f ys)"
  by (induct xs) (simp_all add: sw_comb_def sw_comp_comb)

lemma sw_fold_snoc:
  "sw_assoc f \<Longrightarrow> sw_fold f (xs @ [x]) =
     Some (case sw_fold f xs of None \<Rightarrow> x | Some b \<Rightarrow> f b x)"
  by (simp add: sw_fold_append sw_comb_def sw_comp_def split: option.splits)

lemma sw_strip_simps[simp]:
  "sw_strip [] = []" "sw_strip ((t, e, a) # fr) = (t, e) # sw_strip fr"
  "sw_strip (xs @ ys) = sw_strip xs @ sw_strip ys" "length (sw_strip fr) = length fr"
  by (simp_all add: sw_strip_def)

lemma drop_sw_strip: "drop i (sw_strip fr) = sw_strip (drop i fr)"
  by (simp add: sw_strip_def drop_map)

lemma sw_sfx_Nil[simp]: "sw_sfx f g []"
  by (simp add: sw_sfx_def)

lemma sw_sfx_Cons:
  "sw_sfx f g ((t, e, a) # fr) \<longleftrightarrow>
     a = sw_comp f (g e) (sw_fold f (map (g \<circ> snd) (sw_strip fr))) \<and> sw_sfx f g fr"
  (is "?l \<longleftrightarrow> ?r")
proof
  assume l: ?l
  have "Some a = sw_fold f (map (g \<circ> snd) (sw_strip ((t, e, a) # fr)))"
    using l[unfolded sw_sfx_def, rule_format, of 0] by simp
  moreover have "sw_sfx f g fr"
    unfolding sw_sfx_def
  proof (intro allI impI)
    fix i assume "i < length fr"
    then show "Some (snd (snd (fr ! i))) = sw_fold f (map (g \<circ> snd) (drop i (sw_strip fr)))"
      using l[unfolded sw_sfx_def, rule_format, of "Suc i"] by simp
  qed
  ultimately show ?r by simp
next
  assume r: ?r
  show ?l unfolding sw_sfx_def
  proof (intro allI impI)
    fix i assume i: "i < length ((t, e, a) # fr)"
    show "Some (snd (snd (((t, e, a) # fr) ! i))) =
        sw_fold f (map (g \<circ> snd) (drop i (sw_strip ((t, e, a) # fr))))"
    proof (cases i)
      case 0 then show ?thesis using r by simp
    next
      case (Suc k)
      then show ?thesis using r i unfolding sw_sfx_def by simp
    qed
  qed
qed

lemma sw_sfx_head: "sw_sfx f g fr \<Longrightarrow> sw_head fr = sw_fold f (map (g \<circ> snd) (sw_strip fr))"
  by (cases fr) (auto simp: sw_head_def sw_sfx_Cons)

lemma sw_sfx_drop: "sw_sfx f g fr \<Longrightarrow> sw_sfx f g (drop k fr)"
  unfolding sw_sfx_def by (auto simp: drop_sw_strip add.commute[of k])

lemma sw_sfx_dropWhile: "sw_sfx f g fr \<Longrightarrow> sw_sfx f g (dropWhile P fr)"
  using sw_sfx_drop[of f g fr "length (takeWhile P fr)"]
  by (metis append_eq_conv_conj takeWhile_dropWhile_id)

lemma sw_flip:
  "sw_sfx f g fr \<Longrightarrow> sw_sfx f g (sw_flip f g bk fr) \<and> sw_strip (sw_flip f g bk fr) = rev bk @ sw_strip fr"
proof (induct f g bk fr rule: sw_flip.induct)
  case (2 f g t e bk fr)
  have "sw_sfx f g ((t, e, sw_comp f (g e) (sw_head fr)) # fr)"
    using 2(2) by (simp add: sw_sfx_Cons sw_sfx_head)
  then show ?case using 2(1) by simp
qed simp

lemma sw_rel_empty: "sw_rel f g sw_empty []"
  by (simp add: sw_rel_def sw_empty_def)

lemma sw_rel_push:
  assumes a: "sw_assoc f" and r: "sw_rel f g s W"
  shows "sw_rel f g (sw_push f g t e s) (W @ [(t, e)])"
  using r by (cases s) (auto simp: sw_rel_def sw_push_def sw_fold_snoc[OF a] split: option.splits)

lemma sw_query:
  assumes a: "sw_assoc f" and r: "sw_rel f g s W"
  shows "sw_query f s = sw_fold f (map (g \<circ> snd) W)"
proof -
  obtain fr bk B where s: "s = (fr, bk, B)" by (cases s)
  have W: "W = sw_strip fr @ rev bk" and sf: "sw_sfx f g fr"
    and B: "B = sw_fold f (map (g \<circ> snd) (rev bk))" using r by (auto simp: s sw_rel_def)
  show ?thesis
  proof (cases fr)
    case Nil then show ?thesis by (simp add: s W B sw_query_def)
  next
    case (Cons x fr')
    obtain t e c where x: "x = (t, e, c)" by (cases x)
    have h: "sw_fold f (map (g \<circ> snd) (sw_strip ((t, e, c) # fr'))) = Some c"
      using sf unfolding Cons x by (simp add: sw_sfx_Cons)
    show ?thesis unfolding s W B Cons x map_append sw_fold_append[OF a] h
      by (simp add: sw_query_def sw_comb_def)
  qed
qed

lemma sw_null:
  assumes r: "sw_rel f g s W"
  shows "sw_null s \<longleftrightarrow> W = []"
  using r by (cases s) (auto simp: sw_rel_def sw_null_def split: list.splits)

subsection \<open>Correctness of popping\<close>

lemma takeWhile_map_fst: "takeWhile (\<lambda>x. P (fst x)) (sw_strip fr) = sw_strip (takeWhile (\<lambda>(t, _). P t) fr)"
  by (induct fr) auto

lemma dropWhile_map_fst: "dropWhile (\<lambda>x. P (fst x)) (sw_strip fr) = sw_strip (dropWhile (\<lambda>(t, _). P t) fr)"
  by (induct fr) auto

lemma sw_strip4_simps[simp]:
  "sw_strip4 (sw_tag B xs) = sw_strip xs" "sw_strip4 (ys @ zs) = sw_strip4 ys @ sw_strip4 zs"
  by (simp_all add: sw_strip4_def sw_tag_def sw_strip_def split_beta)

lemma length_sw_tag[simp]: "length (sw_tag B xs) = length xs"
  by (simp add: sw_tag_def)

definition sw_out :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 't \<times> 'e \<times> 'a \<times> 'a option \<Rightarrow> 'a" where
  "sw_out f y = (case y of (_, _, a, B) \<Rightarrow> sw_comp f a B)"

lemma sw_sfx_fold:
  assumes a: "sw_assoc f" and sf: "sw_sfx f g fr" and k: "k < length fr"
  shows "sw_fold f (map (g \<circ> snd) (drop k (sw_strip fr) @ X)) =
    Some (sw_comp f (snd (snd (fr ! k))) (sw_fold f (map (g \<circ> snd) X)))"
proof -
  have "sw_fold f (map (g \<circ> snd) (drop k (sw_strip fr))) = Some (snd (snd (fr ! k)))"
    using sf k unfolding sw_sfx_def by simp
  then show ?thesis unfolding map_append sw_fold_append[OF a] by (simp add: sw_comb_def)
qed

lemma sw_out_tag:
  assumes a: "sw_assoc f" and sf: "sw_sfx f g fr" and k: "k < length (takeWhile Q fr)"
  shows "Some (sw_out f (sw_tag (sw_fold f (map (g \<circ> snd) X)) (takeWhile Q fr) ! k)) =
    sw_fold f (map (g \<circ> snd) (drop k (sw_strip fr @ X)))"
proof -
  have kf: "k < length fr" using k length_takeWhile_le[of Q fr] by linarith
  have t: "sw_tag (sw_fold f (map (g \<circ> snd) X)) (takeWhile Q fr) ! k =
      (fst (fr ! k), fst (snd (fr ! k)), snd (snd (fr ! k)), sw_fold f (map (g \<circ> snd) X))"
    using k by (simp add: sw_tag_def takeWhile_nth split_beta)
  have d: "drop k (sw_strip fr @ X) = drop k (sw_strip fr) @ X" using kf by simp
  show ?thesis by (simp only: t d sw_sfx_fold[OF a sf kf] sw_out_def prod.case)
qed

lemma sw_popx:
  assumes r: "sw_rel f g s W" and p: "sw_popx f g P s = (ys, s')"
  shows "sw_strip4 ys = takeWhile (\<lambda>x. P (fst x)) W \<and> sw_rel f g s' (dropWhile (\<lambda>x. P (fst x)) W) \<and>
    (sw_assoc f \<longrightarrow> (\<forall>k < length ys. Some (sw_out f (ys ! k)) = sw_fold f (map (g \<circ> snd) (drop k W))))"
proof -
  obtain fr bk B where s: "s = (fr, bk, B)" by (cases s)
  have W: "W = sw_strip fr @ rev bk" and sf: "sw_sfx f g fr"
    and B: "B = sw_fold f (map (g \<circ> snd) (rev bk))" using r by (auto simp: s sw_rel_def)
  let ?P = "\<lambda>(t, _ :: 'b \<times> 'a). P t" and ?Q = "\<lambda>x. P (fst x)"
  have front: "Some (sw_out f (sw_tag B (takeWhile ?P fr) ! k)) = sw_fold f (map (g \<circ> snd) (drop k W))"
    if a: "sw_assoc f" and k: "k < length (takeWhile ?P fr)" for k
    unfolding B W by (rule sw_out_tag[OF a sf k])
  show ?thesis
  proof (cases "dropWhile ?P fr")
    case Nil
    have allP: "\<forall>x \<in> set (sw_strip fr). ?Q x"
      using Nil by (auto simp: sw_strip_def)
    have tw: "takeWhile ?P fr = fr" using Nil by simp
    have tW: "takeWhile ?Q W = sw_strip fr @ takeWhile ?Q (rev bk)"
      unfolding W by (rule takeWhile_append2) (use allP in blast)
    have dW: "dropWhile ?Q W = dropWhile ?Q (rev bk)"
      unfolding W by (rule dropWhile_append2) (use allP in blast)
    show ?thesis
    proof (cases bk)
      case Nil
      have p': "ys = sw_tag B (takeWhile ?P fr)" "s' = ([], [], None)"
        using p unfolding s sw_popx_def Let_def
        by (simp_all add: Nil \<open>dropWhile ?P fr = []\<close>)
      show ?thesis unfolding p'(2) tW dW using Nil front by (simp add: p'(1) tw sw_rel_def)
    next
      case (Cons b bk')
      define fl where "fl = sw_flip f g bk []"
      have fl: "sw_sfx f g fl" "sw_strip fl = rev bk" using sw_flip[of f g "[]" bk] by (simp_all add: fl_def)
      have p': "ys = sw_tag B (takeWhile ?P fr) @ sw_tag None (takeWhile ?P fl)"
        "s' = (dropWhile ?P fl, [], None)"
        using p unfolding s sw_popx_def Let_def fl_def[symmetric]
        by (simp_all add: \<open>dropWhile ?P fr = []\<close> Cons fl_def)
      have agg: "Some (sw_out f (ys ! k)) = sw_fold f (map (g \<circ> snd) (drop k W))"
        if a: "sw_assoc f" and k: "k < length ys" for k
      proof (cases "k < length (takeWhile ?P fr)")
        case True
        then show ?thesis using front[OF a True] by (simp add: p'(1) nth_append)
      next
        case False
        define k' where "k' = k - length fr"
        have k': "k' < length (takeWhile ?P fl)" "k = length fr + k'"
          using k False by (simp_all add: p'(1) tw k'_def)
        have "Some (sw_out f (sw_tag (sw_fold f (map (g \<circ> snd) [])) (takeWhile ?P fl) ! k')) =
            sw_fold f (map (g \<circ> snd) (drop k' (sw_strip fl @ [])))"
          using sw_out_tag[OF a fl(1) k'(1), of "[]"] by simp
        then show ?thesis using k' by (simp add: p'(1) nth_append tw W fl(2))
      qed
      show ?thesis unfolding p'(2) tW dW sw_rel_def
        using sw_sfx_dropWhile[OF fl(1)] fl(2) agg
        by (simp add: p'(1) tw takeWhile_map_fst[symmetric] dropWhile_map_fst[symmetric])
    qed
  next
    case (Cons x fr')
    then obtain y where y: "y \<in> set fr" "\<not> ?P y"
      by (metis dropWhile_eq_Cons_conv list.set_intros(1) set_dropWhileD)
    have y': "(fst y, fst (snd y)) \<in> set (sw_strip fr)" "\<not> ?Q (fst y, fst (snd y))"
      using y by (force simp: sw_strip_def)+
    have tW: "takeWhile ?Q W = takeWhile ?Q (sw_strip fr)"
      unfolding W by (rule takeWhile_append1[where P = ?Q, OF y'])
    have dW: "dropWhile ?Q W = dropWhile ?Q (sw_strip fr) @ rev bk"
      unfolding W by (rule dropWhile_append1[where P = ?Q, OF y'])
    have p': "ys = sw_tag B (takeWhile ?P fr)" "s' = (dropWhile ?P fr, bk, B)"
      using p unfolding s sw_popx_def Let_def by (simp_all add: Cons)
    show ?thesis unfolding p'(2) tW dW sw_rel_def
      using sw_sfx_dropWhile[OF sf] B front by (simp add: p'(1) takeWhile_map_fst dropWhile_map_fst)
  qed
qed

lemma sw_pop:
  assumes r: "sw_rel f g s W" and p: "sw_pop f g P s = (ys, s')"
  shows "ys = takeWhile (\<lambda>x. P (fst x)) W \<and> sw_rel f g s' (dropWhile (\<lambda>x. P (fst x)) W)"
proof -
  obtain zs where z: "sw_popx f g P s = (zs, s')" and ys: "ys = sw_strip4 zs"
    using p by (cases "sw_popx f g P s") (simp add: sw_pop_def)
  show ?thesis using sw_popx[OF r z] ys by simp
qed
(*<*)
end
(*>*)

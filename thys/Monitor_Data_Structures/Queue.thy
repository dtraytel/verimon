(*<*)
theory Queue
  imports "HOL-Library.Simps_Case_Conv" "HOL-Library.Mapping"
begin
(*>*)

section \<open>Queues as pairs of lists\<close>

subsection \<open>Representation and operations\<close>

type_synonym 'a queue_t = "'a list \<times> 'a list"

definition queue_invariant :: "'a queue_t \<Rightarrow> bool" where
  "queue_invariant q = (case q of ([], []) \<Rightarrow> True | (fs, l # ls) \<Rightarrow> True | _ \<Rightarrow> False)"

typedef 'a queue = "{q :: 'a queue_t. queue_invariant q}"
  by (auto simp: queue_invariant_def split: list.splits)

setup_lifting type_definition_queue

lift_definition linearize :: "'a queue \<Rightarrow> 'a list" is "(\<lambda>q. case q of (fs, ls) \<Rightarrow> fs @ rev ls)" .

lift_definition empty_queue :: "'a queue" is "([], [])"
  by (auto simp: queue_invariant_def split: list.splits)

lemma empty_queue_rep: "linearize empty_queue = []"
  by transfer (simp add: empty_queue_def linearize_def)

lift_definition is_empty :: "'a queue \<Rightarrow> bool" is "\<lambda>q. (case q of ([], []) \<Rightarrow> True | _ \<Rightarrow> False)" .

lemma linearize_t_Nil: "(case q of (fs, ls) \<Rightarrow> fs @ rev ls) = [] \<longleftrightarrow> q = ([], [])"
  by (auto split: prod.splits)

lemma is_empty_alt: "is_empty q \<longleftrightarrow> linearize q = []"
  by transfer (auto simp: linearize_t_Nil list.case_eq_if)

fun prepend_queue_t :: "'a \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "prepend_queue_t a ([], []) = ([], [a])"
| "prepend_queue_t a (fs, l # ls) = (a # fs, l # ls)"
| "prepend_queue_t a (f # fs, []) = undefined"

lift_definition prepend_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is prepend_queue_t
  by (auto simp: queue_invariant_def split: list.splits elim: prepend_queue_t.elims)

lemma prepend_queue_rep: "linearize (prepend_queue a q) = a # linearize q"
  by transfer
    (auto simp add: queue_invariant_def linearize_def elim: prepend_queue_t.elims split: prod.splits)

lift_definition append_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is
  "(\<lambda>a q. case q of (fs, ls) \<Rightarrow> (fs, a # ls))"
  by (auto simp: queue_invariant_def split: list.splits)

lemma append_queue_rep: "linearize (append_queue a q) = linearize q @ [a]"
  by transfer (auto simp add: linearize_def split: prod.splits)

fun safe_hd_t :: "'a queue_t \<Rightarrow> 'a option \<times> 'a queue_t" where
  "safe_hd_t ([], []) = (None, ([], []))"
| "safe_hd_t ([], [l]) = (Some l, ([], [l]))"
| "safe_hd_t ([], l # ls) = (let fs = rev ls in (Some (hd fs), (fs, [l])))"
| "safe_hd_t (f # fs, l # ls) = (Some f, (f # fs, l # ls))"
| "safe_hd_t (f # fs, []) = undefined"

lift_definition(code_dt) safe_hd :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" is safe_hd_t
proof -
  fix q :: "'a queue_t"
  assume "queue_invariant q"
  then show "pred_prod top queue_invariant (safe_hd_t q)"
    by (cases q rule: safe_hd_t.cases) (auto simp: queue_invariant_def Let_def split: list.split)
qed

lemma safe_hd_rep: "safe_hd q = (\<alpha>, q') \<Longrightarrow> linearize q = linearize q' \<and>
  (case \<alpha> of None \<Rightarrow> linearize q = [] | Some a \<Rightarrow> linearize q \<noteq> [] \<and> a = hd (linearize q))"
  by transfer
    (auto simp add: queue_invariant_def Let_def hd_append split: list.splits elim: safe_hd_t.elims)

fun tl_queue_t :: "'a queue_t \<Rightarrow> 'a queue_t" where
  "tl_queue_t ([], []) = ([], [])"
| "tl_queue_t ([], [l]) = ([], [])"
| "tl_queue_t ([], l # ls) = (tl (rev ls), [l])"
| "tl_queue_t (a # as, fs) = (as, fs)"

lift_definition tl_queue :: "'a queue \<Rightarrow> 'a queue" is tl_queue_t
  by (auto simp: queue_invariant_def split: list.splits elim!: tl_queue_t.elims)

subsection \<open>Code equations\<close>

text \<open>The code equations return the argument wherever it is the result, so that unchanged queues
  are not rebuilt.\<close>

declare [[code drop: safe_hd_t]]

lemma safe_hd_t_code[code]:
  "safe_hd_t q = (case q of (fs, ls) \<Rightarrow>
     (case fs of
        f # fs' \<Rightarrow> (case ls of [] \<Rightarrow> undefined | _ \<Rightarrow> (Some f, q))
      | [] \<Rightarrow> (case ls of
                [] \<Rightarrow> (None, q)
              | [l] \<Rightarrow> (Some l, q)
              | l # v # va \<Rightarrow> (let gs = rev (v # va) in (Some (hd gs), (gs, [l]))))))"
  by (cases q rule: safe_hd_t.cases) (auto simp: Let_def)

declare [[code drop: prepend_queue_t]]

lemma prepend_queue_t_code[code]:
  "prepend_queue_t a q = (case q of (fs, ls) \<Rightarrow>
     (case ls of [] \<Rightarrow> (case fs of [] \<Rightarrow> ([], [a]) | _ \<Rightarrow> undefined)
      | _ \<Rightarrow> (a # fs, ls)))"
  by (cases "(a, q)" rule: prepend_queue_t.cases) auto

declare [[code drop: tl_queue_t]]

lemma tl_queue_t_code[code]:
  "tl_queue_t q = (case q of (fs, ls) \<Rightarrow>
     (case fs of
        a # as \<Rightarrow> (as, ls)
      | [] \<Rightarrow> (case ls of
                [] \<Rightarrow> q
              | [l] \<Rightarrow> ([], [])
              | l # v # va \<Rightarrow> (tl (rev (v # va)), [l]))))"
  by (cases q rule: tl_queue_t.cases) auto

subsection \<open>Head and normalisation\<close>

text \<open>Splitting @{const safe_hd} into its two components avoids the intermediate datatype that
  @{text code_dt} introduces for its pair result.\<close>

fun hd_queue_t :: "'a queue_t \<Rightarrow> 'a option" where
  "hd_queue_t ([], []) = None"
| "hd_queue_t ([], [l]) = Some l"
| "hd_queue_t ([], l # ls) = Some (last ls)"
| "hd_queue_t (f # fs, l # ls) = Some f"
| "hd_queue_t (f # fs, []) = undefined"

fun norm_queue_t :: "'a queue_t \<Rightarrow> 'a queue_t" where
  "norm_queue_t ([], []) = ([], [])"
| "norm_queue_t ([], [l]) = ([], [l])"
| "norm_queue_t ([], l # ls) = (rev ls, [l])"
| "norm_queue_t (f # fs, l # ls) = (f # fs, l # ls)"
| "norm_queue_t (f # fs, []) = undefined"

lemma safe_hd_t_split:
  "queue_invariant q \<Longrightarrow> safe_hd_t q = (hd_queue_t q, norm_queue_t q)"
  by (cases q rule: safe_hd_t.cases)
     (auto simp: queue_invariant_def Let_def hd_rev)

lemma norm_queue_t_invariant:
  "queue_invariant q \<Longrightarrow> queue_invariant (norm_queue_t q)"
  by (cases q rule: norm_queue_t.cases)
     (auto simp: queue_invariant_def split: list.splits)

lift_definition hd_queue :: "'a queue \<Rightarrow> 'a option" is hd_queue_t .

lift_definition norm_queue :: "'a queue \<Rightarrow> 'a queue" is norm_queue_t
  by (rule norm_queue_t_invariant)

lemma hd_queue_t_front:
  "fs \<noteq> [] \<Longrightarrow> ls \<noteq> [] \<Longrightarrow> hd_queue_t (fs, ls) = Some (hd fs)"
  by (cases fs; cases ls) auto

lemma hd_queue_t_norm:
  "queue_invariant q \<Longrightarrow> hd_queue_t (norm_queue_t q) = hd_queue_t q"
  by (cases q rule: norm_queue_t.cases)
     (auto simp: queue_invariant_def hd_queue_t_front hd_rev hd_append
           split: list.splits)

declare [[code drop: safe_hd]]

text \<open>On the normalised queue, the head is the first element of the front list.\<close>

lemma safe_hd_code[code]: "safe_hd q = (let q' = norm_queue q in (hd_queue q', q'))"
  unfolding Let_def
  by transfer (simp add: safe_hd_t_split hd_queue_t_norm)

declare [[code drop: norm_queue_t]]

lemma norm_queue_t_code[code]:
  "norm_queue_t q = (case q of (fs, ls) \<Rightarrow>
     (case fs of
        f # fs' \<Rightarrow> (case ls of [] \<Rightarrow> undefined | _ \<Rightarrow> q)
      | [] \<Rightarrow> (case ls of
                 [] \<Rightarrow> q
               | [l] \<Rightarrow> q
               | l # v # va \<Rightarrow> (rev (v # va), [l]))))"
  by (cases q rule: norm_queue_t.cases) auto

lemma hd_queue_t_rep:
  "queue_invariant q \<Longrightarrow>
   hd_queue_t q = (case (case q of (fs, ls) \<Rightarrow> fs @ rev ls) of [] \<Rightarrow> None | x # _ \<Rightarrow> Some x)"
  by (cases q rule: hd_queue_t.cases)
     (auto simp: queue_invariant_def hd_rev hd_append list.case_eq_if)

lemma hd_queue_rep: "hd_queue q = (case linearize q of [] \<Rightarrow> None | x # _ \<Rightarrow> Some x)"
  by transfer (rule hd_queue_t_rep)

subsection \<open>Dropping the head\<close>

text \<open>Popping does @{const safe_hd} followed by @{const tl_queue} in a single step.\<close>

fun pop_queue_t :: "'a queue_t \<Rightarrow> 'a queue_t" where
  "pop_queue_t ([], []) = ([], [])"
| "pop_queue_t ([], [l]) = ([], [])"
| "pop_queue_t ([], l # ls) = (tl (rev ls), [l])"
| "pop_queue_t (f # fs, ls) = (fs, ls)"

text \<open>Matching inside the body rather than on the parameter compiles to a one-argument function
  without an adapter for the pair.\<close>

declare [[code drop: hd_queue_t]]

lemma hd_queue_t_code[code]:
  "hd_queue_t q = (case q of (fs, ls) \<Rightarrow>
     (case fs of
        f # fs' \<Rightarrow> (case ls of [] \<Rightarrow> undefined | _ \<Rightarrow> Some f)
      | [] \<Rightarrow> (case ls of
                 [] \<Rightarrow> None
               | [l] \<Rightarrow> Some l
               | l # v # va \<Rightarrow> Some (last (v # va)))))"
  by (cases q rule: hd_queue_t.cases) auto

lemma pop_queue_t_invariant:
  "queue_invariant q \<Longrightarrow> queue_invariant (pop_queue_t q)"
  by (cases q rule: pop_queue_t.cases)
     (auto simp: queue_invariant_def split: list.splits)

lift_definition pop_queue :: "'a queue \<Rightarrow> 'a queue" is pop_queue_t
  by (rule pop_queue_t_invariant)

declare [[code drop: pop_queue_t]]

lemma pop_queue_t_code[code]:
  "pop_queue_t q = (case q of (fs, ls) \<Rightarrow>
     (case fs of
        f # fs' \<Rightarrow> (fs', ls)
      | [] \<Rightarrow> (case ls of
                 [] \<Rightarrow> q
               | [l] \<Rightarrow> ([], [])
               | l # v # va \<Rightarrow> (tl (rev (v # va)), [l]))))"
  by (cases q rule: pop_queue_t.cases) auto

lemma pop_queue_t_rep:
  "queue_invariant q \<Longrightarrow>
   (case pop_queue_t q of (fs, ls) \<Rightarrow> fs @ rev ls) =
   tl (case q of (fs, ls) \<Rightarrow> fs @ rev ls)"
  by (cases q rule: pop_queue_t.cases)
     (auto simp: queue_invariant_def tl_append2[symmetric] split: list.splits)

lemma pop_queue_rep: "linearize (pop_queue q) = tl (linearize q)"
  by transfer (rule pop_queue_t_rep)

subsection \<open>Appending a list\<close>

text \<open>A list is appended in one pass, reversed onto the back list by a named function, since the
  library's code for @{const rev} applies a closure per element.\<close>

fun rev_prepend :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_prepend [] ys = ys"
| "rev_prepend (x # xs) ys = rev_prepend xs (x # ys)"

lemma rev_prepend_eq: "rev_prepend xs ys = rev xs @ ys"
  by (induction xs arbitrary: ys) auto

lift_definition append_queue_list :: "'a list \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is
  "\<lambda>ys q. (case q of (fs, ls) \<Rightarrow> (fs, rev_prepend ys ls))"
  by (auto simp: queue_invariant_def rev_prepend_eq split: list.splits)

lemma append_queue_list_rep:
  "linearize (append_queue_list ys q) = linearize q @ ys"
  by transfer (auto simp: linearize_def rev_prepend_eq)

lemma fold_append_queue_rep: "linearize (fold (\<lambda>x q. append_queue x q) xs q) = linearize q @ xs"
  by (induction xs arbitrary: q) (auto simp add: append_queue_rep)

subsection \<open>Dropping and taking prefixes\<close>

lemma tl_queue_rep: "linearize (tl_queue q) = tl (linearize q)"
  by transfer (auto simp: tl_append2[symmetric] split: prod.splits list.splits elim!: tl_queue_t.elims)

lemma length_tl_queue_rep: "\<not>is_empty q \<Longrightarrow>
  length (linearize (tl_queue q)) < length (linearize q)"
  by transfer (auto split: prod.splits list.splits elim: tl_queue_t.elims)

lemma length_tl_queue_safe_hd:
  assumes "safe_hd q = (Some a, q')"
  shows "length (linearize (tl_queue q')) < length (linearize q)"
  using safe_hd_rep[OF assms]
  by (auto simp add: length_tl_queue_rep is_empty_alt)

function dropWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "dropWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> q'
  | (Some a, q') \<Rightarrow> if f a then dropWhile_queue f (tl_queue q') else q')"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma dropWhile_hd_tl: "xs \<noteq> [] \<Longrightarrow>
  dropWhile P xs = (if P (hd xs) then dropWhile P (tl xs) else xs)"
  by (cases xs) auto

lemma dropWhile_queue_rep: "linearize (dropWhile_queue f q) = dropWhile f (linearize q)"
  by (induction f q rule: dropWhile_queue.induct)
     (auto simp add: tl_queue_rep dropWhile_hd_tl is_empty_alt
      split: prod.splits option.splits dest: safe_hd_rep)

function takeWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> ('a queue \<times> 'a queue)" where
  "takeWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> (q', q')
  | (Some a, q') \<Rightarrow> if f a
    then let (q'', rem) = takeWhile_queue f (tl_queue q') in (prepend_queue a q'', q')
    else (empty_queue, q'))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma takeWhile_hd_tl: "xs \<noteq> [] \<Longrightarrow>
  takeWhile P xs = (if P (hd xs) then hd xs # takeWhile P (tl xs) else [])"
  by (cases xs) auto

lemma takeWhile_queue_rep_fst: "linearize (fst (takeWhile_queue f q)) = takeWhile f (linearize q)"
proof(induction f q rule: takeWhile_queue.induct)
  case (1 f q)
  then obtain hd rm where safe_hd_eq: "safe_hd q = (hd, rm)" by (meson prod.exhaust_sel)
  then show ?case 
  proof(cases "hd")
    case None
    then show ?thesis using safe_hd_eq by(auto dest: safe_hd_rep)
  next
    case (Some a)
    then show ?thesis 
    proof(cases "f a")
      case True
      then show ?thesis using safe_hd_eq Some 1[OF safe_hd_eq[symmetric] Some True] 
        by(auto simp add: prepend_queue_rep tl_queue_rep  takeWhile_hd_tl is_empty_alt split: prod.splits dest: safe_hd_rep)
    next
      case False
      then show ?thesis using safe_hd_eq Some by(auto simp add: empty_queue_rep takeWhile_hd_tl  dest: safe_hd_rep) 
    qed
  qed
qed

lemma takeWhile_queue_rep_snd: "linearize (snd (takeWhile_queue f q)) = linearize q"
proof -
  obtain x rm where safe_hd_eq: "safe_hd q = (x, rm)" by (cases "safe_hd q")
  have "snd (takeWhile_queue f q) = rm"
    using safe_hd_eq by (simp add: case_prod_unfold split: option.split)
  then show ?thesis
    using safe_hd_rep[OF safe_hd_eq] by simp
qed

function takedropWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue \<times> 'a list" where
  "takedropWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> (q', [])
  | (Some a, q') \<Rightarrow> if f a
    then (case takedropWhile_queue f (tl_queue q') of (q'', as) \<Rightarrow> (q'', a # as))
    else (q', []))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma takedropWhile_queue_fst: "fst (takedropWhile_queue f q) = dropWhile_queue f q"
proof (induction f q rule: takedropWhile_queue.induct)
  case (1 f q)
  then show ?case
    by (simp split: prod.splits) (auto simp add: case_prod_unfold split: option.splits)
qed

lemma takedropWhile_queue_snd: "snd (takedropWhile_queue f q) = takeWhile f (linearize q)"
proof (induction f q rule: takedropWhile_queue.induct)
  case (1 f q)
  then show ?case
    by (simp split: prod.splits)
      (auto simp add: case_prod_unfold tl_queue_rep takeWhile_hd_tl is_empty_alt
        split: option.splits dest: safe_hd_rep)
qed

lemma not_empty_head_q:
  assumes "\<not>is_empty q"
  shows "\<exists>ts tss. safe_hd q = (Some ts, tss)"
proof -
  obtain x q' where safe_hd_eq: "safe_hd q = (x, q')" by (cases "safe_hd q")
  have "linearize q \<noteq> []"
    using assms by (simp add: is_empty_alt)
  with safe_hd_rep[OF safe_hd_eq] obtain ts where "x = Some ts"
    by (cases x) auto
  with safe_hd_eq show ?thesis by blast
qed

end
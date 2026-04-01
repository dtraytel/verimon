# Incremental Freeze: Detailed Design

## Motivation

The current `MFrz` algorithm replays ψ **from scratch** for every pending
snapshot, each time recomputing all tables from `jpsi0'` to `jpsij'`. Only one
table per replay is actually used (the "diagonal" element). This is correct
(once the counter bug is fixed) but wasteful: the total work per step is
O(|αs| × L) where L = jpsij' − jpsi0'.

The incremental approach stores a per-snapshot ψ monitor state and advances
each one by δ steps, reducing the per-step cost to O(|αs| × δ).

---

## Current algorithm recap

### Semantics

```
sat σ V v i (Frz p φ ψ) = sat σ (V(pn ↦ λw k. sat σ V w i φ)) v i ψ
```

The frozen binding uses the **outer** time `i` inside φ — the snapshot is
"frozen" at the query time `i`.

### Progress

```
frz_progress P p φ ψ j =
  LEAST i. i ≤ j ∧ progress(P(pn ↦ if i < progress P φ j then j else 0)) ψ j ≤ i
```

### Current state

```
MFrz p m φ ψ jfrz jpsi0 jphi αs
```

- `φ`: snapshot submonitor
- `ψ`: **shared** template ψ monitor (advanced under P(pn↦0))
- `jfrz`: freeze progress (number of output tables produced so far)
- `jpsi0`: ψ-progress under P(pn↦0)
- `jphi`: φ-progress (number of snapshots produced)
- `αs`: pending snapshot queue (event_data table list)

### Current algorithm step

```
xs       := meval φ          -- xs covers [jphi..jphi')
zs0      := meval ψ on db0   -- zs0 covers [jpsi0..jpsi0')    (db0: pn ↦ [])
zs0_out  := drop (jfrz - jpsi0) zs0
jpsi0'   := jpsi0 + |zs0|
αs1      := drop (jfrz - jphi + |zs0_out|) (αs @ xs)
(ys, αs') := freeze_meval0 (λα. meval ψ from scratch with pn ↦ replicate j α) 0 αs1
output   := zs0_out @ ys
```

### Current bugs / issues

1. **Counter bug**: initial counter should be `(jfrz - jpsi0)` (updated jpsi0),
   not `0`. Without this fix, when `jfrz > jpsi0'`, the diagonal extracts the
   wrong element.

2. **Performance**: each replay recomputes L tables but only uses 1. Over N
   steps, a snapshot that entered at step k pays O(Σ_{s=k}^{N} L_s) work
   instead of O(Σ_{s=k}^{N} δ_s) = O(N - k) work.

---

## Incremental design

### Key idea

Instead of replaying ψ from scratch each time, store a **per-snapshot ψ
monitor state** in the queue. Each step incrementally advances each ψ_α by δ
new time steps. We use the same diagonal extraction as before (counter `k`
in `freeze_step`), but each `eval` call is now O(δ) instead of O(L).

### New state

```
MFrz p m φ ψ_template jfrz jphi αψs
```

Changes from current:
- **Removed** `jpsi0` — no longer tracked (the shared ψ run is only used to
  advance the template, not to produce output)
- **Changed** `αs : table list` → `αψs : (table × mformula) list` — each
  queue entry is a (snapshot, ψ-state) pair
- The shared ψ monitor `ψ_template` is kept and advanced (with pn ↦ []) so
  that new entries start from the latest shared progress

The datatype change:

```isabelle
(* Current *)
| MFrz Formula.name nat "mformula" "mformula"
    nat nat nat "event_data table list"

(* Incremental *)
| MFrz Formula.name nat "mformula" "mformula"
    nat nat "(event_data table × mformula) list"
```

Fields: `p`, `m`, `φ`, `ψ_template`, `jfrz`, `jphi`, `αψs`.

Note: Isabelle's datatype system should handle the `(table × mformula) list`
recursion. The `MAnds` constructor already uses `mformula list`, so recursive
occurrences in lists are supported. We need to verify that `(table × mformula)
list` is also accepted (products of recursive types in lists).

### Size preservation (termination)

The `meval` termination measure is `size φ` (the mformula size). For the
recursive calls:
- `meval ... φ` — size decreases. ✓
- `meval ... ψ_template` — same as current shared ψ call. ✓
- `meval ... ψ_α` for each ψ_α in the queue — needs `size ψ_α = size ψ`.
  This is guaranteed by `size_snd_meval`: `size (snd (meval ...)) = size ψ`.
  Initially each ψ_α is created as a copy of `ψ_template`, so
  `size ψ_α = size ψ_template = size ψ`. After each meval step,
  `size ψ_α' = size ψ_α = size ψ`. ✓

As in the current approach, the recursive calls on ψ_α happen inside a helper
function (`freeze_step`) via a lambda, so they appear as calls to the lambda
rather than direct recursive calls of `meval`.

### New helper function: `freeze_step`

```isabelle
fun freeze_step where
  "freeze_step eval k [] = ([], [])"
| "freeze_step eval k ((α, ψ_α) # rest) =
    (let (us, ψ_α') = eval α ψ_α
     in case drop k us of
       [] ⇒ ([], (α, ψ_α') #
              map (λ(a, s). let (_, s') = eval a s in (a, s')) rest)
     | y # _ ⇒
         let (zs, rest') = freeze_step eval (Suc k) rest
         in (y # zs, rest'))"
```

This is structurally identical to `freeze_meval0`, with two differences:
1. `eval` takes two arguments `(α, ψ_α)` instead of one `α`
2. When stopping (non-producing entry), we still advance all remaining
   entries via `map` to keep their ψ states up to date

The counter `k` performs the same diagonal extraction as before.

When we stop at a non-producing entry, all later entries are also
non-producing (by monotonicity: earlier entries have more accumulated pn data,
hence higher ψ progress). So we just advance them without trying to extract.

### Algorithm step

```isabelle
| "meval n ts db (MFrz p m φ ψ_tmpl jfrz jphi αψs) =
    (let (xs, φ') = meval m ts db φ;
         δ = length ts;
         db0 = Mapping.update (p, m) [] db;
         (* Advance the template ψ (shared run with no pn data) *)
         (_, ψ_tmpl') = meval n ts db0 ψ_tmpl;
         (* Create new entries from the UPDATED template *)
         new_entries = map (λα. (α, ψ_tmpl')) xs;
         (* Trim: drop entries at indices below jfrz *)
         αψs1 = drop (jfrz - jphi) (αψs @ new_entries);
         (* Per-snapshot advancement: override pn with δ copies of snapshot *)
         (ys, αψs') = freeze_step
           (λα ψ_α. meval n ts (Mapping.update (p, m) (replicate δ α) db) ψ_α)
           0 αψs1;
         jphi' = jphi + length xs;
         jfrz' = jfrz + length ys
     in (ys, MFrz p m φ' ψ_tmpl' jfrz' jphi' αψs'))"
```

Key differences from current:
- No `zs0` / `zs0_out` / `jpsi0` — no separate shared-run output
- Each entry is `(snapshot, ψ-state)` instead of just `snapshot`
- `eval` advances ψ_α by δ steps (not from scratch)
- Output is just `ys` (no `zs0_out @ ys`)

### Why the shared ψ run output (zs0_out) is eliminated

In the current approach, `zs0_out` provides "free" output at indices where
V-insensitivity applies (the frozen binding doesn't matter for i < jpsi0').

In the incremental approach, the per-snapshot entries produce the SAME tables
at those indices — by V-insensitivity, the value of V(pn) doesn't affect
`sat` for `i < jpsi0'`. And per-snapshot entries have at least as much pn
data as the shared run, so their progress is ≥ jpsi0'. They produce output
at those indices at least as fast.

So the shared run output is redundant. The shared run is still needed to
advance the template for creating new entries, but its output is discarded.

### Why the initial counter is 0 (and may still need an offset)

The counter `k` in `freeze_step` starts at 0. Entry i in the queue
corresponds to snapshot index `jfrz + i` (the first entry is for the first
un-output index).

Entry i's ψ_α has progress `prog_α_i`. The output `us_i` covers
`[prog_α_i..<prog_α_i + |us_i|)`. We want the table at index `jfrz + i`.
The position within `us_i` is `(jfrz + i) - prog_α_i`.

For the diagonal to work with starting counter 0, we need the first entry
to have `(jfrz + 0) - prog_α_0 = 0`, i.e., `prog_α_0 = jfrz`. And each
subsequent entry's offset increases by 1.

Is `prog_α_0 = jfrz` guaranteed? Entry 0 is the oldest entry, with the most
pn data. Its pn-progress equals the number of steps it has been in the queue
times δ. Its overall ψ progress is `progress(P_α_0) ψ (j+δ)`.

In general, `prog_α_0 ≤ jfrz` is possible (the entry hasn't caught up yet).
In that case, the counter should start at `jfrz - prog_α_0` instead of 0.

**This is the same counter-offset issue as in the current algorithm.**
The fix is the same: start the counter at `jfrz - prog_α_0` where
`prog_α_0` is the first entry's ψ progress.

However, `prog_α_0` is not directly stored — it's implicit in the ψ_α state.
We'd need to either:
1. Compute it from `ψ_α` (requires a `progress` function on mformula states)
2. Store it explicitly in the queue entry
3. Prove it always equals `jfrz` (via invariant)

Option 3 is the cleanest. If we can maintain the invariant that every entry
in the queue has `prog_α ≥ target_index`, then the counter 0 works and the
first element of `us` is always the right table.

Alternatively, option 2 (store `prog_α` per entry) adds a nat to each entry:
```
αψs : (table × mformula × nat) list
```

### How different entries' outputs relate

All entries receive the SAME non-pn data (same `db` for q ≠ pn). Earlier
entries (at the front of the queue) have accumulated MORE pn data (they've
been in the queue longer). So:

- `prog_α_0 ≥ prog_α_1 ≥ ... ≥ prog_α_N`

The diagonal requires:
- Entry 0: extract position `k0`
- Entry 1: extract position `k0 + 1`
- Entry i: extract position `k0 + i`

Where `k0 = jfrz - prog_α_0`.

But wait: the extraction position for entry i is `(jfrz + i) - prog_α_i`.
For the diagonal to work, we need:
```
(jfrz + i) - prog_α_i = k0 + i = (jfrz - prog_α_0) + i
```
which requires `prog_α_i = prog_α_0` for all i. This means ALL entries
must have the SAME progress, which is only true if the accumulated pn data
doesn't affect progress.

**This is NOT generally true.** Different entries have different pn data
histories, leading to different progresses.

### The diagonal breaks for incremental!

In the from-scratch approach, all replays start from the same ψ_new state
and use the same P(pn↦j+δ), so all produce the same number of tables L.
The diagonal works because every replay has the same output length and
structure.

In the incremental approach, different entries have different ψ states
and different accumulated pn data, so different output lengths. **The
uniform diagonal no longer applies.**

### Solution: per-entry extraction

Instead of a global counter, each entry needs its own extraction offset.
This changes `freeze_step`:

```isabelle
fun freeze_step where
  "freeze_step eval [] = ([], [])"
| "freeze_step eval ((α, ψ_α, off) # rest) =
    (let (us, ψ_α') = eval α ψ_α;
         off' = off + length us   (* advance offset by output length *)
     in if off < length us then  (* i.e., drop off us ≠ [] *)
         let y = us ! off;
             (zs, rest') = freeze_step eval rest
         in (y # zs, rest')
       else
         ([], (α, ψ_α', off - length us) #
              map (λ(a, s, o). let (us', s') = eval a s in (a, s', o - length us')) rest))"
```

Wait, this doesn't work cleanly either. Let me reconsider.

Actually, the offset should represent "how many tables from this entry's ψ
have already been consumed by previous steps." After each step, `us` has new
tables. The total tables produced by this ψ over its lifetime is some N_total.
We need the one at position `target - initial_progress`.

Let me think about this differently. Store `consumed` — the number of tables
already produced AND skipped by this entry's ψ:

```
Entry: (α, ψ_α, consumed)
```

- `ψ_α` has produced `consumed` tables so far (these were either used for
  output at previous indices or skipped because they were below jfrz)
- After `eval α ψ_α → (us, ψ_α')`:
  - `consumed' = consumed + length us`
  - The table we want is at position `target - initial_prog` within the
    total output. Since `consumed` tables have already been produced and the
    target is the entry's assigned index, we need the `(target - initial_prog
    - consumed)`-th element of `us`. But `target - initial_prog - consumed`
    is just `target - (initial_prog + consumed) = target - current_prog_before`.
    And `current_prog_before` = `initial_prog + consumed`. So the position is
    `target - current_prog_before`.

Hmm, this is getting complicated. Let me simplify.

### Simpler formulation: store remaining offset

Each entry has `(α, ψ_α, k)` where `k` is the remaining number of tables to
skip before reaching the target:

```isabelle
fun freeze_step where
  "freeze_step eval [] = ([], [])"
| "freeze_step eval ((α, ψ_α, k) # rest) =
    (let (us, ψ_α') = eval α ψ_α
     in case drop k us of
       [] ⇒ let k' = k - length us in
             ([], (α, ψ_α', k') #
              map (λ(a, s, ki). let (us', s') = eval a s in (a, s', ki - length us')) rest)
     | y # _ ⇒
         let (zs, rest') = freeze_step eval rest
         in (y # zs, rest'))"
```

After `eval α ψ_α`:
- `us` has `length us` new tables
- `drop k us` gives the tables starting from position k
- If non-empty: `y = hd (drop k us)` is our output. Remove entry.
- If empty: `k - length us` is the remaining offset. Keep entry.

For the NEXT entry in `rest`: its offset is independent (each entry has its
own `k`). So we don't need `Suc k` — each entry carries its own offset.

This is cleaner than the diagonal counter! Each entry independently tracks
how many tables to skip.

### When do we initialize k?

When a new snapshot α arrives at step with index `i = jphi + position`:
- A fresh ψ state is created from `ψ_tmpl'` (at progress `jpsi0_tmpl'`)
- The target index for this entry is `i`
- The initial skip is `k = i - jpsi0_tmpl'`
  (how many tables to skip before reaching index i)

Wait, `jpsi0_tmpl'` is the template's progress under P(pn↦0). But the
entry gets P(pn↦δ) for pn data, so its actual progress will be higher.

Actually, the initial k should be `i - prog_initial` where `prog_initial`
is the ψ progress at the time the entry is created. Since the entry starts
from `ψ_tmpl'` and immediately gets `eval α ψ_tmpl'` (with pn data), the
initial progress is whatever `ψ_tmpl'` is at.

But `ψ_tmpl'` has progress `jpsi0' = progress(P'(pn↦0)) ψ (j+δ)` for
the shared run. So `k_initial = i - jpsi0'` (nat subtraction: 0 if i ≤ jpsi0').

Actually wait — entries are not evaluated immediately upon creation. They're
created and put in the queue. `freeze_step` then evaluates them. So the
initial progress is the template progress jpsi0', and k = target - jpsi0'
(nat subtraction).

But we don't store jpsi0' explicitly (we removed it from the state). We'd
need to compute it or store k at creation time.

### Revised state with per-entry offset

```
MFrz p m φ ψ_template jfrz jphi αψs
```

Where `αψs : (table × mformula × nat) list`.

Each entry is `(α, ψ_α, k)`:
- `α`: frozen snapshot table
- `ψ_α`: incremental ψ monitor state
- `k`: remaining offset (tables to skip before reaching target index)

### Creation of new entries

```
new_entries = map (λα. (α, ψ_tmpl', target - jpsi0')) xs
```

But `target` differs per snapshot. Snapshot at position p in xs has target
`jphi + p`. Wait, after trimming, the target depends on where in the queue
the entry ends up.

Actually, let's think about it differently. At creation time, `k` is set to
`target_index - template_progress`. The target index for snapshot at
position p in xs is `jphi + p`. The template progress is `jpsi0'`.

So: `k_p = (jphi + p) - jpsi0'` (nat subtraction).

But we don't store jpsi0' in the state. We'd need to compute it.

**Alternative**: compute k at creation time from the template progress, which
we CAN compute: it's the template ψ's progress, which equals jpsi0'.

Or we can store jpsi0' temporarily during the step (it's a local variable).

### Actually, we can recover jpsi0' from the shared run

```
(zs0, ψ_tmpl') = meval n ts db0 ψ_tmpl
jpsi0' = jpsi0_old + length zs0
```

But we removed `jpsi0_old` from the state! We'd need to either:
1. Keep `jpsi0` in the state after all
2. Compute it some other way
3. Use a different scheme for initializing k

**Option: keep jpsi0 in the state for computing offsets.**

Actually, let's reconsider: is jpsi0 needed for anything else? In the current
algorithm, it's used for `zs0_out = drop (jfrz - jpsi0) zs0` and for the
counter offset. If we keep it, we can compute k for new entries.

### Revised state (keeping jpsi0)

```
MFrz p m φ ψ_template jfrz jpsi0 jphi αψs
```

where `αψs : (table × mformula × nat) list`.

The algorithm step:

```
(xs, φ') = meval m ts db φ
db0 = update (p,m) [] db
(zs0, ψ_tmpl') = meval n ts db0 ψ_tmpl
δ = length ts
jpsi0' = jpsi0 + length zs0
-- Create new entries with computed offset
new_entries = mapi (λi α. (α, ψ_tmpl', (jphi + i) - jpsi0')) xs
   where mapi enumerates starting at 0
-- Actually, since jphi + i could be < jpsi0', the offset is 0 (nat sub)
-- Those entries will immediately produce output (they're already past target)

-- Trim old entries below jfrz
αψs1 = drop (jfrz - jphi) (αψs @ new_entries)

-- Advance and extract
(ys, αψs') = freeze_step
  (λα ψ_α. meval n ts (update (p,m) (replicate δ α) db) ψ_α)
  αψs1

jphi' = jphi + length xs
jpsi0' = jpsi0 + length zs0  (already computed)
jfrz' = jfrz + length ys

output = ys
state' = MFrz p m φ' ψ_tmpl' jfrz' jpsi0' jphi' αψs'
```

Hmm, the `mapi` is awkward. Let me reconsider.

### Actually, can we avoid per-entry offsets entirely?

The fundamental question: is there an invariant that ensures `k = 0` for
entries that are about to produce? If yes, we don't need per-entry offsets.

Claim: after one step in the queue, every entry's ψ_α has progress ≥ its
target index.

Consider entry at target index `i`, created at step `j₀` from template at
progress `jpsi0_j₀`. Its initial offset is `i - jpsi0_j₀` (nat sub).

After one step (δ₁ timestamps, pn gets δ₁ copies of α):
- non-pn predicates advance by δ₁ (same as main run)
- pn advances from 0 to δ₁

The new pn progress is δ₁. The overall ψ progress is
`progress(P'(pn↦δ₁)) ψ (j₀+δ₁)`.

Is this ≥ i? Not necessarily. If ψ = `Pred p ts` (only references pn),
then `progress(P'(pn↦δ₁)) ψ (j₀+δ₁) = δ₁`. And i could be up to j₀ - 1.
So we need δ₁ ≥ i, which is not guaranteed.

**The offset CAN be > 0 for multiple steps.** We need per-entry offsets.

### Simplification: don't store offset, compute it

Instead of storing `k` per entry, we can compute it at evaluation time:
- The target index for entry at position p in the queue is `jfrz + p`
- The entry's ψ_α has some progress `prog_α`
- The offset is `(jfrz + p) - prog_α`

But we don't have `prog_α` without evaluating. And after evaluation, the
output length tells us.

Actually, we CAN track the accumulated pn data per entry. If entry was
created at step j₀ and current step is j₁, its pn data is `Σ δ_s` for
s ∈ [j₀..j₁). This equals `j₁ - j₀`.

But this requires tracking creation time per entry, which is another nat.

### The cleanest formulation: just store the offset

Add a `nat` per entry. Initialize it at creation time. Decrease it as the
entry's ψ produces output. This is the simplest approach:

```isabelle
(* Entry: (snapshot, ψ-state, skip-offset) *)
type_synonym frz_entry = "event_data table × mformula × nat"

fun freeze_step where
  "freeze_step eval [] = ([], [])"
| "freeze_step eval ((α, ψ_α, k) # rest) =
    (let (us, ψ_α') = eval α ψ_α
     in if k < length us then
         let y = us ! k;
             (zs, rest') = freeze_step eval rest
         in (y # zs, rest')
       else
         let rest' = map (λ(a, s, ki). let (us', s') = eval a s
                                       in (a, s', ki - length us')) rest
         in ([], (α, ψ_α', k - length us) # rest'))"
```

Note: when entry produces output (k < length us), we take element k and
REMOVE the entry from the queue. When it doesn't (k ≥ length us), we keep
it with reduced offset.

Also note: remaining entries after a non-producing entry are also advanced
(via map) but not checked for output — by monotonicity, they can't produce
either.

### Monotonicity argument

Why later entries can't produce if an earlier one doesn't:

- Entry at position 0 has offset k₀ and output length |us₀|.
  Non-producing means k₀ ≥ |us₀|.
- Entry at position 1 has offset k₁ and output length |us₁|.
- k₁ ≥ k₀ (later entries have higher target index and lower progress)
- |us₁| ≤ |us₀| (later entries have less pn data, hence lower progress,
  hence shorter output)
  Wait — they have LESS pn data but the OUTPUT length is the progress
  increase, which depends on the total pn data not just the increment.
  
  Actually, all entries get the same δ increment of pn data this step.
  The output length is `progress_after - progress_before`. Entries with
  more total pn data may have HIGHER progress_before AND higher
  progress_after. The output length (the difference) could go either way.

Hmm, the monotonicity argument is not straightforward. Let me reconsider.

**Claim**: If entry i doesn't produce (its target index `jfrz + i` is not
reached), then entry i+1 (target `jfrz + i + 1`, less pn data) also doesn't.

Entry i: needs progress_after_i ≥ jfrz + i + 1 (to have at least k_i + 1
tables). But progress_after_i < jfrz + i (since k_i ≥ |us_i|).

Wait, this isn't quite right. Let me formalize:
- Entry i: prog_before_i + |us_i| = prog_after_i. Target = jfrz + i.
  Offset k_i = jfrz + i - prog_before_i (assuming this is the correct
  invariant). Non-producing means k_i ≥ |us_i|, i.e.,
  jfrz + i - prog_before_i ≥ prog_after_i - prog_before_i, i.e.,
  jfrz + i ≥ prog_after_i.

- Entry i+1: prog_before_{i+1} ≤ prog_before_i (less pn data, same non-pn).
  prog_after_{i+1} ≤ prog_after_i (monotonicity of progress in pn data).
  Target = jfrz + i + 1.
  k_{i+1} = jfrz + i + 1 - prog_before_{i+1} ≥ jfrz + i + 1 - prog_before_i > k_i.
  |us_{i+1}| = prog_after_{i+1} - prog_before_{i+1} ≤ prog_after_i - prog_before_{i+1}.
  
  Need: k_{i+1} ≥ |us_{i+1}|, i.e., 
  jfrz + i + 1 - prog_before_{i+1} ≥ prog_after_{i+1} - prog_before_{i+1},
  i.e., jfrz + i + 1 ≥ prog_after_{i+1}.
  
  We have jfrz + i ≥ prog_after_i ≥ prog_after_{i+1}.
  So jfrz + i + 1 > prog_after_{i+1}. ✓

**Monotonicity holds!** If entry i doesn't produce, entry i+1 doesn't either.
The key step is `prog_after_i ≥ prog_after_{i+1}` (monotonicity of progress
in accumulated pn data).

### Summary of incremental design

**State:**
```
MFrz p m φ ψ_tmpl jfrz jpsi0 jphi αψs
```
where `αψs : (event_data table × mformula × nat) list`.

**Helper:**
```isabelle
fun freeze_step where
  "freeze_step eval [] = ([], [])"
| "freeze_step eval ((α, ψ_α, k) # rest) =
    (let (us, ψ_α') = eval α ψ_α
     in if k < length us then
         let y = us ! k;
             (zs, rest') = freeze_step eval rest
         in (y # zs, rest')
       else
         let rest' = map (λ(a, s, ki). let (us', s') = eval a s
                          in (a, s', ki - length us')) rest
         in ([], (α, ψ_α', k - length us) # rest'))"
```

**Step:**
```
(xs, φ') = meval m ts db φ
db0 = update(pn, []) db
(zs0, ψ_tmpl') = meval n ts db0 ψ_tmpl
jpsi0' = jpsi0 + length zs0

-- Create new entries: offset = target_index - jpsi0'
new_entries = map_with_index (λi α. (α, ψ_tmpl', (jphi + i) - jpsi0')) xs

-- Trim entries below jfrz
αψs1 = drop (jfrz - jphi) (αψs @ new_entries)

-- Advance and extract
(ys, αψs') = freeze_step
  (λα ψ_α. meval n ts (update(pn, replicate δ α) db) ψ_α)
  αψs1

jphi' = jphi + length xs
jfrz' = jfrz + length ys
output = ys
```

---

## Comparison: current vs. incremental

| Aspect | Current (from-scratch replay) | Incremental |
|--------|-------------------------------|-------------|
| Per-step work | O(queue × L) where L = jpsij' - jpsi0' | O(queue × δ) |
| Memory | O(queue) tables only | O(queue × size(ψ)) monitor states + nat offsets |
| Output structure | zs0_out @ ys (two parts) | ys only (one part) |
| Shared ψ run | Produces zs0_out output | Only advances template (output discarded) |
| jpsi0 | Stored, used for trimming | Stored, used for offset computation |
| Diagonal | Global counter k | Per-entry offset k |
| Monotonicity | All replays have same output length L | Different output lengths; monotonicity proved above |
| Counter bug | Affects current algorithm | Replaced by per-entry offset (no global counter) |
| Proof complexity | Moderate | Higher (per-entry invariants, offset tracking) |

---

## Proof implications

### Invariant changes

**Per-entry invariant** (replaces `wf_frz_queue`):
```
wf_frz_entry σ j P V p m φ ψ i (α, ψ_α, k) ≡
  frz_qtable σ V m φ i α ∧
  wf_mformula σ j P_α V_α n R ψ_α ψ' ∧
  k = i - progress σ P_α ψ' j
```
where:
- `i` is the target index for this entry
- `P_α(pn) = accumulated_pn_data` and `P_α(q) = P(q)` for q ≠ pn
- `V_α(pn) = λw j. sat σ V w i φ'`

The key proof obligations are:
1. **Entry creation**: new entries satisfy the invariant with k = target - jpsi0'
2. **Entry advancement**: after `meval`, the invariant is preserved with updated k
3. **Output correctness**: when k < |us|, `us ! k` is the correct Frz table
4. **Monotonicity**: if entry i doesn't produce, later entries don't either
5. **Progress equation**: `jfrz' = jfrz + length ys`

### What becomes easier

- No more `zs0_out_rows` proof (no shared output)
- No more counter-offset bug (per-entry offsets are explicit)
- No more V-insensitivity argument for zs0_out (eliminated)

### What becomes harder

- Per-entry ψ well-formedness tracking (each entry has its own P_α)
- Accumulated pn data tracking per entry (depends on creation time)
- The `wf_frz_queue` becomes a richer structure
- Need to handle `(table × mformula × nat) list` in the datatype

---

## Recommendation

1. **If the primary goal is correctness proof completion**: Fix the counter
   bug (change 0 to jfrz - jpsi0) and complete the proof with the current
   algorithm. The performance issue is a concern for the runtime but doesn't
   block the proof.

2. **If performance is critical**: Implement the incremental approach. The
   proof will be more complex but the runtime cost drops from O(queue × L)
   to O(queue × δ) per step.

3. **Hybrid approach**: Complete the current correctness proof first, then
   implement the incremental optimization as a verified refinement.

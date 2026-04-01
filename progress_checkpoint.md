# Progress Checkpoint — Freeze Correctness Proof

**Date**: 2026-03-31
**Status**: Isabelle MCP became unavailable mid-session. Buffer was NOT saved.

## Critical: Unsaved Isabelle Buffer Changes

The Isabelle buffer for Correctness.thy has unsaved modifications. When restarting:

1. **Check if Isabelle saved the buffer** — if the file on disk matches what we wrote, great.
   If not, the edits need to be re-applied from the description below.

2. **What was changed in this session** (on top of previous sessions):

### A) Added `frz_meval` abbreviation and `freeze_meval0_post_exact` lemma

These were accidentally deleted when the discharge_skip block was removed in a prior session.
They were added back between `sat_V_cong` (ends ~line 1506 in buffer) and the new `frz_step_post`.

The `frz_meval` abbreviation:
```isabelle
abbreviation (in maux) "frz_meval n p m j db ψ ≡ (λα. meval j n [] (Mapping.update (p, m) (replicate j α) (Mapping.map_values (λ_ _. []) db)) ψ)"
```

The `freeze_meval0_post_exact` lemma: Proves that `freeze_meval0` produces a valid drop of the queue.
Full text can be found in the on-disk file at lines 1462-1498 (pre-session version).

### B) Rewrote `frz_step_post` 

The old `frz_step_post` used `discharge_skip` and `skip0`/`skip1` parameters.
New version uses `jphi0` parameter and `drop`-based queue manipulation.

**New signature**:
```isabelle
lemma (in maux) frz_step_post:
  assumes state: "wf_frz_state σ j P V p m φ ψ jphi0 alphas"
    and phi_res: "list_all2 ..."
    and phi_mono: "..."
    and d_eq: "d = progress σ P (Formula.Frz p φ ψ) j - jphi0 + length zs0_out"
    and alphas1_eq: "alphas1 = drop d (alphas @ xs)"
    and ef: "freeze_meval0 (frz_meval n p m (j + δ) db ψ_m') alphas1 = (ys, alphas2)"
    and frz_prog: "progress σ P' (Formula.Frz p φ ψ) (j + δ) = ..."
  shows "wf_frz_state σ (j + δ) P' V p m φ ψ (jphi0 + length xs) alphas2"
    and "list_all2 ... (zs0_out @ ys)"
```

**New proof structure**:
- First conclusion (wf_frz_state): Uses `wf_frz_queue_after_drop` to get intermediate queue,
  then `freeze_meval0_post_exact` for the replay. **Has a sorry for `d_bound`** 
  (see issue below).
- Second conclusion (semantic rows): Still `sorry`.

### C) DID NOT YET rewrite `meval_correct` MFrz case

Still at line ~1750+ in buffer, still uses old `MFrz p m φ ψ skip0 αs` pattern.
This is the next thing to do.

## IMPORTANT: Bug in `wf_frz_queue_after_drop` (jfrz > jphi case)

Discovered during this session: the `wf_frz_queue_after_drop` lemma (lines 1320-1381 in buffer)
has a potential issue in its `jfrz > jphi` case.

**The problem**: When `jfrz > jphi`:
- `αs = []`, so `αs @ xs = xs`
- `drop d (αs @ xs) = drop d xs`
- The proof tries to show `drop (?jfrz - ?jphi + d) xs = drop d (αs @ xs)`
  i.e., `drop (?jfrz - ?jphi + d) xs = drop d xs`
- But `?jfrz - ?jphi + d ≠ d` when `?jfrz > ?jphi`

**Potential fix**: The `d` parameter to `wf_frz_queue_after_drop` should represent
the drop amount from the START of `αs @ xs`, not from `jfrz`. This means the result
interval should be `[jfrz + d - (jphi - jfrz)...]` or something. Alternatively,
reformulate the lemma differently.

**Actually**: Looking again, the algorithm does `drop (jfrz - jphi + |zs0_out|) (αs @ xs)`.
When `αs = []` (jfrz > jphi), this drops `(jfrz - jphi + |zs0_out|)` elements from `xs`.
Since `xs` covers `[jphi..<jphi']`, this starts from index `jphi + (jfrz - jphi + |zs0_out|) = jfrz + |zs0_out|`.
So the result interval IS `[jfrz + |zs0_out|..<jphi']`, regardless of case.

**Better fix for `wf_frz_queue_after_drop`**: Change the conclusion to state that
`drop d (αs @ xs)` gives a queue starting at `min jfrz jphi + d`, or better yet,
use a different formulation that directly gives `[jfrz + |zs0_out|..<jphi']`.

**Simplest approach**: Instead of using `wf_frz_queue_after_drop`, prove the queue
property directly in `frz_step_post` by case-splitting on `jfrz ≤ jphi`.

## What needs to be done (in order)

1. **Fix `wf_frz_queue_after_drop` or bypass it** in `frz_step_post`
2. **Close `d_bound` sorry** in `frz_step_post`  
3. **Rewrite `meval_correct` MFrz case** — change pattern to three nats, match new algorithm
4. **Close `frz_prog_eq` sorry** (sorry 2 — progress equation)
5. **Close semantic rows sorry** (sorry 1 — in `frz_step_post`)
6. **Save and verify** in Isabelle

## How to rewrite meval_correct MFrz case

Current (broken, line ~1750 in buffer):
```isabelle
case (MFrz p m φ ψ skip0 αs)
```

New (matching Monitor.thy three-nat design):
```isabelle
case (MFrz p m φ ψ jfrz0 jpsi0_val jphi0 αs)
```

Key changes needed:
- Pattern: `MFrz p m φ ψ jfrz0 jpsi0_val jphi0 αs`
- Extract from wf_mformula.Frz: `jfrz0 = progress σ P (Frz p φ1 ψ1) j`,
  `jpsi0_val = progress σ (P(pn↦0)) ψ1 j`, `wf_frz_state ... jphi0 αs`
- Algorithm: match Monitor.thy lines 1728-1738
  - `zs0_out = drop (jfrz0 - jpsi0_val) zs0`
  - `d = jfrz0 - jphi0 + length zs0_out`
  - `αs1 = drop d (αs @ xs)`
  - `(ys, αs2) = freeze_meval0 ... αs1`
  - New state: `MFrz p m φ_new ψ_new (jfrz0 + |zs0_out| + |ys|) (jpsi0_val + |zs0|) (jphi0 + |xs|) αs2`
- meq: `meval ... (MFrz p m φ ψ jfrz0 jpsi0_val jphi0 αs) = (zs0_out @ ys, MFrz p m φ_new ψ_new ...)`
- Call `frz_step_post` with new signature
- wf_mformula.Frz conclusion needs `jfrz = progress σ P' (Frz ...) (j+δ)` and `jpsi0 = progress σ (P'(pn↦0)) ψ (j+δ)`

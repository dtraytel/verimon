# Agent: Freeze Quantifier Correctness in VeriMon

## Goal

Prove the correctness of the freeze quantifier (`Formula.Frz` / `MFrz`) in VeriMon's MFODL monitor. The implementation lives in the theory `Monitor` of the `MFODL_Monitor_Devel` session; correctness is established in the theory `Correctness`, with auxiliary progress reasoning in `Progress`.

## Background

Refer to `freeze_simplified.md` in the repository root for:
- the final runtime algorithm and state (`MFrz p m φ ψ jfrz jpsi0 jphi αs`),
- the key definitions (`freeze_meval0`, `frz_meval`),
- the proof objects and invariants (`wf_frz_state`, `wf_frz_queue`, `frz_qtable`),
- the completed proof story for the `MFrz` case,
- the index split at `M = max jfrz jpsi0'`,
- the role of V-insensitivity, and
- the arithmetic case split that was needed in the queue proof.

Refer to `isabelle_guidance.md` for general rules on working with Isabelle/HOL.

## Key files

All theory files are under `thys/MFODL_Monitor_Devel/`.

| File | Role | Key locations |
|---|---|---|
| `Monitor.thy` | Algorithm implementation | `freeze_meval0` (line 1679), `meval` MFrz case (line 1733) |
| `Correctness.thy` | Main proof file | `wf_frz_state` (line ~54), `wf_mformula.Frz` (line ~107), `frz_step_post`, MFrz case of `meval_correct` |
| `Progress.thy` | Progress function and preservation | `progress` for Frz (line 81), `sat_prefix_conv_gen` (line 2152), Frz case of `sat_prefix_conv_gen` (line 2212) |
| `Formula.thy` | Syntax and semantics | `Formula.Frz` (line 170), `sat` for `Frz` (line 421), `not_contains_pred_sat` (line 912) |
| `Safety.thy` | Safety predicate | `safe_formula` for Frz (line 730) |
| `Correct_Until.thy` | Shared wf_envs infrastructure | `wf_envs` (line 17), `wf_envs_empty` (line 32), `wf_envs_update` (line 36) |

## Current state

### Monitor.thy — DONE (0 errors)

The MFrz algorithm has been corrected and simplified. Key design choices:

1. **Three explicit progress nats**: `MFrz p m φ ψ jfrz jpsi0 jphi αs`
   - `jfrz`: progress of `Frz p φ ψ` (= number of output tables produced so far)
   - `jpsi0`: progress of ψ under `P(pn↦0)` (= how far the shared ψ-run has advanced)
   - `jphi`: progress of φ (= how many snapshots have been produced so far)
   - `αs`: pending snapshot queue (snapshots awaiting replay)

2. **No more `discharge_skip`**: The old `discharge_skip` function has been removed entirely.
   Queue trimming is now a plain `drop`:
   ```
   αs = drop (jfrz - jphi + length zs0_out) (αs @ xs)
   ```
   This is possible because the three stored progress values make the skip always
   computable as `jfrz - jphi` — no need to thread it through a stateful function.

3. **Corrected algorithm step** (Monitor.thy line 1733):
   ```
   (xs, φ')    = meval m ts db φ              -- xs covers [jphi..jphi')
   db0          = update (p,m) [] db
   (zs0, ψ')   = meval n ts db0 ψ            -- zs0 covers [jpsi0..jpsi0')
   zs0_out      = drop (jfrz - jpsi0) zs0     -- trim: only output [jfrz..jpsi0')
   jpsi0'       = jpsi0 + |zs0|
   αs_trimmed   = drop (jfrz - jphi + |zs0_out|) (αs @ xs)
   (ys, αs')    = freeze_meval0 (...) αs_trimmed
   jphi'        = jphi + |xs|
   jfrz'        = jfrz + |zs0_out| + |ys|
   output       = zs0_out @ ys
   ```

### Correctness.thy — DONE

The `MFrz` proof has been updated to match the simplified runtime.

Completed items:

1. `wf_frz_state` now uses the explicit `jphi` state component.
2. The `wf_mformula.Frz` constructor matches `MFrz p m φ ψ jfrz jpsi0 jphi αs`.
3. The old `discharge_skip`-based reasoning has been removed from the active proof path.
4. `frz_step_post` is proved for the drop-based algorithm.
5. The `MFrz` case of `meval_correct` is fully proved.
6. The semantic output proof is split into `zs0_out_rows` and `ys_rows`, then recombined with `list_all2_appendI`.

## The algorithm bug (critical discovery from earlier sessions)

The original `MFrz` algorithm was **incorrect**. The issue:

1. **`psi_rows` (`zs0`)** from the shared ψ-run covers indices `[jpsi0..jpsi0')` where `jpsi0 = progress(P(pn↦0)) ψ j`.
2. **Frz output** should cover indices `[jfrz..jfrz')` where `jfrz = progress P (Frz p φ ψ) j`.
3. **Index alignment problem**: `jpsi0 ≤ jfrz` in general (not equal!). When `jpsi0 < jfrz`, the first `jfrz - jpsi0` tables in `zs0` are at indices BELOW `jfrz` and should NOT be output. The old algorithm output ALL of `zs0`, which is wrong.

The fix: `zs0_out = drop (jfrz - jpsi0) zs0` trims the shared-run output.

Additionally, the old algorithm only discharged `|zs0|` snapshots from the queue,
missing the gap `jfrz - jphi`. The fix: discharge `(jfrz - jphi) + |zs0_out|`.

## Final proof status

The main freeze facts are now established:

- `frz_prog_eq`:
  ```
  progress σ P' (Formula.Frz p φ1 ψ1) (j+δ) =
    progress σ P (Formula.Frz p φ1 ψ1) j + length zs0_out + length ys
  ```
- semantic output correctness for `(zs0_out @ ys)` on the interval
  `[progress σ P (Formula.Frz p φ1 ψ1) j ..< progress σ P' (Formula.Frz p φ1 ψ1) (j+δ)]`
- post-state queue correctness (`frz_step_post`)
- full re-establishment of the `wf_mformula` invariant in the `MFrz` branch

## Proof strategy that ended up working

1. Split the output interval at
   ```
   M = jfrz + |zs0_out| = max jfrz jpsi0'
   ```
   so `[jfrz..<jfrz') = [jfrz..<M] @ [M..<jfrz')`.
2. Prove `zs0_out_rows` from the shared `psi` run and convert the semantics via `sat_V_cong`.
3. Prove `ys_rows` from replay:
   - `freeze_meval0_diagonal` identifies the diagonal replay output,
   - `queue_αs1_B` supplies the frozen `φ` table at index `M + i`,
   - `IHψ_new` gives the replay rows for `ψ1`,
   - unfolding `Formula.sat` for `Frz` converts those `ψ1` rows into `Frz` rows.
4. Recombine with `list_all2_appendI`.

### Key lemmas to use

- `sat_prefix_conv_gen` (Progress.thy:2152) — V-insensitivity at sat level; critical for both sorries.
- `not_contains_pred_progress` (Progress.thy:582) — progress independence from unused predicates.
- `not_contains_pred_sat` (Formula.thy:912) — sat independence from unused predicates.
- `progress_le_gen`, `progress_mono_gen` — standard progress bounds and monotonicity.
- `wf_envs_empty` (Correct_Until.thy:32) — produces `wf_envs` with δ=0.
- `wf_envs_update` (Correct_Until.thy:36) — extends `wf_envs` with a new predicate binding.
- `freeze_meval0D` (Correctness.thy) — 3 conclusions: queue drop, replay rows, replay stop.

### Key semantic identity

The sat definition for Frz (Formula.thy:421):
```
sat σ V v i (Frz p φ ψ) = sat σ (V((p, nfv φ) ↦ λw j. sat σ V w i φ)) v i ψ
```
Note: the frozen binding uses the *outer* time `i`, not the queried time inside ψ.

## Key semantic facts

1. **`FV(Frz p φ ψ) = FV ψ`**, **`nfv(Frz p φ ψ) = nfv ψ`**
2. **V-insensitivity**: When `P(pn)=0`, for `i < progress σ (P(pn↦0)) ψ j`,
   `sat σ V(pn↦f) v i ψ = sat σ V(pn↦g) v i ψ` for any `f, g`.
   Tool: `sat_prefix_conv_gen` (Progress.thy:2152).
3. **`frz_progress` definition**: `LEAST i. i ≤ j ∧ progress (P(pn ↦ if i < jphi then j else 0)) ψ j ≤ i`
4. **`jpsi0 ≤ jfrz`** always holds.
5. **`jfrz ≤ jphi`** when `jpsi0 ≤ jphi`.
6. **`jfrz = jpsi0`** when `jpsi0 ≥ jphi`.
7. **`M = max jfrz jpsi0'`** is the exact boundary between shared output and replay output.
8. **`jfrz' = jfrz + |zs0_out| + |ys|`** is the final progress equation.

## Dead ends — do not repeat these

- Do not try to reuse the old additive frontier lemma under the new invariant.
- Do not prove `zs0` as if the plain ψ run were already a replay run.
- Do not force the post-state exact interval before the debt interpretation has been propagated through extend, discharge, and replay.
- Do not use `Mapping.empty` for the replay db — use `Mapping.map_values (λ_ _. []) db` (this was the key refactoring that unblocked the proof).
- Do not assume `sat σ V(pn↦⊥) v i ψ = sat σ V(pn↦f) v (i+d) ψ` for d>0 — V-insensitivity does NOT give temporal shifting.
- Do not try to split sorry 1 without first resolving the index alignment problem.
- The `safe_formula` for Frz has NO `not_contains_pred` restriction on ψ, so ψ CAN reference pn — V-insensitivity is necessary, not just `not_contains_pred_sat`.
- Do not use `discharge_skip` — it has been removed. Use plain `drop` instead.

## Nat arithmetic reminder

All frontier/debt arithmetic is over natural numbers, not integers.
- `jfrz - jphi` is nat subtraction (truncates at 0).
- The useful normal form for drop arithmetic is `drop (a - b + c) (xs @ ys)`.
- The formula `length (αs @ xs) = jphi' - jfrz` is valid only in the case `jfrz ≤ jphi`.
- When `jfrz > jphi`, the old queue is empty and the queue proof must work directly from `xs`.

## Workflow

1. **Use the Isabelle MCP tools** for all edits to theory files. Do not edit `.thy` files via other means — states may diverge.
2. **Save files explicitly** after every edit.
3. **Check for errors and timeouts** after each change. Commands returning "running" indicate timeouts.
4. Follow the formalization policy in `isabelle_guidance.md`:
   - Write the right statement first, even with `sorry`.
   - Add intermediate lemmas with `sorry` rather than getting stuck inside a large proof.
   - Replace one `sorry` at a time.
   - Keep the project error-free at every stage.
   - Prefer structured Isar proofs; avoid long unstructured `apply` scripts.
5. The I/R REPL may be unavailable; MCP file/context tools were sufficient for the finished proof.
6. When stuck, isolate the hard part into a named lemma (with `sorry` temporarily), add `text ‹ … ›` notes about the intended strategy, and continue with downstream development.

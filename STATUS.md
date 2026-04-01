# Freeze Status

The freeze quantifier proof is complete.

## Completed work

- Fixed the `Monitor.thy` replay-counter bug in the `MFrz` step.
- Proved the final freeze progress equation:
  ```text
  jfrz' = jfrz + |zs0_out| + |ys|
  ```
- Proved semantic output correctness for the full freeze output interval.
- Proved post-state queue correctness for the drop-based algorithm.
- Finished the `MFrz` case of `meval_correct`.

## Main proof ideas

- Split the output at
  ```text
  M = max jfrz jpsi0'
  ```
- Use `zs0_out` for `[jfrz..<M]`.
- Use replay output `ys` for `[M..<jfrz')`.
- Use `sat_V_cong` to move between the shared `psi` valuation and the frozen
  `Frz` valuation.
- Split queue arithmetic on `jfrz ≤ jphi` vs `jfrz > jphi`.

## Where to read more

- `freeze_simplified.md` — completed proof story
- `AGENT.md` — current working notes for future agents

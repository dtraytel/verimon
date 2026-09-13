# Micro-benchmark of the auxiliary structures

`since_bench.ml` drives the verified Since and Until structures directly (one time point per
iteration, one tuple or one empty table per time point, 200000 time points, time stamps
advancing every 1700 time points as in the P2/P3 logs) and times each operation, next to a
hash-table based imperative sliding window that does the same work. It is the basis of
Section 10 of `EFFICIENCY.md`.

The benchmark needs the internal operations of the kernel, which the generated module hides
behind its signature. To run it, copy the directory somewhere inside the dune project (or
create a temporary one), then:

    python3 unseal.py ../../src/verified.ml      # creates verified_open.ml
    cp dune.template dune
    dune build --profile=release ./since_bench.exe && ./_build/default/.../since_bench.exe

(the directory has no `dune` file of its own so that the ordinary build does not depend on
the generated copy).

`until_dq_bench.ml` does the same for the deque-based Until structure of
`Optimized_Until_Deque.thy` (Section 11 of `EFFICIENCY.md`): it times the pieces of
`add_new_dq` and records which deque entries the new table's pairs touch and how often the
front list of the deque is empty when they do.

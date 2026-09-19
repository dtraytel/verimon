# Micro-benchmark of the heap-resident tables and mappings

`table_bench.ml` and `map_bench.ml` drive the hash set and the hash map of
`thys/MFODL_Monitor_Imp/Table_Imp.thy` against the Containers red-black-tree tables and
mappings of the verified kernel, and against a hand-written OCaml `Hashtbl` that serves as
the ceiling for what the generated code could reach.

The benchmarks need the internal operations of the kernel, which the generated module hides
behind its signature. To run them:

    python3 ../since_bench/unseal.py ../../src/verified.ml   # creates verified_open.ml
    cp dune.template dune
    dune build --profile=release ./table_bench.exe ./map_bench.exe
    ../../_build/default/evaluation/table_bench/table_bench.exe
    ../../_build/default/evaluation/table_bench/map_bench.exe

(the directory has no `dune` file of its own so that the ordinary build does not depend on
the generated copy).

Since the export list of `thys/MFODL_Monitor_Imp/Monitor_Code_Imp.thy` was trimmed to the
monitor over the short tuples (Section 20.38 of `EFFICIENCY.md`), the kernel no longer
contains the hash set over the wide tuples nor the map operations these drivers call
(`table_of_list`, `ht_mem`, `ht_of_list`, `im_lookup`).  To run them, add those constants
back to the `export_code` command, rebuild the session and regenerate `src/verified.ml`; the
drivers themselves are unchanged.

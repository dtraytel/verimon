(lang dune 3.0)
(name verimon)
(version 2.0)

(generate_opam_files true)
(cram enable)

(license "LGPL-2.1-only WITH OCaml-LGPL-linking-exception")
(maintainers "Dmitriy Traytel <traytel@di.ku.dk>")
(source (github dtraytel/verimon))

(package
  (name verimon)
  (synopsis "A verified monitor for metric first-order dynamic logic")
  (description "\
VeriMon checks the compliance of logs with respect to policies specified in metric
first-order dynamic logic (MFODL), with MonPoly's input formats. Its decisions are
made by code generated from an Isabelle/HOL formalization: the formula parser, the
signature reader, the log parser and the monitor are verified.")
  (depends
    (ocaml (>= 4.14))
    (zarith (>= 1.11))
    dune-build-info))

# Web version of VeriMon

The verified monitor compiled to JavaScript with js_of_ocaml: a page with a signature, an MFODL
formula and a log, which checks the inputs as they are edited and shows the verdicts. It runs the
same generated code as the `verimon` executable (`src/verimon_code.ml`), driven as the command line
drives it (`main_js.ml`).

## Additional dependencies

Install the following packages using OPAM, besides the dependencies of `verimon`:

- `js_of_ocaml`
- `js_of_ocaml-lwt`
- `js_of_ocaml-ppx`
- `zarith_stubs_js`

Without them, `dune` skips the web version.

## Build instructions

Run `dune build --profile=release web/verimon_js.zip` from the project root.

This builds a ZIP archive `_build/default/web/verimon_js.zip` which contains all files needed to
run the web version (`index.html`, `verimon.js`, `verimon.css` and two images; the examples are
embedded in `verimon.js`). The archive's contents can be deployed to a web server, for example.

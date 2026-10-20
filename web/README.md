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
run the web version (`index.html`, `help.html`, `verimon.js`, `verimon.css`, the logo, the icons and three images; the examples are
embedded in `verimon.js`). The archive's contents can be deployed to a web server, for example.

## Deployment

The workflow `.github/workflows/pages.yml` builds the web version and deploys it to GitHub Pages
(<https://dtraytel.github.io/verimon/>) on every push to `main` that changes `web/`, `src/` or
`dune-project`, and on demand from the Actions tab. It needs Pages to be enabled with
"GitHub Actions" as its source (Settings → Pages).

## Logo

`verimon-logo.svg` is the VeriMon logo (with the Isabelle/HOL cubes as the dot of the i),
converted from its PDF with its background removed and its view box cropped to the drawing;
its letters' baseline is 6.82 units above its bottom, which `verimon.css` uses to align it with
the text of the headings. `favicon-32.png` and `apple-touch-icon.png` show the logo on two lines (Veri over Mon),
`og-image.png` is the preview image for links to the page.

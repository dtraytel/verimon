# Examples of the web version

Each example is a signature (`.sig`), a formula (`.mfotl`) and a log (`.log`); `main_js.ml` lists
them, in groups, with whether the formula is negated. They are embedded in `verimon.js`.

| Example | Files | Source |
|---|---|---|
| until | `ex` | MonPoly's web version |
| since | `since` | [WhyMon](https://runtime-monitoring.github.io/whymon/) (since) |
| aggregations | `agg` | MonPoly's web version |
| recursive let | `letpast` | MonPoly's web version |
| publish/approve | `rv11` | MonPoly's web version |
| publish/approve/manager | `rv11b` | MonPoly's web version |
| three attempts | `attempts` | WhyMon (three-attempts) |
| failed logins (regular expression) | `logins` | new |
| unprotected access (let) | `locks` | new, after WhyMon's data-race example |
| Nokia: propagation of deletions | `nokia` | WhyMon (nokia-del-2-3), from the Nokia case study of MonPoly |
| GDPR: consent to use data | `gdpr` | [MonitoringFace](https://github.com/MonitoringFace-Benchmark/MonitoringFace) (`Local_GDPR_MonPoly`, policy `consent.mfotl` with free variables, the first 110 entries of its log) |

WhyMon's formulas are written in MonPoly's syntax here. Policies that are implications are
negated to report violations (publish/approve). The Nokia and GDPR formulas instead state the
violations directly. WhyMon's data race policy quantifies over locks in a way that VeriMon cannot
monitor, so `locks` checks a simpler lock discipline: no thread reads or writes while it holds no
lock.

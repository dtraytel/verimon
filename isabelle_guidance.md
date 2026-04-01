# Rules for Working with Isabelle/HOL

## Interaction with Isabelle
- Use the MCP server for jEdit (Isabelle/Q) to edit and check theories.
- Theory files need to be saved explicitly after every edit to commit changes to disk.
- **Do not edit theory files via other means than the Isabelle MCP, otherwise states may diverge.**
- Use MCP to check for errors and timeouts after each change ("running" indicates timeouts).

---

## File and theory structure

- Keep theory files readable and structured with Isabelle sections (e.g. `section`, `subsection`, `text`).
- You can import other theories from the Isabelle distribution as needed. You can find these theories at `$ISABELLE_HOME/src/HOL`.
- If theories become too large, you may split into helper theories.

---

## Formalization policy
**Avoid writing complex Isar proofs in a single step**
For anything but trivial proofs:
1. Write the right statement with `sorry' proof.
2. Write a proof skeleton with `sorry's and comments that describe how to fill the gaps.
3. Fill the gaps iteratively one-by-one, ensure that there are no errors/timeouts after every edit.
4. Restructure the proof as necessary.


### Allowed and encouraged
- Use `sorry` to keep momentum.
- Add intermediate lemmas with `sorry` rather than getting stuck inside a large proof.
- Replace one `sorry` at a time with real proofs, keeping the theory error-free.
- After every change to theorems, proofs or definitions, check that there are **no errors** and **no timeouts**
- Commands for which Isabelle returns "running" indicate timeouts/non-termination
- Use short timeouts for checking the theory file, rough guideline: proof steps that take >1s are problematic

### Preferred pattern
1. Write the *right statement* first (even with `sorry`).
2. Add minimal helper lemmas (possibly also with `sorry`).
3. Prove easy pieces immediately.
4. Chip away at the remaining `sorry`s until the file becomes mostly admit-free.

### Avoid
- Leaving large unstructured blocks of `sorry` without a plan.
- "Proving" by changing the statement to something weaker unless clearly justified.
- Adding large amounts of new material at once, which can make it hard to identify the source of errors or timeouts.


---

## Documentation and change logging

### Document changes in the source
- Use `text ‹ … ›` for prose explanations.
- Add short explanations before major definitions/theorems:
  - why the definition is chosen,
  - intended use,
  - key dependencies (e.g. "uses continuity results from `Complex_Main`").

---

## Proof engineering guidelines (Isabelle/HOL)

### Prefer structured Isar proofs
- Use `proof -` / `qed` blocks for clarity.
- Use `have`/`show` for intermediate steps.
- Avoid unstructured `apply` scripts, which can be brittle and hard to maintain.

### Use definitions for abstraction
- Introduce new definitions for each relevant concept.
- Prove relevant properties of the definitions first, including intro/elim/dest/simp rules where appropriate.
- Mostly avoid unfolding definitions afterwards.

### Structured Statements
- Prefer structured Isar statements over Meta-Quantifiers over object-level quantifiers, e.g.
    - `obtains` > existential quantifier in conclusion
    - `and` > object-level conjunction
    - implicit quantification > `for` > Meta forall > object-level forall

### Structure proofs for maintainability
- Split big theorems into named helper lemmas.
- Use `have`/`show` blocks and local facts to keep context clear.

### Use existing library facts first
Before proving something from scratch:
- browse existing facts
- prefer standard lemmas and simp rules over custom rewrite systems.

### Automation
- Keep simp sets under control
    - Add simp rules deliberately (`simp` attribute) and avoid global simp explosions.
    - Prefer local `simp` calls with `simp add:` / `simp del:` when needed.
- Prefer specialized methods such as `simp` and `blast` over `auto`
- Strike a balance between readability, verboseness, and automation.
- When automation is brittle, switch to structured Isar proofs and add intermediate steps.

### Naming conventions
- Lemmas/theorems: descriptive names
- Use suffixes like `I`, `E`, `D`, `_iff` when conventional.


---

## Quality bar and progression targets

### The project must remain error-free
At every stage, the project should remain error free.

### Progress targets
- Reduce the number of `sorry`s steadily over time.
- Prioritize the main results.
- Don’t leave "easy" holes behind if they block later work.

### If something is hard
Do **not** stall:
- isolate the hard part into one or more lemmas (with `sorry` temporarily),
- add notes in `text ‹ … ›` about intended proof strategy,
- continue with downstream development, then return to discharge the `sorry`s.

## ⚠ Careful Use of Potentially Exploding Tactics (Timeout Discipline)

In general, automation can easily explode.
We must proceed in a way that makes **the failing tactic immediately identifiable**.
In case of timeouts, split automation into multiple steps.
Keep the simp set small and controlled.

---

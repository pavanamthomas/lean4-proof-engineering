# lean4-proof-engineering

A compact Lean 4 + mathlib library of executable proof-engineering cases.
The repository is a Lake project: every listed theorem is compiled, not sketched.

The corpus is organized to show how formal proofs are designed, decomposed,
debugged, reviewed, and maintained. It is not a tutorial dump of isolated snippets.

## Technical scope

The library covers:

- propositional and quantifier reasoning
- structured proof design (`have`, `suffices`, `calc`, `refine`, `obtain`)
- controlled rewriting and simplification
- algebraic automation (`norm_num`, `ring`, `linarith`, `nlinarith`) with explicit
  nonzero, positivity, division, and coercion hypotheses
- induction and recursive definitions
- type-driven mistakes on `Nat`, `Int`, `Rat`, and `Real`
- paired automation-heavy and structured proofs of the same statement
- reviewer repairs whose defective candidates stay in comments only

Intentionally false or ill-typed examples are never compiled.

## Environment

Pinned versions:

| Item | Pin |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.33.0` (`lean-toolchain`) |
| mathlib | tag `v4.33.0`, revision `db584cd6d46c92f209a44c0f1c829460d327499d` (`lakefile.toml`, `lake-manifest.json`) |

These two pins must stay aligned. Updating one without the other will break the
mathlib cache and, typically, the build.

Confirmed locally during construction:

- `lean --version` → Lean 4.33.0
- `lake --version` → Lake 5.0.0 (Lean 4.33.0)
- mathlib cache retrieved with `lake exe cache get` (also run automatically by `lake update`)

## Repository architecture

```
ProofEngineering.lean                 root import
ProofEngineering/
  Foundations.lean                    propositional and quantifier cases
  StructuredProofs.lean               have / suffices / calc / refine
  Rewriting.lean                      rw, simp, simpa, ext, congr
  Algebra.lean                        ring, linarith, fields, positivity
  Induction.lean                      Nat / List induction and recursion
  TypeDrivenReasoning.lean            carriers, coercions, typeclasses
  Robustness.lean                     automation vs structured pairs
  ReviewerCases.lean                  defective comments + repaired theorems
scripts/
  build_and_check.sh                  cache + full build + hole check
  check_no_sorry.sh                   reject sorry, admit, custom axioms
.github/workflows/ci.yml              GitHub Actions build
CASE_INDEX.md                         case matrix
AUDIT_CHECKLIST.md                    review checklist
lakefile.toml                         Lake package and mathlib require
lean-toolchain                        exact Lean version
lake-manifest.json                    locked dependency revisions
```

## Proof-engineering principles

- Prefer the current mathlib statement of a lemma over a restated weaker copy.
- Keep quantifier order, carriers, and hypotheses faithful to the intended claim.
- Use classical reasoning only when the goal is not constructive.
- Prefer `simp only` when the rewrite set should stay reviewable.
- Record nonzero, positivity, and divisibility hypotheses instead of hoping
  automation will invent them.
- Keep defective attempts out of the elaborator: comments or Markdown only.
- Do not treat a short tactic proof as automatically better than a structured
  one, or the reverse. `Robustness.lean` compares both styles on the same types.

Each major case documents mathematical intent, Lean representation, assumptions,
proof architecture, the decisive mechanism, validation, and a common failure mode.

## Build

Install [elan](https://github.com/leanprover/elan), then from the repository root:

```bash
lake exe cache get
lake build
```

`lake exe cache get` downloads prebuilt mathlib artifacts for the pinned
revision. Do not compile all of mathlib from source unless the cache is
unavailable.

The first `lake update` (already recorded in `lake-manifest.json`) clones
mathlib at `v4.33.0` and fetches the cache.

## Verification

```bash
bash scripts/check_no_sorry.sh
bash scripts/build_and_check.sh
```

`check_no_sorry.sh` searches project `.lean` files, excluding `.lake`, for
`sorry`, `admit`, and `axiom` declarations.

CI (`.github/workflows/ci.yml`) runs the same hole check, then
`leanprover/lean-action@v1` with `build: true` and the mathlib cache enabled.
Nanoda is not enabled.

## Case index

`CASE_INDEX.md` lists every case with its area, mathematical concept, Lean
mechanism, primary failure mode, difficulty, and source file. Every row
corresponds to an executable declaration in this repository.

## Limitations

- The corpus is a designed sample, not a formalization of a research paper.
- Several identities already exist in mathlib; they are re-proved here to
  exhibit tactic structure, not to replace the library.
- `import Mathlib.Tactic` is used for tactic availability. Import footprints
  are therefore larger than a minimal mathlib import set.
- Reviewer defective snippets are comments. They are not typechecked; the
  repaired theorems are.
- Lean and mathlib APIs move quickly. The pins above are the supported pair.

## Reproducibility

1. Use the committed `lean-toolchain`.
2. Use the committed `lakefile.toml` (`rev = "v4.33.0"`) and `lake-manifest.json`.
3. Fetch the mathlib cache before building.
4. Run `lake build` and `scripts/check_no_sorry.sh`.
5. Treat CI on `main` and on pull requests as the remote confirmation of those
   same steps.

Do not edit `lake-manifest.json` by hand. Regenerate it with `lake update` only
when intentionally changing a dependency pin.

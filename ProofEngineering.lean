/-
Copyright (c) 2026 lean4-proof-engineering contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProofEngineering.Foundations
import ProofEngineering.StructuredProofs
import ProofEngineering.Rewriting
import ProofEngineering.Algebra
import ProofEngineering.Induction
import ProofEngineering.TypeDrivenReasoning
import ProofEngineering.Robustness
import ProofEngineering.ReviewerCases

/-!
# ProofEngineering

Root module for the executable proof-engineering corpus.

The project is a Lake library depending on mathlib at the revision pinned in
`lakefile.toml` and `lake-manifest.json`. Building this module typechecks every
case in the corpus.

See `CASE_INDEX.md` for the case matrix and `AUDIT_CHECKLIST.md` for the
verification checklist.
-/

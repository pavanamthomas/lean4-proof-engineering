/-
Copyright (c) 2026 lean4-proof-engineering contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Proof robustness

Each pair below proves the same mathematical statement twice: once with a short
automation-heavy script, and once with a structured, auditable script.

Neither style is universally superior.

* Automation is shorter and tracks small definitional changes well.
* Structure is easier to debug, review, semantically audit, refactor, and
  maintain when an intermediate claim becomes the thing that fails.

The comparison is local to these identities.
-/

namespace ProofEngineering.Robustness

/-!
### Case B01 — Binomial square: `ring` versus a structured expansion

**Mathematical intent.** `(a + b)² = a² + 2ab + b²` in a commutative ring.
**Lean representation.** `add_sq_automated` and `add_sq_structured`.
**Assumptions.** `{R : Type*} [CommRing R]`.
**Proof architecture.**
  * Automated: one `ring` call.
  * Structured: reduce the power, distribute, commute, collect `2ab`.
**Decisive Lean mechanism.** Style comparison, not a new algebraic fact.
**Validation.** Both theorems have the same type.
**Common failure mode.** Treating the short proof as self-documenting. If `ring`
fails after a refactor (for example after the carrier loses commutativity), the
structured proof names the exact law that disappeared.

Advantages of the structured proof in this case:
* **Debugging.** A failure occurs at a named `have`, not inside a black-box tactic.
* **Review.** A reviewer can accept distributivity independently of the `2ab` step.
* **Semantic auditing.** The use of `mul_comm` is visible, so a non-commutative
  restatement is obviously unjustified.
* **Refactoring.** If the statement is later specialized to `ℕ`, the same steps
  still make sense; `ring` may still work, but the audit trail is unchanged.
* **Maintenance.** A changed lemma name in the expansion is localized.

The automated proof remains the right tool when the identity is standard and
the carrier's typeclasses are stable.
-/
theorem add_sq_automated {R : Type*} [CommRing R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

theorem add_sq_structured {R : Type*} [CommRing R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  suffices (a + b) * (a + b) = a ^ 2 + 2 * a * b + b ^ 2 by
    rw [pow_two, this]
  have hdist : (a + b) * (a + b) = a * a + a * b + b * a + b * b := by
    calc
      (a + b) * (a + b) = a * (a + b) + b * (a + b) := add_mul a b (a + b)
      _ = a * a + a * b + (b * a + b * b) := by rw [mul_add, mul_add]
      _ = a * a + a * b + b * a + b * b := by simp [add_assoc]
  have hcomm : b * a = a * b := mul_comm b a
  calc
    (a + b) * (a + b) = a * a + a * b + b * a + b * b := hdist
    _ = a * a + a * b + a * b + b * b := by rw [hcomm]
    _ = a ^ 2 + (a * b + a * b) + b ^ 2 := by simp [pow_two, add_assoc]
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [← two_mul, mul_assoc]

/-!
### Case B02 — Quadratic inequality: `nlinarith` versus an explicit expansion

**Mathematical intent.** `2ab ≤ a² + b²` for real `a`, `b`.
**Lean representation.** `two_mul_le_automated` and `two_mul_le_structured`.
**Assumptions.** `a b : ℝ`. No extra positivity hypotheses: the inequality is
unconditional because it is `(a - b)² ≥ 0` rearranged.
**Proof architecture.**
  * Automated: `nlinarith [sq_nonneg (a - b)]`.
  * Structured: name the nonnegative square, expand it by `ring`, then `linarith`.
**Decisive Lean mechanism.** Explicit intermediate equality versus nonlinear arithmetic.
**Validation.** Both theorems have the same type as `Algebra.two_mul_le_sq_add_sq`.
**Common failure mode.** Adding unnecessary hypotheses such as `0 ≤ a` and `0 ≤ b`,
which would change the meaning to a weaker, conditional statement.

Advantages of the structured proof in this case:
* **Debugging.** If the expansion is wrong, `ring` fails on a named `have`.
* **Review.** The rewrite `(a - b)² = a² - 2ab + b²` is a checkable equation.
* **Semantic auditing.** A reader can see that no positivity of `a` or `b` is used.
* **Refactoring.** Replacing `ℝ` by an ordered ring still makes sense; the
  structured proof lists the exact lemmas that must survive.
* **Maintenance.** The nonlinear search is confined to a single `linarith` step
  after the algebra has been made linear.

The automated proof is appropriate when the inequality is a standard consequence
of square-nonnegativity and the surrounding development already depends on
`nlinarith`.
-/
theorem two_mul_le_automated (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem two_mul_le_structured (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have hsq : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have hexp : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by ring
  linarith

end ProofEngineering.Robustness

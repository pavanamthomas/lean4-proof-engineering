/-
Copyright (c) 2026 lean4-proof-engineering contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Algebraic proof engineering

Executable cases for `norm_num`, `ring`, `ring_nf`, `linarith`, `nlinarith`,
together with explicit management of nonzero hypotheses, positivity, field
division, coercions, and carrier types.
-/

namespace ProofEngineering.Algebra

/-!
### Case A01 — `norm_num` on a concrete rational identity

**Mathematical intent.** `3/2 + 1/2 = 2` in `ℚ`.
**Lean representation.** `norm_num_rat_halves : (3 : ℚ) / 2 + 1 / 2 = 2`.
**Assumptions.** The numerals are coerced to `ℚ`, so `/` is field division, not `Nat` division.
**Proof architecture.** `norm_num` evaluates the closed numeric expression.
**Decisive Lean mechanism.** `norm_num`.
**Validation.** The same numerals on `ℕ` would use integer division and the identity would fail.
**Common failure mode.** Writing the identity on `ℕ` (`3 / 2 + 1 / 2 = 2` is `1 + 0 = 2`).
-/
theorem norm_num_rat_halves : (3 : ℚ) / 2 + 1 / 2 = 2 := by
  norm_num

/-!
### Case A02 — `ring` for a cubic binomial identity

**Mathematical intent.** `(a + b)³ = a³ + 3a²b + 3ab² + b³` in a commutative ring.
**Lean representation.** `add_cube_ring` over `{R : Type*} [CommRing R]`.
**Assumptions.** Commutativity is required for the mixed terms to collect as shown.
**Proof architecture.** A single `ring` call. The statement is kept in full generality.
**Decisive Lean mechanism.** `ring`.
**Validation.** This is the standard cubic expansion; coefficients are the ring element `3`.
**Common failure mode.** Stating the identity in a non-commutative ring, where it is false.
-/
theorem add_cube_ring {R : Type*} [CommRing R] (a b : R) :
    (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  ring

/-!
### Case A03 — `ring_nf` for a difference of squares

**Mathematical intent.** `(a + b)(a - b) = a² - b²`.
**Lean representation.** `sq_sub_sq_ring_nf` over `{R : Type*} [CommRing R]`.
**Assumptions.** Commutative ring (so `a * b = b * a` can cancel).
**Proof architecture.** Normalize both sides; no search is required.
**Decisive Lean mechanism.** `ring_nf`.
**Validation.** Holds in every commutative ring, including `ℤ` and `ℝ`.
**Common failure mode.** Stating the identity on a non-commutative ring, or writing
`a - b` on `ℕ` and expecting it to be an additive inverse.
-/
theorem sq_sub_sq_ring_nf {R : Type*} [CommRing R] (a b : R) :
    (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring_nf

/-!
### Case A04 — `linarith` on a linear chain in `ℤ`

**Mathematical intent.** `a ≤ b` and `b < c` imply `a < c`.
**Lean representation.** `lt_of_le_of_lt_linarith` on `ℤ`.
**Assumptions.** The two comparison hypotheses; the carrier is an ordered ring.
**Proof architecture.** `linarith` solves the linear inequality.
**Decisive Lean mechanism.** `linarith`.
**Validation.** Transitivity of `≤` then `<`; the strictness of the second hypothesis
is preserved.
**Common failure mode.** Feeding `linarith` a nonlinear goal such as `a * b ≤ c`.
-/
theorem lt_of_le_of_lt_linarith (a b c : ℤ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  linarith

/-!
### Case A05 — `nlinarith` with an explicit square-nonnegativity fact

**Mathematical intent.** For real `a`, `b`, one has `2ab ≤ a² + b²`.
**Lean representation.** `two_mul_le_sq_add_sq` on `ℝ`.
**Assumptions.** The carrier is `ℝ` (an ordered ring in which squares are nonnegative).
**Proof architecture.** Supply `sq_nonneg (a - b)` to `nlinarith`. Expanding
`(a - b)² = a² - 2ab + b² ≥ 0` is the algebraic content.
**Decisive Lean mechanism.** `nlinarith` with a named nonlinear witness.
**Validation.** Equivalent to `(a - b)² ≥ 0`; no extra positivity hypotheses are added.
**Common failure mode.** Omitting `sq_nonneg` and expecting `nlinarith` to invent it.
-/
theorem two_mul_le_sq_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-!
### Case A06 — Field division with an explicit nonzero hypothesis

**Mathematical intent.** In a field, `a / b * b = a` whenever `b ≠ 0`.
**Lean representation.** `div_mul_cancel_of_ne` over `{K : Type*} [Field K]`.
**Assumptions.** `hb : b ≠ 0`. The statement is false without this hypothesis.
**Proof architecture.** `field_simp` uses `hb` to cancel the denominator.
**Decisive Lean mechanism.** `field_simp` with a tracked nonzero assumption.
**Validation.** The hypothesis is necessary: if `b = 0` then `a / 0 * 0 = 0`, which
equals `a` only when `a = 0`.
**Common failure mode.** Dropping `b ≠ 0`, or stating the identity on `ℕ` where `/`
is truncated division.
-/
theorem div_mul_cancel_of_ne {K : Type*} [Field K] (a b : K) (hb : b ≠ 0) :
    a / b * b = a := by
  field_simp

/-!
### Case A07 — Positivity and a coerced natural numeral

**Mathematical intent.** If `0 < a` and `0 < b` in `ℝ` then `0 < a * b`.
**Lean representation.** `mul_pos_real` proved by `positivity`.
**Assumptions.** Both factors are strictly positive. The product is in `ℝ`, not `ℕ`.
**Proof architecture.** `positivity` reads the two strict inequalities and the
`ℝ` typeclass instance.
**Decisive Lean mechanism.** `positivity`.
**Validation.** The conclusion is strict positivity, matching the hypotheses.
**Common failure mode.** Passing a weak inequality `0 ≤ a` and expecting a strict
conclusion `0 < a * b` when `a` could be zero.
-/
theorem mul_pos_real {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  positivity

end ProofEngineering.Algebra

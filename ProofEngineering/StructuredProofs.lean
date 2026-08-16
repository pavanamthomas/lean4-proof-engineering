/-
Copyright (c) 2026 lean4-proof-engineering contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-!
# Structured proof design

These cases show how `have`, `suffices`, `calc`, helper lemmas, local definitions,
`constructor`, `obtain` / `rcases`, `refine`, `exact`, and `apply` make a proof
auditable. A decomposed proof is not automatically better than a short tactic
block, but it exposes intermediate claims that a reviewer can check independently.
-/

namespace ProofEngineering.StructuredProofs

/-!
### Case S01 — `have` / `suffices` expansion of `(a + b)²`

**Mathematical intent.** In a commutative ring, `(a + b)² = a² + 2ab + b²`.
**Lean representation.** `add_sq_have_suffices` over `{R : Type*} [CommRing R]`.
**Assumptions.** `R` is a commutative ring, so `mul_comm` and `two_mul` are available.
**Proof architecture.** Reduce the power to a product (`suffices`), expand by distributivity
(`have`), commute the middle terms, then reassociate to `2 * a * b`.
**Decisive Lean mechanism.** `suffices`, `have`, and `calc`.
**Validation.** The statement is the standard binomial identity; it is not weakened to a
special case such as `ℕ` or `ℝ`.
**Common failure mode.** Expanding `(a + b) * (a + b)` and then being unable to identify
`a * b + b * a` with `2 * a * b` because commutativity was never used.
-/
theorem add_sq_have_suffices {R : Type*} [CommRing R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  suffices (a + b) * (a + b) = a ^ 2 + 2 * a * b + b ^ 2 by
    rw [pow_two, this]
  have hdist : (a + b) * (a + b) = a * a + a * b + b * a + b * b := by
    calc
      (a + b) * (a + b) = a * (a + b) + b * (a + b) := add_mul a b (a + b)
      _ = a * a + a * b + (b * a + b * b) := by rw [mul_add, mul_add]
      _ = a * a + a * b + b * a + b * b := by
        simp [add_assoc]
  have hcomm : b * a = a * b := mul_comm b a
  calc
    (a + b) * (a + b) = a * a + a * b + b * a + b * b := hdist
    _ = a * a + a * b + a * b + b * b := by rw [hcomm]
    _ = a ^ 2 + (a * b + a * b) + b ^ 2 := by
        simp [pow_two, add_assoc]
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by
        rw [← two_mul, mul_assoc]

/-!
### Case S02 — `calc` for a linear inequality chain

**Mathematical intent.** If `0 ≤ b` then `a ≤ a + b` in `ℤ`.
**Lean representation.** `le_add_of_nonneg_right_int : 0 ≤ b → a ≤ a + b`.
**Assumptions.** `b` is nonnegative. The carrier is `ℤ`, so addition is cancellative and
unbounded below; the same words on `ℕ` are true for a different reason (`Nat.le_add_right`).
**Proof architecture.** Rewrite `a` as `a + 0`, then apply monotonicity of addition.
**Decisive Lean mechanism.** `calc` with named intermediate equalities/inequalities.
**Validation.** Each `calc` step is a standalone lemma application.
**Common failure mode.** Dropping the hypothesis `0 ≤ b` and hoping the inequality is unconditional.
-/
theorem le_add_of_nonneg_right_int (a b : ℤ) (hb : 0 ≤ b) : a ≤ a + b := by
  calc
    a = a + 0 := (add_zero a).symm
    _ ≤ a + b := add_le_add_right hb a

/-!
### Case S03 — `constructor` and `obtain` on a bundled interval

**Mathematical intent.** A closed integer interval `[lo, hi]` with `lo ≤ hi` contains an integer.
**Lean representation.** Structure `ClosedInterval` plus `ClosedInterval.exists_mem`.
**Assumptions.** The structure field `lo_le_hi : lo ≤ hi` is the only numeric hypothesis.
**Proof architecture.** `refine` supplies the witness `lo`; `obtain` is shown on a derived
existential that packages both bounds.
**Decisive Lean mechanism.** `constructor` / structure fields, `refine`, `obtain`.
**Validation.** The witness is `I.lo`, which satisfies both inequalities by `le_rfl` and
`I.lo_le_hi`.
**Common failure mode.** Forgetting the structure invariant and claiming every pair `lo, hi`
forms a nonempty interval.
-/
structure ClosedInterval where
  lo : ℤ
  hi : ℤ
  lo_le_hi : lo ≤ hi

theorem ClosedInterval.exists_mem (I : ClosedInterval) :
    ∃ n : ℤ, I.lo ≤ n ∧ n ≤ I.hi := by
  refine ⟨I.lo, ?_⟩
  constructor
  · exact le_rfl
  · exact I.lo_le_hi

theorem exists_and_left_of_exists_and {P Q : ℤ → Prop}
    (h : ∃ n, P n ∧ Q n) : ∃ n, P n := by
  obtain ⟨n, hp, _hq⟩ := h
  exact ⟨n, hp⟩

/-!
### Case S04 — `refine` / `apply` / `exact` composition

**Mathematical intent.** From `P → Q`, `Q → R`, and `P` conclude `R`.
**Lean representation.** `apply_exact_chain : (P → Q) → (Q → R) → P → R`.
**Assumptions.** None beyond the three hypotheses.
**Proof architecture.** `refine` creates a hole for `R`; `apply` reduces it to `Q`; `exact`
closes the last hole. The same fact is also proved in F01 by direct application; here the
point is the tactic interface used in larger developments.
**Decisive Lean mechanism.** `refine`, `apply`, `exact`.
**Validation.** Semantically identical to implication transitivity; the proof term is explicit.
**Common failure mode.** `apply` on a lemma whose conclusion does not match the current goal
(usually a missing implicit argument or a more specific type).
-/
theorem apply_exact_chain {P Q R : Prop} (hpq : P → Q) (hqr : Q → R) (hp : P) : R := by
  refine hqr ?_
  apply hpq
  exact hp

/-- Local abbreviation used only to name an intermediate predicate in S04's companion. -/
def Implies (P Q : Prop) : Prop := P → Q

theorem apply_local_def {P Q : Prop} (h : Implies P Q) (hp : P) : Q := by
  exact h hp

end ProofEngineering.StructuredProofs

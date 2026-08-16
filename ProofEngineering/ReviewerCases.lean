/-
Copyright (c) 2026 lean4-proof-engineering contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Reviewer cases

Each case records a defective candidate as a *non-executable* comment, then
gives a corrected, executable theorem. Defective snippets never enter the
environment: they are documentation only.

For every case the record is:

1. mathematical intent
2. defective candidate (comment only)
3. exact failure category
4. diagnostic reasoning
5. corrected Lean statement and proof
6. executable verification
7. why the repair preserves semantics
-/

namespace ProofEngineering.ReviewerCases

/-!
### Case C01 — Wrong carrier for subtraction cancellation

1. **Mathematical intent.** Cancelling a subtracted term: `a - b + b = a`.
2. **Defective candidate** (not executable):
     theorem defective_nat_sub (a b : Nat) : a - b + b = a := by
       -- attempted as if Nat were an additive group
       abel
3. **Failure category.** Domain / carrier error. The statement is false on `Nat`.
4. **Diagnostic reasoning.** `Nat` subtraction is truncated: if `b > a` then
   `a - b = 0`, so the left-hand side is `b`, not `a`. Counterexample:
   `a = 1`, `b = 2` yields `0 + 2 = 2 ≠ 1`. `abel` cannot succeed because
   `Nat` is not an additive group.
5. **Correction.** State the identity on `Int`, where subtraction is a group inverse.
6. **Executable verification.** `int_sub_cancel` below compiles.
7. **Semantic preservation.** The intended algebraic law is the group law
   `a + (-b) + b = a`. Moving the carrier from `Nat` to `Int` restores that law
   rather than restricting the quantifiers. The alternative repair
   `b ≤ a → a - b + b = a` on `Nat` is a different, weaker theorem; it is
   recorded in `TypeDrivenReasoning.nat_sub_add_of_le` and is not substituted
   here.
-/
theorem int_sub_cancel (a b : ℤ) : a - b + b = a := by
  abel

/-!
### Case C02 — Missing nonzero hypothesis for field cancellation

1. **Mathematical intent.** Cancel a denominator: `a / b * b = a`.
2. **Defective candidate** (not executable):
     theorem defective_div (a b : Real) : a / b * b = a := by
       field_simp
3. **Failure category.** Missing hypothesis. The statement is false when `b = 0`.
4. **Diagnostic reasoning.** In a field, `a / 0` is defined (typically as `0` in
   Lean's `DivisionRing` convention), so `a / 0 * 0 = 0`, which equals `a` only
   if `a = 0`. `field_simp` refuses to cancel without a proof of `b ≠ 0`.
5. **Correction.** Add the hypothesis `b ≠ 0` and keep the carrier a field.
6. **Executable verification.** `div_mul_cancel_real` below compiles.
7. **Semantic preservation.** The intended identity is the field cancellation
   law, whose standard statement already includes `b ≠ 0`. Adding that
   hypothesis does not change the intended meaning; it makes the meaning
   explicit. Dropping the conclusion to `a / b * b = 0` when `b = 0` would be
   a different theorem.
-/
theorem div_mul_cancel_real (a b : ℝ) (hb : b ≠ 0) : a / b * b = a := by
  field_simp

/-!
### Case C03 — Swapped quantifiers for an unbounded order

1. **Mathematical intent.** `Nat` is unbounded above: every `n` is strictly below
   some `m`.
2. **Defective candidate** (not executable):
     theorem defective_quantifiers : ∃ m : Nat, ∀ n : Nat, n < m := by
       -- no such m exists
       refine ⟨0, ?_⟩
       intro n
       exact ?false
3. **Failure category.** Quantifier-order error. The swapped statement is false.
4. **Diagnostic reasoning.** `∃ m, ∀ n, n < m` asserts a finite upper bound for
   all of `Nat`. Instantiating `n = m` yields `m < m`. The intended statement is
   `∀ n, ∃ m, n < m`, which is witnessed by `m = n + 1`.
5. **Correction.** Restore the quantifier order `∀` then `∃`, and exhibit `n + 1`.
6. **Executable verification.** `nat_unbounded` below compiles.
7. **Semantic preservation.** The repair restores the original meaning
   (unboundedness), rather than proving a weaker true statement such as
   `∃ m, ∃ n, n < m`.
-/
theorem nat_unbounded : ∀ n : ℕ, ∃ m : ℕ, n < m := by
  intro n
  exact ⟨n + 1, Nat.lt_succ_self n⟩

/-!
### Case C04 — Zero-product law stated without a disjunction

1. **Mathematical intent.** In an integral domain, `a * b = 0` implies `a = 0`
   or `b = 0`.
2. **Defective candidate** (not executable):
     theorem defective_zero_product {R : Type*} [CommRing R]
         (a b : R) (h : a * b = 0) : a = 0 := by
       -- missing the disjunct b = 0, and missing NoZeroDivisors
       exact ?unjustified
3. **Failure category.** Strengthened conclusion and missing typeclass.
   `a * b = 0 → a = 0` is false even in `Int` (`a = 2`, `b = 0`).
4. **Diagnostic reasoning.** The zero-product property is a disjunction and
   requires `NoZeroDivisors`. A ring without that typeclass (for example
   `Int × Int`) has zero divisors. Concluding only `a = 0` drops a live case.
5. **Correction.** Assume `[CommRing R] [NoZeroDivisors R]` and conclude
   `a = 0 ∨ b = 0`.
6. **Executable verification.** `mul_eq_zero_iff_or` below compiles.
7. **Semantic preservation.** The repair is the standard zero-product law.
   It does not substitute a weaker claim such as `a * b = 0 → a * b = b * a`,
   nor a stronger one such as `a = 0`.
-/
theorem mul_eq_zero_iff_or {R : Type*} [CommRing R] [NoZeroDivisors R]
    (a b : R) (h : a * b = 0) : a = 0 ∨ b = 0 :=
  mul_eq_zero.mp h

/-!
### Case C05 — Vacuous implication mistaken for a classification

1. **Mathematical intent.** Classify the natural numbers that are `≤ 0`.
   The intended theorem is `n ≤ 0 → n = 0` on `Nat`.
2. **Defective candidate** (not executable as a useful classification):
     theorem defective_vacuous (n : Nat) : n < 0 → n = 37 := by
       intro h
       exact (Nat.not_lt_zero n h).elim
   This compiles if written, but it is vacuous: `n < 0` is never true on `Nat`,
   so any conclusion follows. A reviewer who wanted a classification of
   nonpositive naturals has a true statement with the wrong meaning.
3. **Failure category.** Vacuous truth / wrong predicate. The implication is
   true for the wrong reason.
4. **Diagnostic reasoning.** On `Nat`, `< 0` is uninhabited. Replacing `37` by
   any numeral still yields a theorem. The intended predicate is `≤ 0`,
   which is inhabited by `0`.
5. **Correction.** State `n ≤ 0 → n = 0` and prove it by the standard `Nat` lemma.
6. **Executable verification.** `nat_le_zero_iff_eq_zero` below compiles.
7. **Semantic preservation.** The repair matches the classification intent.
   It does not keep the vacuous implication and merely change `37` to `0`.
-/
theorem nat_le_zero_iff_eq_zero (n : ℕ) : n ≤ 0 → n = 0 :=
  Nat.le_zero.mp

end ProofEngineering.ReviewerCases

/-
Copyright (c) 2026 lean4-proof-engineering contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Type-driven reasoning

Cases involving `ℕ`, `ℤ`, `ℚ`, `ℝ`, coercions, implicit arguments, and typeclass
inference. Several domain mistakes are recorded as comments: they are not
executable, because the corresponding statements are false or ill-typed.
-/

namespace ProofEngineering.TypeDrivenReasoning

/-!
### Case T01 — Cancellation of subtraction on `ℤ`, not on `ℕ`

**Mathematical intent.** In an additive group, `a - b + b = a`.
**Lean representation.** `int_sub_add : ∀ a b : ℤ, a - b + b = a`.
**Assumptions.** The carrier is `ℤ`. The same words on `ℕ` are false when `b > a`,
because `ℕ` subtraction saturates at `0`.
**Proof architecture.** `abel` uses the additive group structure of `ℤ`.
**Decisive Lean mechanism.** Typeclass inference of `AddCommGroup ℤ`.
**Validation.** The statement is the group cancellation law; it is not restated on `ℕ`.
**Common failure mode.** Copying the identity onto `ℕ`. Counterexample: `a = 1`,
`b = 2` gives `(1 - 2) + 2 = 0 + 2 = 2 ≠ 1`.

The defective `ℕ` statement is intentionally not executable:

  theorem nat_sub_add (a b : ℕ) : a - b + b = a
  -- false; Lean will not prove it, and the statement must not be weakened
  -- to `b ≤ a → a - b + b = a` unless that restricted claim is the intent.
-/
theorem int_sub_add (a b : ℤ) : a - b + b = a := by
  abel

theorem nat_sub_add_of_le (a b : ℕ) (h : b ≤ a) : a - b + b = a :=
  Nat.sub_add_cancel h

/-!
### Case T02 — Coercion of a `ℕ` sum into `ℝ`

**Mathematical intent.** The coercion `ℕ → ℝ` is a monoid homomorphism:
`(n : ℝ) + (m : ℝ) = ((n + m : ℕ) : ℝ)`.
**Lean representation.** `nat_cast_add_real`.
**Assumptions.** The left-hand addition is `ℝ`-addition; the inner `n + m` is `ℕ`-addition.
**Proof architecture.** Apply the canonical `Nat.cast_add` lemma.
**Decisive Lean mechanism.** Coercion / `NatCast` typeclass.
**Validation.** The two sides have type `ℝ`. Swapping the coercions silently changes
which `+` is used.
**Common failure mode.** Writing `(n + m : ℝ)` and expecting Lean to add in `ℕ` first
without an explicit inner annotation when other coercions are in play.
-/
theorem nat_cast_add_real (n m : ℕ) : (n : ℝ) + (m : ℝ) = ((n + m : ℕ) : ℝ) :=
  (Nat.cast_add (R := ℝ) n m).symm

/-!
### Case T03 — Field inversion on `ℚ` with a nonzero hypothesis

**Mathematical intent.** Every nonzero rational has a multiplicative inverse:
`q ≠ 0 → q⁻¹ * q = 1`.
**Lean representation.** `rat_inv_mul` on `ℚ`.
**Assumptions.** `hq : q ≠ 0`. `ℚ` is a field, so inversion is defined on all of `ℚ`
and the identity requires the nonzero hypothesis.
**Proof architecture.** `field_simp` consumes `hq`.
**Decisive Lean mechanism.** `Inv` / `Field` typeclass on `ℚ`.
**Validation.** The statement is the left inverse law, not a claim that inversion
is a total function satisfying `0⁻¹ * 0 = 1`.
**Common failure mode.** The same identity on `ℕ` is meaningless: inversion is not
an operation on `ℕ`. On `ℝ` the identity is true but uses a different instance.
-/
theorem rat_inv_mul (q : ℚ) (hq : q ≠ 0) : q⁻¹ * q = 1 := by
  field_simp

/-!
### Case T04 — Implicit arguments and typeclass inference

**Mathematical intent.** In any additive commutative monoid, `a + b = b + a`.
**Lean representation.** `add_comm_of_monoid {M : Type*} [AddCommMonoid M] (a b : M)`.
**Assumptions.** The typeclass `AddCommMonoid M` is inferred; no explicit ring
structure is required.
**Proof architecture.** `exact add_comm a b` lets Lean fill the instance.
**Decisive Lean mechanism.** Implicit instance arguments.
**Validation.** Instantiates correctly on `ℕ`, `ℤ`, `ℚ`, and `ℝ` without restating
the theorem at each type.
**Common failure mode.** Annotating a type that has `Add` but not `AddCommMonoid`
(for example a non-commutative monoid) and wondering why `add_comm` cannot be found.

A related domain failure, kept non-executable:

  -- (n : Nat) / (m : Nat) * (m : Nat) = n
  -- false: 3 / 2 * 2 = 1 * 2 = 2 ≠ 3.
  -- The intended field identity requires a field carrier and `m ≠ 0`.
  -- On Nat the correct repair is the divisibility hypothesis below, not a
  -- nonzero hypothesis: `0 ∣ n` already forces `n = 0`.
-/
theorem add_comm_of_monoid {M : Type*} [AddCommMonoid M] (a b : M) : a + b = b + a :=
  add_comm a b

theorem nat_div_mul_of_dvd (n m : ℕ) (h : m ∣ n) : n / m * m = n :=
  Nat.div_mul_cancel h

/-!
### Case T05 — Strict inequality is not preserved by `ℕ` subtraction

**Mathematical intent.** On `ℤ`, `a < b` implies `a - c < b - c`. On `ℕ` the
translated statement `a < b → a - c < b - c` is false (take `a = 1`, `b = 2`,
`c = 3`: both sides become `0 < 0`).
**Lean representation.** `int_sub_lt_sub` on `ℤ`.
**Assumptions.** Ordered additive group structure of `ℤ`.
**Proof architecture.** `linarith` after rewriting subtraction as addition of an inverse.
**Decisive Lean mechanism.** Domain choice: `ℤ` rather than `ℕ`.
**Validation.** The statement uses a cancellative ordered group. The `ℕ` analogue
is documented, not executed.
**Common failure mode.** Translating a group lemma onto `ℕ` without the side
condition `c ≤ a ∧ c ≤ b`.
-/
theorem int_sub_lt_sub (a b c : ℤ) (h : a < b) : a - c < b - c := by
  linarith

end ProofEngineering.TypeDrivenReasoning

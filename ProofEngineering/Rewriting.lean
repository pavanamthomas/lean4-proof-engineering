/-
Copyright (c) 2026 lean4-proof-engineering contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-!
# Rewriting and simplification

Cases for `rw`, `simp`, `simp only`, `simpa`, congruence, extensionality, and
normalization. Unrestricted `simp` is convenient; `simp only` is preferable when
the rewrite set must stay auditable.
-/

namespace ProofEngineering.Rewriting

/-!
### Case R01 — Directed rewriting of an additive identity

**Mathematical intent.** `a + b + c = a + (c + b)` on `ℕ`.
**Lean representation.** `rw_reassoc_comm : a + b + c = a + (c + b)`.
**Assumptions.** The left-hand side is left-associated (`(a + b) + c`).
**Proof architecture.** Reassociate, then commute the inner pair.
**Decisive Lean mechanism.** `rw` with an explicit lemma list.
**Validation.** Only `Nat.add_assoc` and `Nat.add_comm` are used; no extra lemmas fire.
**Common failure mode.** Rewriting `add_comm` at the wrong occurrence and looping or
changing the wrong pair.
-/
theorem rw_reassoc_comm (a b c : ℕ) : a + b + c = a + (c + b) := by
  rw [Nat.add_assoc, Nat.add_comm b]

/-!
### Case R02 — Controlled simplification versus unrestricted `simp`

**Mathematical intent.** A local wrapper `shift n := n + 0` should satisfy
`shift (n + m) = shift n + m` without unfolding unrelated `simp` lemmas.
**Lean representation.** `shift_add` proved with `simp only`.
**Assumptions.** `shift` is a definition in this file, not a typeclass method.
**Proof architecture.** Unfold `shift` and cancel `+ 0`. A comment records why
`simp` without a restriction is less desirable here: it can rewrite through any
`@[simp]` lemma in scope, including lemmas a reviewer did not intend to authorize.
**Decisive Lean mechanism.** `simp only`.
**Validation.** The simp set is `{shift, Nat.add_zero}`.
**Common failure mode.** A later `@[simp]` lemma changes the normal form and a
previously green `simp` proof silently proves a different-looking goal.
-/
def shift (n : ℕ) : ℕ := n + 0

theorem shift_add (n m : ℕ) : shift (n + m) = shift n + m := by
  simp only [shift, Nat.add_zero]

/-!
### Case R03 — `simpa` closing a rewritten hypothesis

**Mathematical intent.** From `a + 0 = b` conclude `a = b`.
**Lean representation.** `eq_of_add_zero_eq : a + 0 = b → a = b`.
**Assumptions.** `a, b : ℕ`.
**Proof architecture.** `simpa` simplifies the hypothesis with `Nat.add_zero` and
closes the goal in one step.
**Decisive Lean mechanism.** `simpa using`.
**Validation.** Equivalent to `rw [Nat.add_zero] at h; exact h`, but packed.
**Common failure mode.** `simpa` with a large default simp set, hiding the rewrite
that actually mattered.
-/
theorem eq_of_add_zero_eq {a b : ℕ} (h : a + 0 = b) : a = b := by
  simpa using h

/-!
### Case R04 — Function extensionality

**Mathematical intent.** The functions `n ↦ n + 1` and `n ↦ 1 + n` are equal.
**Lean representation.** `succ_eq_one_add_fun : (fun n : ℕ => n + 1) = fun n => 1 + n`.
**Assumptions.** Function equality is pointwise (`funext`).
**Proof architecture.** `ext n` reduces the goal to a pointwise identity, then commute.
**Decisive Lean mechanism.** `ext` / extensionality.
**Validation.** The statement is equality of functions, not a pointwise `∀` theorem
(though the two are equivalent by `funext`).
**Common failure mode.** Proving `∀ n, f n = g n` and stopping, when the goal is `f = g`.
-/
theorem succ_eq_one_add_fun : (fun n : ℕ => n + 1) = fun n => 1 + n := by
  ext n
  exact Nat.add_comm n 1

/-!
### Case R05 — Congruence of a binary operation

**Mathematical intent.** If `a = c` and `b = d` then `a * b = c * d`.
**Lean representation.** `mul_congr_of_eq : a = c → b = d → a * b = c * d`.
**Assumptions.** The equalities are propositional; no algebraic law is required beyond
the function `Nat.mul`.
**Proof architecture.** `congr` lifts the two equalities through the binary operation.
**Decisive Lean mechanism.** `congr`.
**Validation.** This is the congruence rule for `HMul.hMul`, not a ring identity.
**Common failure mode.** Using `congr` when the function itself is not definitionally
the same on both sides (for example after an unexpected coercion).
-/
theorem mul_congr_of_eq {a b c d : ℕ} (h₁ : a = c) (h₂ : b = d) : a * b = c * d := by
  congr

/-!
### Case R06 — Normalization before comparison

**Mathematical intent.** Two polynomially written expressions in a commutative ring
are equal after normalization: `(a + b) * (a + b) = a * a + 2 * a * b + b * b`.
**Lean representation.** `mul_self_normalized` over `[CommRing R]`.
**Assumptions.** Commutative ring structure.
**Proof architecture.** `ring_nf` puts both sides in a common normal form.
**Decisive Lean mechanism.** `ring_nf` (normalization, not a search).
**Validation.** Same identity as S01, proved by normalization rather than by a
hand-built `calc` chain, for comparison of styles.
**Common failure mode.** Expecting `ring_nf` to handle division or inequalities.
-/
theorem mul_self_normalized {R : Type*} [CommRing R] (a b : R) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  ring_nf

end ProofEngineering.Rewriting

/-
Copyright (c) 2026 lean4-proof-engineering contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Induction and recursion

Natural-number induction, list induction, a recursive definition, and a
dependency-aware decomposition in which a helper lemma is proved first and
then reused.
-/

namespace ProofEngineering.Induction

open Finset

/-!
### Case I01 — Natural-number induction for Gauss's closed form

**Mathematical intent.** `2 * ∑_{i = 0}^{n} i = n * (n + 1)`.
**Lean representation.** `two_mul_sum_range : 2 * ∑ i ∈ range (n + 1), i = n * (n + 1)`.
**Assumptions.** The sum is over `Finset.range (n + 1)`, i.e. `{0, …, n}`. Working with
the doubled sum avoids `ℕ`-division.
**Proof architecture.** Induction on `n`. The successor step uses `sum_range_succ`
and then a ring identity.
**Decisive Lean mechanism.** `induction` on `ℕ` plus `Finset.sum_range_succ`.
**Validation.** The statement matches Gauss's formula without weakening the range
or replacing `ℕ` by `ℚ`.
**Common failure mode.** Writing `∑ i ∈ range n, i = n * (n + 1) / 2` and losing
the last term, or using truncated `ℕ` division without proving evenness.
-/
theorem two_mul_sum_range (n : ℕ) :
    2 * ∑ i ∈ range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

/-!
### Case I02 — List induction for reverse-append

**Mathematical intent.** `(l₁ ++ l₂).reverse = l₂.reverse ++ l₁.reverse`.
**Lean representation.** `reverse_append_ind` over `{α : Type*}`.
**Assumptions.** None; the identity is purely structural.
**Proof architecture.** Induction on `l₁`. The successor step uses `reverse_cons`
and the inductive hypothesis, then reassociates `++`.
**Decisive Lean mechanism.** `induction` on `List`.
**Validation.** The statement is the standard interaction of `reverse` and `append`.
The proof is written out rather than deferred to the `@[simp]` library lemma, so
the inductive step remains visible.
**Common failure mode.** Inducting on `l₂` instead of `l₁`, which does not follow
the recursive structure of `++`.
-/
theorem reverse_append_ind {α : Type*} (l₁ l₂ : List α) :
    (l₁ ++ l₂).reverse = l₂.reverse ++ l₁.reverse := by
  induction l₁ with
  | nil =>
    simp
  | cons x xs ih =>
    calc
      (x :: xs ++ l₂).reverse = (xs ++ l₂).reverse ++ [x] := by
        simp [List.reverse_cons]
      _ = (l₂.reverse ++ xs.reverse) ++ [x] := by rw [ih]
      _ = l₂.reverse ++ (xs.reverse ++ [x]) := by rw [List.append_assoc]
      _ = l₂.reverse ++ (x :: xs).reverse := by simp [List.reverse_cons]

/-!
### Case I03 — Recursive factorial and a positivity helper

**Mathematical intent.** A recursively defined factorial is strictly positive.
**Lean representation.** `myFact` with `myFact_pos : ∀ n, 0 < myFact n`.
**Assumptions.** The recursive equations are the definition; no external `Nat.factorial`
is used for the definition itself.
**Proof architecture.** Recursion on `n` for the definition; induction on `n` for
positivity, using `Nat.mul_pos` in the successor step.
**Decisive Lean mechanism.** Pattern-matching definition plus induction that follows
the same dependency.
**Validation.** `myFact 0 = 1` and `myFact (n+1) = (n+1) * myFact n`; positivity is
strict (`0 < _`), not merely `≠ 0`.
**Common failure mode.** Proving `myFact n ≠ 0` by `norm_num` on a few values and
treating that as a universal proof.
-/
def myFact : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * myFact n

theorem myFact_pos (n : ℕ) : 0 < myFact n := by
  induction n with
  | zero =>
    simp [myFact]
  | succ n ih =>
    simp only [myFact]
    exact Nat.mul_pos (Nat.succ_pos n) ih

/-!
### Case I04 — Helper lemma reused in a second induction

**Mathematical intent.** A recursively counted occurrence function is invariant
under list reversal: `countEq x l.reverse = countEq x l`.
**Lean representation.** `countEq`, helper `countEq_append`, then `countEq_reverse`.
**Assumptions.** `DecidableEq α` so the branch `y = x` is decidable.
**Proof architecture.** First prove additivity over `++` by induction on the left
list. Then induct on `l` for reversal, reducing the `cons` case to the helper
plus `countEq_singleton`.
**Decisive Lean mechanism.** Dependency-aware decomposition: the append lemma is
an independently auditable helper, not an inlined subproof.
**Validation.** The helper is used exactly where `reverse (x :: xs)` produces an
`append`; the reversal theorem does not re-prove additivity.
**Common failure mode.** Attempting the reverse proof first and then discovering
that the `append` case is the missing lemma.
-/
def countEq [DecidableEq α] (x : α) : List α → ℕ
  | [] => 0
  | y :: ys => (if y = x then 1 else 0) + countEq x ys

theorem countEq_append [DecidableEq α] (x : α) (l₁ l₂ : List α) :
    countEq x (l₁ ++ l₂) = countEq x l₁ + countEq x l₂ := by
  induction l₁ with
  | nil =>
    simp [countEq]
  | cons y ys ih =>
    simp [countEq, ih, Nat.add_assoc]

theorem countEq_singleton [DecidableEq α] (x y : α) :
    countEq x [y] = if y = x then 1 else 0 := by
  simp [countEq]

theorem countEq_reverse [DecidableEq α] (x : α) (l : List α) :
    countEq x l.reverse = countEq x l := by
  induction l with
  | nil =>
    simp [countEq]
  | cons y ys ih =>
    have hrev : (y :: ys).reverse = ys.reverse ++ [y] := List.reverse_cons
    rw [hrev, countEq_append, countEq_singleton, ih]
    simp [countEq, Nat.add_comm]

end ProofEngineering.Induction

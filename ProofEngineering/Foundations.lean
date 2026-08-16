/-
Copyright (c) 2026 lean4-proof-engineering contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-!
# Foundations

Executable cases for the propositional and quantifier layer of proof engineering:
implication, conjunction, disjunction, negation, iff, universal and existential
quantification, equality, and classical reasoning used only where it is required.

Each case records mathematical intent, the Lean representation, assumptions,
proof architecture, the decisive mechanism, validation, and a common failure mode.
-/

namespace ProofEngineering.Foundations

/-!
### Case F01 — Implication transitivity

**Mathematical intent.** Implication is transitive: from `P → Q` and `Q → R` conclude `P → R`.
**Lean representation.** `implication_trans : (P → Q) → (Q → R) → P → R`.
**Assumptions.** None beyond the two given implications. `P`, `Q`, `R` are propositions.
**Proof architecture.** Introduce the antecedent, apply the first implication, then the second.
**Decisive Lean mechanism.** `intro` and `exact` with function application.
**Validation.** Compiles as a purely constructive implication chain.
**Common failure mode.** Reversing the implication direction (`R → Q` instead of `Q → R`).
-/
theorem implication_trans {P Q R : Prop} (hpq : P → Q) (hqr : Q → R) : P → R := by
  intro hp
  exact hqr (hpq hp)

/-!
### Case F02 — Conjunction commutativity

**Mathematical intent.** `P ∧ Q` is equivalent to `Q ∧ P`.
**Lean representation.** `and_comm_prop : P ∧ Q ↔ Q ∧ P`.
**Assumptions.** None.
**Proof architecture.** Prove each direction by pairing the two conjuncts in reverse order.
**Decisive Lean mechanism.** `constructor` and anonymous constructor `⟨_, _⟩`.
**Validation.** Both directions are constructive and definitionally use the pair projections.
**Common failure mode.** Treating `∧` as a single hypothesis and forgetting to split it.
-/
theorem and_comm_prop {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h
    exact ⟨h.right, h.left⟩
  · intro h
    exact ⟨h.right, h.left⟩

/-!
### Case F03 — Disjunction commutativity

**Mathematical intent.** `P ∨ Q` is equivalent to `Q ∨ P`.
**Lean representation.** `or_comm_prop : P ∨ Q ↔ Q ∨ P`.
**Assumptions.** None.
**Proof architecture.** Case-split each disjunction and re-inject into the opposite constructor.
**Decisive Lean mechanism.** `cases` / `Or.inl` / `Or.inr`.
**Validation.** Both directions compile by exhaustive case analysis.
**Common failure mode.** Using `Or.inl` where `Or.inr` is required (or the reverse).
-/
theorem or_comm_prop {P Q : Prop} : P ∨ Q ↔ Q ∨ P := by
  constructor
  · intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  · intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp

/-!
### Case F04 — Modus tollens

**Mathematical intent.** From `P → Q` and `¬Q` conclude `¬P`.
**Lean representation.** `modus_tollens : (P → Q) → ¬Q → ¬P`.
**Assumptions.** The implication and the negated conclusion.
**Proof architecture.** Unfold `¬P` as `P → False`, assume `P`, derive `Q`, then contradict `¬Q`.
**Decisive Lean mechanism.** Negation as implication into `False`.
**Validation.** Constructive; no classical axiom is used.
**Common failure mode.** Attempting to conclude `¬Q` from `¬P` (the converse is not valid).
-/
theorem modus_tollens {P Q : Prop} (hpq : P → Q) (hnq : ¬Q) : ¬P := by
  intro hp
  exact hnq (hpq hp)

/-!
### Case F05 — Biconditional as a pair of implications

**Mathematical intent.** `P ↔ Q` means both `P → Q` and `Q → P`.
**Lean representation.** `iff_iff_implications : (P ↔ Q) ↔ (P → Q) ∧ (Q → P)`.
**Assumptions.** None.
**Proof architecture.** Unpack `Iff` into its two directions and reassemble.
**Decisive Lean mechanism.** `Iff.mp` / `Iff.mpr` and `And`.
**Validation.** This is the definitional interface of `Iff` in Lean.
**Common failure mode.** Proving only one direction and treating it as an equivalence.
-/
theorem iff_iff_implications {P Q : Prop} : (P ↔ Q) ↔ (P → Q) ∧ (Q → P) := by
  constructor
  · intro h
    exact ⟨h.mp, h.mpr⟩
  · intro h
    exact ⟨h.left, h.right⟩

/-!
### Case F06 — Universal quantification over a numeric identity

**Mathematical intent.** For every natural number `n`, `n + 0 = n`.
**Lean representation.** `forall_add_zero : ∀ n : ℕ, n + 0 = n`.
**Assumptions.** `n` ranges over `ℕ` (not `ℤ`); the right identity is the `Nat` operation.
**Proof architecture.** Introduce the bound variable and apply the canonical `Nat` lemma.
**Decisive Lean mechanism.** `intro` for `∀`, then `exact` of a library identity.
**Validation.** The statement is the standard right-identity law on `ℕ`.
**Common failure mode.** Stating the identity on a type whose `+` is not known to be a monoid.
-/
theorem forall_add_zero : ∀ n : ℕ, n + 0 = n := by
  intro n
  exact Nat.add_zero n

/-!
### Case F07 — Existential witness for an unbounded order

**Mathematical intent.** Every natural number is strictly below some larger natural number.
**Lean representation.** `exists_nat_gt : ∀ n : ℕ, ∃ m : ℕ, n < m`.
**Assumptions.** The order is the standard order on `ℕ`.
**Proof architecture.** For each `n`, exhibit the witness `n + 1` and prove `n < n + 1`.
**Decisive Lean mechanism.** Existential introduction via `⟨witness, proof⟩`.
**Validation.** `Nat.lt_succ_self` is the exact comparison required.
**Common failure mode.** Swapping quantifiers to `∃ m, ∀ n, n < m`, which is false on `ℕ`.
-/
theorem exists_nat_gt (n : ℕ) : ∃ m : ℕ, n < m :=
  ⟨n + 1, Nat.lt_succ_self n⟩

/-!
### Case F08 — Equality substitution in an operation

**Mathematical intent.** Equality is a congruence for addition: `a = b` implies `a + c = b + c`.
**Lean representation.** `eq_subst_add : a = b → a + c = b + c` on `ℕ`.
**Assumptions.** `a`, `b`, `c : ℕ`. The hypothesis is propositional equality, not inequality.
**Proof architecture.** Rewrite the left summand by the given equality.
**Decisive Lean mechanism.** `rw` along `Eq`.
**Validation.** Specializes the substitutivity of equality to `Nat.add`.
**Common failure mode.** Rewriting in the wrong occurrence, or treating `=` as definitional `≡`.
-/
theorem eq_subst_add {a b c : ℕ} (h : a = b) : a + c = b + c := by
  rw [h]

/-!
### Case F09 — Double-negation elimination (classical)

**Mathematical intent.** Classically, `¬¬P` is equivalent to `P`.
**Lean representation.** `not_not_iff : ¬¬P ↔ P`.
**Assumptions.** Uses Lean's built-in classical choice (`Classical.em`). No custom axiom is declared.
**Proof architecture.** One direction is constructive (`P → ¬¬P`). The converse case-splits on `P`.
**Decisive Lean mechanism.** `Classical.em` / excluded middle; classical reasoning is required here.
**Validation.** The forward direction `¬¬P → P` is not constructive; the proof records that dependency.
**Common failure mode.** Using excluded middle for a goal that has a constructive proof.
-/
theorem not_not_iff (P : Prop) : ¬¬P ↔ P := by
  constructor
  · intro hnn
    cases Classical.em P with
    | inl hp => exact hp
    | inr hn => exact (hnn hn).elim
  · intro hp hn
    exact hn hp

end ProofEngineering.Foundations

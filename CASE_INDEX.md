# Case index

Every row is an executable case in this repository. Companion lemmas that exist
only to support a listed case are named in the notes column, not given a second
case id.

Difficulty:

- **foundational** — propositional, quantifier, or single-lemma rewriting
- **intermediate** — structured algebra, induction, or a tracked hypothesis
- **advanced** — fields, nonlinear arithmetic, recursion, typeclass or review work

| Case | Area | Mathematical concept | Lean mechanism | Primary failure mode | Difficulty | Source file |
| --- | --- | --- | --- | --- | --- | --- |
| F01 | Foundations | Implication transitivity | `intro`, `exact` | Reversed implication | foundational | `ProofEngineering/Foundations.lean` |
| F02 | Foundations | Conjunction commutativity | `constructor`, `⟨_, _⟩` | Forgetting to split `And` | foundational | `ProofEngineering/Foundations.lean` |
| F03 | Foundations | Disjunction commutativity | `cases`, `Or.inl` / `Or.inr` | Wrong disjunct constructor | foundational | `ProofEngineering/Foundations.lean` |
| F04 | Foundations | Modus tollens | Negation as `→ False` | Concluding the converse | foundational | `ProofEngineering/Foundations.lean` |
| F05 | Foundations | Biconditional as two implications | `Iff.mp` / `Iff.mpr` | Proving only one direction | foundational | `ProofEngineering/Foundations.lean` |
| F06 | Foundations | Universal identity `n + 0 = n` | `∀` introduction | Wrong monoid / carrier | foundational | `ProofEngineering/Foundations.lean` |
| F07 | Foundations | Unboundedness of `Nat` | Existential witness | Swapped `∃` / `∀` | foundational | `ProofEngineering/Foundations.lean` |
| F08 | Foundations | Equality congruence for `+` | `rw` | Rewriting the wrong occurrence | foundational | `ProofEngineering/Foundations.lean` |
| F09 | Foundations | Double-negation elimination | `Classical.em` | Using classical reasoning unnecessarily | intermediate | `ProofEngineering/Foundations.lean` |
| S01 | Structured proofs | `(a + b)²` expansion | `have`, `suffices`, `calc` | Missing `mul_comm` for `2ab` | intermediate | `ProofEngineering/StructuredProofs.lean` |
| S02 | Structured proofs | `a ≤ a + b` from `0 ≤ b` | `calc` | Dropping nonnegativity | intermediate | `ProofEngineering/StructuredProofs.lean` |
| S03 | Structured proofs | Nonempty closed interval | `refine`, `constructor`, `obtain` | Ignoring `lo ≤ hi` | intermediate | `ProofEngineering/StructuredProofs.lean` |
| S04 | Structured proofs | Implication composition | `refine`, `apply`, `exact` | `apply` on a non-matching conclusion | foundational | `ProofEngineering/StructuredProofs.lean` |
| R01 | Rewriting | Additive reassociation | `rw` | Rewriting the wrong `+` pair | foundational | `ProofEngineering/Rewriting.lean` |
| R02 | Rewriting | Wrapper identity for `shift` | `simp only` | Unrestricted `simp` changing normal form | intermediate | `ProofEngineering/Rewriting.lean` |
| R03 | Rewriting | Cancel `+ 0` in a hypothesis | `simpa` | Hidden default simp set | intermediate | `ProofEngineering/Rewriting.lean` |
| R04 | Rewriting | Function equality `n ↦ n+1` | `ext` | Stopping at a pointwise `∀` | intermediate | `ProofEngineering/Rewriting.lean` |
| R05 | Rewriting | Congruence of multiplication | `congr` | Congruence after an unexpected coercion | advanced | `ProofEngineering/Rewriting.lean` |
| R06 | Rewriting | Normalized self-product | `ring_nf` | Using normalization on inequalities | advanced | `ProofEngineering/Rewriting.lean` |
| A01 | Algebra | `3/2 + 1/2 = 2` in `Rat` | `norm_num` | Same numerals on `Nat` (truncated `/`) | intermediate | `ProofEngineering/Algebra.lean` |
| A02 | Algebra | Cubic binomial theorem | `ring` | Stating it in a non-commutative ring | intermediate | `ProofEngineering/Algebra.lean` |
| A03 | Algebra | Difference of squares | `ring_nf` | `Nat` subtraction is not an inverse | intermediate | `ProofEngineering/Algebra.lean` |
| A04 | Algebra | Linear strict transitivity | `linarith` | Nonlinear goal | intermediate | `ProofEngineering/Algebra.lean` |
| A05 | Algebra | `2ab ≤ a² + b²` | `nlinarith` | Omitting `sq_nonneg` | advanced | `ProofEngineering/Algebra.lean` |
| A06 | Algebra | Field cancellation | `field_simp` | Missing `b ≠ 0` | advanced | `ProofEngineering/Algebra.lean` |
| A07 | Algebra | Product of positive reals | `positivity` | Weak `≤` used for a strict goal | advanced | `ProofEngineering/Algebra.lean` |
| I01 | Induction | Gauss doubled-sum formula | `Nat` induction, `sum_range_succ` | Off-by-one range or `Nat` division | intermediate | `ProofEngineering/Induction.lean` |
| I02 | Induction | `reverse` of an append | `List` induction | Inducting on the wrong list | intermediate | `ProofEngineering/Induction.lean` |
| I03 | Induction | Recursive factorial positivity | Recursive `def`, induction | Spot-checking values | advanced | `ProofEngineering/Induction.lean` |
| I04 | Induction | Occurrence count under `reverse` | Helper lemma then induction | Proving reverse before append | advanced | `ProofEngineering/Induction.lean` |
| T01 | Type-driven | `a - b + b = a` on `Int` | `abel`, `AddCommGroup` | Copying the identity onto `Nat` | intermediate | `ProofEngineering/TypeDrivenReasoning.lean` |
| T02 | Type-driven | `Nat → Real` homomorphism | `Nat.cast_add` | Ambiguous which `+` is used | intermediate | `ProofEngineering/TypeDrivenReasoning.lean` |
| T03 | Type-driven | Rational inverse law | `field_simp` on `Rat` | Inversion on `Nat` | advanced | `ProofEngineering/TypeDrivenReasoning.lean` |
| T04 | Type-driven | Commutative monoid add | Typeclass inference | Missing `AddCommMonoid` instance | advanced | `ProofEngineering/TypeDrivenReasoning.lean` |
| T05 | Type-driven | Translation of `<` on `Int` | `linarith` | Same lemma on `Nat` subtraction | advanced | `ProofEngineering/TypeDrivenReasoning.lean` |
| B01 | Robustness | Same square identity, two styles | `ring` vs structured `calc` | Treating `ring` as self-documenting | advanced | `ProofEngineering/Robustness.lean` |
| B02 | Robustness | Same quadratic inequality, two styles | `nlinarith` vs `have` + `linarith` | Adding unused positivity hypotheses | advanced | `ProofEngineering/Robustness.lean` |
| C01 | Review | Subtraction cancellation | Domain repair `Nat` → `Int` | False `Nat` statement | intermediate | `ProofEngineering/ReviewerCases.lean` |
| C02 | Review | Field cancellation | Restored `b ≠ 0` | Missing nonzero hypothesis | advanced | `ProofEngineering/ReviewerCases.lean` |
| C03 | Review | Unbounded `Nat` | Restored `∀` then `∃` | Swapped quantifiers | intermediate | `ProofEngineering/ReviewerCases.lean` |
| C04 | Review | Zero-product law | `NoZeroDivisors`, disjunction | Strengthened to `a = 0` | advanced | `ProofEngineering/ReviewerCases.lean` |
| C05 | Review | Classification of `n ≤ 0` | `Nat.le_zero` | Vacuous `n < 0 → …` | advanced | `ProofEngineering/ReviewerCases.lean` |

## Companion declarations

These are executable but indexed under a parent case:

| Parent | Companions |
| --- | --- |
| S03 | `exists_and_left_of_exists_and`, structure `ClosedInterval` |
| S04 | `Implies`, `apply_local_def` |
| R02 | `shift` |
| I03 | `myFact` |
| I04 | `countEq`, `countEq_append`, `countEq_singleton` |
| T01 | `nat_sub_add_of_le` (restricted `Nat` repair; not substituted for the `Int` law) |
| T04 | `nat_div_mul_of_dvd` |
| B01 | `add_sq_automated`, `add_sq_structured` |
| B02 | `two_mul_le_automated`, `two_mul_le_structured` |

## Counts

| Difficulty | Cases |
| --- | --- |
| Foundational | 10 |
| Intermediate | 17 |
| Advanced | 15 |
| **Total** | **42** |

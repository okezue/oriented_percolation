import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace OrientedPercolation

/-!
# Bad-start counting on a 1D transversal

In the Aldous-flow / discrete-Hammersley argument, the *discretization error term* is
controlled by counting how often a "bad" configuration *starts* along a 1D time parameter.

Given a predicate `bad : ℕ → Prop`, define

* `badStart bad k` := `bad k ∧ (k = 0 ∨ ¬ bad (k-1))`.

On a finite time window `{0,1,...,n-1}`, we represent the set of bad indices and the set of
bad starts as finsets, using `Finset.range n`.

This is designed to be paired with `NextStep.lean` / `BadCountNegligible.lean`: one typically
defines events `A ε k` meaning "a bad start occurs at time k" and then bounds
`μ(A ε k) ≤ C*ε` uniformly, yielding `E[B]/(n*√ε) → 0`.
-/

namespace BadStarts

/-- A "bad start" at time `k`: the configuration is bad at `k`, and it was not bad at `k-1`
(or `k=0`). -/
def badStart (bad : ℕ → Prop) (k : ℕ) : Prop :=
  bad k ∧ (k = 0 ∨ ¬ bad (k - 1))

instance (bad : ℕ → Prop) [DecidablePred bad] (k : ℕ) : Decidable (badStart bad k) :=
  inferInstanceAs (Decidable (bad k ∧ (k = 0 ∨ ¬ bad (k - 1))))

/-- The set of bad indices in `{0,...,n-1}`. -/
def badSet (n : ℕ) (bad : ℕ → Prop) [DecidablePred bad] : Finset ℕ :=
  (Finset.range n).filter bad

/-- The set of bad-start indices in `{0,...,n-1}`. -/
def badStarts (n : ℕ) (bad : ℕ → Prop) [DecidablePred bad] : Finset ℕ :=
  (Finset.range n).filter (badStart bad)

lemma mem_badSet_iff {n : ℕ} {bad : ℕ → Prop} [DecidablePred bad] {k : ℕ} :
    k ∈ badSet n bad ↔ k < n ∧ bad k := by
  simp [badSet]

lemma mem_badStarts_iff {n : ℕ} {bad : ℕ → Prop} [DecidablePred bad] {k : ℕ} :
    k ∈ badStarts n bad ↔ k < n ∧ badStart bad k := by
  simp [badStarts, badStart]

/-- Every bad-start is (in particular) a bad index. -/
lemma badStarts_subset_badSet (n : ℕ) (bad : ℕ → Prop) [DecidablePred bad] :
    badStarts n bad ⊆ badSet n bad := by
  intro k hk
  rcases (mem_badStarts_iff (n := n) (bad := bad) (k := k)).1 hk with ⟨hkn, hkstart⟩
  have hkbad : bad k := hkstart.1
  exact (mem_badSet_iff (n := n) (bad := bad) (k := k)).2 ⟨hkn, hkbad⟩

/-- Cardinality bound: #bad-starts ≤ #bad-indices. -/
lemma card_badStarts_le_card_badSet (n : ℕ) (bad : ℕ → Prop) [DecidablePred bad] :
    (badStarts n bad).card ≤ (badSet n bad).card := by
  exact Finset.card_le_card (badStarts_subset_badSet (n := n) (bad := bad))

end BadStarts

end OrientedPercolation

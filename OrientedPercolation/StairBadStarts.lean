import OrientedPercolation.StairBadCols
import OrientedPercolation.BadStartsNat

namespace StairGrid

namespace Stair

open scoped BigOperators

/-!
# Bad-start indices for `badCol`

`StairBadCols.lean` defined, for two height profiles `h₁ h₂`, a per-column predicate

  badCol n h₁ h₂ x : Prop  :=  (h₂ x).1 ≤ (h₁ x).1 + 1.

This marks columns where the vertical separation is < 2. In later stages, these are the
only places where gridification can force adjacent lines into the same discrete corridor.

For the *error term* we usually want to count **maximal bad segments** (runs of bad columns).
A standard way is to count **bad starts**:

  badStart(k) := bad(k) ∧ (k=0 ∨ ¬ bad(k-1)).

Here we reindex columns by naturals `k : ℕ` with `k < n` and reuse the generic combinatorics
from `BadStartsNat.lean`.
-/

namespace BadStarts

/-- Extend `badCol` to a predicate on natural indices, declaring it false outside `k < n`. -/
def badColAt (n : ℕ) (h₁ h₂ : Fin n → Fin (n+1)) (k : ℕ) : Prop :=
  if hk : k < n then badCol n h₁ h₂ ⟨k, hk⟩ else False

instance (n : ℕ) (h₁ h₂ : Fin n → Fin (n+1)) (k : ℕ) : Decidable (badColAt n h₁ h₂ k) := by
  unfold badColAt
  by_cases hk : k < n
  · simp only [hk, dite_true]
    exact inferInstanceAs (Decidable (badCol n h₁ h₂ ⟨k, hk⟩))
  · simp only [hk, dite_false]
    exact inferInstanceAs (Decidable False)

/-- The predicate "bad start at k" for the staircase separation test. -/
def badStartAt (n : ℕ) (h₁ h₂ : Fin n → Fin (n+1)) (k : ℕ) : Prop :=
  OrientedPercolation.BadStarts.badStart (badColAt n h₁ h₂) k

instance (n : ℕ) (h₁ h₂ : Fin n → Fin (n+1)) : DecidablePred (badColAt n h₁ h₂) :=
  fun k => inferInstance

/-- The finset of bad-start indices in `{0,...,n-1}`. -/
def badStarts (n : ℕ) (h₁ h₂ : Fin n → Fin (n+1)) : Finset ℕ :=
  OrientedPercolation.BadStarts.badStarts n (badColAt n h₁ h₂)

/-- A bad-start index is always in range. -/
lemma mem_badStarts_imp_lt {n : ℕ} {h₁ h₂ : Fin n → Fin (n+1)} {k : ℕ}
    (hk : k ∈ badStarts n h₁ h₂) : k < n := by
  -- unfold and simp: membership in `Finset.range n` comes out.
  rcases (OrientedPercolation.BadStarts.mem_badStarts_iff (n := n)
      (bad := badColAt n h₁ h₂) (k := k)).1 hk with ⟨hkn, _⟩
  exact hkn

/-- Cardinality bound: #bad-starts ≤ n. -/
lemma card_badStarts_le (n : ℕ) (h₁ h₂ : Fin n → Fin (n+1)) :
    (badStarts n h₁ h₂).card ≤ n := by
  -- `badStarts` is a subset of `range n`.
  have : badStarts n h₁ h₂ ⊆ Finset.range n := by
    intro k hk
    have hkn : k < n := mem_badStarts_imp_lt (n := n) (h₁ := h₁) (h₂ := h₂) hk
    simpa [Finset.mem_range] using hkn
  -- hence the card bound
  simpa [Finset.card_range] using Finset.card_le_card this

end BadStarts

end Stair

end StairGrid

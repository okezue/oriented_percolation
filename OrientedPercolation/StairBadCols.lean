import OrientedPercolation.StairGrid

namespace StairGrid

namespace Stair

open scoped BigOperators

/-- A "bad column" for separation: at column `x`, the vertical gap is < 2.

In the later (full) argument, these are the places where discretization can force
adjacent gridified lines into the same corridor.
-/
def badCol (n : ℕ) (h₁ h₂ : Fin n → Fin (n+1)) (x : Fin n) : Prop :=
  (h₂ x).1 ≤ (h₁ x).1 + 1

instance (n : ℕ) (h₁ h₂ : Fin n → Fin (n+1)) (x : Fin n) : Decidable (badCol n h₁ h₂ x) :=
  inferInstanceAs (Decidable ((h₂ x).1 ≤ (h₁ x).1 + 1))

/-- The finset of bad columns. -/
def badCols (n : ℕ) (h₁ h₂ : Fin n → Fin (n+1)) : Finset (Fin n) :=
  Finset.univ.filter (fun x => badCol n h₁ h₂ x)

/-- If the separation-by-2 hypothesis holds everywhere, there are no bad columns. -/
lemma badCols_eq_empty_of_sep2
    (n : ℕ) (h₁ h₂ : Fin n → Fin (n+1))
    (hsep : ∀ x, (h₁ x).1 + 2 ≤ (h₂ x).1) :
    badCols n h₁ h₂ = ∅ := by
  ext x
  simp only [badCols, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hbad
    unfold badCol at hbad
    have hle : (h₁ x).1 + 2 ≤ (h₂ x).1 := hsep x
    omega
  · intro h
    exact absurd h (Finset.notMem_empty x)

/-- If there are no bad columns, then the separation-by-2 condition holds everywhere.

This is the converse of `badCols_eq_empty_of_sep2`.
-/
lemma sep2_of_badCols_eq_empty
    (n : ℕ) (h₁ h₂ : Fin n → Fin (n+1))
    (hempty : badCols n h₁ h₂ = ∅) :
    ∀ x, (h₁ x).1 + 2 ≤ (h₂ x).1 := by
  intro x
  -- If the separation failed, `x` would be a bad column.
  by_contra hfail
  have hxbad : badCol n h₁ h₂ x := by
    unfold badCol
    omega
  -- Now `x ∈ badCols`, contradicting `hempty`.
  have hxmem : x ∈ badCols n h₁ h₂ := by
    simp only [badCols, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hxbad
  -- But `badCols = ∅`.
  rw [hempty] at hxmem
  exact Finset.notMem_empty x hxmem

/-- A convenient corollary: if there are no bad columns, then the toy staircase paths
are edge-disjoint (by `disjoint_stairPath_of_sep2`). -/
lemma disjoint_stairPath_of_badCols_empty
    (n : ℕ) (h₁ h₂ : Fin n → Fin (n+1))
    (hempty : badCols n h₁ h₂ = ∅) :
    Disjoint (stairPath n h₁).edges (stairPath n h₂).edges := by
  apply disjoint_stairPath_of_sep2 (n := n) (h₁ := h₁) (h₂ := h₂)
  exact sep2_of_badCols_eq_empty (n := n) (h₁ := h₁) (h₂ := h₂) hempty

end Stair

end StairGrid

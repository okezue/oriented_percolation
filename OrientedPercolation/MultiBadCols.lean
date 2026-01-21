import OrientedPercolation.StairBadCols

/-!
# MultiBadCols.lean

Deterministic "next step" in the toy StairGrid model.

We have already defined, for two height profiles h₁ h₂:
  - badCol n h₁ h₂ x : Prop      (gap < 2 at column x)
  - badCols n h₁ h₂ : Finset     (all bad columns)

Here we lift this to a *family* of (W+1) profiles H i,
and define:
  - badColAdj : badness for adjacent indices i,i+1
  - badColsGlobal : columns where *some* adjacent pair is bad

Then we prove a basic monotonicity fact:
  if badColsGlobal is empty, then every adjacent pair has empty badCols,
  hence every adjacent pair of stairPaths is edge-disjoint.
-/

namespace StairGrid

namespace Stair

open scoped BigOperators

/-- Badness predicate for an *adjacent pair* in a family of `W+1` height profiles.

We index adjacent pairs by `i : Fin W` and interpret this as the pair
`(i.castSucc, i.succ) : Fin (W+1)`.
-/
def badColAdj (n W : ℕ)
    (H : Fin (W+1) → Fin n → Fin (n+1))
    (i : Fin W) (x : Fin n) : Prop :=
  badCol n (H i.castSucc) (H i.succ) x

instance (n W : ℕ) (H : Fin (W+1) → Fin n → Fin (n+1)) (i : Fin W) (x : Fin n) :
    Decidable (badColAdj n W H i x) :=
  inferInstanceAs (Decidable (badCol n (H i.castSucc) (H i.succ) x))

/-- A column is *globally bad* if there exists some adjacent pair with gap < 2 there. -/
def badColGlobal (n W : ℕ)
    (H : Fin (W+1) → Fin n → Fin (n+1))
    (x : Fin n) : Prop :=
  ∃ i : Fin W, badColAdj n W H i x

instance (n W : ℕ) (H : Fin (W+1) → Fin n → Fin (n+1)) (x : Fin n) :
    Decidable (badColGlobal n W H x) :=
  Fintype.decidableExistsFintype

/-- The finset of globally bad columns. -/
def badColsGlobal (n W : ℕ)
    (H : Fin (W+1) → Fin n → Fin (n+1)) : Finset (Fin n) :=
  Finset.univ.filter (fun x => badColGlobal n W H x)

/-- If the global bad-column set is empty, then each adjacent pair has no bad columns. -/
lemma badCols_adj_eq_empty_of_badColsGlobal_eq_empty
    (n W : ℕ)
    (H : Fin (W+1) → Fin n → Fin (n+1))
    (hempty : badColsGlobal n W H = ∅) :
    ∀ i : Fin W, badCols n (H i.castSucc) (H i.succ) = ∅ := by
  intro i
  ext x
  constructor
  · intro hx
    -- From membership in `badCols`, get the pointwise badness.
    have hxbad : badCol n (H i.castSucc) (H i.succ) x := by
      -- `badCols` is `univ.filter (badCol ...)`
      simp only [badCols, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx

    -- Then `x` is globally bad (witness `i`).
    have hxglob : x ∈ badColsGlobal n W H := by
      simp only [badColsGlobal, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, hxbad⟩

    -- Contradiction with `hempty`.
    rw [hempty] at hxglob
    exact (Finset.notMem_empty x hxglob).elim
  · intro hx
    -- membership in empty set is impossible
    exact (Finset.notMem_empty x hx).elim

/-- Corollary: if there are no globally bad columns, then each adjacent pair of
staircase paths is edge-disjoint.

This is the direct bridge into the later multi-line argument: edge collisions can only
occur where the local separation condition fails.
-/
lemma disjoint_adj_stairPath_of_badColsGlobal_eq_empty
    (n W : ℕ)
    (H : Fin (W+1) → Fin n → Fin (n+1))
    (hempty : badColsGlobal n W H = ∅) :
    ∀ i : Fin W,
      Disjoint (stairPath n (H i.castSucc)).edges (stairPath n (H i.succ)).edges := by
  intro i
  -- Reduce to the two-profile lemma `disjoint_stairPath_of_badCols_empty`.
  have hempty' : badCols n (H i.castSucc) (H i.succ) = ∅ :=
    badCols_adj_eq_empty_of_badColsGlobal_eq_empty (n := n) (W := W) (H := H) hempty i
  exact disjoint_stairPath_of_badCols_empty (n := n) (h₁ := H i.castSucc) (h₂ := H i.succ) hempty'

end Stair

end StairGrid

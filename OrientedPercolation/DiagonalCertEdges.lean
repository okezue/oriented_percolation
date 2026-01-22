import OrientedPercolation.StairGrid
import Mathlib.Tactic

/-!
# Deterministic diagonal certificate windows

This file defines a very simple *deterministic* family of constant-size edge sets in the
`n×n` directed grid from `StairGrid.lean`.

For each `k : Fin n`, we take the 1×1 square (cell) with bottom-left corner `(k,k)` and
collect its four directed boundary edges.

These are convenient as *certificate sets* for union-bound style probability estimates: the
cardinality is uniformly bounded by `4`.
-/

namespace OrientedPercolation

open StairGrid

namespace Diagonal

/-- The four boundary edges of the diagonal unit cell with bottom-left corner `(k,k)`.
    For k : Fin n, the cell has corners at (k,k), (k+1,k), (k,k+1), (k+1,k+1).
    Edge types: H : Fin n → Fin (n+1) → Edge n, V : Fin (n+1) → Fin n → Edge n -/
noncomputable def diagCellEdges (n : ℕ) (k : Fin n) : Finset (Edge n) :=
  -- Bottom horizontal: (k, k) → (k+1, k)
  ({Edge.H k (Fin.castSucc k)} : Finset (Edge n)) ∪
  -- Top horizontal: (k, k+1) → (k+1, k+1)
  ({Edge.H k (Fin.succ k)} : Finset (Edge n)) ∪
  -- Left vertical: (k, k) → (k, k+1)
  ({Edge.V (Fin.castSucc k) k} : Finset (Edge n)) ∪
  -- Right vertical: (k+1, k) → (k+1, k+1)
  ({Edge.V (Fin.succ k) k} : Finset (Edge n))

/-- A uniform cardinality bound: each diagonal cell has at most 4 edges. -/
lemma card_diagCellEdges_le_four (n : ℕ) (k : Fin n) :
    (diagCellEdges n k).card ≤ 4 := by
  classical
  -- Name the four singleton finsets so we can apply `card_union_le` repeatedly.
  let A : Finset (Edge n) := {Edge.H k (Fin.castSucc k)}
  let B : Finset (Edge n) := {Edge.H k (Fin.succ k)}
  let C : Finset (Edge n) := {Edge.V (Fin.castSucc k) k}
  let D : Finset (Edge n) := {Edge.V (Fin.succ k) k}

  -- Rewrite `diagCellEdges` in terms of `A,B,C,D`.
  have hdef : diagCellEdges n k = A ∪ B ∪ C ∪ D := by
    simp [diagCellEdges, A, B, C, D, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]

  -- Now apply the crude union-cardinality bound (we do not need disjointness).
  -- Step 1: add D
  have h1 : (A ∪ B ∪ C ∪ D).card ≤ (A ∪ B ∪ C).card + D.card := by
    -- `A ∪ B ∪ C ∪ D = (A ∪ B ∪ C) ∪ D`
    simpa [Finset.union_assoc] using (Finset.card_union_le (A ∪ B ∪ C) D)
  -- Step 2: add C
  have h2 : (A ∪ B ∪ C).card ≤ (A ∪ B).card + C.card := by
    simpa [Finset.union_assoc] using (Finset.card_union_le (A ∪ B) C)
  -- Step 3: add B
  have h3 : (A ∪ B).card ≤ A.card + B.card := by
    simpa using (Finset.card_union_le A B)

  -- Combine bounds.
  have : (A ∪ B ∪ C ∪ D).card ≤ ((A.card + B.card) + C.card) + D.card := by
    calc
      (A ∪ B ∪ C ∪ D).card
          ≤ (A ∪ B ∪ C).card + D.card := h1
      _ ≤ ((A ∪ B).card + C.card) + D.card := by
            exact Nat.add_le_add_right h2 _
      _ ≤ ((A.card + B.card) + C.card) + D.card := by
            -- Use the bound on `(A ∪ B).card`.
            have := Nat.add_le_add_right h3 C.card
            -- rearrange parentheses
            -- `(A ∪ B).card + C.card ≤ (A.card + B.card) + C.card`
            -- then add `D.card` on the right.
            exact Nat.add_le_add_right (by simpa [Nat.add_assoc] using this) D.card

  -- Finish by plugging in `A=B=C=D=singleton`, so each card is 1.
  have hbound4 : (A ∪ B ∪ C ∪ D).card ≤ 4 := by
    -- Each of `A,B,C,D` is a singleton, so the RHS becomes `((1+1)+1)+1 = 4`.
    simpa [A, B, C, D, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

  -- Finally, rewrite back to `diagCellEdges`.
  simpa [hdef] using hbound4

end Diagonal

end OrientedPercolation

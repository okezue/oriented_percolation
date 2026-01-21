import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace StairGrid

/-!
A tiny, self-contained "toy grid" formalization.

We define a directed `n × n` grid (vertices `(0..n) × (0..n)`) with horizontal
and vertical edges directed East / North.

Then we define a (toy) "staircase gridification" associated to a height profile
`h : Fin n → Fin (n+1)` by taking, for each `x : Fin n`, the horizontal edge
`(x, h x) → (x+1, h x)`.

Finally we prove a basic separation lemma:
If `h₂ x ≥ h₁ x + 2` for all `x`, then the two staircase paths are edge-disjoint.

This is the core type of *regularity of gridification* fact we'll need later.
The full development will add the vertical connector edges and boundary
conditions, but the disjointness argument is already visible here.
-/

/-- Vertices of the `(n×n)` box are coordinates in `{0,…,n} × {0,…,n}`. -/
abbrev Vertex (n : ℕ) := Fin (n+1) × Fin (n+1)

/-- Directed grid edges (east or north). -/
inductive Edge (n : ℕ)
| H : Fin n → Fin (n+1) → Edge n  -- (x,y) → (x+1,y)
| V : Fin (n+1) → Fin n → Edge n  -- (x,y) → (x,y+1)
deriving DecidableEq

/-- A (finite) directed path is represented just by the set of edges it uses.
    (This matches the earlier `Path` abstraction you already have.) -/
structure Path (n : ℕ) where
  edges : Finset (Edge n)

instance {n : ℕ} : Coe (Path n) (Finset (Edge n)) := ⟨Path.edges⟩

namespace Stair

/-- Horizontal edges of the toy staircase path associated to a height function `h`.

We keep only these in the toy model; later we'll add the vertical connector edges.
-/
noncomputable def horizEdges (n : ℕ) (h : Fin n → Fin (n+1)) : Finset (Edge n) :=
  Finset.univ.image (fun x => Edge.H x (h x))

/-- The toy staircase path: just the collection of horizontal edges. -/
noncomputable def stairPath (n : ℕ) (h : Fin n → Fin (n+1)) : Path n :=
  ⟨horizEdges n h⟩

/-- If two height profiles differ by at least `2` everywhere, then the corresponding
horizontal-edge staircase paths are edge-disjoint.

This is the "gridification regularity" lemma in its simplest, purely discrete form.
-/
lemma disjoint_stairPath_of_sep2
    (n : ℕ) (h₁ h₂ : Fin n → Fin (n+1))
    (hsep : ∀ x, (h₁ x).1 + 2 ≤ (h₂ x).1) :
    Disjoint (stairPath n h₁).edges (stairPath n h₂).edges := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro e he1 he2
  -- Unpack membership in each `image`.
  simp only [stairPath, horizEdges, Finset.mem_image, Finset.mem_univ, true_and] at he1 he2
  obtain ⟨x1, rfl⟩ := he1
  obtain ⟨x2, hEq⟩ := he2
  -- Equality of two `H`-edges forces the same `x` and the same height.
  have hinj : x2 = x1 ∧ h₂ x2 = h₁ x1 := by
    injection hEq with hx hy
    exact ⟨hx, hy⟩
  obtain ⟨hx, hh⟩ := hinj
  -- Now `hsep x1` reads `a+2 ≤ a`, contradiction.
  have hle : (h₁ x1).1 + 2 ≤ (h₂ x1).1 := hsep x1
  -- Rewrite using hx to convert x1 to x2
  rw [← hx] at hle
  -- Now hle : (h₁ x2).1 + 2 ≤ (h₂ x2).1
  -- And hh : h₂ x2 = h₁ x1 = h₁ x2 (using hx)
  have hh' : h₂ x2 = h₁ x2 := by rw [hh, hx]
  rw [hh'] at hle
  omega

end Stair

end StairGrid

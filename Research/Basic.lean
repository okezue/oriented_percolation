import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Basic

open scoped Topology BigOperators Asymptotics
open Filter Asymptotics

namespace Research

/-!
This file contains two reusable "verification" lemmas:

(1) Matching upper/lower bounds up to constants = Theta (`f =Θ[l] g`).
(2) A generic bridge/packaging lemma: if your construction already produced an
    edge-disjoint cover of size `W + B`, then the formal feasibility statement is immediate.

Both parts are independent; you can delete whichever you don't need.
-/

-- =========================================================
-- Part A: "matching bounds up to constants" (Theta)
-- =========================================================

section Asymptotics

variable {α β : Type*} [NormedField β]
variable {l : Filter α}
variable {f g : α → β}

/-- If you have a big-O upper bound and a big-O lower bound (rewritten as `g =O[l] f`),
then you have matching bounds up to constants: `f =Θ[l] g`.

In mathlib, `f =Θ[l] g` is definitionally `f =O[l] g ∧ g =O[l] f`.
-/
theorem isTheta_of_bigO (hfg : f =O[l] g) (hgf : g =O[l] f) : f =Θ[l] g :=
  ⟨hfg, hgf⟩

/-- If `f/g → 1` along `l` and `g` is eventually nonzero, then `f ~[l] g`,
and hence `f =Θ[l] g`.

This uses the characterization `u ~[l] v ↔ Tendsto (u/v) l (𝓝 1)`
under an eventual nonvanishing hypothesis, and then `IsEquivalent.isTheta`.
-/
theorem isTheta_of_tendsto_div_one
    (hg : ∀ᶠ x in l, g x ≠ 0)
    (h : Tendsto (fun x => f x / g x) l (𝓝 (1 : β))) :
    f =Θ[l] g := by
  have heq : f ~[l] g :=
    (Asymptotics.isEquivalent_iff_tendsto_one (l := l) (u := f) (v := g) hg).2 h
  exact heq.isTheta

end Asymptotics

-- =========================================================
-- Part B: "bridge lemma" packaging for a W+B construction
-- =========================================================

section BridgePacking

universe u
variable {Edge : Type u} [DecidableEq Edge]

/-- Abstract path: for the packing/bridge step we only care about the finite set of edges it uses.
Later you can refine this to "valid directed lattice path" etc. -/
structure Path (Edge : Type u) where
  edges : Finset Edge

/-- Union of edge sets used by a list of paths. -/
def edgesUnion (L : List (Path Edge)) : Finset Edge :=
  L.foldl (fun acc P => acc ∪ P.edges) ∅

/-- Pairwise edge-disjointness. -/
def EdgeDisjoint (L : List (Path Edge)) : Prop :=
  L.Pairwise (fun P Q => Disjoint P.edges Q.edges)

/-- Feasibility predicate: there exists an edge-disjoint cover of `Eclosed` by `k` paths. -/
def Feasible (Eclosed : Finset Edge) (k : ℕ) : Prop :=
  ∃ L : List (Path Edge),
    L.length = k ∧ EdgeDisjoint L ∧ Eclosed ⊆ edgesUnion L

/-- Concatenate a finite family of lists of paths into one list. -/
def allPaths {W : ℕ} (pieces : Fin W → List (Path Edge)) : List (Path Edge) :=
  (List.ofFn pieces).flatten

omit [DecidableEq Edge] in
/-- Length bookkeeping: `flatten` sums lengths. -/
lemma length_allPaths {W : ℕ} (pieces : Fin W → List (Path Edge)) :
    (allPaths pieces).length = (List.map List.length (List.ofFn pieces)).sum := by
  simp only [allPaths, List.length_flatten]

/-- **Bridge packaging lemma.**

If your explicit construction already produced a list `allPaths pieces`
with length `W+B`, edge-disjointness, and coverage of the closed edges,
then the formal feasibility statement `Feasible Eclosed (W+B)` follows immediately.
-/
theorem feasible_of_pieces {W B : ℕ}
    (Eclosed : Finset Edge)
    (pieces : Fin W → List (Path Edge))
    (h_len : (allPaths pieces).length = W + B)
    (h_disj : EdgeDisjoint (allPaths pieces))
    (h_cov : Eclosed ⊆ edgesUnion (allPaths pieces)) :
    Feasible Eclosed (W + B) :=
  ⟨allPaths pieces, h_len, h_disj, h_cov⟩

end BridgePacking

end Research

import OrientedPercolation.AldousFullProof_Events
import OrientedPercolation.BadStartDiagonalProb

/-!
# Instantiating `AldousFullProof_Events` with diagonal-cell certificate events

This file shows how to feed a *concrete* bad-event family into the already-verified
endgame theorem `GridFlow.aldous_claim_of_squeeze_with_bad_events`.

We take the transversal to be the `n` diagonal unit cells `(k,k)` and define the bad event
`A ε k` to be: *some directed edge on that diagonal cell is closed*.

This depends on at most 4 edges, so if each edge is closed with probability at most `ε`,
then `P(A ε k) ≤ 4ε` by a union bound.

The only additional input still needed for the full Aldous claim is the deterministic
squeeze `W ≤ U ≤ W + Bfun` for this particular choice of `A`.
-/

namespace GridFlow

open MeasureTheory

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A concrete bad-event family indexed by diagonal cells: in cell `k`, some edge is closed. -/
noncomputable def A_diagCell (n : ℕ)
    (closed : ℝ → StairGrid.Edge n → Set Ω) (ε : ℝ) (k : Fin n) : Set Ω :=
  OrientedPercolation.badStartEvent (OrientedPercolation.Diagonal.diagCellEdges n) (closed ε) k

/-- Uniform `O(ε)` probability bound for the diagonal-cell bad events, with constant `4`. -/
theorem prob_A_diagCell_le (n : ℕ) (closed : ℝ → StairGrid.Edge n → Set Ω)
    (hP : ∀ ε, 0 ≤ ε → ∀ e, μ.real (closed ε e) ≤ ε)
    {ε : ℝ} (hε : 0 ≤ ε) (k : Fin n) :
    μ.real (A_diagCell (Ω:=Ω) n closed ε k) ≤ 4 * ε := by
  -- Apply the diagonal-cell union bound lemma at parameter `ε`.
  simpa [A_diagCell] using
    OrientedPercolation.Diagonal.badStartEvent_prob_le_diagCell
      (μ:=μ) (n:=n) (ε:=ε) (hε:=hε) (closed:=closed ε)
      (hP:=by intro e; exact hP ε hε e) k

end GridFlow

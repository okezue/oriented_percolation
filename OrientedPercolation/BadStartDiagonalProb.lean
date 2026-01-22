import OrientedPercolation.DiagonalCertEdges
import OrientedPercolation.BadStartEventProb
import Mathlib.Tactic

/-!
# Probability bound for diagonal-cell bad-start certificates

This file specializes the generic union-bound lemma

`OrientedPercolation.badStartEvent_prob_le`

to the diagonal unit-cell certificates `OrientedPercolation.Diagonal.diagCellEdges`.

Since each diagonal cell contains at most 4 directed edges, we obtain a uniform
`O(ε)` bound.
-/

namespace OrientedPercolation

open MeasureTheory

namespace Diagonal

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- If each edge is closed with probability `≤ ε`, then the diagonal-cell certificate event
has probability `≤ 4ε`.

This is the concrete `P(A ε i) ≤ C·ε` input needed by the endgame file
`AldousFullProof_Events.lean`, with the choice `C = 4`.
-/
theorem badStartEvent_prob_le_diagCell
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (closed : StairGrid.Edge n → Set Ω)
    (hP : ∀ e, μ.real (closed e) ≤ ε)
    (k : Fin n) :
    μ.real (badStartEvent (diagCellEdges n) closed k) ≤ 4 * ε := by
  have h1 :
      μ.real (badStartEvent (diagCellEdges n) closed k)
        ≤ (diagCellEdges n k).card * ε :=
    badStartEvent_prob_le (μ := μ) (ε := ε) (closed := closed)
      (certEdges := diagCellEdges n) k hP

  have hcard : (diagCellEdges n k).card ≤ 4 := card_diagCellEdges_le_four n k
  have hcard' : ((diagCellEdges n k).card : ℝ) ≤ (4 : ℝ) := by
    exact_mod_cast hcard

  -- Combine the generic bound with the uniform card bound.
  calc
    μ.real (badStartEvent (diagCellEdges n) closed k)
        ≤ (diagCellEdges n k).card * ε := h1
    _ ≤ (4 : ℝ) * ε := by
        -- `mul_le_mul_of_nonneg_right` uses the nonnegativity of `ε`.
        simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hcard' hε)

end Diagonal
end OrientedPercolation

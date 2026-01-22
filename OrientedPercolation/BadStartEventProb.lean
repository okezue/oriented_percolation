import OrientedPercolation.BadStartEventFamily
import OrientedPercolation.BadStartCertificates
import Mathlib.Tactic

namespace OrientedPercolation

open MeasureTheory

section

variable {Ω Edge : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsFiniteMeasure μ]
variable [DecidableEq Edge]

variable {n : ℕ}
variable (certEdges : Fin n → Finset Edge)
variable (closed : Edge → Set Ω)

lemma badStartEvent_prob_le
    (ε : ℝ) (i : Fin n)
    (hP : ∀ e, μ.real (closed e) ≤ ε) :
    μ.real (badStartEvent certEdges closed i) ≤ ((certEdges i).card : ℝ) * ε := by
  -- This is just the finite union bound.
  -- We invoke the generic lemma from `GridFlow.BadStartCertificates` with `A = ⋃ ...`.
  simpa [badStartEvent] using
    (GridFlow.measureReal_le_card_mul_of_subset_biUnion (μ := μ)
      (A := badStartEvent certEdges closed i) (cert := certEdges i) (f := closed) (ε := ε)
      hP (by
        intro ω h
        exact h))

end

end OrientedPercolation

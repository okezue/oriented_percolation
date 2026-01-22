import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OrientedPercolation

open MeasureTheory

section

variable {Ω Edge : Type*} [MeasurableSpace Ω]
variable [DecidableEq Edge]

variable {n : ℕ}

/--
The bad-start event at index `i`, defined as: "some certificate edge in `certEdges i` is closed".

This is the exact shape needed to apply `measureReal_le_card_mul_of_subset_biUnion`.
-/
def badStartEvent (certEdges : Fin n → Finset Edge) (closed : Edge → Set Ω) (i : Fin n) : Set Ω :=
  ⋃ e ∈ certEdges i, closed e

end

end OrientedPercolation

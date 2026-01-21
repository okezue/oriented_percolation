import Mathlib.Data.Fintype.Fin
import OrientedPercolation.BadCountNegligible

/-!
# BadColsGlobalProb.lean

Probabilistic/analytic step: instantiate the generic
`BadCountNegligible` wrapper for a *column-indexed* bad-event family.

This matches the intended Aldous-flow usage:
  - choose an O(n)-sized transversal index set (columns, diagonals, etc.),
  - prove P(column is bad) ≤ C*ε uniformly,
  - conclude the normalized expected bad count is o(1) on the √ε scale.
-/

open scoped BigOperators Topology

namespace GridFlow

open MeasureTheory Filter

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Specialization of `tendsto_integral_badCount_div_card_sqrt` to the index set
`Fin n` (think: columns, or a 1D transversal of size `n`).

If each bad event has probability ≤ C*ε, then the expected bad count divided by
`n * √ε` tends to 0 as ε→0⁺.
-/
theorem tendsto_integral_badCount_div_n_sqrt
    (n : ℕ) (hn : 0 < n)
    (A : ℝ → Fin n → Set Ω)
    (hA : ∀ ε i, MeasurableSet (A ε i))
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ ε, 0 < ε → ∀ i, μ.real (A ε i) ≤ C * ε) :
    Tendsto
      (fun ε : ℝ =>
        (∫ ω, badCount (Finset.univ : Finset (Fin n)) (fun i => A ε i) ω ∂μ)
          / ((n : ℝ) * Real.sqrt ε))
      (𝓝[>] (0 : ℝ))
      (𝓝 (0 : ℝ)) := by
  -- Apply the generic wrapper with `s = univ`.
  have hs : 0 < (Finset.univ : Finset (Fin n)).card := by
    -- `card univ = n`.
    simpa using hn

  -- First use the wrapper normalized by `(card univ) * √ε`, then rewrite `card univ = n`.
  have hwrap :=
    GridFlow.tendsto_integral_badCount_div_card_sqrt (μ := μ)
      (s := (Finset.univ : Finset (Fin n)))
      (A := A) (hA := hA) (C := C) (hC := hC) (hs := hs) (hP := hP)

  -- Rewrite `(card univ : ℝ)` as `n`.
  simpa using hwrap

end

end GridFlow

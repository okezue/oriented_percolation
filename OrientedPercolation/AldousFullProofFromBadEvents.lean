import OrientedPercolation.BadColsGlobalProb

open scoped BigOperators Topology

namespace GridFlow

/-!
# Turning a per-event probability bound into `B(ε)/√ε → 0`

This file is optional glue: in the Aldous-flow proof, the error term `B(ε)` is
usually an *expected count* of "bad" transversal events, normalized by the
transversal size `n`.

Concretely, one typically defines

* an index set `Fin n` (columns/diagonals/etc),
* bad events `A ε i`, and
* the random variable `badCount` counting how many bad indices occur.

Then

`B(ε) := (1/n) * E[ badCount(ε) ]`.

If you can show a uniform bound `P(A ε i) ≤ C*ε`, our previously verified lemma
`BadColsGlobalProb.tendsto_integral_badCount_div_n_sqrt` implies

`B(ε)/√ε → 0` as `ε → 0⁺`.

So this file gives a clean interface from probability to the analytic squeeze.
-/

open MeasureTheory Filter

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Define the normalized expected bad count `B(ε) := E[badCount]/n`.

This is the canonical choice of the "error term" in the percolation proof.
-/
noncomputable def Bfun (n : ℕ) (A : ℝ → Fin n → Set Ω) (ε : ℝ) : ℝ :=
  (∫ ω, badCount (Finset.univ : Finset (Fin n)) (fun i => A ε i) ω ∂μ) / (n : ℝ)

/-- If each of the `n` bad events has probability `≤ C*ε`, then
`B(ε)/√ε → 0`.

This is exactly the normalization needed to plug into the final squeeze.
-/
theorem tendsto_Bfun_div_sqrt
    (n : ℕ) (hn : 0 < n)
    (A : ℝ → Fin n → Set Ω)
    (hA : ∀ ε i, MeasurableSet (A ε i))
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ ε, 0 < ε → ∀ i, μ.real (A ε i) ≤ C * ε) :
    Tendsto (fun ε : ℝ => (Bfun (μ := μ) n A ε) / Real.sqrt ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  -- Expand the definition: `Bfun/√ε = E[badCount] / (n*√ε)`.
  have hmain :=
    GridFlow.tendsto_integral_badCount_div_n_sqrt (μ := μ)
      (n := n) (hn := hn)
      (A := A) (hA := hA)
      (C := C) (hC := hC)
      (hP := hP)

  -- `Bfun` is just `E[badCount] / n`.
  -- Divide again by `√ε` and simplify.
  simpa [Bfun, div_div, mul_assoc, mul_left_comm, mul_comm] using hmain

end

end GridFlow

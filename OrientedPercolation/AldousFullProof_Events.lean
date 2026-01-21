import OrientedPercolation.SqueezeLimit
import OrientedPercolation.AldousFullProofFromBadEvents

open scoped BigOperators Topology

namespace GridFlow

/-!
# Final √ε-squeeze using a probabilistic error term

This file gives a one-stop theorem:

* you provide the deterministic squeeze `W ≤ U ≤ W + Bfun`,
* you provide the width scaling `W/√ε → √2`,
* you provide uniform bad-event bounds `P(A ε i) ≤ C*ε` over a transversal `Fin n`.

Then the analytic/probabilistic lemmas already verified imply

`U/√ε → √2`.

So the only remaining work to complete the Aldous conjecture is to:

1. build `W` and prove its √ε-limit,
2. define the concrete bad events `A ε i` controlling gridification collisions,
3. prove the deterministic squeeze with `Bfun`.
-/

open MeasureTheory Filter

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsFiniteMeasure μ]

variable (U W : ℝ → ℝ)
variable (n : ℕ)
variable (A : ℝ → Fin n → Set Ω)

/-- **One-shot endgame.**

Assume:

* `W(ε) ≤ U(ε) ≤ W(ε) + Bfun(n,A,ε)` for all `ε>0`,
* `W(ε)/√ε → √2`,
* `P(A ε i) ≤ C*ε` for all `i` and `ε>0`.

Then `U(ε)/√ε → √2`.
-/
theorem aldous_claim_of_squeeze_with_bad_events
    (hn : 0 < n)
    (hLower : ∀ ε, 0 < ε → W ε ≤ U ε)
    (hUpper : ∀ ε, 0 < ε → U ε ≤ W ε + Bfun (μ := μ) n A ε)
    (hW : Tendsto (fun ε : ℝ => W ε / Real.sqrt ε) (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 2)))
    (hA : ∀ ε i, MeasurableSet (A ε i))
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ ε, 0 < ε → ∀ i, μ.real (A ε i) ≤ C * ε) :
    Tendsto (fun ε : ℝ => U ε / Real.sqrt ε) (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 2)) := by
  -- The probabilistic lemma gives `Bfun/√ε → 0`.
  have hB : Tendsto (fun ε : ℝ => (Bfun (μ := μ) n A ε) / Real.sqrt ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    GridFlow.tendsto_Bfun_div_sqrt (μ := μ)
      (n := n) (hn := hn)
      (A := A) (hA := hA)
      (C := C) (hC := hC)
      (hP := hP)

  -- Now apply the √ε-squeeze lemma.
  exact
    GridFlow.tendsto_div_sqrt_of_squeeze
      (U := U) (W := W) (B := fun ε => Bfun (μ := μ) n A ε) (c := Real.sqrt 2)
      (hLower := hLower)
      (hUpper := hUpper)
      (hW := hW)
      (hB := hB)

end

end GridFlow

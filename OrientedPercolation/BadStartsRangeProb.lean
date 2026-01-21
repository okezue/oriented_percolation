import Mathlib.Data.Finset.Interval

import OrientedPercolation.BadCountNegligible

open scoped BigOperators Topology

namespace GridFlow

open MeasureTheory Filter

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsFiniteMeasure μ]

/-- A range-indexed version of the bad-count negligibility lemma.

We take the transversal index set to be `Finset.range n` (indices `0,...,n-1`).

If each event `A ε k` (for `k<n`) has probability ≤ `C*ε`, then

  E[ badCount_{k<n} 1_{A ε k} ] / (n * √ε) → 0  as ε → 0⁺.

This is the exact form convenient for "start-of-overlap" counts along a 1D time parameter.
-/
theorem tendsto_integral_badCount_div_n_sqrt_range
    (n : ℕ) (hn : 0 < n)
    (A : ℝ → ℕ → Set Ω)
    (hA : ∀ ε k, MeasurableSet (A ε k))
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ ε, 0 < ε → ∀ k, k < n → μ.real (A ε k) ≤ C * ε) :
    Tendsto
      (fun ε : ℝ =>
        (∫ ω, badCount (Finset.range n) (fun k => A ε k) ω ∂μ)
          / ((n : ℝ) * Real.sqrt ε))
      (𝓝[>] (0 : ℝ))
      (𝓝 (0 : ℝ)) := by
  -- Define an extension `A'` that is empty outside the range; then the uniform bound holds for all k.
  let A' : ℝ → ℕ → Set Ω := fun ε k => if h : k < n then A ε k else ∅

  have hA' : ∀ ε k, MeasurableSet (A' ε k) := by
    intro ε k
    by_cases hk : k < n
    · simp [A', hk, hA]
    · simp [A', hk]

  have hP' : ∀ ε, 0 < ε → ∀ k, μ.real (A' ε k) ≤ C * ε := by
    intro ε hε k
    by_cases hk : k < n
    · simp [A', hk]
      exact hP ε hε k hk
    · simp [A', hk]
      -- `μ.real ∅ = 0`.
      exact mul_nonneg hC (le_of_lt hε)

  -- The badCount over `range n` is unchanged by replacing `A` by `A'`.
  have h_same : ∀ ε ω,
      badCount (Finset.range n) (fun k => A ε k) ω =
      badCount (Finset.range n) (fun k => A' ε k) ω := by
    intro ε ω
    unfold badCount
    -- pointwise equality of summands for k∈range n
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk' : k < n := by
      -- `k ∈ range n` iff `k < n`
      simpa [Finset.mem_range] using hk
    -- On-range, `A' ε k = A ε k`.
    simp [A', hk']

  -- Replace the integrand by the equivalent one.
  have h_int_same : ∀ ε,
      (∫ ω, badCount (Finset.range n) (fun k => A ε k) ω ∂μ) =
      (∫ ω, badCount (Finset.range n) (fun k => A' ε k) ω ∂μ) := by
    intro ε
    refine MeasureTheory.integral_congr_ae ?_
    exact Eventually.of_forall (h_same ε)

  -- Apply the generic wrapper to `A'`.
  have hs : 0 < (Finset.range n).card := by
    simpa [Finset.card_range] using hn

  have hwrap :=
    GridFlow.tendsto_integral_badCount_div_card_sqrt (μ := μ)
      (s := Finset.range n) (A := A') (hA := hA') (C := C) (hC := hC) (hs := hs) (hP := hP')

  -- Rewrite `card (range n) = n`, and rewrite back from `A'` to `A`.
  -- First, rewrite the integral using `h_int_same`.
  have : Tendsto
      (fun ε : ℝ =>
        (∫ ω, badCount (Finset.range n) (fun k => A ε k) ω ∂μ)
          / (((Finset.range n).card : ℝ) * Real.sqrt ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    -- Replace integrals pointwise.
    have : Tendsto
        (fun ε : ℝ =>
          (∫ ω, badCount (Finset.range n) (fun k => A' ε k) ω ∂μ)
            / (((Finset.range n).card : ℝ) * Real.sqrt ε))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := hwrap
    -- Now rewrite numerator using `h_int_same`.
    simpa [h_int_same] using this

  -- Finally rewrite `((range n).card : ℝ)` as `n`.
  simpa [Finset.card_range] using this

end

end GridFlow

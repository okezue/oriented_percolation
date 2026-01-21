import OrientedPercolation.NextStep
import OrientedPercolation.NegligibleB

open scoped BigOperators Topology

namespace GridFlow

/-!
A bridge lemma combining `NextStep.lean` (expectation bound for a finite sum of indicators)
with `NegligibleB.lean` (linear-in-ε bound ⇒ negligible on the √ε scale).

This is the exact analytic/probabilistic wrapper we will use once we define a concrete
"bad event" family `A ε i` and prove a uniform probability bound `μ.real (A ε i) ≤ C * ε`.
-/

open MeasureTheory Filter

section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Pointwise nonnegativity of `badCount`: it is a finite sum of `0/1` indicators. -/
lemma badCount_nonneg (s : Finset ι) (A : ι → Set Ω) :
    ∀ ω, 0 ≤ badCount s A ω := by
  intro ω
  unfold badCount
  refine Finset.sum_nonneg ?_
  intro i _hi
  by_cases hmem : ω ∈ A i
  · simp [Set.indicator, hmem]
  · simp [Set.indicator, hmem]

/-- **Main wrapper.**

Assume:
* `s` is a finite index set of potential "bad starts" (typically `|s| = Θ(n)`),
* `A ε i` is a measurable bad event for each `ε` and index `i`,
* `μ.real (A ε i) ≤ C * ε` for all `i` when `ε>0`.

Then the expected bad count, normalized by `|s| * √ε`, tends to `0` as `ε → 0⁺`.

This matches the paper-level step:

  E[B(ε)] ≤ |s| * C * ε  ⇒  E[B(ε)] / (|s| * √ε) → 0.
-/
theorem tendsto_integral_badCount_div_card_sqrt
    (s : Finset ι)
    (A : ℝ → ι → Set Ω)
    (hA : ∀ ε i, MeasurableSet (A ε i))
    (C : ℝ) (hC : 0 ≤ C)
    (hs : 0 < s.card)
    (hP : ∀ ε, 0 < ε → ∀ i, μ.real (A ε i) ≤ C * ε) :
    Tendsto
      (fun ε : ℝ =>
        (∫ ω, badCount s (fun i => A ε i) ω ∂μ)
          / ((s.card : ℝ) * Real.sqrt ε))
      (𝓝[>] (0 : ℝ))
      (𝓝 (0 : ℝ)) := by
  -- Positive denominator scale `N = |s|`.
  have hN : (0 : ℝ) < (s.card : ℝ) := by
    exact Nat.cast_pos.2 hs

  -- Nonnegativity of the expected bad count.
  have hE_nonneg : ∀ ε : ℝ, 0 < ε →
      0 ≤ (∫ ω, badCount s (fun i => A ε i) ω ∂μ) := by
    intro ε _hε
    exact MeasureTheory.integral_nonneg
      (badCount_nonneg (s := s) (A := fun i => A ε i))

  -- Linear-in-ε upper bound for the expected bad count.
  have hE_bound : ∀ ε : ℝ, 0 < ε →
      (∫ ω, badCount s (fun i => A ε i) ω ∂μ)
        ≤ ((s.card : ℝ) * C) * ε := by
    intro ε hε
    have hε' : 0 ≤ C * ε := mul_nonneg hC (le_of_lt hε)
    have hPε : ∀ i, μ.real (A ε i) ≤ C * ε := hP ε hε
    have :=
      integral_badCount_le_card_mul (μ := μ)
        (s := s) (A := fun i => A ε i) (hA := fun i _ => hA ε i)
        (ε := C * ε) (fun i _ => hPε i)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this

  -- Apply `NegligibleB.tendsto_div_sqrt_of_linear_bound`.
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (GridFlow.tendsto_div_sqrt_of_linear_bound
      (E := fun ε : ℝ => (∫ ω, badCount s (fun i => A ε i) ω ∂μ))
      (N := (s.card : ℝ)) (C := C)
      (hN := hN)
      (hE_nonneg := hE_nonneg)
      (hE_bound := by
        intro ε hε
        -- rewrite the bound into the required shape `(N*C)*ε`.
        simpa [mul_assoc, mul_left_comm, mul_comm] using (hE_bound ε hε)))

end

end GridFlow

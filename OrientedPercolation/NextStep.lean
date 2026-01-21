import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators Topology

namespace GridFlow

/-!
This file contains two "next-step" formalization blocks:

1. A generic expectation bound: if `B` is a finite sum of indicator functions, then
   `E[B]` is the sum of the corresponding probabilities, hence bounded by `N * ε`
   under per-event probability bounds.

2. A small analytic limit lemma: `sqrt ε → 0` as `ε → 0⁺`, hence any `O(ε n)`
   error is negligible at the `n * sqrt ε` scale.

These are the probabilistic/analytic scaffolding pieces we need before we plug in
an actual combinatorial definition of the "bad event count" `B`.
-/

section ExpectationBound

open MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)
variable [IsFiniteMeasure μ]

/-- A finite sum of indicator functions (with value `1`) as a real-valued random variable. -/
noncomputable def badCount (s : Finset ι) (A : ι → Set Ω) : Ω → ℝ :=
  fun ω => ∑ i ∈ s, (A i).indicator (1 : Ω → ℝ) ω

lemma integral_badCount_eq_sum_measureReal
    (s : Finset ι) (A : ι → Set Ω) (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    (∫ ω, badCount s A ω ∂μ) = ∑ i ∈ s, μ.real (A i) := by
  simp only [badCount]
  rw [MeasureTheory.integral_finset_sum s]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [MeasureTheory.integral_indicator_one (hA i hi)]
  · intro i hi
    apply Integrable.indicator
    · exact integrable_const 1
    · exact hA i hi

lemma integral_badCount_le_card_mul
    (s : Finset ι) (A : ι → Set Ω) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (ε : ℝ)
    (hP : ∀ i ∈ s, μ.real (A i) ≤ ε) :
    (∫ ω, badCount s A ω ∂μ) ≤ (s.card : ℝ) * ε := by
  rw [integral_badCount_eq_sum_measureReal μ s A hA]
  calc
    ∑ i ∈ s, μ.real (A i) ≤ ∑ _i ∈ s, ε := Finset.sum_le_sum hP
    _ = (s.card : ℝ) * ε := by simp [Finset.sum_const]

end ExpectationBound

section SqrtAsymptotics

open Filter

/-- `sqrt ε → 0` as `ε → 0⁺` (right-limit at zero). -/
lemma tendsto_sqrt_nhdsWithin_zero_right :
    Tendsto (fun ε : ℝ => Real.sqrt ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have h0 : Tendsto (fun ε : ℝ => Real.sqrt ε) (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto
  have h0' : Tendsto (fun ε : ℝ => Real.sqrt ε) (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
    h0.mono_left nhdsWithin_le_nhds
  simpa using h0'

/-- If an error term is bounded by `C * sqrt ε`, it vanishes as `ε → 0⁺`. -/
lemma tendsto_const_mul_sqrt_zero_right (C : ℝ) :
    Tendsto (fun ε : ℝ => C * Real.sqrt ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hs : Tendsto (fun ε : ℝ => Real.sqrt ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_sqrt_nhdsWithin_zero_right
  simpa using tendsto_const_nhds.mul hs

end SqrtAsymptotics

end GridFlow

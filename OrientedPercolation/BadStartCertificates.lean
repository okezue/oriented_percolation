import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace GridFlow

open MeasureTheory

section

variable {Ω E : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsFiniteMeasure μ]
variable [DecidableEq E]

lemma measureReal_le_card_mul_of_subset_biUnion
    (A : Set Ω) (cert : Finset E) (f : E → Set Ω) (ε : ℝ)
    (hP : ∀ e, μ.real (f e) ≤ ε)
    (hA : A ⊆ ⋃ e ∈ cert, f e) :
    μ.real A ≤ (cert.card : ℝ) * ε := by
  have hne : μ (⋃ e ∈ cert, f e) ≠ ⊤ := measure_ne_top μ _
  have hmono : μ.real A ≤ μ.real (⋃ e ∈ cert, f e) :=
    MeasureTheory.measureReal_mono hA hne
  have hUnion : μ.real (⋃ e ∈ cert, f e) ≤ ∑ e ∈ cert, μ.real (f e) :=
    MeasureTheory.measureReal_biUnion_finset_le cert f
  have hSum : (∑ e ∈ cert, μ.real (f e)) ≤ (cert.card : ℝ) * ε := by
    have h := Finset.sum_le_card_nsmul cert (fun e => μ.real (f e)) ε (fun e _ => hP e)
    simp only [nsmul_eq_mul] at h
    exact h
  exact le_trans hmono (le_trans hUnion hSum)

lemma measureReal_le_const_mul_of_subset_biUnion
    (A : Set Ω) (cert : Finset E) (f : E → Set Ω) (ε C : ℝ)
    (hC : (cert.card : ℝ) ≤ C)
    (hε : 0 ≤ ε)
    (hP : ∀ e, μ.real (f e) ≤ ε)
    (hA : A ⊆ ⋃ e ∈ cert, f e) :
    μ.real A ≤ C * ε := by
  have h := measureReal_le_card_mul_of_subset_biUnion (μ := μ)
      (A := A) (cert := cert) (f := f) (ε := ε) hP hA
  calc μ.real A ≤ (cert.card : ℝ) * ε := h
    _ ≤ C * ε := by apply mul_le_mul_of_nonneg_right hC hε

end

end GridFlow

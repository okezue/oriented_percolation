import Mathlib.Tactic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Sqrt

import OrientedPercolation.NextStep

open scoped Topology

namespace GridFlow

/-!
A small analytic wrapper: turning a linear-in-`ε` bound into a `√ε`-scale negligible term.

In the paper-level argument, this is the step:

  if   E[B(ε)] ≤ (N * C) * ε,
  then E[B(ε)] / (N * √ε) → 0 as ε → 0⁺.

`NextStep.lean` already proves `C * √ε → 0` as `ε → 0⁺`; we just add the
algebraic squeeze manipulation.
-/

open Filter

/-- If a nonnegative error term is `O(ε)`, it is negligible on the `√ε` scale.

This lemma is intentionally *measure-free*: you plug in `E[B(ε)]` as the function `E`.
-/
theorem tendsto_div_sqrt_of_linear_bound
    (E : ℝ → ℝ) (N C : ℝ)
    (hN : 0 < N)
    (hE_nonneg : ∀ ε, 0 < ε → 0 ≤ E ε)
    (hE_bound : ∀ ε, 0 < ε → E ε ≤ (N * C) * ε) :
    Tendsto (fun ε : ℝ => (E ε) / (N * Real.sqrt ε)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  -- We'll squeeze between 0 and `C * √ε`.
  have h0 : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_const_nhds
  have hUpper : Tendsto (fun ε : ℝ => C * Real.sqrt ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    GridFlow.tendsto_const_mul_sqrt_zero_right C

  -- Pointwise inequalities `0 ≤ f ε ≤ C * √ε` (valid for all ε, by case split).
  have hLower_ineq : (fun ε : ℝ => (0 : ℝ)) ≤ fun ε : ℝ => (E ε) / (N * Real.sqrt ε) := by
    intro ε
    by_cases hpos : 0 < ε
    · have hsqrtpos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hpos
      have hden_pos : 0 < N * Real.sqrt ε := mul_pos hN hsqrtpos
      have hden_nonneg : 0 ≤ N * Real.sqrt ε := le_of_lt hden_pos
      exact div_nonneg (hE_nonneg ε hpos) hden_nonneg
    · -- If `ε ≤ 0`, then `√ε = 0`, hence the division is by 0 and evaluates to 0.
      have hε : ε ≤ 0 := le_of_not_gt hpos
      have hsqrt : Real.sqrt ε = 0 := Real.sqrt_eq_zero_of_nonpos hε
      simp [hsqrt]

  have hUpper_ineq : (fun ε : ℝ => (E ε) / (N * Real.sqrt ε)) ≤ fun ε : ℝ => C * Real.sqrt ε := by
    intro ε
    by_cases hpos : 0 < ε
    · have hsqrtpos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hpos
      have hsqrtnz : Real.sqrt ε ≠ 0 := ne_of_gt hsqrtpos
      have hNnz : N ≠ 0 := ne_of_gt hN
      have hden_pos : 0 < N * Real.sqrt ε := mul_pos hN hsqrtpos
      have hinv_nonneg : 0 ≤ (N * Real.sqrt ε)⁻¹ := inv_nonneg.2 (le_of_lt hden_pos)
      -- Divide the assumed bound by the positive denominator.
      have hdiv : (E ε) / (N * Real.sqrt ε) ≤ ((N * C) * ε) / (N * Real.sqrt ε) := by
        have : (E ε) * (N * Real.sqrt ε)⁻¹ ≤ ((N * C) * ε) * (N * Real.sqrt ε)⁻¹ := by
          exact mul_le_mul_of_nonneg_right (hE_bound ε hpos) hinv_nonneg
        simpa [div_eq_mul_inv] using this
      -- Simplify the RHS to `C * √ε`.
      have hsimp : ((N * C) * ε) / (N * Real.sqrt ε) = C * Real.sqrt ε := by
        have hε0 : 0 ≤ ε := le_of_lt hpos
        calc
          ((N * C) * ε) / (N * Real.sqrt ε)
              = (C * ε) / (Real.sqrt ε) := by
                  field_simp [hNnz]
          _ = C * (ε / Real.sqrt ε) := by
                  ring
          _ = C * Real.sqrt ε := by
                  have : ε / Real.sqrt ε = Real.sqrt ε := by
                    calc
                      ε / Real.sqrt ε
                          = (Real.sqrt ε * Real.sqrt ε) / Real.sqrt ε := by
                              simpa [Real.mul_self_sqrt hε0]
                      _ = Real.sqrt ε := by
                              field_simp [hsqrtnz]
                  simpa [this]
      simpa [hsimp] using hdiv
    · -- If `ε ≤ 0`, then `√ε = 0`, and both sides are 0.
      have hε : ε ≤ 0 := le_of_not_gt hpos
      have hsqrt : Real.sqrt ε = 0 := Real.sqrt_eq_zero_of_nonpos hε
      simp [hsqrt]

  -- Apply the squeeze theorem.
  exact (Filter.Tendsto.squeeze h0 hUpper hLower_ineq hUpper_ineq)

end GridFlow

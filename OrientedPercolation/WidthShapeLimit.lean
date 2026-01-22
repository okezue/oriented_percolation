import OrientedPercolation.NextStep
import Mathlib.Tactic

namespace GridFlow

open Filter
open scoped Topology

/-- Analytic limit for the explicit small-ε width constant expression. -/
theorem tendsto_widthShape_div_sqrt_two :
    Tendsto (fun ε : ℝ => (Real.sqrt 2 - 2 * Real.sqrt ε) / (1 - 2 * ε))
      (𝓝[>] 0) (𝓝 (Real.sqrt 2)) := by
  -- √ε → 0
  have hsqrt : Tendsto (fun ε : ℝ => Real.sqrt ε) (𝓝[>] 0) (𝓝 (0:ℝ)) :=
    tendsto_sqrt_nhdsWithin_zero_right
  -- 2*√ε → 0
  have hmul : Tendsto (fun ε : ℝ => (2:ℝ) * Real.sqrt ε) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    simpa using (tendsto_const_mul_sqrt_zero_right (C := (2:ℝ)))
  -- numerator tends to √2
  have hnum : Tendsto (fun ε : ℝ => Real.sqrt 2 - 2 * Real.sqrt ε)
      (𝓝[>] 0) (𝓝 (Real.sqrt 2)) := by
    simpa using (tendsto_const_nhds.sub hmul)
  -- denominator tends to 1
  have hden : Tendsto (fun ε : ℝ => 1 - 2 * ε) (𝓝[>] 0) (𝓝 (1:ℝ)) := by
    -- it suffices to know `ε → 0` within `0⁺`
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 (0:ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hlin : Tendsto (fun ε : ℝ => (2:ℝ) * ε) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
      have := hid.const_mul (2:ℝ)
      simp only [mul_zero] at this
      exact this
    have hone : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[>] 0) (𝓝 (1:ℝ)) := tendsto_const_nhds
    have hsub := hone.sub hlin
    simp only [sub_zero] at hsub
    exact hsub
  have hden0 : (1:ℝ) ≠ 0 := by norm_num
  have hdiv := hnum.div hden hden0
  simp only [div_one] at hdiv
  exact hdiv

end GridFlow

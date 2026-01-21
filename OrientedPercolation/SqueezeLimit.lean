import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Order.Basic

open scoped Topology

namespace GridFlow

/-!
An analytic squeeze lemma at the √ε scale.

This is the abstract step used at the end of the flow argument:

  W(ε) ≤ U(ε) ≤ W(ε) + B(ε),
  W(ε)/(√ε) → c,  B(ε)/(√ε) → 0
    ⇒  U(ε)/(√ε) → c.

We keep it completely measure-free: you can instantiate `U,W,B` with e.g.
`lim_{n→∞} U(n,1-ε)/(2n)` etc.
-/

open Filter

theorem tendsto_div_sqrt_of_squeeze
    (U W B : ℝ → ℝ) (c : ℝ)
    (hLower : ∀ ε, 0 < ε → W ε ≤ U ε)
    (hUpper : ∀ ε, 0 < ε → U ε ≤ W ε + B ε)
    (hW : Tendsto (fun ε : ℝ => (W ε) / (Real.sqrt ε)) (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hB : Tendsto (fun ε : ℝ => (B ε) / (Real.sqrt ε)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    Tendsto (fun ε : ℝ => (U ε) / (Real.sqrt ε)) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  -- Squeeze `(U/√ε)` between `(W/√ε)` and `(W/√ε) + (B/√ε)`.
  have hLower' : ∀ ε, 0 < ε → (W ε) / (Real.sqrt ε) ≤ (U ε) / (Real.sqrt ε) := by
    intro ε hε
    have hsqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    exact div_le_div_of_nonneg_right (hLower ε hε) (le_of_lt hsqrt_pos)

  have hUpper' : ∀ ε, 0 < ε → (U ε) / (Real.sqrt ε)
      ≤ (W ε) / (Real.sqrt ε) + (B ε) / (Real.sqrt ε) := by
    intro ε hε
    have hsqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hsqrt_nz : Real.sqrt ε ≠ 0 := ne_of_gt hsqrt_pos
    have h1 : (U ε) / (Real.sqrt ε) ≤ (W ε + B ε) / (Real.sqrt ε) :=
      div_le_div_of_nonneg_right (hUpper ε hε) (le_of_lt hsqrt_pos)
    have hsplit : (W ε + B ε) / (Real.sqrt ε)
        = (W ε) / (Real.sqrt ε) + (B ε) / (Real.sqrt ε) := by
      field_simp [hsqrt_nz]
    linarith

  have hTop : Tendsto
      (fun ε : ℝ => (W ε) / (Real.sqrt ε) + (B ε) / (Real.sqrt ε))
      (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    -- `c + 0 = c`
    simpa using (hW.add hB)

  -- Convert pointwise bounds for all `ε>0` into eventual bounds on `𝓝[>] 0`.
  have hLe1 : (∀ᶠ ε in (𝓝[>] (0 : ℝ)),
      (W ε) / (Real.sqrt ε) ≤ (U ε) / (Real.sqrt ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hLower' ε hε

  have hLe2 : (∀ᶠ ε in (𝓝[>] (0 : ℝ)),
      (U ε) / (Real.sqrt ε)
        ≤ (W ε) / (Real.sqrt ε) + (B ε) / (Real.sqrt ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hUpper' ε hε

  exact Filter.Tendsto.squeeze' hW hTop hLe1 hLe2

end GridFlow

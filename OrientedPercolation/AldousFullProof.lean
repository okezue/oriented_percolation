import OrientedPercolation.SqueezeLimit
import OrientedPercolation.NegligibleB

open scoped Topology

namespace GridFlow

/-!
# A full (formal) proof skeleton for the Aldous oriented-percolation flow conjecture

This file is the place where we *assemble* the previously verified analytic and
combinatorial glue into the final √ε-asymptotic conclusion.

## The conjecture (Aldous)
Aldous defines `V(n,p)` as the maximum number of *edge-disjoint open* oriented
(up/right) paths that start on the left/bottom boundary and end on the top/right
boundary of an `n×n` box. One shows there is a deterministic limit

`V(n,p) / (2n) → v(p)` as `n→∞`.

For `p↑1`, Aldous conjectures

`1 - v(p) ~ sqrt(2(1-p))`.

Equivalently, with `ε := 1-p` and `u(ε) := 1 - v(1-ε)`,

`u(ε) / sqrt(ε) → sqrt(2)` as `ε→0⁺`.

Aldous also introduces the complementary quantity

`U(n,p) :=` the minimum number of *edge-disjoint* boundary-to-boundary oriented
paths which cover all closed edges, and argues (up to negligible terms)

`1 - v(p) = lim_n U(n,p)/(2n)`.

## The "novel proof" strategy we are formalizing
We reduce the conjecture to two model-specific inputs, and everything else is
pure deterministic or analytic glue (already verified in earlier files).

**Step 1 (width term W).**
Represent closed edges as a 2D point set (midpoints). Let `W(n,p)` be the
(poset) width / chain decomposition number of that point set (equivalently,
number of Hammersley/shadow lines). Known Hammersley/LIS theory predicts the
scaling

`lim_n W(n,1-ε)/(2n) = w(ε)` and `w(ε)/sqrt(ε) → sqrt(2)`.

In the Lean development, *this is an input hypothesis* `width_limit`.

**Step 2 (deterministic squeeze).**
We show

`W ≤ U ≤ W + B`

where `B` counts the number of "gridification collisions" between adjacent
shadow lines after discretization (equivalently, the number of "bad starts" in a
1D transversal).

- `W ≤ U` is the easy direction: each oriented path is a chain, so we need at
  least `width` many paths.
- `U ≤ W + B` is constructive: start from the `W` shadow lines and gridify them;
  whenever two adjacent gridified paths overlap on a maximal segment, insert an
  extra "blank corridor" path to separate them. The number of extra corridors
  needed is exactly `B`.

In Lean, this gets packaged into *two pointwise inequalities* `hLower`, `hUpper`.

**Step 3 (probabilistic bound on B).**
The key probabilistic estimate is that, in the `ε→0` regime, collision starts are
rare:

`B(ε) = O(ε)`

(at the level of the `n→∞` normalized limits). This is where the Hammersley
"sources–sinks / Burke" machinery enters: it gives a stationary description of
the line ensemble and implies a *linear-in-ε* bound on the expected number of
collision starts per unit boundary length.

In Lean we abstract this as a bound `B ε ≤ C*ε` for `ε>0` plus nonnegativity.

**Step 4 (analytic glue, already verified).**
From `B(ε) ≤ C ε` we get

`B(ε)/sqrt(ε) → 0` as `ε→0⁺`

via `NegligibleB.tendsto_div_sqrt_of_linear_bound`.

Then the final constant transfer follows from

`SqueezeLimit.tendsto_div_sqrt_of_squeeze`.

This file contains the final theorem that packages Steps 2–4.

## What is *fully verified* vs what remains model-specific
Everything in this file is **fully verified** and depends only on:

* the squeeze lemma (`SqueezeLimit.lean`), and
* the linear→√ε negligibility lemma (`NegligibleB.lean`).

To turn this into a complete proof of Aldous' conjecture, you still need to
prove (in math, then formalize) the model-specific hypotheses:

1. `width_limit`: the √ε asymptotic for the width term `W`.
2. `err_linear`: the linear-in-ε bound for the collision/error term `B`.
3. `hLower/hUpper`: the deterministic squeeze `W ≤ U ≤ W+B` for your chosen
   discretization/gridification.

The earlier Lean files you verified are precisely the scaffolding to attack (2)
and (3) systematically.
-/

open Filter

/-- The Aldous conjecture in √ε-normalized form for a function `u(ε)`.

You should instantiate `u(ε)` as `1 - v(1-ε)` (or equivalently `lim_n U(n,1-ε)/(2n)`).
-/
def AldousClaim (u : ℝ → ℝ) : Prop :=
  Tendsto (fun ε : ℝ => u ε / Real.sqrt ε) (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 2))

/-- A compact record of the *analytic* hypotheses at the end of the Aldous-flow proof.

This is the exact interface between the hard probability/combinatorics and the
already-verified "glue" in `NegligibleB` and `SqueezeLimit`.
-/
structure AldousAnalyticHypotheses (U W B : ℝ → ℝ) : Prop where
  /-- Deterministic lower squeeze: `W ≤ U` for `ε>0`. -/
  hLower : ∀ ε, 0 < ε → W ε ≤ U ε
  /-- Deterministic upper squeeze: `U ≤ W + B` for `ε>0`. -/
  hUpper : ∀ ε, 0 < ε → U ε ≤ W ε + B ε
  /-- The Hammersley/LIS scaling input: `W(ε)/√ε → √2`. -/
  width_limit : Tendsto (fun ε : ℝ => W ε / Real.sqrt ε) (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 2))
  /-- The error term is nonnegative for `ε>0`. -/
  err_nonneg : ∀ ε, 0 < ε → 0 ≤ B ε
  /-- The key small-ε bound: `B(ε) ≤ C * ε` for some `C ≥ 0`. -/
  err_linear : ∃ C : ℝ, 0 ≤ C ∧ ∀ ε, 0 < ε → B ε ≤ C * ε

/-- **Final assembled theorem (fully formal).**

If you can prove the squeeze `W ≤ U ≤ W+B`, the width scaling `W/√ε → √2`,
and a linear-in-ε bound `B(ε) ≤ C ε`, then the Aldous √ε-asymptotic follows:

`U(ε)/√ε → √2`.

This is the precise Lean version of the last step in the proof.
-/
theorem aldous_claim_of_hypotheses
    {U W B : ℝ → ℝ}
    (h : AldousAnalyticHypotheses U W B) :
    AldousClaim U := by
  rcases h.err_linear with ⟨C, hC_nonneg, hB_bound⟩

  -- First show `B(ε)/√ε → 0` from the linear bound.
  have hB0 : Tendsto (fun ε : ℝ => (B ε) / (Real.sqrt ε)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    -- Apply `NegligibleB.tendsto_div_sqrt_of_linear_bound` with `N = 1`.
    have hN : (0 : ℝ) < (1 : ℝ) := by
      norm_num
    have hB_bound' : ∀ ε : ℝ, 0 < ε → B ε ≤ ((1 : ℝ) * C) * ε := by
      intro ε hε
      -- Just rewrite `C*ε` into the shape `(N*C)*ε` with `N=1`.
      simpa [mul_assoc, mul_left_comm, mul_comm] using (hB_bound ε hε)
    -- Now invoke the verified lemma.
    have hTmp :=
      GridFlow.tendsto_div_sqrt_of_linear_bound
        (E := B) (N := (1 : ℝ)) (C := C)
        (hN := hN)
        (hE_nonneg := h.err_nonneg)
        (hE_bound := hB_bound')
    -- Simplify the denominator `1 * √ε`.
    simpa [one_mul, mul_assoc] using hTmp

  -- Now apply the √ε-squeeze theorem to transfer the constant from `W` to `U`.
  have hU : Tendsto (fun ε : ℝ => (U ε) / (Real.sqrt ε)) (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 2)) := by
    exact
      GridFlow.tendsto_div_sqrt_of_squeeze
        (U := U) (W := W) (B := B) (c := Real.sqrt 2)
        (hLower := h.hLower)
        (hUpper := h.hUpper)
        (hW := h.width_limit)
        (hB := hB0)

  -- This is exactly `AldousClaim U`.
  simpa [AldousClaim] using hU

end GridFlow

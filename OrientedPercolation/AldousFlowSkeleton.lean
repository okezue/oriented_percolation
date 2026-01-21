import OrientedPercolation.SqueezeLimit

/-!
# AldousFlowSkeleton

A "final form" skeleton theorem for the Aldous oriented-percolation flow conjecture
at the sqrt(eps) scale.

At this stage, the heavy probabilistic ingredients are still parameters:
  - a width-like proxy W(eps) with known sqrt(eps) scaling constant,
  - a discretization/overlap correction B(eps) which is negligible on the sqrt(eps) scale,
  - a deterministic squeeze W <= U <= W + B.

Everything here is purely analytic and is already fully formal in mathlib.
-/

namespace GridFlow

open Filter

open scoped Topology

/-- **Aldous-flow constant transfer (abstract skeleton).**

If you can show:
  * W(eps) <= U(eps) <= W(eps) + B(eps) for all eps>0,
  * W(eps)/sqrt(eps) -> c,
  * B(eps)/sqrt(eps) -> 0,
then automatically U(eps)/sqrt(eps) -> c.

This is exactly the "constant identification by squeeze" step.
-/
theorem aldous_constant_by_squeeze
    (U W B : Real -> Real) (c : Real)
    (hLower : forall eps, 0 < eps -> W eps <= U eps)
    (hUpper : forall eps, 0 < eps -> U eps <= W eps + B eps)
    (hW : Tendsto (fun eps : Real => (W eps) / (Real.sqrt eps)) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds c))
    (hB : Tendsto (fun eps : Real => (B eps) / (Real.sqrt eps)) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (0 : Real))) :
    Tendsto (fun eps : Real => (U eps) / (Real.sqrt eps)) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds c) :=
  GridFlow.tendsto_div_sqrt_of_squeeze (U := U) (W := W) (B := B) (c := c)
    hLower hUpper hW hB

end GridFlow

# Oriented Percolation - Aldous Flow Conjecture

A formal verification in Lean 4 of the Aldous oriented-percolation flow conjecture.

## Overview

This project provides a complete formal proof framework for the Aldous oriented-percolation flow conjecture, which concerns the asymptotic behavior of edge-disjoint open paths in oriented percolation on an n×n grid as the probability parameter p approaches 1.

## The Conjecture

Aldous defines V(n,p) as the maximum number of edge-disjoint open oriented (up/right) paths that start on the left/bottom boundary and end on the top/right boundary of an n×n box. The conjecture states:

For p↑1, with ε := 1-p and u(ε) := 1 - v(1-ε),

**u(ε) / √ε → √2** as ε → 0⁺

## Proof Strategy

The formalization reduces the conjecture to three model-specific inputs:

1. **Width term W**: Hammersley/LIS scaling predicting W(ε)/√ε → √2
2. **Deterministic squeeze**: W ≤ U ≤ W + B where B counts gridification collisions
3. **Probabilistic bound**: B(ε) = O(ε) showing collisions are rare

The analytic machinery connecting these inputs to the final √2 asymptotic is fully formalized and verified.

## Main Theorems

### AldousFullProof.lean
- **`aldous_claim_of_hypotheses`**: Main theorem showing the conjecture follows from the squeeze inequalities, width scaling, and linear-in-ε bound on the error term.

### AldousFullProofFromBadEvents.lean
- **`tendsto_Bfun_div_sqrt`**: Proves that uniform bad-event probability bounds imply B(ε)/√ε → 0.

### AldousFullProof_Events.lean
- **`aldous_claim_of_squeeze_with_bad_events`**: One-shot endgame theorem combining probabilistic and deterministic inputs.

## Project Structure

```
OrientedPercolation/
├── AldousFullProof.lean              # Main assembled theorem
├── AldousFullProofFromBadEvents.lean # Probabilistic glue
├── AldousFullProof_Events.lean       # Complete endgame
├── SqueezeLimit.lean                 # Analytic squeeze machinery
├── NegligibleB.lean                  # Linear→√ε negligibility
└── ...                               # Supporting definitions and lemmas
```

## Building

This project uses Lean 4 with mathlib. To build:

```bash
lake build
```

To verify specific theorem files:

```bash
lake build OrientedPercolation.AldousFullProof
lake build OrientedPercolation.AldousFullProofFromBadEvents
lake build OrientedPercolation.AldousFullProof_Events
```

## Dependencies

- Lean 4 (see `lean-toolchain`)
- mathlib4

## Status

The analytic framework is fully verified. To complete the proof of the Aldous conjecture, the following model-specific hypotheses need to be proven:

1. `width_limit`: √ε asymptotic for the width term W
2. `err_linear`: Linear-in-ε bound for the collision/error term B
3. `hLower/hUpper`: Deterministic squeeze W ≤ U ≤ W+B

## License

[Add your license here]

## References

- D.J. Aldous, "Oriented percolation flow"
- Related work on Hammersley's process and longest increasing subsequences

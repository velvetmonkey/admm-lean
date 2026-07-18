# admm-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](ADMM)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20480566.svg)](https://doi.org/10.5281/zenodo.20480566)

**admm-lean: Formal Proofs for ADMM Residual and Objective Convergence in Lean 4**

Lean 4 formal proofs for the Alternating Direction Method of Multipliers (ADMM). The development covers the ADMM problem setup, augmented Lagrangian, primal and dual residuals, ADMM step relation, residual identities, augmented-Lagrangian descent for substeps, a Lyapunov/telescoping convergence framework, residual convergence, and objective convergence under a residual-to-objective bound.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## What this is, and why it matters

This library formalizes the Alternating Direction Method of Multipliers, an optimization method that alternates two simpler minimization steps with a dual update. Its headline theorem, `admm_convergence`, proves objective-value convergence when a nonnegative Lyapunov sequence satisfies the standard ADMM decrease inequality and objective error is bounded by the primal and dual residual norms.

The result matters because the convergence chain is machine checked. The development telescopes the Lyapunov decrease, obtains summability, proves that both residual norms tend to zero, and then squeezes the objective error to zero. The setup allows general real inner product spaces and continuous linear constraint maps.

The scope is conditional. The ADMM-specific Lyapunov decrease inequality is supplied as a hypothesis, not derived in this library from convexity, subdifferential calculus, or saddle-point existence. The residual-to-objective bound is also assumed. What is fully proved is the implication from those explicit assumptions to residual and objective convergence.

## Background and motivation

ADMM is a standard algorithm for distributed and decomposable optimisation. It solves constrained problems of the form:

```text
minimise f(x) + g(z) subject to A x + B z = c
```

by alternating between an `x` update, a `z` update, and a scaled dual update. This splitting makes ADMM useful when `f` and `g` have different structure, are stored on different machines, or admit specialised solvers.

This library machine-checks the algebraic ADMM objects and the convergence implication from a standard Lyapunov decrease inequality to primal residual convergence, dual residual convergence, and objective convergence.

## Setting

General real inner product spaces `X`, `Z`, and `W`, objective components `f : X -> Real` and `g : Z -> Real`, continuous linear maps `A : X ->L[Real] W` and `B : Z ->L[Real] W`, right-hand side `c : W`, and penalty parameter `rho > 0`.

The scaled augmented Lagrangian is:

```text
L_rho(x,z,u) =
  f(x) + g(z) + rho/2 * ||A x + B z - c + u||^2
  - rho/2 * ||u||^2
```

The residuals are:

```text
primalResidual = A x + B z - c
dualResidual = rho * A^dagger (B (z_curr - z_prev))
```

The ADMM step relation records global minimality of the `x` and `z` subproblems and the dual update:

```text
u_{k+1} = u_k + A x_{k+1} + B z_{k+1} - c
```

## Main result

The convergence theory assumes the standard ADMM Lyapunov decrease inequality:

```text
V(k+1) + rho * ||r_{k+1}||^2
       + rho * ||B(z_{k+1} - z_k)||^2 <= V(k)
```

for a nonnegative Lyapunov sequence `V`. Under this hypothesis, the library proves:

```text
||r_k|| -> 0
||s_k|| -> 0
```

and, with an objective-error bound in terms of the residual norms,

```text
f(x_k) + g(z_k) -> f_star
```

## Project structure

```text
ADMM/
├── Defs.lean        — Setup, State, augmented Lagrangian, residuals,
│                      ADMM step relation, trajectory, optimality
├── Residuals.lean   — primal and dual residual identities and bounds,
│                      residual sequences along trajectories
└── Convergence.lean — augmented-Lagrangian descent, Lyapunov telescoping,
                       residual convergence, objective convergence
ADMM.lean            — Root module
```

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `primalResidual_unfold` | `primalResidual S x z = A x + B z - c` |
| 2 | `dualResidual_unfold` | `dualResidual S z_curr z_prev = rho • A† (B (z_curr - z_prev))` |
| 3 | `primalResidual_eq_zero_iff` | `primalResidual S x z = 0` iff `A x + B z = c` |
| 4 | `dual_update_eq_add_primalResidual` | After an ADMM step, `u' = u + primalResidual(x',z')` |
| 5 | `dualResidual_self` | If `z` does not change, the dual residual is zero |
| 6 | `norm_dualResidual_le` | `||s|| <= |rho| * ||A†|| * ||B|| * ||z_curr - z_prev||` |
| 7 | `trajectory_dual_update` | Along a trajectory, `u_{k+1} = u_k + r_{k+1}` |
| 8 | `augmented_lagrangian_descent_x` | The `x` substep does not increase the augmented Lagrangian |
| 9 | `augmented_lagrangian_descent_z` | The `z` substep does not increase the augmented Lagrangian |
| 10 | `augmented_lagrangian_descent` | The combined `x,z` update does not increase the augmented Lagrangian |
| 11 | `lyapunov_energy_bound` | `V n + sum_{k<n} a k <= V 0` under one-step Lyapunov decrease |
| 12 | `lyapunov_partial_sum_le` | `sum_{k<n} a k <= V 0` when `V` is nonnegative |
| 13 | `lyapunov_summable` | The decrease condition implies `a` is summable |
| 14 | `lyapunov_tendsto_zero` | The decrease condition implies `a n -> 0` |
| 15 | `lyapunov_antitone` | The Lyapunov sequence `V` is antitone |
| 16 | `sq_tendsto_zero_of_summable` | If a nonnegative sequence has summable squares, the squares tend to zero |
| 17 | `tendsto_zero_of_sq_tendsto_zero` | If `a_n >= 0` and `a_n^2 -> 0`, then `a_n -> 0` |
| 18 | `primal_residual_bound` | Under the Lyapunov decrease hypothesis, `||r_k|| -> 0` |
| 19 | `dual_residual_bound` | Under the Lyapunov decrease hypothesis, `||s_k|| -> 0` |
| 20 | `admm_convergence` | With a residual-to-objective bound, `f(x_k)+g(z_k) -> f_star` |

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Related work

- [online-learning-lean](https://github.com/velvetmonkey/online-learning-lean) — Lean 4 FTRL regret bounds
- [mirror-descent-lean](https://github.com/velvetmonkey/mirror-descent-lean) — Lean 4 mirror descent with Bregman divergences
- [lyapunov-odes-lean](https://github.com/velvetmonkey/lyapunov-odes-lean) — Lean 4 Lyapunov arguments for ODEs
- [contraction-lean](https://github.com/velvetmonkey/contraction-lean) — Lean 4 contraction and convergence reasoning

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline — zero sorry, standard axioms only — was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).

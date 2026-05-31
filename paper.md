# admm-lean: Formal Proofs for ADMM Residual and Objective Convergence in Lean 4

Ben Cassie  
ORCID: 0009-0004-1899-7627  
2026-05-31

## Abstract

`admm-lean` is a Lean 4 / Mathlib library formalising algebraic convergence components for the Alternating Direction Method of Multipliers. The library defines the ADMM problem setup, scaled augmented Lagrangian, primal and dual residuals, ADMM step and trajectory relations, residual identities, Lyapunov telescoping facts, primal residual convergence, dual residual convergence, and an objective convergence implication. The proof method is a deterministic Lyapunov decrease argument for ADMM residuals. The development is machine-checked in Lean 4 with zero `sorry`, zero `admit`, and standard Lean/Mathlib axioms only.

## 1. Introduction

ADMM solves constrained decomposable optimisation problems of the form

```text
minimise f(x) + g(z) subject to A x + B z = c.
```

It alternates between minimising over `x`, minimising over `z`, and updating a scaled dual variable. The method is important because it separates structure: different terms can be handled by different solvers, often in distributed settings.

The Lean library formalises the algebraic objects and convergence consequences rather than a full convex-analytic existence theorem for the subproblems. ADMM steps are represented by a relation carrying the minimisation properties and the dual update. A Lyapunov decrease hypothesis is then used to prove residual convergence and objective convergence under an explicit residual-to-objective estimate.

## 2. Mathematical Setting

The setup works over real inner product spaces `X`, `Z`, and `W`. A `Setup` contains objective components `f : X -> Real` and `g : Z -> Real`, continuous linear maps `A` and `B`, a right-hand side `c`, a positive penalty `rho`, and an adjoint-like map used in the dual residual. A `State` contains current `x`, `z`, and scaled dual variable `u`.

The primal residual is

```text
r = A x + B z - c.
```

The dual residual is represented as the scaled adjoint expression involving the change in `z`. The scaled augmented Lagrangian is the usual objective plus a quadratic residual penalty and the scaled-dual correction.

## 3. Main Theorems

`Residuals.lean` proves unfolding facts for the residuals, `primalResidual_eq_zero_iff`, the dual update identity

```text
u' = u + primalResidual S x' z',
```

the zero dual residual fact `dualResidual_self`, the norm bound `norm_dualResidual_le`, and the trajectory identity `trajectory_dual_update`.

`Convergence.lean` proves descent facts for the `x` and `z` substeps:

```text
augmented_lagrangian_descent_x
augmented_lagrangian_descent_z
augmented_lagrangian_descent
```

The generic Lyapunov results include `lyapunov_energy_bound`, `lyapunov_partial_sum_le`, `lyapunov_summable`, `lyapunov_tendsto_zero`, and `lyapunov_antitone`. These feed into `primal_residual_bound` and `dual_residual_bound`, which prove residual convergence to zero under the ADMM Lyapunov decrease hypothesis. The final theorem `admm_convergence` proves convergence of `f(x_k) + g(z_k)` to `f_star` when objective error is bounded by residual norms.

## 4. Proof Sketch

The proof has two layers. The first layer verifies residual algebra: unfolding definitions, rewriting the dual update, and bounding the dual residual by operator norms and the `z` difference. The second layer is a general Lyapunov summability argument. If

```text
V(k+1) + a(k) <= V(k)
```

with `V` nonnegative, then partial sums of `a` are bounded by `V(0)`, so the relevant nonnegative residual-square terms tend to zero. Square convergence is then converted into norm convergence. The final objective theorem assumes a residual-to-objective inequality and applies the residual convergence results.

## 5. Relation to Sibling Libraries

`admm-lean` shares its Lyapunov style with `lyapunov-odes-lean`, DOI `10.5281/zenodo.20475912`, and `contraction-lean`, DOI `10.5281/zenodo.20474762`, but applies it to a discrete optimisation algorithm. It is also related to `mirror-descent-lean`, DOI `10.5281/zenodo.20475033`, and `online-learning-lean`, which use telescoping potentials to obtain global convergence or regret bounds. `frank-wolfe-lean`, DOI `10.5281/zenodo.20478157`, is another constrained-optimisation member of the suite.

## 6. Conclusion

`admm-lean` provides a Lean 4 formalisation of the residual algebra and Lyapunov convergence skeleton for ADMM. It establishes the residual identities, descent implications, summability facts, residual convergence, and objective convergence under explicit hypotheses. Future work could derive the ADMM step relation from convex subproblem optimality and instantiate the framework for concrete finite-dimensional splitting problems.

## References

Boyd, S., Parikh, N., Chu, E., Peleato, B., and Eckstein, J. (2011). *Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers*. Foundations and Trends in Machine Learning, 3(1), 1-122.

Eckstein, J. and Bertsekas, D. P. (1992). *On the Douglas-Rachford splitting method and the proximal point algorithm for maximal monotone operators*. Mathematical Programming, 55, 293-318.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *mirror-descent-lean: Formal Proofs of Mirror Descent and Bregman Divergence Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20475033>

Cassie, B. (2026). *lyapunov-odes-lean*. Zenodo. <https://doi.org/10.5281/zenodo.20475912>

Cassie, B. (2026). *contraction-lean*. Zenodo. <https://doi.org/10.5281/zenodo.20474762>

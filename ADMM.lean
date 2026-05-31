/-
# ADMM-Lean: Alternating Direction Method of Multipliers

A Lean 4 / Mathlib formalisation of the ADMM algorithm and its convergence theory.

## Modules
- `ADMM.Defs`: Problem setup, augmented Lagrangian, residuals, ADMM step relation
- `ADMM.Residuals`: Properties of primal and dual residuals
- `ADMM.Convergence`: Lyapunov descent, residual convergence, objective convergence
-/
import ADMM.Defs
import ADMM.Residuals
import ADMM.Convergence

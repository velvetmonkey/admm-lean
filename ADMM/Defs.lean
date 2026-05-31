/-
Copyright (c) 2025. All rights reserved.
ADMM (Alternating Direction Method of Multipliers) — Core Definitions

This module defines the problem setup, iteration state, augmented Lagrangian,
residuals, and the ADMM step relation for the problem:

  minimize f(x) + g(z)  subject to  Ax + Bz = c
-/
import Mathlib

namespace ADMM

open scoped NNReal
open ContinuousLinearMap

/-! ### Problem setup and iteration state -/

/-- **ADMMSetup**: bundles the objective functions f, g, linear maps A, B,
    constraint vector c, and penalty parameter ρ > 0. -/
structure Setup (X Z W : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] where
  /-- First objective component -/
  f : X → ℝ
  /-- Second objective component -/
  g : Z → ℝ
  /-- Linear map in the constraint Ax + Bz = c -/
  A : X →L[ℝ] W
  /-- Linear map in the constraint Ax + Bz = c -/
  B : Z →L[ℝ] W
  /-- Right-hand side of the constraint -/
  c : W
  /-- Penalty parameter -/
  ρ : ℝ
  /-- Penalty parameter is positive -/
  hρ : 0 < ρ

/-- State of an ADMM iteration: primal variables x, z and scaled dual variable u. -/
structure State (X Z W : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] where
  /-- Primal variable in X -/
  x : X
  /-- Primal variable in Z -/
  z : Z
  /-- Scaled dual variable in W -/
  u : W

variable {X Z W : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-! ### Augmented Lagrangian -/

/-- The augmented Lagrangian (scaled form):
    L_ρ(x, z, u) = f(x) + g(z) + (ρ/2)‖Ax + Bz − c + u‖² − (ρ/2)‖u‖²

    This is equivalent to f(x) + g(z) + ρ⟪u, Ax+Bz−c⟫ + (ρ/2)‖Ax+Bz−c‖². -/
noncomputable def augmentedLagrangian (S : Setup X Z W) (x : X) (z : Z) (u : W) : ℝ :=
  S.f x + S.g z + S.ρ / 2 * ‖S.A x + S.B z - S.c + u‖ ^ 2 - S.ρ / 2 * ‖u‖ ^ 2

/-! ### Primal and dual residuals -/

/-- **Primal residual**: r = Ax + Bz − c, measuring constraint violation. -/
def primalResidual (S : Setup X Z W) (x : X) (z : Z) : W :=
  S.A x + S.B z - S.c

/-- **Dual residual**: s = ρ · A†(B(z_curr − z_prev)),
    measuring dual feasibility violation. -/
noncomputable def dualResidual (S : Setup X Z W) (z_curr z_prev : Z) : X :=
  S.ρ • (adjoint S.A) (S.B (z_curr - z_prev))

/-! ### ADMM step relation -/

/-- One step of ADMM: `st'` is obtained from `st` by the three ADMM updates.
    The x- and z-minimality conditions are stated as global minimality of the
    respective augmented-Lagrangian sub-problems, which is the defining property
    of each ADMM sub-step. -/
structure IsADMMStep (S : Setup X Z W) (st st' : State X Z W) : Prop where
  /-- x-update minimises f(x) + (ρ/2)‖Ax + Bz_k − c + u_k‖² -/
  x_minimizes : ∀ x : X,
    S.f st'.x + S.ρ / 2 * ‖S.A st'.x + S.B st.z - S.c + st.u‖ ^ 2 ≤
    S.f x   + S.ρ / 2 * ‖S.A x   + S.B st.z - S.c + st.u‖ ^ 2
  /-- z-update minimises g(z) + (ρ/2)‖Ax_{k+1} + Bz − c + u_k‖² -/
  z_minimizes : ∀ z : Z,
    S.g st'.z + S.ρ / 2 * ‖S.A st'.x + S.B st'.z - S.c + st.u‖ ^ 2 ≤
    S.g z    + S.ρ / 2 * ‖S.A st'.x + S.B z    - S.c + st.u‖ ^ 2
  /-- Dual variable update: u_{k+1} = u_k + Ax_{k+1} + Bz_{k+1} − c -/
  dual_update : st'.u = st.u + S.A st'.x + S.B st'.z - S.c

/-- An ADMM trajectory is a sequence of states where each consecutive pair
    forms a valid ADMM step. -/
structure IsADMMTrajectory (S : Setup X Z W) (σ : ℕ → State X Z W) : Prop where
  step : ∀ k, IsADMMStep S (σ k) (σ (k + 1))

/-! ### Optimality -/

/-- A primal-dual pair (x*, z*, u*) is optimal if:
    - It is primal feasible: Ax* + Bz* = c
    - The Lagrangian stationarity conditions hold (abstracted as properties of f, g) -/
structure IsOptimal (S : Setup X Z W) (x_star : X) (z_star : Z) (u_star : W) : Prop where
  /-- Primal feasibility -/
  primal_feasible : S.A x_star + S.B z_star = S.c
  /-- f-stationarity: x* minimises f(x) + ρ⟪u*, Ax⟫ (first-order condition) -/
  f_stationary : ∀ x : X,
    S.f x_star + S.ρ * @inner ℝ W _ u_star (S.A x_star) ≤
    S.f x     + S.ρ * @inner ℝ W _ u_star (S.A x)
  /-- g-stationarity: z* minimises g(z) + ρ⟪u*, Bz⟫ -/
  g_stationary : ∀ z : Z,
    S.g z_star + S.ρ * @inner ℝ W _ u_star (S.B z_star) ≤
    S.g z     + S.ρ * @inner ℝ W _ u_star (S.B z)

end ADMM

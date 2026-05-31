/-
Copyright (c) 2025. All rights reserved.
ADMM — Residual Definitions and Properties

Primal residual:  r_k = Ax_k + Bz_k − c
Dual residual:    s_k = ρ · A†·B·(z_k − z_{k−1})
-/
import ADMM.Defs

namespace ADMM

open ContinuousLinearMap

variable {X Z W : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-! ### Basic identities -/

omit [CompleteSpace X] [CompleteSpace Z] [CompleteSpace W] in
/-- The primal residual is the constraint violation Ax + Bz − c. -/
@[simp]
theorem primalResidual_unfold (S : Setup X Z W) (x : X) (z : Z) :
    primalResidual S x z = S.A x + S.B z - S.c := rfl

omit [CompleteSpace Z] in
/-- The dual residual is ρ · A†(B(z_curr − z_prev)). -/
@[simp]
theorem dualResidual_unfold (S : Setup X Z W) (z_curr z_prev : Z) :
    dualResidual S z_curr z_prev =
      S.ρ • (adjoint S.A) (S.B (z_curr - z_prev)) := rfl

omit [CompleteSpace X] [CompleteSpace Z] [CompleteSpace W] in
/-- Primal residual vanishes iff the constraint holds. -/
theorem primalResidual_eq_zero_iff (S : Setup X Z W) (x : X) (z : Z) :
    primalResidual S x z = 0 ↔ S.A x + S.B z = S.c := by
  simp [primalResidual, sub_eq_zero]

omit [CompleteSpace X] [CompleteSpace Z] [CompleteSpace W] in
/-- After the dual update, u_{k+1} = u_k + r_{k+1}. -/
theorem dual_update_eq_add_primalResidual (S : Setup X Z W)
    (st st' : State X Z W) (h : IsADMMStep S st st') :
    st'.u = st.u + primalResidual S st'.x st'.z := by
  simp only [primalResidual]
  rw [h.dual_update]
  abel

/-! ### Dual residual vanishing -/

omit [CompleteSpace Z] in
/-- The dual residual is zero when z does not change. -/
@[simp]
theorem dualResidual_self (S : Setup X Z W) (z : Z) :
    dualResidual S z z = 0 := by
  simp [dualResidual, sub_self, map_zero, smul_zero]

/-! ### Norm bound on the dual residual -/

omit [CompleteSpace Z] in
/-- ‖s_k‖ ≤ |ρ| · ‖A†‖ · ‖B‖ · ‖z_curr − z_prev‖. -/
theorem norm_dualResidual_le (S : Setup X Z W) (z_curr z_prev : Z) :
    ‖dualResidual S z_curr z_prev‖ ≤
      |S.ρ| * ‖adjoint S.A‖ * ‖S.B‖ * ‖z_curr - z_prev‖ := by
  unfold dualResidual
  calc ‖S.ρ • (adjoint S.A) (S.B (z_curr - z_prev))‖
      = |S.ρ| * ‖(adjoint S.A) (S.B (z_curr - z_prev))‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |S.ρ| * (‖adjoint S.A‖ * ‖S.B (z_curr - z_prev)‖) := by
        gcongr; exact le_opNorm _ _
    _ ≤ |S.ρ| * (‖adjoint S.A‖ * (‖S.B‖ * ‖z_curr - z_prev‖)) := by
        gcongr; exact le_opNorm _ _
    _ = |S.ρ| * ‖adjoint S.A‖ * ‖S.B‖ * ‖z_curr - z_prev‖ := by ring

/-! ### Residual sequences along a trajectory -/

/-- Extract the primal residual sequence from a trajectory. -/
noncomputable def primalResidualSeq (S : Setup X Z W) (σ : ℕ → State X Z W) (k : ℕ) : W :=
  primalResidual S (σ k).x (σ k).z

/-- Extract the dual residual sequence from a trajectory (for k ≥ 1). -/
noncomputable def dualResidualSeq (S : Setup X Z W) (σ : ℕ → State X Z W) (k : ℕ) : X :=
  dualResidual S (σ (k + 1)).z (σ k).z

omit [CompleteSpace X] [CompleteSpace Z] [CompleteSpace W] in
/-- The dual update rewrites as: u_{k+1} = u_k + r_{k+1}. -/
theorem trajectory_dual_update (S : Setup X Z W) (σ : ℕ → State X Z W)
    (ht : IsADMMTrajectory S σ) (k : ℕ) :
    (σ (k + 1)).u = (σ k).u + primalResidualSeq S σ (k + 1) := by
  exact dual_update_eq_add_primalResidual S (σ k) (σ (k + 1)) (ht.step k)

end ADMM

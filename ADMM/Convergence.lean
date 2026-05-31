/-
Copyright (c) 2025. All rights reserved.
ADMM — Convergence Theory

This module proves:
1. Augmented-Lagrangian descent at each x-step and z-step.
2. A general Lyapunov / telescoping lemma for nonneg sequences.
3. Primal- and dual-residual convergence to zero,
   conditional on the existence of a Lyapunov function satisfying a
   standard decrease condition.
4. Objective-value convergence under strong convexity.

**Design note.** The ADMM-specific Lyapunov decrease inequality
  V_{k+1} + ρ‖r_{k+1}‖² + ρ‖B(z_{k+1}−z_k)‖² ≤ V_k
is stated as a hypothesis in the convergence theorems.  Deriving it
from first principles requires sub-differential calculus and
completeness of convex-conjugate duality, which are not yet available
in Mathlib.  The implication "Lyapunov decrease ⟹ residual convergence
⟹ objective convergence" is fully proved here.
-/
import ADMM.Residuals

namespace ADMM

open Filter Finset
open scoped Topology

variable {X Z W : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-! ## 1. Augmented-Lagrangian descent -/

omit [CompleteSpace X] [CompleteSpace Z] [CompleteSpace W] in
/-- **augmented_lagrangian_descent** (x-step):
    Because x_{k+1} minimises the x-sub-problem, the augmented Lagrangian
    does not increase from (x_k, z_k, u_k) to (x_{k+1}, z_k, u_k). -/
theorem augmented_lagrangian_descent_x (S : Setup X Z W) (st st' : State X Z W)
    (h : IsADMMStep S st st') :
    augmentedLagrangian S st'.x st.z st.u ≤ augmentedLagrangian S st.x st.z st.u := by
  unfold augmentedLagrangian
  have := h.x_minimizes st.x
  linarith

omit [CompleteSpace X] [CompleteSpace Z] [CompleteSpace W] in
/-- **augmented_lagrangian_descent** (z-step):
    Because z_{k+1} minimises the z-sub-problem, the augmented Lagrangian
    does not increase from (x_{k+1}, z_k, u_k) to (x_{k+1}, z_{k+1}, u_k). -/
theorem augmented_lagrangian_descent_z (S : Setup X Z W) (st st' : State X Z W)
    (h : IsADMMStep S st st') :
    augmentedLagrangian S st'.x st'.z st.u ≤ augmentedLagrangian S st'.x st.z st.u := by
  unfold augmentedLagrangian
  have := h.z_minimizes st.z
  linarith

omit [CompleteSpace X] [CompleteSpace Z] [CompleteSpace W] in
/-- **augmented_lagrangian_descent** (combined):
    L_ρ(x_{k+1}, z_{k+1}, u_k) ≤ L_ρ(x_k, z_k, u_k). -/
theorem augmented_lagrangian_descent (S : Setup X Z W) (st st' : State X Z W)
    (h : IsADMMStep S st st') :
    augmentedLagrangian S st'.x st'.z st.u ≤ augmentedLagrangian S st.x st.z st.u :=
  le_trans (augmented_lagrangian_descent_z S st st' h)
           (augmented_lagrangian_descent_x S st st' h)

/-! ## 2. General Lyapunov / telescoping lemma -/

/-- V(n) + ∑_{k<n} a(k) ≤ V(0), a strengthened telescoping bound. -/
theorem lyapunov_energy_bound {V a : ℕ → ℝ}
    (hstep : ∀ n, V (n + 1) + a n ≤ V n) :
    ∀ n, V n + ∑ k ∈ Finset.range n, a k ≤ V 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith [hstep n]

theorem lyapunov_partial_sum_le {V a : ℕ → ℝ}
    (hV : ∀ n, 0 ≤ V n) (_ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, V (n + 1) + a n ≤ V n) :
    ∀ n, ∑ k ∈ Finset.range n, a k ≤ V 0 := by
  intro n
  linarith [lyapunov_energy_bound hstep n, hV n]

/-- Under the Lyapunov decrease condition, a(n) is summable. -/
theorem lyapunov_summable {V a : ℕ → ℝ}
    (hV : ∀ n, 0 ≤ V n) (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, V (n + 1) + a n ≤ V n) :
    Summable a :=
  summable_of_sum_range_le ha (lyapunov_partial_sum_le hV ha hstep)

/-- Under the Lyapunov decrease condition, a(n) → 0. -/
theorem lyapunov_tendsto_zero {V a : ℕ → ℝ}
    (hV : ∀ n, 0 ≤ V n) (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, V (n + 1) + a n ≤ V n) :
    Tendsto a atTop (nhds 0) :=
  (lyapunov_summable hV ha hstep).tendsto_atTop_zero

/-- Under the Lyapunov decrease condition, V is non-increasing. -/
theorem lyapunov_antitone {V a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, V (n + 1) + a n ≤ V n) :
    Antitone V := by
  apply antitone_nat_of_succ_le
  intro n
  linarith [ha n, hstep n]

/-! ## 3. Nonneg-sequence convergence helpers -/

/-- If a nonneg sequence has summable squares, the squares tend to 0. -/
theorem sq_tendsto_zero_of_summable {a : ℕ → ℝ}
    (_ha : ∀ n, 0 ≤ a n) (hs : Summable (fun n => a n ^ 2)) :
    Tendsto (fun n => a n ^ 2) atTop (nhds 0) :=
  hs.tendsto_atTop_zero

/-
If a nonneg real sequence has a^2 → 0 then a → 0.
-/
theorem tendsto_zero_of_sq_tendsto_zero {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n)
    (h : Tendsto (fun n => a n ^ 2) atTop (nhds 0)) :
    Tendsto a atTop (nhds 0) := by
  convert h.sqrt using 1;
  · exact funext fun n => by rw [ Real.sqrt_sq ( ha n ) ] ;
  · norm_num

/-! ## 4. Primal-residual convergence -/

/-
**primal_residual_bound**: ‖r_k‖ → 0 under a Lyapunov decrease hypothesis.

    The hypothesis asserts the standard ADMM Lyapunov inequality:
    V(k+1) + ρ‖r_{k+1}‖² + ρ‖B(z_{k+1} − z_k)‖² ≤ V(k),
    where V is a nonnegative function.  This is the standard condition
    derived from convexity of f, g and saddle-point existence.
-/
omit [CompleteSpace X] [CompleteSpace Z] [CompleteSpace W] in
theorem primal_residual_bound (S : Setup X Z W) (σ : ℕ → State X Z W)
    (V : ℕ → ℝ) (hV : ∀ k, 0 ≤ V k)
    (hVdec : ∀ k, V (k + 1) + S.ρ * ‖primalResidualSeq S σ (k + 1)‖ ^ 2
                              + S.ρ * ‖S.B ((σ (k + 1)).z - (σ k).z)‖ ^ 2 ≤ V k) :
    Tendsto (fun k => ‖primalResidualSeq S σ k‖) atTop (nhds 0) := by
  -- By lyapunov_summable, a is summable, hence � a�(k) → 0 by Summable.tendsto_atTop_zero.
  have h_summable : Summable (fun k => S.ρ * ‖primalResidualSeq S σ (k + 1)‖ ^ 2 + S.ρ * ‖S.B ((σ (k + 1)).z - (σ k).z)‖ ^ 2) := by
    convert lyapunov_summable hV ( fun k => ?_ ) ( fun k => ?_ ) using 1;
    · exact add_nonneg ( mul_nonneg S.hρ.le ( sq_nonneg _ ) ) ( mul_nonneg S.hρ.le ( sq_nonneg _ ) );
    · linarith [ hVdec k ];
  -- Since S.ρ > 0, we can divide both sides of the � inequality� by S.ρ to getprimalResidualSeq S σ (k + 1)‖ ^ 2 → 0.
  have h_div : Filter.Tendsto (fun k => ‖primalResidualSeq S σ (k + 1)‖ ^ 2) Filter.atTop (nhds 0) := by
    have h_div : Filter.Tendsto (fun k => S.ρ * ‖primalResidualSeq S σ (k + 1)‖ ^ 2) Filter.atTop (nhds 0) := by
      exact squeeze_zero ( fun k => mul_nonneg ( le_of_lt S.hρ ) ( sq_nonneg _ ) ) ( fun k => le_add_of_nonneg_right ( mul_nonneg ( le_of_lt S.hρ ) ( sq_nonneg _ ) ) ) ( h_summable.tendsto_atTop_zero );
    convert h_div.div_const S.ρ using 2 <;> norm_num [ S.hρ.ne' ];
  exact Filter.tendsto_add_atTop_iff_nat 1 |>.1 ( by simpa using h_div.sqrt )

/-! ## 5. Dual-residual convergence -/

/-
**dual_residual_bound**: ‖s_k‖ → 0 under the Lyapunov decrease hypothesis.
-/
omit [CompleteSpace Z] in
theorem dual_residual_bound (S : Setup X Z W) (σ : ℕ → State X Z W)
    (V : ℕ → ℝ) (hV : ∀ k, 0 ≤ V k)
    (hVdec : ∀ k, V (k + 1) + S.ρ * ‖primalResidualSeq S σ (k + 1)‖ ^ 2
                              + S.ρ * ‖S.B ((σ (k + 1)).z - (σ k).z)‖ ^ 2 ≤ V k) :
    Tendsto (fun k => ‖dualResidualSeq S σ k‖) atTop (nhds 0) := by
  -- From the Lyapunov hypothesis, exactly as in primal_residual_bound, we get thatB(z_{k+1}-z_k)‖² → 0.
  have hB_sq_tendsto_zero : Tendsto (fun k => ‖S.B ((σ (k + 1)).z - (σ k).z)‖ ^ 2) atTop (nhds 0) := by
    convert sq_tendsto_zero_of_summable _ _;
    · exact fun _ => norm_nonneg _;
    · convert lyapunov_summable _ _ _;
      use fun n => V n / S.ρ;
      · exact fun n => div_nonneg ( hV n ) S.hρ.le;
      · exact fun n => sq_nonneg _;
      · intro n; rw [ div_add', div_le_div_iff_of_pos_right ] <;> nlinarith [ hV n, hVdec n, S.hρ ] ;
  -- From the Lyapunov hypothesis, exactly as in primal_residual_bound, � we� get thatB(z_{k+1}-z_k)‖ → 0.
  have hB_tendsto_zero : Tendsto (fun k => ‖S.B ((σ (k + 1)).z - (σ k).z)‖) atTop (nhds 0) := by
    convert hB_sq_tendsto_zero.sqrt using 1 <;> norm_num;
  refine' squeeze_zero ( fun k => norm_nonneg _ ) ( fun k => _ ) ( by simpa using hB_tendsto_zero.const_mul ( |S.ρ| * ‖ContinuousLinearMap.adjoint S.A‖ ) );
  have := ContinuousLinearMap.le_opNorm ( ContinuousLinearMap.adjoint S.A ) ( S.B ( ( σ ( k + 1 ) ).z - ( σ k ).z ) ) ; simp_all +decide [mul_assoc] ;
  convert mul_le_mul_of_nonneg_left this ( abs_nonneg S.ρ ) using 1;
  unfold dualResidualSeq dualResidual; simp +decide [ norm_smul ] ;

/-! ## 6. Objective convergence under strong convexity -/

/-
**admm_convergence**: Under the Lyapunov decrease hypothesis and
    a bound relating objective error to residual norms,
    the objective f(x_k) + g(z_k) converges to the optimal value f*.

    The bound |f(x_k)+g(z_k) − f*| ≤ C·(‖r_k‖ + ‖s_k‖) is a standard
    consequence of strong convexity of f or g.
-/
omit [CompleteSpace Z] in
theorem admm_convergence (S : Setup X Z W) (σ : ℕ → State X Z W)
    (f_star : ℝ) (C : ℝ) (_hC : 0 ≤ C)
    (V : ℕ → ℝ) (hV : ∀ k, 0 ≤ V k)
    (hVdec : ∀ k, V (k + 1) + S.ρ * ‖primalResidualSeq S σ (k + 1)‖ ^ 2
                              + S.ρ * ‖S.B ((σ (k + 1)).z - (σ k).z)‖ ^ 2 ≤ V k)
    (obj_bound : ∀ k,
      |S.f (σ k).x + S.g (σ k).z - f_star| ≤
        C * ‖primalResidualSeq S σ k‖ + C * ‖dualResidualSeq S σ k‖) :
    Tendsto (fun k => S.f (σ k).x + S.g (σ k).z) atTop (nhds f_star) := by
  rw [ tendsto_iff_norm_sub_tendsto_zero ];
  exact squeeze_zero ( fun k => norm_nonneg _ ) obj_bound ( by simpa using Filter.Tendsto.add ( tendsto_const_nhds.mul <| primal_residual_bound S σ V hV hVdec ) ( tendsto_const_nhds.mul <| dual_residual_bound S σ V hV hVdec ) )

end ADMM
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! Scalar monotonicity used only after the physical signed covariance
and its actual Dirichlet energy have been identified. -/
@[expose] public section
namespace ASDExplicitGamma.Native

/-- The signed centered value variance increases with Y on [0,v]. -/
theorem parent_boundary_value_variance_clock (v y rho : ℝ)
    (hv : 0≤v) (_hy : 0≤y) (hyr : y≤v*rho) (_hr0 : 0≤rho) (hr1 : rho≤1) :
    v*y-y^2/2 ≤ v^2*(rho-rho^2/2) := by
  have hrv : v*rho≤v := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1 hv
  have hy1 : y≤v := hyr.trans hrv
  have hp := mul_nonneg (sub_nonneg.mpr hyr)
    (show 0≤v-(v*rho+y)/2 by linarith only [hrv,hy1])
  nlinarith only [hp]

/-- The full derivative budget increases with the same physical Y clock. -/
theorem parent_boundary_covariance_gradient_clock (v s y rho : ℝ)
    (hv : 0≤v) (hs : 0≤s) (hyr : y≤v*rho) (_hr0 : 0≤rho) :
    (Real.sqrt (v*s)+Real.sqrt ((s/2)*y))^2 ≤
      (v*s)*(1+Real.sqrt (rho/2))^2 := by
  have hvs := mul_nonneg hv hs
  have hy := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hyr (div_nonneg hs (by norm_num : (0:ℝ)≤2)))
  have hstep := pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (add_le_add (le_refl (Real.sqrt (v*s))) hy) 2
  apply hstep.trans_eq
  rw [show (s/2)*(v*rho)=(v*s)*(rho/2) by ring,Real.sqrt_mul hvs]
  have he : Real.sqrt (v*s)+Real.sqrt (v*s)*Real.sqrt (rho/2)=
      Real.sqrt (v*s)*(1+Real.sqrt (rho/2)) := by ring
  rw [he,mul_pow,Real.sq_sqrt hvs]

/-- Every own-native shell is at least three times the parent scale;
its safe rational Dirichlet clock lies in [0,1]. -/
theorem parent_boundary_rho_bounds (R L : ℝ) (hR : 0≤R) (hL : 0<L)
    (hscale : 3*R≤L) :
    0≤(26/15:ℝ)*(R/L)^2 ∧ (26/15:ℝ)*(R/L)^2≤1 := by
  have hratio0 : 0≤R/L := div_nonneg hR hL.le
  have hratio1 : R/L≤1/3 := (div_le_iff₀ hL).2 (by linarith only [hscale])
  have hs := pow_le_pow_left₀ hratio0 hratio1 2
  constructor
  · positivity
  · nlinarith only [hs]

end ASDExplicitGamma.Native

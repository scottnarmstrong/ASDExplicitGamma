module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The exact two algebraic branches in reciprocal-to-scalar conversion. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

/-- The large-S branch uses the source positive cubic factor. -/
theorem reciprocal_cubic_factor (Y : ℝ) (hY : 1≤Y) : 3*Y-2≤Y^3 := by
  have h := mul_nonneg (sq_nonneg (Y-1)) (show 0≤Y+2 by linarith only [hY])
  nlinarith only [h]

/-- The small-S branch has the source constant 3Y−2 throughout 1≤x≤Y. -/
theorem reciprocal_ratio_bound (x Y : ℝ) (hx : 1≤x) (hxY : x≤Y) :
    2*x^2/(x+1)≤3*Y-2 := by
  apply (div_le_iff₀ (show 0<x+1 by linarith only [hx])).mpr
  have h := mul_nonneg (sub_nonneg.mpr hx) (show 0≤x+2 by linarith only [hx])
  have hxy := mul_nonneg (sub_nonneg.mpr hxY) (show 0≤x+1 by linarith only [hx])
  nlinarith only [h,hxy]

/-- Evaluation of the large-S integral branch, followed by its sharp common majorant. -/
theorem reciprocal_large_region_bound (nu S Y : ℝ) (hY : 1≤Y) :
    S^2*(Y-1)+(Y*S^2-Y^3*nu^2)/2≤(3*Y-2)*(S^2-nu^2)/2 := by
  have h := mul_nonneg (sub_nonneg.mpr (reciprocal_cubic_factor Y hY)) (sq_nonneg nu)
  nlinarith only [h]

/-- Evaluation of the small-S integral branch, with the same common majorant. -/
theorem reciprocal_small_region_bound (nu S Y : ℝ) (hnu : 0<nu) (hS : nu≤S)
    (hSY : S≤Y*nu) : S^3*(nu⁻¹-S⁻¹)≤(3*Y-2)*(S^2-nu^2)/2 := by
  have hS0 : 0<S := hnu.trans_le hS
  have h1 : 1≤S/nu := (one_le_div hnu).mpr hS
  have h2 : S/nu≤Y := (div_le_iff₀ hnu).mpr hSY
  have hrat := reciprocal_ratio_bound (S/nu) Y h1 h2
  have hfactor : 0≤S^2-nu^2 := by nlinarith only [hS,hnu]
  have h := mul_le_mul_of_nonneg_right hrat hfactor
  have hden : 0<S/nu+1 := by linarith only [h1]
  rw [div_mul_eq_mul_div,(div_le_iff₀ hden)] at h
  field_simp [hnu.ne',hS0.ne'] at h ⊢
  apply (mul_le_mul_iff_of_pos_right (show 0<S+nu by linarith only [hS0,hnu])).mp
  convert h using 1
  ring

end ASDExplicitGamma.Scalar

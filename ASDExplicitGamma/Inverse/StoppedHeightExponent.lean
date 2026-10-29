module

public import ASDExplicitGamma.Numerics.Inverse.SelectedTails

/-! Uniform source height exponents at the fixed planar buffer b=40. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The literal exponent scale of the source stopped-height tail. -/
def heightExponent (h : ℕ) : ℝ := (3:ℝ)^((h:ℝ)/4-40)

/-- The source height exponent grows by exactly the fourth root of three. -/
theorem height_exponent_succ (h : ℕ) :
    heightExponent (h+1) = heightExponent h*((3:ℝ)^(1/4:ℝ)) := by
  unfold heightExponent
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  congr 1
  push_cast
  ring

/-- Fixed-buffer entrance 333 already supplies far more than the required
finite union and summation allowance. Entrance 377 follows by monotonicity. -/
theorem height_exponent_lower (h : ℕ) (hh : 333 ≤ h) : (3:ℝ)^43 ≤ heightExponent h := by
  unfold heightExponent
  rw [show (3:ℝ)^43 = (3:ℝ)^(43:ℝ) by norm_num [Real.rpow_natCast]]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
  have hhR : (333:ℝ) ≤ h := by exact_mod_cast hh
  linarith only [hhR]

/-- The affine logarithmic block count is absorbed by one twelfth of the
actual source exponent for every later integer height. -/
theorem height_linear_payment (h : ℕ) (hh : 333 ≤ h) :
    3+(11/5:ℝ)*(h:ℝ) ≤ heightExponent h/12 := by
  induction h,hh using Nat.le_induction with
  | base =>
    have he := height_exponent_lower 333 (by omega)
    norm_num at he ⊢
    linarith only [he]
  | succ h hh ih =>
    have hg := ASDExplicitGamma.Numerics.Inverse.inv_quarter_growth.le
    have hp : 0 ≤ heightExponent h := Real.rpow_nonneg (by norm_num) _
    have hstep : (13/10:ℝ)*heightExponent h ≤ heightExponent (h+1) := by
      rw [height_exponent_succ]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hg hp
    have hhR : (333:ℝ) ≤ h := by exact_mod_cast hh
    push_cast
    nlinarith only [ih,hstep,hhR]

/-- The complete source sequence is a positive supergeometric profile. -/
theorem height_exponent_add (h n : ℕ) :
    heightExponent (h+n) = heightExponent h*((3:ℝ)^(1/4:ℝ))^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show h+(n+1) = (h+n)+1 by omega,height_exponent_succ,ih,pow_succ]
    ring

end
end ASDExplicitGamma.Inverse

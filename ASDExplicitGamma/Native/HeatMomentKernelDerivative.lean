module

public import ASDExplicitGamma.Native.HeatMomentGreenKernel

/-! The affine kernel solves the complete triangular moment recurrence. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- Exponential-power differentiation without a spurious negative power at
zeroth degree. -/
theorem heat_exp_power_hasDerivAt (c : ℝ) (j : ℕ) (t : ℝ) :
    HasDerivAt (fun s => (Real.exp (c*s))^j)
      ((j:ℝ)*c*(Real.exp (c*t))^j) t := by
  have he := (Real.hasDerivAt_exp (c*t)).comp t ((hasDerivAt_id t).const_mul c)
  convert he.pow j using 1
  · funext s
    rfl
  · cases j with
    | zero => simp
    | succ j => simp only [Function.comp_apply,Nat.add_sub_cancel,pow_succ,Nat.cast_add,Nat.cast_one]; ring

/-- Every off-diagonal Green kernel solves its degree-specific affine row,
including the predecessor contribution that propagates lower-degree forcing. -/
theorem heat_moment_green_kernel_hasDerivAt_succ (c : ℝ) (j d : ℕ) (t : ℝ) :
    HasDerivAt (heatMomentGreenKernel c j (d+1))
      (c*(j+d+1:ℕ)*heatMomentGreenKernel c j (d+1) t +
        4*c*(d+1:ℕ)*heatMomentGreenKernel c j d t) t := by
  have he := (Real.hasDerivAt_exp (c*t)).comp t ((hasDerivAt_id t).const_mul c)
  have hb := ((he.sub_const 1).const_mul 4).pow (d+1)
  have hh := (heat_exp_power_hasDerivAt c j t).mul hb
  convert hh using 1
  · funext s
    rfl
  · unfold heatMomentGreenKernel
    simp only [Pi.pow_apply,Function.comp_apply,Nat.add_sub_cancel,pow_succ,Nat.cast_add,Nat.cast_one]
    ring

/-- Diagonal kernel; the nonexistent predecessor entry is exactly absent. -/
theorem heat_moment_green_kernel_hasDerivAt_zero (c : ℝ) (j : ℕ) (t : ℝ) :
    HasDerivAt (heatMomentGreenKernel c j 0)
      (c*(j:ℝ)*heatMomentGreenKernel c j 0 t) t := by
  convert heat_exp_power_hasDerivAt c j t using 1
  · funext s
    simp [heatMomentGreenKernel]
  · simp only [heatMomentGreenKernel,pow_zero,mul_one]
    ring

end
end ASDExplicitGamma.Native

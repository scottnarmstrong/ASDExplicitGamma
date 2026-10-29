module

public import ASDExplicitGamma.Native.OldSignedDerivativeRowProduct

/-! The derivative-only OLD row coefficient in the source convention,
obtained from the existing sharper Dirichlet bridges. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization ASDExplicitGamma.Triadic
noncomputable section

/-- The existing sharp Dirichlet positive constant is below AN's 2/pi. -/
theorem old_signed_planarFD_le_two_div_pi : planarFD≤2/Real.pi := by
  unfold planarFD
  apply (div_le_div_iff_of_pos_right Real.pi_pos).mpr
  apply Real.sqrt_le_iff.mpr
  norm_num

/-- The existing L2 Dirichlet constant is below AN's c0. -/
theorem old_signed_planarCD_le_planarC0 : planarCD≤planarC0 := by
  apply (sq_le_sq₀ (show 0≤planarCD from Real.sqrt_nonneg _)
    (show 0≤planarC0 from Real.sqrt_nonneg _)).mp
  rw [planarCD_sq,planarC0_sq_eq_planarC1_sq_add]
  apply add_le_add le_rfl
  rw [div_le_div_iff₀ (by positivity : (0:ℝ)<2*Real.pi^2) (sq_pos_of_ne_zero Real.pi_ne_zero)]
  nlinarith only [sq_nonneg Real.pi]

/-- AN (3.1) with the sharper actual q3 ROW variances of AN (3.3),
retaining the first-jet and full flattened Hessian eigenvalues. -/
def oldSignedDerivativeKappa (r b L : ℝ) : ℝ :=
  (2/Real.pi)*r*Real.sqrt ((78/5)*b^2/L^2)+
    planarC0*planarC1*r^2*Real.sqrt ((23244/25)*b^2/L^4)

/-- The source derivative-only kappa bounds the actual row coefficient
already proved for every finite family of distinct zero-trace potentials. -/
theorem old_signed_derivative_row_coefficient_le_kappa {r : ℝ} (hr : 0≤r) (b L : ℝ) :
    oldSignedDerivativeRowCoefficient r b L≤oldSignedDerivativeKappa r b L := by
  unfold oldSignedDerivativeRowCoefficient oldSignedDerivativeKappa
  calc
    _ ≤ r*(2/Real.pi)*Real.sqrt ((78/5)*b^2/L^2)+
        r^2*planarC0*planarC1*Real.sqrt ((23244/25)*b^2/L^4) :=
      add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left old_signed_planarFD_le_two_div_pi hr) (Real.sqrt_nonneg _))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left old_signed_planarCD_le_planarC0 (sq_nonneg r))
            (show 0≤planarC1 from Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    _ = _ := by ring

end
end ASDExplicitGamma.Native

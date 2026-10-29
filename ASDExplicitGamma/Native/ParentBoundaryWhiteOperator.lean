module

public import ASDExplicitGamma.Native.OldSignedWhiteRow
public import ASDExplicitGamma.Gaussian.SupMeanKernelTensorBounds

/-! The actual white-row derivative operator cap, distinct from its full
Frobenius trace. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
noncomputable section

/-- The physical first-derivative covariance operator is sigma²/2.
This controls the derivative of a complete covariance row sharply. -/
theorem parent_boundary_white_derivative_operator (b : ℝ)
    (L : {l : ℝ // 0<l}) (x : Vec 2) (z : WhiteNoise) :
    (∑ i : Fin 2,(inner ℝ ((fderiv ℝ (q3Section b L h3Zero) x) (basisVec i)) z)^2) ≤
      (mainFlatSigmaSq b L/2)*‖z‖^2 := by
  have hm : 0≤waveEll1^2*(b^2/L.1^2) := by positivity
  have hn := supMean_kernel_first_cm_norm b L z x
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg z))).2 hn
  rw [EuclideanSpace.real_norm_sq_eq,mul_pow,Real.sq_sqrt hm] at hs
  simp only [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] at hs
  rw [←Finset.mul_sum] at hs
  have hell : waveEll1^2*(b^2/L.1^2)=mainFlatSigmaSq b L := by
    unfold waveEll1 waveR1 mainFlatSigmaSq
    rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2*(78/5:ℝ))]
    ring
  rw [hell] at hs
  have he (i : Fin 2) :
      inner ℝ ((fderiv ℝ (q3Section b L h3Zero) x) (basisVec i)) z =
        q3Convolution b L (supMeanKernelJetIndex (.first i)) z x := by
    rw [old_signed_white_section_derivative,real_inner_comm]
    congr 1
    fin_cases i <;> rfl
  simp_rw [he]
  nlinarith only [hs]

end
end ASDExplicitGamma.Native

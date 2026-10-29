module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandSobolevEnvelope
public import Mathlib.Analysis.Calculus.MeanValue

/-! The actual scalar band derivative is paid by its full first tensor. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Gaussian Model Triadic Inverse Algsuperdiff.Section3
noncomputable section

/-- The operator norm from the planar Pi space is bounded by the sum of the
two coordinate derivatives. -/
theorem upper_cell_linear_form_norm (L : Vec 2 →L[ℝ] ℝ) :
    ‖L‖ ≤ |L (basisVec 0)|+|L (basisVec 1)| := by
  apply L.opNorm_le_bound (add_nonneg (abs_nonneg _) (abs_nonneg _))
  intro v
  have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec,Pi.single_apply]
  have he : L v = v 0*L (basisVec 0)+v 1*L (basisVec 1) := by
    conv_lhs => rw [hv]
    simp only [map_add,map_smul,smul_eq_mul]
  rw [he,Real.norm_eq_abs]
  have h0 : |v 0| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0
  have h1 : |v 1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 1
  calc
    _ ≤ |v 0*L (basisVec 0)|+|v 1*L (basisVec 1)| := abs_add_le _ _
    _ = |v 0| *|L (basisVec 0)|+|v 1| *|L (basisVec 1)| := by rw [abs_mul,abs_mul]
    _ ≤ ‖v‖*|L (basisVec 0)|+‖v‖*|L (basisVec 1)| :=
      add_le_add (mul_le_mul_of_nonneg_right h0 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
    _ = _ := by ring

/-- The two-coordinate sum has the exact planar Frobenius payment. -/
theorem upper_cell_two_abs_le_tensor_norm (a b : ℝ) :
    |a|+|b| ≤ Real.sqrt 2*Real.sqrt (a^2+b^2) := by
  have hsq : (|a|+|b|)^2 ≤ (Real.sqrt 2*Real.sqrt (a^2+b^2))^2 := by
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),
      Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))]
    nlinarith only [sq_abs a,sq_abs b,sq_nonneg (|a|-|b|)]
  exact (sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hsq

/-- The literal finite-band derivative is bounded on the physical cube by
its actual compact first-tensor norm, with no shellwise triangle loss. -/
theorem upper_cell_band_fderiv_norm_le
    (Q : TriadicCube 2) (n : ℤ) (height : ℕ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) {x : Vec 2} (hx : x ∈ cubeSet Q) :
    ‖fderiv ℝ (laterScalarBand n (n+(height:ℤ)) weights ω) x‖ ≤
      ‖upperCellBandSquareTensor (upperCellPhysicalBandLabel n height)
        (fun i => weights (upperCellPhysicalBandLabel n height i)) Q3SpatialJet.first
        (cubeCenter Q) (cubeScaleFactor Q) ω‖ := by
  let f := laterScalarBand n (n+(height:ℤ)) weights ω
  have hl := upper_cell_linear_form_norm (fderiv ℝ f x)
  have ht := upper_cell_two_abs_le_tensor_norm
    ((fderiv ℝ f x) (basisVec 0)) ((fderiv ℝ f x) (basisVec 1))
  have he : Real.sqrt 2*Real.sqrt (((fderiv ℝ f x) (basisVec 0))^2+
      ((fderiv ℝ f x) (basisVec 1))^2) =
      ‖laterBandTensor Q3SpatialJet.first n (n+(height:ℤ)) weights ω x‖ := by
    rw [later_band_first_tensor_norm Q]
    simp only [planarEuclideanNorm,planarW1Value,Fin.sum_univ_two,
      laterBandW2,smooth_w2_gradient,smoothScalarDerivative,f]
  exact (hl.trans ht).trans (he.le.trans
    (upper_cell_band_sobolev_tensor_norm_le Q Q3SpatialJet.first n height weights ω hx))

end
end ASDExplicitGamma.Scalar

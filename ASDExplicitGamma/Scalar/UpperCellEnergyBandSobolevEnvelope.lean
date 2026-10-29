module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandSobolevTensor

/-! Actual Sobolev sensitivity is dominated by the proved full-band compact envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Gaussian Model Triadic Inverse
open Algsuperdiff.Section3
noncomputable section

/-- The Sobolev gradient supremum is paid by the full actual first-tensor
compact norms, on this same sample and this same physical cube. -/
theorem upper_cell_band_gradient_LInf_le (Q : TriadicCube 2) (n : ℤ) (height : ℕ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    Real.sqrt 2*planarGradientLInf (laterBandW2 Q n (n+(height:ℤ)) weights ω) ≤
      ‖upperCellBandSquareTensor (upperCellPhysicalBandLabel n height)
        (fun i => weights (upperCellPhysicalBandLabel n height i)) Q3SpatialJet.first
        (cubeCenter Q) (cubeScaleFactor Q) ω‖ := by
  let B := ‖upperCellBandSquareTensor (upperCellPhysicalBandLabel n height)
    (fun i => weights (upperCellPhysicalBandLabel n height i)) Q3SpatialJet.first
    (cubeCenter Q) (cubeScaleFactor Q) ω‖
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hh := planarW1ValueLInf_le_of_bound (laterBandW2 Q n (n+(height:ℤ)) weights ω).gradient
    (div_nonneg hB hs.le) (by
      filter_upwards [normalized_cube_support Q] with x hx
      have hn := upper_cell_band_sobolev_tensor_norm_le Q Q3SpatialJet.first n height weights ω hx
      rw [later_band_first_tensor_norm Q] at hn
      apply (le_div_iff₀ hs).mpr
      simpa only [mul_comm] using hn)
  change Real.sqrt 2*planarW1ValueLInf (laterBandW2 Q n (n+(height:ℤ)) weights ω).gradient ≤ B
  calc
    _ ≤ Real.sqrt 2*(B/Real.sqrt 2) := mul_le_mul_of_nonneg_left hh hs.le
    _ = B := by field_simp

/-- The Sobolev Hessian supremum has the same exact compact tensor payment. -/
theorem upper_cell_band_hessian_LInf_le (Q : TriadicCube 2) (n : ℤ) (height : ℕ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    Real.sqrt 2*planarHessianFrobeniusLInf (laterBandW2 Q n (n+(height:ℤ)) weights ω) ≤
      ‖upperCellBandSquareTensor (upperCellPhysicalBandLabel n height)
        (fun i => weights (upperCellPhysicalBandLabel n height i))
        (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2)
        (cubeCenter Q) (cubeScaleFactor Q) ω‖ := by
  let B := ‖upperCellBandSquareTensor (upperCellPhysicalBandLabel n height)
    (fun i => weights (upperCellPhysicalBandLabel n height i))
    (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2)
    (cubeCenter Q) (cubeScaleFactor Q) ω‖
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hh := planarW1DerivativeFrobeniusLInf_le_of_bound (laterBandW2 Q n (n+(height:ℤ)) weights ω).gradient
    (div_nonneg hB hs.le) (by
      filter_upwards [normalized_cube_support Q] with x hx
      have hn := upper_cell_band_sobolev_tensor_norm_le Q (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2)
        n height weights ω hx
      rw [later_band_second_tensor_norm Q] at hn
      apply (le_div_iff₀ hs).mpr
      simpa only [mul_comm] using hn)
  change Real.sqrt 2*planarW1DerivativeFrobeniusLInf (laterBandW2 Q n (n+(height:ℤ)) weights ω).gradient ≤ B
  calc
    _ ≤ Real.sqrt 2*(B/Real.sqrt 2) := mul_le_mul_of_nonneg_left hh hs.le
    _ = B := by field_simp

/-- The genuine W^{2,∞} sensitivity size is bounded by the full-band
compact envelope on the same sample and physical cube. -/
theorem upper_cell_band_Dsharp_le_envelope
    (Q : TriadicCube 2) (n : ℤ) (height : ℕ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    sensitivityDsharp Q (laterBandW2 Q n (n+(height:ℤ)) weights ω) ≤
      upperCellBandEnvelope (upperCellPhysicalBandLabel n height)
        (fun i => weights (upperCellPhysicalBandLabel n height i))
        (cubeCenter Q) (cubeScaleFactor Q) (cubeScaleFactor Q) ((cubeScaleFactor Q)^2) ω := by
  let h := laterBandW2 Q n (n+(height:ℤ)) weights ω
  have hs := (Homogenization.cubeScaleFactor_pos' Q).le
  have hD1 := mul_le_mul_of_nonneg_left
    (upper_cell_band_gradient_LInf_le Q n height weights ω) hs
  have hD2 := mul_le_mul_of_nonneg_left
    (upper_cell_band_hessian_LInf_le Q n height weights ω) (sq_nonneg (cubeScaleFactor Q))
  have hD20 : 0 ≤ sensitivityD2 Q h := by
    unfold sensitivityD2 planarHessianFrobeniusLInf planarW1DerivativeFrobeniusLInf
    positivity
  have hh := add_le_add (le_refl (sensitivityD1 Q h))
    (mul_le_of_le_one_left hD20 sensitivity_kappa_le_one)
  change sensitivityDsharp Q h ≤ sensitivityD1 Q h+sensitivityD2 Q h at hh
  apply hh.trans
  simpa only [upperCellBandEnvelope,sensitivityD1,sensitivityD2,h,mul_assoc] using
    add_le_add hD1 hD2

end
end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalLargeComparison
public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalOldQuadratic
public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalSmallComparison
public import ASDExplicitGamma.Scalar.UpperCellEnergyAllEventAlgebra

/-! The exact all-event additive comparison for the actual upper trial's
centered physical coefficient and arbitrary doubled load. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Variational Triadic Inverse Algsuperdiff.Section3
noncomputable section

/-- The source additive sensitivity payment holds pointwise, with no assumed
matrix comparison, no small-event premise and no independence hypothesis. -/
theorem upper_cell_physical_all_event_comparison
    (M : ABKModel 2) (n ell : ℤ) (height : ℕ) (ω : Cutoff.CutoffSample 2) (P : BlockVec 2) :
    let Q := originCube 2 (n-ell)
    let sigma := (Annealed.sigmaBar M n:ℝ)
    let h := laterBandW2 Q n (n+(height:ℤ)) (fun _ => sigma⁻¹) ω
    let F := upperCellBandEnvelope (upperCellPhysicalBandLabel n height)
      (fun _ => sigma⁻¹) (cubeCenter Q) (cubeScaleFactor Q) (cubeScaleFactor Q) ((cubeScaleFactor Q)^2) ω
    let A := 1+2*(lagTraceHistory M n ell ω).toReal+Real.sqrt (2*(lagTraceHistory M n ell ω).toReal)
    let centered := oldCutoffSkewCoefficient (n+(height:ℤ)) Q ω-
      BoundedContinuousFunction.const (closure (openCubeSet Q)) (sigma*cubeAverage Q h.value.toFun)
    blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q)
      (responseFramePlanarCoefficientField M.nu sigma centered)) P) ≤
    blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q)
      (responseFramePlanarCoefficientField M.nu sigma (oldCutoffSkewCoefficient n Q ω))) P)+
      6*A^2*F*(1+2*F+4*F^2)*blockVecDot P P := by
  dsimp only
  let Q := originCube 2 (n-ell)
  let sigma := (Annealed.sigmaBar M n:ℝ)
  let h := laterBandW2 Q n (n+(height:ℤ)) (fun _ => sigma⁻¹) ω
  let F := upperCellBandEnvelope (upperCellPhysicalBandLabel n height)
    (fun _ => sigma⁻¹) (cubeCenter Q) (cubeScaleFactor Q) (cubeScaleFactor Q) ((cubeScaleFactor Q)^2) ω
  let A := 1+2*(lagTraceHistory M n ell ω).toReal+Real.sqrt (2*(lagTraceHistory M n ell ω).toReal)
  let hp := div_pos M.nu_pos (Annealed.sigmaBar M n).property
  let theta := sensitivityPathLambdaInverse (M.nu/sigma) hp
    (sigma⁻¹ • oldCutoffSkewCoefficient n Q ω)
    (laterResponseCoefficient Q n (n+(height:ℤ)) (fun _ => sigma⁻¹) ω) (1/4) 0
  have hF : 0≤F := upper_cell_band_envelope_nonneg _ _ _ _ _ _
    (Homogenization.cubeScaleFactor_pos' Q).le (sq_nonneg _) ω
  have hA : 0≤A := by dsimp [A]; positivity
  have ht : 0≤theta := sensitivityPathLambdaInverse_nonneg _ hp _ _ (by norm_num) 0
  have htA : theta≤A := upper_cell_physical_initial_lambda_majorant M n ell ω _
  have hD : sensitivityDsharp Q h≤F := upper_cell_band_Dsharp_le_envelope Q n height _ ω
  have ho := upper_cell_physical_old_quadratic_bounds M n ell ω P
  apply upper_cell_all_event_comparison_algebra A F theta (blockVecDot P P) _ _
    hA hF htA (blockVecDot_nonneg P) ho.1 ho.2
  · intro hs
    have hd : sensitivityDsharp Q h*theta ≤ theta*F :=
      (mul_le_mul_of_nonneg_right hD ht).trans_eq (mul_comm F theta)
    have hh := upper_cell_physical_small_comparison M Q n (n+(height:ℤ))
      (by omega) sigma (Annealed.sigmaBar M n).property ω (hd.trans hs) P
    rw [sensitivityBlockScale_quadratic] at hh
    have hb := mul_le_mul_of_nonneg_right
      (add_le_add (le_refl (1:ℝ)) (mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ)≤5/4))) ho.1
    nlinarith only [hh,hb]
  · exact upper_cell_physical_large_comparison M n ell height ω P

end
end ASDExplicitGamma.Scalar

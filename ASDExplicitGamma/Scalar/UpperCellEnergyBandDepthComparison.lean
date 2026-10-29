module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBookSubadditivity
public import ASDExplicitGamma.Scalar.UpperCellEnergyBandOscillation

/-! Parent-cell comparison from the actual fresh band at a chosen descendant
depth. Only the OLD descendant norm bound remains as an analytic input. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Variational Triadic Inverse Algsuperdiff.Section3
noncomputable section

/-- The full actual band, local sensitivity, gauge correction and coarse
subadditivity give the parent quadratic bound at any admissible common depth. -/
theorem upper_cell_band_depth_comparison
    (Q : TriadicCube 2) (nu : ℝ) (hnu : 0<nu)
    (k : ResponseCoefficient (openCubeSet Q))
    (n : ℤ) (height : ℕ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    (j : ℕ) (B : ℝ)
    (hOld : ∀ (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j),
      ‖HilbertBlockVec.applyBlockMat
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R nu hnu (sensitivityResponseCoefficientRestrict k hR)))‖ ≤ B) :
    let kH := laterResponseCoefficient Q n (n+(height:ℤ)) weights ω
    let h := laterBandW2 Q n (n+(height:ℤ)) weights ω
    let F := upperCellBandEnvelope (upperCellPhysicalBandLabel n height)
      (fun i => weights (upperCellPhysicalBandLabel n height i))
      (cubeCenter Q) (cubeScaleFactor Q) (cubeScaleFactor Q) ((cubeScaleFactor Q)^2) ω
    let x := sensitivityDsharp Q h * sensitivityPathLambdaInverse nu hnu k kH (1/4) 0
    x/(Real.sqrt 3)^j ≤ 2/5 → ∀ P : BlockVec 2,
      blockVecDot P (blockMatVecMul
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q nu hnu
          (sensitivityResponseCoefficientPath k
            (kH+BoundedContinuousFunction.const (closure (openCubeSet Q))
              (-(cubeAverage Q h.value.toFun))) 1))) P) ≤
        (1+(5/4:ℝ)*(x/(Real.sqrt 3)^j))*B*(1+2*F+4*F^2)*blockVecDot P P := by
  dsimp only
  let kH := laterResponseCoefficient Q n (n+(height:ℤ)) weights ω
  let h := laterBandW2 Q n (n+(height:ℤ)) weights ω
  let F := upperCellBandEnvelope (upperCellPhysicalBandLabel n height)
    (fun i => weights (upperCellPhysicalBandLabel n height i))
    (cubeCenter Q) (cubeScaleFactor Q) (cubeScaleFactor Q) ((cubeScaleFactor Q)^2) ω
  let x := sensitivityDsharp Q h * sensitivityPathLambdaInverse nu hnu k kH (1/4) 0
  let C := 1+(5/4:ℝ)*(x/(Real.sqrt 3)^j)
  have hF : 0≤F := upper_cell_band_envelope_nonneg _ _ _ _ _ _
    (Homogenization.cubeScaleFactor_pos' Q).le (sq_nonneg _) ω
  have hx : 0≤x := mul_nonneg (sensitivityDsharp_nonneg Q h)
    (sensitivityPathLambdaInverse_nonneg nu hnu k kH (by norm_num) 0)
  have hC : 0≤C := by dsimp [C]; positivity
  have hp : 0≤1+2*F+4*F^2 := by positivity
  intro hsmall P
  apply upper_cell_book_subadditivity_bound Q j nu hnu _ (C*B*(1+2*F+4*F^2)) P
  intro R hR
  let kR := sensitivityResponseCoefficientRestrict k hR
  let kHR := sensitivityResponseCoefficientRestrict kH hR
  let meanQ := cubeAverage Q h.value.toFun
  let meanR := cubeAverage R (h.restrict hR).value.toFun
  have hm : |meanR-meanQ|≤2*F := upper_cell_band_mean_difference Q R
    (cubeSet_subset_of_mem_descendantsAtDepth hR) n height weights ω
  have hc := upper_cell_descendant_centered_comparison nu hnu k kH h
    (later_response_coefficient_represents Q n (n+(height:ℤ)) weights ω) hR hsmall
  have ht := upper_cell_gauge_transfer_comparison R nu hnu kR
    (sensitivityResponseCoefficientPath kR
      (kHR+BoundedContinuousFunction.const (closure (openCubeSet R)) (-meanR)) 1)
    C F (meanR-meanQ) hC hF hm hc P
  rw [upper_cell_recentered_path_restriction k kH hR meanQ meanR]
  apply ht.trans
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hOld R hR) hC) hp)
    (blockVecDot_nonneg P)
  exact hb

end
end ASDExplicitGamma.Scalar

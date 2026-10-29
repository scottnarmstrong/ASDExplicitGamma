module

public import ASDExplicitGamma.Scalar.UpperCellEnergyDescendantLambda

/-! Local centered matrix comparisons at a chosen common descendant depth. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Triadic
noncomputable section

/-- The descendant comparison has a uniform root-based factor, preserving the
half-power decay needed for the all-depth response aggregation. -/
theorem upper_cell_descendant_centered_comparison
    {Q R : TriadicCube 2} {j : ℕ}
    (nu : ℝ) (hnu : 0<nu) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[volume.restrict (openCubeSet Q)] h.value.toFun)
    (hR : R ∈ descendantsAtDepth Q j)
    (hsmall : (sensitivityDsharp Q h * sensitivityPathLambdaInverse nu hnu k kH (1/4) 0) /
      (Real.sqrt 3)^j ≤ 2/5) :
    let kR := sensitivityResponseCoefficientRestrict k hR
    let kHR := sensitivityResponseCoefficientRestrict kH hR
    BlockMatLoewnerLE
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R)
        (sensitivityBookCoeffOn R nu hnu (sensitivityResponseCoefficientPath kR
          (kHR + BoundedContinuousFunction.const (closure (openCubeSet R))
            (-(cubeAverage R (h.restrict hR).value.toFun))) 1)))
      (sensitivityBlockScale
        (1+(5/4:ℝ)*((sensitivityDsharp Q h * sensitivityPathLambdaInverse nu hnu k kH (1/4) 0) /
          (Real.sqrt 3)^j))
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R nu hnu kR))) := by
  dsimp only
  let kR := sensitivityResponseCoefficientRestrict k hR
  let kHR := sensitivityResponseCoefficientRestrict kH hR
  have hd := upper_cell_descendant_lambda_decay nu hnu k kH h hR 0
  have hc := upper_cell_small_centered_matrix nu hnu kR kHR (h.restrict hR)
    (sensitivityResponseCoefficientRestrict_represents kH h hkH hR)
    (by norm_num : (0:ℝ)<1/4) le_rfl (hd.trans hsmall)
  intro P
  have hp := hc P
  have hq : 0 ≤ blockVecDot P (blockMatVecMul
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R)
        (sensitivityBookCoeffOn R nu hnu kR)) P) := by
    simpa only [sensitivityCoarseMatrixPathQuadratic,sensitivityResponseCoefficientPath,
      zero_smul,add_zero] using
      sensitivityCoarseMatrixPathQuadratic_nonneg nu hnu kR kHR P 0
  rw [sensitivityBlockScale_quadratic] at hp ⊢
  have hb := mul_le_mul_of_nonneg_right
    (add_le_add (le_refl (1:ℝ)) (mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ)≤5/4))) hq
  exact hp.trans (mul_le_mul_of_nonneg_left hb (by norm_num))

end
end ASDExplicitGamma.Scalar

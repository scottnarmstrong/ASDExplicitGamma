module

public import ASDExplicitGamma.Inverse.SensitivityGate

/-! Pure-flux consequences of the actual coarse sensitivity path. Constant
skew centering is removed using its exact lower-right block identity. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- The sensitivity Book matrix and the public variational matrix describe
the same physical coefficient on the observation cube. -/
theorem sensitivity_book_matrix_eq (Q : TriadicCube 2) (ν : ℝ) (hν : 0 < ν)
    (k : ResponseCoefficient (openCubeSet Q)) :
    Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q ν hν k) =
      coarseBlockMatrix (cubeSet Q) (sensitivityBaseRegField ν k).toFun := by
  have hEll : IsEllipticFieldOn (sensitivityBookCoeffOn Q ν hν k).lam
      (sensitivityBookCoeffOn Q ν hν k).Lam (openCubeSet Q)
      (sensitivityBookCoeffOn Q ν hν k).toCoeffField := by
    simpa [sensitivityBookCoeffOn, div_one] using
      responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν 1 hν one_pos k
  rw [ASDExplicitGamma.Variational.energyMap_coarseBlockMatrix_eq _ _ hEll]
  exact (coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q _).symm

/-- The mean-zero gauge in the ODE does not alter any pure-flux quadratic
form. This is the upper ODE comparison for the uncentered actual path. -/
theorem sensitivity_pure_flux_upper (Q : TriadicCube 2) (ν : ℝ) (hν : 0 < ν)
    (k kH : ResponseCoefficient (openCubeSet Q)) (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[volume.restrict (openCubeSet Q)] h.value.toFun)
    (hsmall : sensitivityB2*sensitivityDsharp Q h*sensitivityPathLambdaInverse ν hν k kH (1/4) 0 < 1)
    (hloc : sensitivityDsharp Q h*sensitivityPathLambdaInverse ν hν k kH (1/4) 0 ≤ sensitivityCloc)
    (v : Vec 2) :
    dotProduct v ((Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
      (sensitivityBookCoeffOn Q ν hν (k+kH))).lowerRight.mulVec v) ≤
      Real.exp (sensitivityCA*(sensitivityDsharp Q h*sensitivityPathLambdaInverse ν hν k kH (1/4) 0))*
        dotProduct v ((Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
          (sensitivityBookCoeffOn Q ν hν k)).lowerRight.mulVec v) := by
  have hode := (sensitivity_coarse_sensitivity_ode_caps ν hν k kH h hkH
    (by norm_num : (0:ℝ)<1/4) le_rfl hsmall hloc).2.2 (0,v)
  rw [sensitivityBlockScale_quadratic,← lower_right_quadratic,← lower_right_quadratic] at hode
  have hg := sensitivityBookCoeffOn_constantShift_sigmaStarInv Q ν hν (k+kH)
    (-(cubeAverage Q h.value.toFun))
  change (Book.Ch02.coarseBlockMatrix _ _).lowerRight=(Book.Ch02.coarseBlockMatrix _ _).lowerRight at hg
  simp only [sensitivityResponseCoefficientPath,one_smul] at hode
  rw [← add_assoc,hg] at hode
  linarith only [hode]

/-- The actual bounded old-plus-later path agrees pointwise with the full
attenuated coefficient on the physical cube. -/
theorem sensitivity_path_represents_attenuated (M : ABKModel 2) (Q : TriadicCube 2)
    (n m J : ℤ) (hn : n ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) {x : Vec 2} (hx : x ∈ openCubeSet Q) :
    sensitivityBaseRegField M.nu (oldResponseCoefficient Q n ω+
      laterResponseCoefficient Q n J (sourceBandWeights m weights) ω) x =
        attenuatedCoefficient M m J weights ω x := by
  rw [attenuated_coefficient_eq_old_add_band M n m J hn hm weights ω x,
    ← old_response_coefficient_represents M Q n ω hx]
  change responsePlanarCoefficient (M.nu/1)
    (responseCoefficientExtension (oldResponseCoefficient Q n ω+
      laterResponseCoefficient Q n J (sourceBandWeights m weights) ω) x/1)=_
  rw [responseCoefficientExtension_add_on _ _ hx,
    responseCoefficientExtension_eq (laterResponseCoefficient Q n J (sourceBandWeights m weights) ω) hx]
  change responsePlanarCoefficient (M.nu/1)
    ((responseCoefficientExtension (oldResponseCoefficient Q n ω) x+
      laterScalarBand n J (sourceBandWeights m weights) ω x)/1)=_
  have hemb (t : ℝ) : ASDExplicitGamma.Gaussian.supMeanSkewEmbedding t=t • responsePlanarJ := by
    ext i j
    change t*ASDExplicitGamma.Model.q3SkewEntry i j=(t • responsePlanarJ) i j
    fin_cases i <;> fin_cases j <;> simp [ASDExplicitGamma.Model.q3SkewEntry,responsePlanarJ]
  rw [hemb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sensitivityBaseRegField,responseFramePlanarCoefficientField,responsePlanarCoefficient,
      responsePlanarJ,Matrix.add_apply,Matrix.smul_apply]
  all_goals ring

end
end ASDExplicitGamma.Inverse

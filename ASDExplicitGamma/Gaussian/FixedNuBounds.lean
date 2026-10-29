module

public import ASDExplicitGamma.Response.ResponseRealization
public import Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich

/-! Constant-competitor bounds for the actual fixed-positive-viscosity response. -/

@[expose] public section

namespace ASDExplicitGamma.Gaussian

open Homogenization MeasureTheory ASDExplicitGamma.Response

/-- Constant competitors are admissible in the genuine doubled variational problem. -/
theorem fixedNu_constant_admissible {d : ℕ} (U : Set (Vec d)) (P : BlockVec d) :
    IsBlockMuAdmissible U P
      { potential := fun _ => P.1, flux := fun _ => P.2 } := by
  have hp : (fun _ : Vec d => P.1 - P.1) = (0 : Vec d → Vec d) := by
    funext x
    exact sub_self _
  have hq : (fun _ : Vec d => P.2 - P.2) = (0 : Vec d → Vec d) := by
    funext x
    exact sub_self _
  refine ⟨?_, ?_, ?_, ?_⟩
  · change MemVectorL2 U (fun _ => P.1 - P.1)
    rw [hp]
    exact MemLp.zero
  · change IsPotentialZeroTraceOn U (fun _ => P.1 - P.1)
    rw [hp]
    exact isPotentialZeroTraceOn_zero
  · change MemVectorL2 U (fun _ => P.2 - P.2)
    rw [hq]
    exact MemLp.zero
  · change IsSolenoidalZeroNormalTraceOn U (fun _ => P.2 - P.2)
    rw [hq]
    exact isSolenoidalZeroNormalTraceOn_zero

/-- The elementary constant-competitor upper bound, with all variational
boundedness proved from ellipticity. -/
theorem fixedNu_Mu_le_constant {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (P : BlockVec d) :
    Mu U P a ≤ volumeAverage U (blockEnergyDensity a
      { potential := fun _ => P.1, flux := fun _ => P.2 }) := by
  have hb : BddBelow (muValueSet U P a) := by
    refine ⟨0, ?_⟩
    rintro r ⟨X, _, rfl⟩
    apply volumeAverage_nonneg_of_nonneg_on hU
    intro x hx
    exact mul_nonneg (by norm_num) (blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x hx) (X.eval x))
  exact csInf_le hb (muValueSet_mem (fixedNu_constant_admissible U P))

/-- The constant-load trial bound in its physical fixed frame. -/
theorem fixedNu_trial_bound {U : Set (Vec 2)} (hU : MeasurableSet U)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient U) (P : BlockVec 2) :
    2 * Mu U P (responseFramePlanarCoefficientField nu sigma k) ≤
      volumeAverage U (fun x => responseFrameEnergyDensity nu sigma
        (responseCoefficientExtension k x) P) := by
  have h := fixedNu_Mu_le_constant hU
    (responseFramePlanarCoefficientField_isElliptic hU nu sigma hnu hsigma k) P
  have heq : blockEnergyDensity (responseFramePlanarCoefficientField nu sigma k)
      { potential := fun _ => P.1, flux := fun _ => P.2 } =
      fun x => (1 / 2 : ℝ) * responseFrameEnergyDensity nu sigma
        (responseCoefficientExtension k x) P := by
    funext x
    simp only [blockEnergyDensity, blockCoeffField, BlockState.eval,
      responseFramePlanarCoefficientField]
    rw [responseFrameEnergyDensity_eq_scaledCoefficientBlock nu sigma _ hnu hsigma]
  rw [heq] at h
  unfold volumeAverage at h ⊢
  rw [integral_const_mul] at h
  linarith only [h]

/-- The inverse-block quadratic cap in the same physical frame. -/
theorem fixedNu_inverse_quadratic_le (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (cubeSet Q)) (q : Vec 2) :
    vecDot q (matVecMul
        (coarseBlockMatrix (cubeSet Q) (responseFramePlanarCoefficientField nu sigma k)).lowerRight q) ≤
      (sigma / nu) * vecNormSq q := by
  have htrial := fixedNu_trial_bound (measurableSet_cubeSet Q) nu sigma hnu hsigma k (0, q)
  have hquad := ASDExplicitGamma.Variational.mu_eq_half_coarseBlockMatrix_elliptic_triCube
    (div_pos hnu hsigma)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q)
      nu sigma hnu hsigma k) (0, q)
  have hvol : (volume (cubeSet Q)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  simp only [responseFrameEnergyDensity,
    matVecMul_zero, smul_zero, sub_zero] at htrial
  have hzero : vecNormSq (0 : Vec 2) = 0 := by
    simp only [vecNormSq, vecDot_zero_left]
  rw [hzero, mul_zero, zero_add] at htrial
  rw [volumeAverage_const hvol] at htrial
  simp only [blockVecDot, blockMatVecMul, matVecMul_zero, zero_add,
    vecDot_zero_left] at hquad
  linarith only [hquad, htrial]

end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Scalar.UpperCellEnergyOldTraceFrame
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetFrame
public import ASDExplicitGamma.Scalar.UpperCellEnergyCoefficientPath
public import ASDExplicitGamma.Scalar.InverseHistoryLambda
public import ASDExplicitGamma.Triadic.SensitivityODELambda
public import ASDExplicitGamma.Native.OldSignedHistoryComparison

/-! The sensitivity inverse lambda is bounded by the complete physical OLD
response history, using the slower quarter-power history discount. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Variational Native Triadic Algsuperdiff.Section3
noncomputable section

/-- Increasing the lambda exponent from one eighth to one quarter decreases
its reciprocal; the one-eighth history is bounded by the full response. -/
theorem upper_cell_inverse_lambda_le_response_history
    (Q : TriadicCube 2) (a : RegCoeffField 2)
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a.toFun) :
    (Book.Ch02.lambdaSqFinite Q (1/4) 2
      (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))⁻¹ ≤
        oldSignedResponseHistory Q a.toFun := by
  let family := Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have h8 := Book.Ch02.lambdaSq_finite_pos Q family (by norm_num : (0:ℝ)<1/8)
    (by norm_num : (1:ℝ)≤2)
  have h4 := Book.Ch02.lambdaSq_finite_pos Q family (by norm_num : (0:ℝ)<1/4)
    (by norm_num : (1:ℝ)≤2)
  have hm := Book.Ch02.lambdaSq_finite_mono Q family (by norm_num : (0:ℝ)<1/8)
    (by norm_num : (1/8:ℝ)<1/4) (by norm_num : (1:ℝ)≤2)
  have hi := (inv_le_inv₀ h4 h8).2 hm
  change (Book.Ch02.lambdaSqFinite Q (1/4) 2 family)⁻¹ ≤ _
  apply hi.trans
  change (Book.Ch02.lambdaSqFinite Q (1/8) 2
    (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))⁻¹ ≤ _
  rw [inverse_lambda_eq_history Q a ha]
  exact old_signed_inverse_history_le_response_history Q a.toFun hEll

/-- At time zero the sensitivity family is the actual initial coefficient;
the direction does not enter the controlling response history. -/
theorem upper_cell_path_initial_lambda_le_history
    (Q : TriadicCube 2) (nu : ℝ) (hnu : 0<nu)
    (k kH : ResponseCoefficient (openCubeSet Q)) :
    sensitivityPathLambdaInverse nu hnu k kH (1/4) 0 ≤
      oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu 1 k) := by
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu 1 hnu one_pos k
  have hh := upper_cell_inverse_lambda_le_response_history Q
    (sensitivityBaseRegField nu k) (sensitivityBaseRegField_aelocal nu hnu k) hEll
  simpa only [sensitivityPathLambdaInverse,sensitivityPathFamily,
    sensitivityResponseCoefficientPath,zero_smul,add_zero,sensitivityCoefficientFamily,
    sensitivityBaseRegField] using hh

/-- Restricting an almost-everywhere coefficient identity to every descendant
preserves the entire response history. -/
theorem upper_cell_response_history_congr
    (Q : TriadicCube 2) (a b : CoeffField 2)
    (hab : a =ᵐ[volume.restrict (openCubeSet Q)] b) :
    completeFullResponseHistory Q a = completeFullResponseHistory Q b := by
  unfold completeFullResponseHistory
  apply congrArg (fun z => ENNReal.ofReal (1-inverseHistoryDiscount)*z)
  apply tsum_congr
  intro j
  apply congrArg ENNReal.ofReal
  apply congrArg (fun z : ℝ => inverseHistoryDiscount^j*z)
  apply Book.Ch02.finsetSupReal_congr
  intro R hR
  have hr := ae_restrict_of_ae_restrict_of_subset
    (openCubeSet_subset_of_mem_descendantsAtDepth hR) hab
  unfold fullResponseOperatorNorm
  rw [cube_coarseMatrix_eq_open R a,cube_coarseMatrix_eq_open R b,
    coarseBlockMatrix_congr_of_ae_eq hr]

/-- Normalization of the bounded skew representative agrees with the actual
normalized cutoff on the physical observation cell. -/
theorem upper_cell_initial_sensitivity_coefficient
    (M : ABKModel 2) (Q : TriadicCube 2) (n : ℤ) (ω : Cutoff.CutoffSample 2) :
    responseFramePlanarCoefficientField (M.nu/(Annealed.sigmaBar M n:ℝ)) 1
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • oldCutoffSkewCoefficient n Q ω) =ᵐ[
        volume.restrict (openCubeSet Q)]
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • (Cutoff.coefficientCutoff M.nu n ω).toFun) := by
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  change responseFramePlanarCoefficientField (M.nu/(Annealed.sigmaBar M n:ℝ)) 1
    ((Annealed.sigmaBar M n:ℝ)⁻¹ • oldCutoffSkewCoefficient n Q ω) x =
      (Annealed.sigmaBar M n:ℝ)⁻¹ • Cutoff.coefficientCutoff M.nu n ω x
  rw [←upper_cell_reset_frame_coefficient M n n Q ω hx]
  change responsePlanarCoefficient ((M.nu/(Annealed.sigmaBar M n:ℝ))/1)
    (responseCoefficientExtension ((Annealed.sigmaBar M n:ℝ)⁻¹ •
      oldCutoffSkewCoefficient n Q ω) x/1) = _
  rw [div_one,div_one,responseCoefficientExtension_smul_on _ _ hx]
  unfold responseFramePlanarCoefficientField
  congr 1
  simp only [div_eq_mul_inv,mul_comm]

/-- The actual sensitivity inverse lambda is controlled by the OLD trace
majorant with no assumed coefficient, history, or inverse-lambda estimate. -/
theorem upper_cell_physical_initial_lambda_majorant
    (M : ABKModel 2) (n ell : ℤ) (ω : Cutoff.CutoffSample 2)
    (kH : ResponseCoefficient (openCubeSet (originCube 2 (n-ell)))) :
    sensitivityPathLambdaInverse (M.nu/(Annealed.sigmaBar M n:ℝ))
      (div_pos M.nu_pos (Annealed.sigmaBar M n).property)
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • oldCutoffSkewCoefficient n (originCube 2 (n-ell)) ω)
      kH (1/4) 0 ≤ 1+2*(lagTraceHistory M n ell ω).toReal+
        Real.sqrt (2*(lagTraceHistory M n ell ω).toReal) := by
  have hb := upper_cell_path_initial_lambda_le_history (originCube 2 (n-ell))
    (M.nu/(Annealed.sigmaBar M n:ℝ))
    (div_pos M.nu_pos (Annealed.sigmaBar M n).property)
    ((Annealed.sigmaBar M n:ℝ)⁻¹ • oldCutoffSkewCoefficient n (originCube 2 (n-ell)) ω) kH
  unfold oldSignedResponseHistory at hb
  rw [upper_cell_response_history_congr _ _ _
    (upper_cell_initial_sensitivity_coefficient M _ n ω)] at hb
  exact hb.trans (upper_cell_old_response_history_majorant M n ell ω)

end
end ASDExplicitGamma.Scalar

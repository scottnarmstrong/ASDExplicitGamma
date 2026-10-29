module

public import ASDExplicitGamma.Native.OldSignedTrialSeries
public import ASDExplicitGamma.Native.OldSignedFlatSignedAssembly
public import ASDExplicitGamma.Native.OldSignedGlobalOldSourceEnergy
public import ASDExplicitGamma.Native.OldSignedGlobalMixedFeedback
public import ASDExplicitGamma.Native.OldSignedGlobalPlusFeedback
public import ASDExplicitGamma.Native.OldSignedGlobalOldSourceFeedback
public import ASDExplicitGamma.Native.OldSignedGlobalMinusFeedback
public import ASDExplicitGamma.Native.OldSignedTopCovarianceBill
public import ASDExplicitGamma.Native.OldSignedBottomCovarianceBill
public import ASDExplicitGamma.Native.OldSignedErrorBillAssembly

/-! Complete signed OLD trial bound in the physical coefficient. Every
local budget and covariance identity is supplied internally. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian
noncomputable section

/-- The complete actual signed trial obeys AN (5.3), including the signed
inverse trace and every joint-cell error term. -/
theorem old_signed_trial_total_bound (m : ℤ) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 m
    let a := responseFramePlanarCoefficientField nu sigma k
    let T := oldSignedTrialTerms Q depth nu sigma hnu hsigma k b L
    Summable T.total ∧ (∑' n,T.total n)≤oldSignedFlatBoundaryEnergy Q b L+
      oldSignedFlatAffineContribution Q depth a b L-
      b^2*(Matrix.trace (coarseBlockMatrix (openCubeSet Q) a).lowerRight-2)+
      descendantsAverage Q depth (fun U => oldSignedCellError Q U depth nu sigma hnu hsigma k b L) := by
  intro Q a T
  have hf := old_signed_flat_signed_energy_bill Q depth nu sigma hnu hsigma k b L
  change Summable T.flat ∧ (∑' n,T.flat n)≤_ at hf
  have hr := old_signed_global_old_source_energy_bill m depth nu sigma hnu hsigma k b L
  change Summable T.source ∧ (∑' n,T.source n)≤_ at hr
  have hmp := old_signed_global_mixed_feedback_bill m depth nu sigma hnu hsigma k b L true
  change Summable T.mixedPlus ∧ |∑' n,T.mixedPlus n|≤_ at hmp
  have hmm := old_signed_global_mixed_feedback_bill m depth nu sigma hnu hsigma k b L false
  change Summable T.mixedMinus ∧ |∑' n,T.mixedMinus n|≤_ at hmm
  have hdp := old_signed_global_plus_feedback_bill Q depth nu sigma hnu hsigma k b L
  change Summable T.feedbackPlus ∧ |∑' n,T.feedbackPlus n|≤_ at hdp
  have hdr := old_signed_global_old_source_feedback_bill m depth nu sigma hnu hsigma k b L
  change Summable T.feedbackSource ∧ |∑' n,T.feedbackSource n|≤_ at hdr
  have hdm := old_signed_global_minus_feedback_bill Q depth nu sigma hnu hsigma k b L
  change Summable T.feedbackMinus ∧ |∑' n,T.feedbackMinus n|≤_ at hdm
  have hcp := old_signed_actual_top_covariance_bill Q depth nu sigma hnu hsigma k b L
  change Summable T.covarianceTop ∧ |∑' n,T.covarianceTop n|≤_ at hcp
  have hcm := old_signed_actual_bottom_covariance_bill Q depth nu sigma hnu hsigma k b L
  change Summable T.covarianceBottom ∧ (∑' n,T.covarianceBottom n)≤_ at hcm
  have hs := old_signed_trial_terms_series T hf.1 hr.1 hmp.1 hmm.1 hdp.1 hdr.1 hdm.1 hcp.1 hcm.1
  have hp := (le_abs_self _).trans hmp.2
  have hm := (neg_le_abs _).trans hmm.2
  have hdp' := (le_abs_self _).trans hdp.2
  have hdr' := (le_abs_self _).trans hdr.2
  have hdm' := (neg_le_abs _).trans hdm.2
  have hcp' := (le_abs_self _).trans hcp.2
  have htwo : 0≤(2:ℝ) := by norm_num
  have h0 := add_le_add hf.2 hr.2
  have h1 := add_le_add h0 (mul_le_mul_of_nonneg_left hp htwo)
  have h2 := add_le_add h1 (mul_le_mul_of_nonneg_left hm htwo)
  have h3 := add_le_add h2 (mul_le_mul_of_nonneg_left hdp' htwo)
  have h4 := add_le_add h3 (mul_le_mul_of_nonneg_left hdr' htwo)
  have h5 := add_le_add h4 (mul_le_mul_of_nonneg_left hdm' htwo)
  have h6 := add_le_add h5 hcp'
  have h7 := add_le_add h6 hcm.2
  refine ⟨hs.1,?_⟩
  calc
    (∑' n,T.total n) = _ := by rw [hs.2]; ring
    _ ≤ _ := h7
    _ = _ := by
      simp only [oldSignedCellError,old_signed_error_bill_split,descendantsAverage_add,
        descendantsAverage_mul_left]
      ring

end
end ASDExplicitGamma.Native

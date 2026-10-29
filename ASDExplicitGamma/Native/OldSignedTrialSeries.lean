module

public import ASDExplicitGamma.Native.OldSignedTrialTerms

/-! Complete sums of the finite signed trial expansion. All nine genuine
convergence statements are required before any real-tsum algebra. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian
noncomputable section

/-- Complete summation of the exact signed trial total. -/
theorem old_signed_trial_terms_series (T : OldSignedTrialTerms)
    (hflat : Summable T.flat) (hsource : Summable T.source)
    (hmixedPlus : Summable T.mixedPlus) (hmixedMinus : Summable T.mixedMinus)
    (hfeedbackPlus : Summable T.feedbackPlus) (hfeedbackSource : Summable T.feedbackSource)
    (hfeedbackMinus : Summable T.feedbackMinus)
    (hcovarianceTop : Summable T.covarianceTop) (hcovarianceBottom : Summable T.covarianceBottom) :
    Summable T.total ∧
      (∑' n,T.total n)=(∑' n,T.flat n)+(∑' n,T.source n)+2*(∑' n,T.mixedPlus n)-
        2*(∑' n,T.mixedMinus n)+2*(∑' n,T.feedbackPlus n)+2*(∑' n,T.feedbackSource n)-
        2*(∑' n,T.feedbackMinus n)+(∑' n,T.covarianceTop n)+(∑' n,T.covarianceBottom n) := by
  have h0 := hflat.add hsource
  have h1 := h0.add (hmixedPlus.mul_left 2)
  have h2 := h1.sub (hmixedMinus.mul_left 2)
  have h3 := h2.add (hfeedbackPlus.mul_left 2)
  have h4 := h3.add (hfeedbackSource.mul_left 2)
  have h5 := h4.sub (hfeedbackMinus.mul_left 2)
  have h6 := h5.add hcovarianceTop
  refine ⟨h6.add hcovarianceBottom,?_⟩
  unfold OldSignedTrialTerms.total
  rw [h6.tsum_add hcovarianceBottom,h5.tsum_add hcovarianceTop,
    h4.tsum_sub (hfeedbackMinus.mul_left 2),h3.tsum_add (hfeedbackSource.mul_left 2),
    h2.tsum_add (hfeedbackPlus.mul_left 2),h1.tsum_sub (hmixedMinus.mul_left 2),
    h0.tsum_add (hmixedPlus.mul_left 2),hflat.tsum_add hsource]
  simp only [tsum_mul_left]

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Scalar.OldHessianTrialMixedGlobalFeedback
public import ASDExplicitGamma.Scalar.OldHessianTrialFeedbackSpatialRoots
public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalDerivativeKappa
public import ASDExplicitGamma.Scalar.OldHessianTrialNinthParentProfile
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedHistoryAdapter

/-! Exact ninth OLD bill attached to the actual mixed-source derivative cross. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The actual original parent mixed-source derivative term with its
full generator coefficient two. -/
def oldHessianMixedFeedbackTerm (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (n : whiteBasisIndex) (ω : Cutoff.CutoffSample 2) : ℝ :=
  2*oldHessianMixedFeedbackMode (originCube 2 (m+129)) 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 (oldHessianOldOpenCoefficient (m+129) m ω)
    b (q3ModelLength (m+1)) n

/-- The actual complete mixed derivative cross is dominated by its
intrinsic paired-parent profile, before contracting probability. -/
theorem old_hessian_actual_mixed_feedback_profile
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun n => oldHessianMixedFeedbackTerm M m b n ω) ∧
      |∑' n,oldHessianMixedFeedbackTerm M m b n ω|≤
        (2*evalReal scalarRealEnv lowerKappaExpr*|b| *(63/50:ℝ))*
          (Real.sqrt 2*(oldHessianGroupedBank M m ω*
            Real.sqrt (oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω))+
          oldHessianGroupedBank M m ω*Real.sqrt (oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω)*
            Real.sqrt (oldHessianParentBottomPairEnergy M m ω)) := by
  filter_upwards [old_hessian_actual_fine_histories_le_bank M h hM hg N hpast m hm,
    old_hessian_actual_source_residual_envelope M h hM hg N hpast m hm] with ω hbank hsource
  let Q := originCube 2 (m+129)
  let L := q3ModelLength (m+1)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) k
  let κ := evalReal scalarRealEnv lowerKappaExpr*|b|
  let β := oldHessianGroupedBank M m ω
  let K := fun U : OldSignedCellIndex Q 134 => oldSignedDerivativeKappa (cubeScaleFactor U.val) b L.val
  let B := fun U : OldSignedCellIndex Q 134 => oldSignedInverseHistory U.val a
  let S := fun U : OldSignedCellIndex Q 134 => ∑' p,vectorPositiveHaarEnergy U.val
    (oldHessianFullModeColumn Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k b L p)
  let G := fun U : OldSignedCellIndex Q 134 => oldHessianBottomPairedCellEnergy Q U.val M.nu
    (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1 k
  have hκ : 0≤κ := mul_nonneg (by norm_num [evalReal,lowerKappaExpr,sc]) (abs_nonneg b)
  have hβ : 0≤β := ENNReal.toReal_nonneg
  have hS (U) : 0≤S U := tsum_nonneg (fun _ => vectorPositiveHaarEnergy_nonneg U.val _)
  have hG (U) : 0≤G U := Finset.sum_nonneg (fun _ _ => vectorWeakHaarEnergy_nonneg U.val _)
  have hB (U : OldSignedCellIndex Q 134) : B U≤β :=
    (old_hessian_fine_history_le Q 134 M.nu (Annealed.sigmaBar M m) k U.val U.property).trans (hbank 5 (by norm_num))
  have hKB (U : OldSignedCellIndex Q 134) : K U*B U≤κ*β :=
    mul_le_mul (old_hessian_physical_derivative_kappa m b U.val U.property) (hB U)
      (lemmaVInverseHistory_nonneg U.val a (Real.one_lt_rpow (by norm_num) (by norm_num))) hκ
  have hh := old_hessian_actual_mixed_global_feedback (m+129) 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k b L
  have hsp := old_hessian_feedback_spatial_roots Q 134 K B S G κ β (63/50) hκ hβ (by norm_num) hKB hS hG
  have hSavg : oldSignedCellAverage Q 134 S≤oldHessianSourceEnvelope M m b L ω :=
    (old_hessian_full_source_cell_average (m+129) 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k b L).trans_le (hsource b L).1
  have hroot := Real.sqrt_le_sqrt hSavg
  have hcap := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg 2))
    (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg (oldSignedCellAverage Q 134 G))))
      (mul_nonneg (mul_nonneg hκ (by norm_num : (0:ℝ)≤63/50)) hβ)
  have hbound := hh.2.trans (hsp.trans hcap)
  refine ⟨hh.1.mul_left 2,?_⟩
  change |∑' n,2*oldHessianMixedFeedbackMode Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k b L n|≤_
  rw [tsum_mul_left,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  exact (mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ)≤2)).trans_eq (by
    change 2*((κ*(63/50:ℝ)*β)*(Real.sqrt 2*Real.sqrt (oldHessianSourceEnvelope M m b L ω)+
      Real.sqrt (oldHessianParentBottomPairEnergy M m ω)*Real.sqrt (oldHessianSourceEnvelope M m b L ω)))=_
    dsimp only [κ,β,L]
    ring)

/-- Exact ninth OLD bill for the literal mixed-source derivative cross.
Every spatial, bank, source, parent and convergence estimate is proved internally. -/
theorem old_hessian_actual_ninth_bill
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (oldHessianNinthBill M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun n => oldHessianMixedFeedbackTerm M m b n ω) ∧
      |∑' n,oldHessianMixedFeedbackTerm M m b n ω|≤oldHessianNinthBill M m b ω) ∧
    (∫ ω,oldHessianNinthBill M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      b^2*evalReal scalarRealEnv lowerTerm9Expr := by
  have hh := old_hessian_ninth_parent_profile_bill M h hM hg N hpast m hm b
  refine ⟨hh.1,?_,hh.2.2⟩
  filter_upwards [old_hessian_actual_mixed_feedback_profile M h hM hg N hpast m hm b,hh.2.1] with ω hω hp
  exact ⟨hω.1,hω.2.trans hp⟩

end
end ASDExplicitGamma.Scalar

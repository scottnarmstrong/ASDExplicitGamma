module

public import ASDExplicitGamma.Native.OldSignedFlatProfileCaps
public import ASDExplicitGamma.Native.OldSignedActualTiledProfiles
public import ASDExplicitGamma.Native.OldSignedSpatialCauchy

/-! The actual AN boundary remainder after its joint spatial contraction. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Main Triadic Variational Response Algsuperdiff.Section3
noncomputable section

/-- Both actual covariance remainders are paid by the same untruncated weak
history. The harmonic flat boundary energy is averaged before estimating. -/
theorem old_signed_actual_boundary_spatial_payment (M : ABKModel 2) (n : ℤ)
    (r : ℕ) (t : ℝ) (ht : 0≤t ∧ t≤1) (ω : Cutoff.CutoffSample 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let sigma : ℝ := Annealed.sigmaBar M n
    let hsigma := (Annealed.sigmaBar_characterization M n).1
    let k := oldSignedPartialResponseCoefficient n 1 t ω
    let V := fun U => oldSignedPrimalErrorSize Q U M.nu sigma M.nu_pos hsigma k
    let G := fun U => oldSignedReciprocalErrorSize Q U M.nu sigma M.nu_pos hsigma k
    let C := b^2+3*(cubeScaleFactor Q/(3:ℝ)^r)*planarC1*|b| *Real.sqrt (mainFlatSigmaSq b L)
    let W := oldSignedActualTiledWeakProxy M n r t ω
    descendantsAverage Q r (fun U =>
      2*(oldSignedCovarianceBeta Q U b L true*V U)+
      2*(oldSignedCovarianceBeta Q U b L false*G U))≤2*C*(Real.sqrt W+Real.sqrt (2*W)) := by
  intro Q sigma hsigma k V G C W
  have hp := old_signed_actual_tiled_profile_bounds M n r t ht ω b L
  have hG : descendantsAverage Q r (fun U => G U^2)≤2*W := by
    apply le_trans _ hp.2.1
    unfold descendantsAverage
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro U _
    exact le_add_of_nonneg_left (sq_nonneg (V U))
  have hC : 0≤C := add_nonneg (sq_nonneg b)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg (Triadic.cubeScaleFactor_pos' Q).le (by positivity))) (Real.sqrt_nonneg _))
      (abs_nonneg b)) (Real.sqrt_nonneg _))
  have hplus := old_signed_descendant_cauchy Q r (fun U => oldSignedCovarianceBeta Q U b L true) V
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)
  have hminus := old_signed_descendant_cauchy Q r (fun U => oldSignedCovarianceBeta Q U b L false) G
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)
  have hplus' := hplus.trans (mul_le_mul (old_signed_covariance_beta_partition_cap Q r b L true)
    (Real.sqrt_le_sqrt hp.1) (Real.sqrt_nonneg _) hC)
  have hminus' := hminus.trans (mul_le_mul (old_signed_covariance_beta_partition_cap Q r b L false)
    (Real.sqrt_le_sqrt hG) (Real.sqrt_nonneg _) hC)
  rw [descendantsAverage_add,descendantsAverage_mul_left,descendantsAverage_mul_left]
  have hh := add_le_add (mul_le_mul_of_nonneg_left hplus' (by norm_num : (0:ℝ)≤2))
    (mul_le_mul_of_nonneg_left hminus' (by norm_num : (0:ℝ)≤2))
  exact hh.trans_eq (by dsimp only [C]; ring)

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.OldSignedCellMixedBounds
public import ASDExplicitGamma.Native.OldSignedReciprocalSpatialEnergy
public import ASDExplicitGamma.Native.OldSignedActualTiledProfiles
public import ASDExplicitGamma.Native.OldSignedJointSpatialProxy

/-! Spatial contraction of all three OLD source mixed-energy terms. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Triadic Algsuperdiff.Section3
noncomputable section

/-- The complete OLD source multiplier is nonnegative. -/
theorem old_signed_source_multiplier_nonneg (Q : TriadicCube 2) (r : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) : 0≤oldSignedSourceMultiplier Q r b L := by
  have hr := (diagMeshRadius_pos Q r).le
  unfold oldSignedSourceMultiplier
  positivity

/-- The common-bank majorant of the source quadratic term and both mixed
terms contracts through the whole spatial energies. No probability product
is split during this step. -/
theorem old_signed_actual_source_mixed_spatial_bound (M : ABKModel 2) (n : ℤ)
    (r : ℕ) (t : ℝ) (ht : 0≤t ∧ t≤1) (ω : Cutoff.CutoffSample 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let sigma : ℝ := Annealed.sigmaBar M n
    let hsigma := (Annealed.sigmaBar_characterization M n).1
    let k := oldSignedPartialResponseCoefficient n 1 t ω
    let d := fun U => oldSignedOldSourceSize Q U r M.nu sigma M.nu_pos hsigma k b L
    let B := rawShellBandLocalHistory M n 1 t ω
    let W := oldSignedActualTiledWeakProxy M n r t ω
    let ka := oldSignedSourceMultiplier Q r b L
    oldSignedCellAverage Q r (fun U =>
      let H := oldSignedMaxTraceHistory U.val (oldSignedPartialFrameField M n 1 t ω)
      let E := oldSignedActualPlusMeanProxy M n r U.val U.property t b L ω+
        oldSignedActualMinusMeanProxy M n r U.val U.property t b L ω
      let F := (B+1)^2*oldSignedFlatOscillationSize Q U.val b L true^2+
        (B*(1+2*H+Real.sqrt (2*H)))*oldSignedFlatOscillationSize Q U.val b L false^2
      B*d U.val^2+2*(d U.val*(Real.sqrt E+Real.sqrt F)))≤
        B*ka^2*W+2*(ka*Real.sqrt W*(Real.sqrt (oldSignedActualJointSpatialProxy M n r t b L ω)+
          Real.sqrt (oldSignedActualReciprocalSpatialEnergy M n r t b L ω))) := by
  intro Q sigma hsigma k d B W ka
  let E := fun (U : OldSignedCellIndex Q r) =>
    oldSignedActualPlusMeanProxy M n r U.val U.property t b L ω+
      oldSignedActualMinusMeanProxy M n r U.val U.property t b L ω
  let F := fun (U : OldSignedCellIndex Q r) =>
    let H := oldSignedMaxTraceHistory U.val (oldSignedPartialFrameField M n 1 t ω)
    (B+1)^2*oldSignedFlatOscillationSize Q U.val b L true^2+
      (B*(1+2*H+Real.sqrt (2*H)))*oldSignedFlatOscillationSize Q U.val b L false^2
  have hE (U : OldSignedCellIndex Q r) : 0≤E U :=
    add_nonneg (old_signed_actual_plus_mean_proxy_nonneg M n r U.val U.property t b L ω)
      (old_signed_actual_minus_mean_proxy_nonneg M n r U.val U.property t b L ω)
  have hF (U : OldSignedCellIndex Q r) : 0≤F U := by
    have hH := old_signed_actual_max_trace_history_nonneg M n r U.val U.property t ω
    exact add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (show 0≤B from ENNReal.toReal_nonneg)
        (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hH)) (Real.sqrt_nonneg _)))
          (sq_nonneg _))
  have hd : oldSignedCellAverage Q r (fun U => d U.val^2)≤ka^2*W := by
    rw [old_signed_cell_average_eq_descendantsAverage Q r (fun U => d U^2)]
    exact (old_signed_actual_tiled_profile_bounds M n r t ht ω b L).2.2
  exact old_signed_cell_source_mixed_bound Q r (fun U => d U.val) E F B ka W
    ENNReal.toReal_nonneg (old_signed_source_multiplier_nonneg Q r b L) hE hF hd

end
end ASDExplicitGamma.Native

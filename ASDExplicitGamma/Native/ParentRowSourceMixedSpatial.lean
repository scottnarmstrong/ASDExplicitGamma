module

public import ASDExplicitGamma.Native.ParentRowCellHistory
public import ASDExplicitGamma.Native.ParentBoundaryBandSpatialProxy
public import ASDExplicitGamma.Native.ParentBoundarySourceProfile
public import ASDExplicitGamma.Native.ParentBoundaryBandWeak
public import ASDExplicitGamma.Native.OldSignedCellMixedBounds
public import ASDExplicitGamma.Native.OldSignedReciprocalSpatialEnergy
public import ASDExplicitGamma.Native.OldSignedActualTiledProfiles
public import ASDExplicitGamma.Native.OldSignedJointSpatialProxy

/-! Spatial contraction of all three OLD source mixed-energy terms. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Triadic Algsuperdiff.Section3
noncomputable section

/-- Actual reciprocal spatial energy with the common bank and cellwise trace history retained. -/
def parentRowReciprocalSpatialEnergy (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  let B := (nativeSourceBandHistory M n height t ω).toReal
  oldSignedCellAverage Q r (fun U =>
    let H := oldSignedMaxTraceHistory U.val (parentBoundaryBandFrameField M n height t ω)
    (B+1)^2*oldSignedFlatOscillationSize Q U.val b L true^2+
      B*(1+2*H+Real.sqrt (2*H))*oldSignedFlatOscillationSize Q U.val b L false^2)

/-- The common-bank majorant of the source quadratic term and both mixed
terms contracts through the whole spatial energies. No probability product
is split during this step. -/
theorem parent_row_source_mixed_spatial (M : ABKModel 2) (n : ℤ)
    (height r : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let sigma : ℝ := Annealed.sigmaBar M n
    let hsigma := (Annealed.sigmaBar_characterization M n).1
    let k := pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω)
    let d := fun U => parentBoundaryCellSourceSize Q U M.nu sigma M.nu_pos hsigma k b L
    let B := (nativeSourceBandHistory M n height t ω).toReal
    let W := parentBoundaryBandWeakProxy M n height r t ω
    let ka := parentBoundaryPotentialSourceClock Q r b L
    oldSignedCellAverage Q r (fun U =>
      let H := oldSignedMaxTraceHistory U.val (parentBoundaryBandFrameField M n height t ω)
      let E := oldSignedFlatDirectionalMeanProxy Q U.val (parentBoundaryBandFrameField M n height t ω) b L true+
        oldSignedFlatDirectionalMeanProxy Q U.val (parentBoundaryBandFrameField M n height t ω) b L false
      let F := (B+1)^2*oldSignedFlatOscillationSize Q U.val b L true^2+
        (B*(1+2*H+Real.sqrt (2*H)))*oldSignedFlatOscillationSize Q U.val b L false^2
      B*d U.val^2+2*(d U.val*(Real.sqrt E+Real.sqrt F)))≤
        B*ka^2*W+2*(ka*Real.sqrt W*(Real.sqrt (parentBoundaryBandJointSpatialProxy M n height r t b L ω)+
          Real.sqrt (parentRowReciprocalSpatialEnergy M n height r t b L ω))) := by
  intro Q sigma hsigma k d B W ka
  let E := fun (U : OldSignedCellIndex Q r) =>
    oldSignedFlatDirectionalMeanProxy Q U.val (parentBoundaryBandFrameField M n height t ω) b L true+
      oldSignedFlatDirectionalMeanProxy Q U.val (parentBoundaryBandFrameField M n height t ω) b L false
  let F := fun (U : OldSignedCellIndex Q r) =>
    let H := oldSignedMaxTraceHistory U.val (parentBoundaryBandFrameField M n height t ω)
    (B+1)^2*oldSignedFlatOscillationSize Q U.val b L true^2+
      (B*(1+2*H+Real.sqrt (2*H)))*oldSignedFlatOscillationSize Q U.val b L false^2
  have hE (U : OldSignedCellIndex Q r) : 0≤E U :=
    add_nonneg (parent_row_cell_flat_proxy_nonneg M n height r U.val U.property t b L ω true)
      (parent_row_cell_flat_proxy_nonneg M n height r U.val U.property t b L ω false)
  have hF (U : OldSignedCellIndex Q r) : 0≤F U := by
    have hH := parent_row_cell_max_history_nonneg M n height r U.val U.property t ω
    exact add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (show 0≤B from ENNReal.toReal_nonneg)
        (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hH)) (Real.sqrt_nonneg _)))
          (sq_nonneg _))
  have hd : oldSignedCellAverage Q r (fun U => d U.val^2)≤ka^2*W := by
    rw [old_signed_cell_average_eq_descendantsAverage Q r (fun U => d U^2)]
    exact (parent_boundary_source_profile Q r M.nu sigma M.nu_pos hsigma k b L).trans
      (mul_le_mul_of_nonneg_left
        (parent_boundary_actual_band_weak_budget M n height r t ω).1 (sq_nonneg _))
  convert old_signed_cell_source_mixed_bound Q r (fun U => d U.val) E F B ka W
    ENNReal.toReal_nonneg (parent_boundary_potential_source_clock_nonneg Q r b L) hE hF hd using 1
  have he := old_signed_cell_average_eq_descendantsAverage Q r (fun U =>
    oldSignedFlatDirectionalMeanProxy Q U (parentBoundaryBandFrameField M n height t ω) b L true+
    oldSignedFlatDirectionalMeanProxy Q U (parentBoundaryBandFrameField M n height t ω) b L false)
  change oldSignedCellAverage Q r E=parentBoundaryBandJointSpatialProxy M n height r t b L ω at he
  rw [he]
  rfl

end
end ASDExplicitGamma.Native

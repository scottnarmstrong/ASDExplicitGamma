module

public import ASDExplicitGamma.Native.ParentRowSourceMixedSpatial
public import ASDExplicitGamma.Native.OldSignedQ1DerivativePayment
public import ASDExplicitGamma.Native.OldSignedCellDerivativeBounds
public import ASDExplicitGamma.Native.OldSignedActualProxyCarrier

/-! Actual root-energy profiles for the complete OLD derivative block. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- The literal minus directional energy on the complete source partition. -/
def parentRowMinusSpatialProxy (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldSignedCellAverage (originCube 2 n) r (fun U =>
    oldSignedFlatDirectionalMeanProxy (originCube 2 n) U.val
      (parentBoundaryBandFrameField M n height t ω) b L false)

/-- The reciprocal offset keeps the same bank and cellwise maximal history. -/
def parentRowReciprocalOffsetEnergy (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  let B := (nativeSourceBandHistory M n height t ω).toReal
  oldSignedCellAverage Q r (fun U =>
    let H := oldSignedMaxTraceHistory U.val (parentBoundaryBandFrameField M n height t ω)
    (Real.sqrt (B*(1+2*H+Real.sqrt (2*H)))+1)^2*oldSignedFlatOscillationSize Q U.val b L false^2)

/-- The actual complete weak proxy is nonnegative before any expectation. -/
theorem parent_row_weak_proxy_nonneg (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) : 0≤parentBoundaryBandWeakProxy M n height r t ω := by
  have hh := (parent_boundary_actual_band_weak_budget M n height r t ω).1
  exact (descendantsAverage_nonneg _ _ _ (fun _ _ => sq_nonneg _)).trans hh

/-- All derivative factors use the same tiled weak energy and the exact
joint/minus/offset spatial proxies. No stochastic estimate is assumed. -/
theorem parent_row_derivative_profile_bounds (M : ABKModel 2) (n : ℤ)
    (height r : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let sigma : ℝ := Annealed.sigmaBar M n
    let hsigma := (Annealed.sigmaBar_characterization M n).1
    let k := pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω)
    let G := fun (U : OldSignedCellIndex Q r) => oldSignedReciprocalErrorSize Q U.val M.nu sigma M.nu_pos hsigma k
    let d := fun (U : OldSignedCellIndex Q r) => parentBoundaryCellSourceSize Q U.val M.nu sigma M.nu_pos hsigma k b L
    let p := fun (U : OldSignedCellIndex Q r) => Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U.val (parentBoundaryBandFrameField M n height t ω) b L true)
    let q := fun (U : OldSignedCellIndex Q r) => Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U.val (parentBoundaryBandFrameField M n height t ω) b L false)
    let e := fun (U : OldSignedCellIndex Q r) =>
      let H := oldSignedMaxTraceHistory U.val (parentBoundaryBandFrameField M n height t ω)
      (Real.sqrt ((nativeSourceBandHistory M n height t ω).toReal*(1+2*H+Real.sqrt (2*H)))+1)*oldSignedFlatOscillationSize Q U.val b L false
    let W := parentBoundaryBandWeakProxy M n height r t ω
    Real.sqrt (oldSignedCellAverage Q r (fun U => G U^2))≤Real.sqrt (2*W) ∧
    Real.sqrt (oldSignedCellAverage Q r (fun U => d U^2))≤parentBoundaryPotentialSourceClock Q r b L*Real.sqrt W ∧
    Real.sqrt (oldSignedCellAverage Q r (fun U => p U^2))≤Real.sqrt (parentBoundaryBandJointSpatialProxy M n height r t b L ω) ∧
    Real.sqrt (oldSignedCellAverage Q r (fun U => q U^2))=Real.sqrt (parentRowMinusSpatialProxy M n height r t b L ω) ∧
    Real.sqrt (oldSignedCellAverage Q r (fun U => e U^2))=Real.sqrt (parentRowReciprocalOffsetEnergy M n height r t b L ω) := by
  intro Q sigma hsigma k G d p q e W
  have hp := parent_boundary_actual_band_weak_budget M n height r t ω
  have hG : oldSignedCellAverage Q r (fun U => G U^2)≤2*W := by
    rw [old_signed_cell_average_eq_descendantsAverage Q r
      (fun U => oldSignedReciprocalErrorSize Q U M.nu sigma M.nu_pos hsigma k^2)]
    apply le_trans _ hp.2.1
    unfold descendantsAverage
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact Finset.sum_le_sum (fun U _ => le_add_of_nonneg_left (sq_nonneg _))
  have hd : oldSignedCellAverage Q r (fun U => d U^2)≤parentBoundaryPotentialSourceClock Q r b L^2*W := by
    rw [old_signed_cell_average_eq_descendantsAverage Q r
      (fun U => parentBoundaryCellSourceSize Q U M.nu sigma M.nu_pos hsigma k b L^2)]
    exact (parent_boundary_source_profile Q r M.nu sigma M.nu_pos hsigma k b L).trans
      (mul_le_mul_of_nonneg_left hp.1 (sq_nonneg _))
  refine ⟨Real.sqrt_le_sqrt hG,old_signed_cell_root_cap Q r d _ W
    (parent_boundary_potential_source_clock_nonneg Q r b L) hd,?_,?_,?_⟩
  · apply Real.sqrt_le_sqrt
    change oldSignedCellAverage Q r (fun U => p U^2)≤descendantsAverage Q r _
    rw [←old_signed_cell_average_eq_descendantsAverage]
    apply old_signed_cell_average_mono
    intro U
    change (Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U.val (parentBoundaryBandFrameField M n height t ω) b L true))^2≤_
    rw [Real.sq_sqrt (parent_row_cell_flat_proxy_nonneg M n height r U.val U.property t b L ω true)]
    exact le_add_of_nonneg_right (parent_row_cell_flat_proxy_nonneg M n height r U.val U.property t b L ω false)
  · apply congrArg Real.sqrt
    change oldSignedCellAverage Q r (fun U => q U^2)=oldSignedCellAverage Q r _
    apply congrArg (oldSignedCellAverage Q r)
    funext U
    exact Real.sq_sqrt (parent_row_cell_flat_proxy_nonneg M n height r U.val U.property t b L ω false)
  · dsimp only [e]
    simp_rw [mul_pow]
    rfl

end
end ASDExplicitGamma.Native

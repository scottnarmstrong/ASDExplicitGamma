module

public import ASDExplicitGamma.Native.ParentRowCellHistory
public import ASDExplicitGamma.Native.ParentBoundaryBandSpatialProxy
public import ASDExplicitGamma.Native.OldSignedCellFlatBounds

/-! Spatial contraction of the four actual parent flat error terms. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- Full matrix history majorant weighted by the actual minus oscillations. -/
def parentRowFlatMatrixEnergy (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  oldSignedCellAverage Q r (fun U =>
    let H := oldSignedMaxTraceHistory U.val (parentBoundaryBandFrameField M n height t ω)
    (1+2*H+Real.sqrt (2*H))*oldSignedFlatOscillationSize Q U.val b L false^2)

/-- Corrector history majorant weighted by the actual flat minus energy. -/
def parentRowFlatCorrectorEnergy (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  oldSignedCellAverage Q r (fun U =>
    let H := oldSignedMaxTraceHistory U.val (parentBoundaryBandFrameField M n height t ω)
    ((1+inverseHistoryDiscount)*(1+2*H+Real.sqrt (2*H))*H)*oldSignedFlatL2Size Q U.val b L false^2)

/-- Whole-partition flat block using the actual joint affine covariance
energy, common inverse bank and weighted corrector/matrix histories. -/
def parentRowFlatEnvelope (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  let op := descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2)
  let om := descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2)
  (2*Real.sqrt op)*Real.sqrt (parentBoundaryBandJointSpatialProxy M n height r t b L ω)+
    op*(nativeSourceBandHistory M n height t ω).toReal+
    (2*Real.sqrt 2*Real.sqrt om)*Real.sqrt (parentRowFlatCorrectorEnergy M n height r t b L ω)+
    parentRowFlatMatrixEnergy M n height r t b L ω

/-- All four actual AN flat terms admit the common-bank envelope almost
surely, with history comparisons obtained from the actual model. -/
theorem parent_row_actual_flat_spatial_majorant
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ l<n,nativeInductionState M h l) (r : ℕ) (hr : r≤5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 n
      let a := parentBoundaryBandFrameField M n height t ω
      descendantsAverage Q r (fun U =>
        2*Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true)*oldSignedFlatOscillationSize Q U b L true+
        oldSignedInverseHistory U a*oldSignedFlatOscillationSize Q U b L true^2+
        2*Real.sqrt (2*oldSignedCorrectorHistory U a)*(oldSignedFlatL2Size Q U b L false*oldSignedFlatOscillationSize Q U b L false)+
        oldSignedResponseHistory U a*oldSignedFlatOscillationSize Q U b L false^2)≤
        parentRowFlatEnvelope M n height r t b L ω := by
  let Q := originCube 2 n
  have hall := parent_row_cell_inverse_history M h hM hg n height hpast r hr t ht.2
  filter_upwards [hall] with ω hω
  dsimp only
  let a := parentBoundaryBandFrameField M n height t ω
  let B := (nativeSourceBandHistory M n height t ω).toReal
  let H := fun (U : OldSignedCellIndex Q r) => oldSignedMaxTraceHistory U.val a
  let A := fun U => 1+2*H U+Real.sqrt (2*H U)
  let T := fun U => (1+inverseHistoryDiscount)*A U*H U
  let p := fun (U : OldSignedCellIndex Q r) => oldSignedFlatDirectionalMeanProxy Q U.val a b L true
  let y := fun (U : OldSignedCellIndex Q r) => oldSignedFlatL2Size Q U.val b L false
  let op := fun (U : OldSignedCellIndex Q r) => oldSignedFlatOscillationSize Q U.val b L true
  let om := fun (U : OldSignedCellIndex Q r) => oldSignedFlatOscillationSize Q U.val b L false
  have hT (U : OldSignedCellIndex Q r) : 0≤T U := by
    have hH := parent_row_cell_max_history_nonneg M n height r U.val U.property t ω
    exact mul_nonneg (mul_nonneg (add_nonneg (by norm_num) inverse_history_discount_range.1.le)
      (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hH)) (Real.sqrt_nonneg _))) hH
  have hJ : oldSignedCellAverage Q r p≤parentBoundaryBandJointSpatialProxy M n height r t b L ω := by
    change oldSignedCellAverage Q r p≤descendantsAverage Q r _
    rw [←old_signed_cell_average_eq_descendantsAverage]
    apply old_signed_cell_average_mono
    intro U
    exact le_add_of_nonneg_right (parent_row_cell_flat_proxy_nonneg M n height r U.val U.property t b L ω false)
  have hh := old_signed_cell_flat_block_bound Q r p T y op om A B
    (parentBoundaryBandJointSpatialProxy M n height r t b L ω)
    (fun U => parent_row_cell_flat_proxy_nonneg M n height r U.val U.property t b L ω true) hT hJ
  have hfinal := hh.trans_eq (show _=parentRowFlatEnvelope M n height r t b L ω from by
    rw [old_signed_cell_average_eq_descendantsAverage Q r
      (fun U => oldSignedFlatOscillationSize Q U b L true^2),
      old_signed_cell_average_eq_descendantsAverage Q r
      (fun U => oldSignedFlatOscillationSize Q U b L false^2)]
    unfold parentRowFlatEnvelope
    dsimp only [parentRowFlatCorrectorEnergy,parentRowFlatMatrixEnergy]
    ring)
  rw [←old_signed_cell_average_eq_descendantsAverage]
  refine (old_signed_cell_average_mono Q r (fun U => ?_)).trans hfinal
  have hm := parent_boundary_band_matrix_history_bounds M n height r U.val U.property t ω
  have hcross : 2*Real.sqrt (2*oldSignedCorrectorHistory U.val a)*(y U*om U)≤
      2*Real.sqrt (2*T U)*(y U*om U) := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left hm.2 (by norm_num : (0:ℝ)≤2))) (by norm_num : (0:ℝ)≤2))
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  exact add_le_add (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right (hω U.val U.property) (sq_nonneg _))) hcross)
      (mul_le_mul_of_nonneg_right hm.1 (sq_nonneg _))

end
end ASDExplicitGamma.Native

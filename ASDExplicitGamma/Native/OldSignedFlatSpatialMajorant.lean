module

public import ASDExplicitGamma.Native.OldSignedCellFlatBounds
public import ASDExplicitGamma.Native.OldSignedQ1FlatPayment
public import ASDExplicitGamma.Native.OldSignedActualProxyCarrier

/-! The literal AN flat block is below the paid spatial flat envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- All four actual AN flat terms admit the common-bank envelope almost
surely, with history comparisons obtained from the actual model. -/
theorem old_signed_actual_flat_spatial_majorant
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (r : ℕ) (hr : r≤5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 n
      let a := oldSignedPartialFrameField M n 1 t ω
      descendantsAverage Q r (fun U =>
        2*Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true)*oldSignedFlatOscillationSize Q U b L true+
        oldSignedInverseHistory U a*oldSignedFlatOscillationSize Q U b L true^2+
        2*Real.sqrt (2*oldSignedCorrectorHistory U a)*(oldSignedFlatL2Size Q U b L false*oldSignedFlatOscillationSize Q U b L false)+
        oldSignedResponseHistory U a*oldSignedFlatOscillationSize Q U b L false^2)≤
        oldSignedActualFlatEnvelope M n r t b L ω := by
  let Q := originCube 2 n
  have hi (U : OldSignedCellIndex Q r) := old_signed_actual_cell_inverse_history_split
    M h hM hg n hpast r hr U.val U.property t ht
  have hall : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ U : OldSignedCellIndex Q r,oldSignedInverseHistory U.val (oldSignedPartialFrameField M n 1 t ω)≤
        rawShellBandLocalHistory M n 1 t ω :=
    Filter.eventually_all.mpr (fun U => (hi U).mono (fun _ hh => hh.1))
  filter_upwards [hall] with ω hω
  dsimp only
  let a := oldSignedPartialFrameField M n 1 t ω
  let B := rawShellBandLocalHistory M n 1 t ω
  let H := fun (U : OldSignedCellIndex Q r) => oldSignedMaxTraceHistory U.val a
  let A := fun U => 1+2*H U+Real.sqrt (2*H U)
  let T := fun U => (1+inverseHistoryDiscount)*A U*H U
  let p := fun (U : OldSignedCellIndex Q r) => oldSignedActualPlusMeanProxy M n r U.val U.property t b L ω
  let y := fun (U : OldSignedCellIndex Q r) => oldSignedFlatL2Size Q U.val b L false
  let op := fun (U : OldSignedCellIndex Q r) => oldSignedFlatOscillationSize Q U.val b L true
  let om := fun (U : OldSignedCellIndex Q r) => oldSignedFlatOscillationSize Q U.val b L false
  have hT (U : OldSignedCellIndex Q r) : 0≤T U := by
    have hH := old_signed_actual_max_trace_history_nonneg M n r U.val U.property t ω
    exact mul_nonneg (mul_nonneg (add_nonneg (by norm_num) inverse_history_discount_range.1.le)
      (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hH)) (Real.sqrt_nonneg _))) hH
  have hJ : oldSignedCellAverage Q r p≤oldSignedActualJointSpatialProxy M n r t b L ω := by
    apply old_signed_cell_average_mono
    intro U
    exact le_add_of_nonneg_right (old_signed_actual_minus_mean_proxy_nonneg M n r U.val U.property t b L ω)
  have hh := old_signed_cell_flat_block_bound Q r p T y op om A B
    (oldSignedActualJointSpatialProxy M n r t b L ω)
    (fun U => old_signed_actual_plus_mean_proxy_nonneg M n r U.val U.property t b L ω) hT hJ
  have hfinal := hh.trans_eq (show _=oldSignedActualFlatEnvelope M n r t b L ω from by
    rw [old_signed_cell_average_eq_descendantsAverage Q r
      (fun U => oldSignedFlatOscillationSize Q U b L true^2),
      old_signed_cell_average_eq_descendantsAverage Q r
      (fun U => oldSignedFlatOscillationSize Q U b L false^2)]
    unfold oldSignedActualFlatEnvelope
    dsimp only [oldSignedActualFlatCorrectorEnergy,oldSignedActualFlatMatrixEnergy]
    ring)
  rw [←old_signed_cell_average_eq_descendantsAverage]
  refine (old_signed_cell_average_mono Q r (fun U => ?_)).trans hfinal
  have hm := old_signed_actual_matrix_history_bounds M n r U.val U.property t ht ω
  rw [old_signed_actual_plus_proxy_eq M n r U.val U.property]
  have hcross : 2*Real.sqrt (2*oldSignedCorrectorHistory U.val a)*(y U*om U)≤
      2*Real.sqrt (2*T U)*(y U*om U) := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left hm.2 (by norm_num : (0:ℝ)≤2))) (by norm_num : (0:ℝ)≤2))
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  exact add_le_add (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right (hω U) (sq_nonneg _))) hcross)
      (mul_le_mul_of_nonneg_right hm.1 (sq_nonneg _))

end
end ASDExplicitGamma.Native

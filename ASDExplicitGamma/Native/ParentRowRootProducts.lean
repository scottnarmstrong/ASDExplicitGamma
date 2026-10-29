module

public import ASDExplicitGamma.Native.ParentRowFlatExpectation
public import ASDExplicitGamma.Native.ParentRowWeakMoments
public import ASDExplicitGamma.Native.OldSignedSqrtProductExpectation

/-! Correlated weak and spatial root products for the parent generator. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- Nonnegativity of the minus affine energy on the actual partition. -/
theorem parent_row_minus_spatial_proxy_nonneg (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    0≤parentRowMinusSpatialProxy M n height r t b L ω := by
  unfold parentRowMinusSpatialProxy oldSignedCellAverage
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg (fun U _ =>
    parent_row_cell_flat_proxy_nonneg M n height r U.val U.property t b L ω false)

/-- Nonnegativity of the reciprocal energy, before any probabilistic bound. -/
theorem parent_row_reciprocal_spatial_energy_nonneg (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    0≤parentRowReciprocalSpatialEnergy M n height r t b L ω := by
  unfold parentRowReciprocalSpatialEnergy oldSignedCellAverage
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro U _
  have hH := parent_boundary_band_max_trace_history_nonneg M n height r U.val U.property t ω
  exact add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hH)) (Real.sqrt_nonneg _)))
      (sq_nonneg _))

/-- Nonnegativity of the reciprocal offset energy. -/
theorem parent_row_reciprocal_offset_energy_nonneg (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    0≤parentRowReciprocalOffsetEnergy M n height r t b L ω := by
  unfold parentRowReciprocalOffsetEnergy oldSignedCellAverage
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The actual weak/joint product is integrable and controlled without independence. -/
theorem parent_row_weak_joint_product
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let W := parentBoundaryBandWeakProxy M n height r t
    let E := parentBoundaryBandJointSpatialProxy M n height r t b L
    Integrable (fun ω => Real.sqrt (W ω)*Real.sqrt (E ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.sqrt (W ω)*Real.sqrt (E ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      Real.sqrt (theta M*parentRowWeakAllowance height t)*Real.sqrt ((theta M*parentRowWeakAllowance height t)*b^2) := by
  intro W E
  have hw := parent_row_weak_expectation M h hM hg n height hheight hh16 hpast hstate r hr t ht
  have he := parent_row_joint_spatial_proxy_payment M h hM hg n height hheight hh16 r hr t ht hpast hstate b L
  have hh := old_signed_sqrt_product_expectation (Cutoff.cutoffSampleLaw M).toMeasure W E hw.1 he.1
    (parent_row_weak_proxy_nonneg M n height r t)
    (parent_row_joint_spatial_proxy_nonneg M n height r t b L)
  exact ⟨hh.1,hh.2.trans (mul_le_mul (Real.sqrt_le_sqrt hw.2) (Real.sqrt_le_sqrt he.2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))⟩

/-- The actual weak/minus product is integrable and controlled without independence. -/
theorem parent_row_weak_minus_product
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let W := parentBoundaryBandWeakProxy M n height r t
    let E := parentRowMinusSpatialProxy M n height r t b L
    Integrable (fun ω => Real.sqrt (W ω)*Real.sqrt (E ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.sqrt (W ω)*Real.sqrt (E ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      Real.sqrt (theta M*parentRowWeakAllowance height t)*Real.sqrt (((theta M/2)*parentRowWeakAllowance height t)*parentBoundaryDirichletEnergy (originCube 2 n) b L) := by
  intro W E
  have hw := parent_row_weak_expectation M h hM hg n height hheight hh16 hpast hstate r hr t ht
  have he := parent_row_minus_spatial_proxy_payment M h hM hg n height hheight hh16 r hr t ht hpast hstate b L
  have hh := old_signed_sqrt_product_expectation (Cutoff.cutoffSampleLaw M).toMeasure W E hw.1 he.1
    (parent_row_weak_proxy_nonneg M n height r t)
    (parent_row_minus_spatial_proxy_nonneg M n height r t b L)
  exact ⟨hh.1,hh.2.trans (mul_le_mul (Real.sqrt_le_sqrt hw.2) (Real.sqrt_le_sqrt he.2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))⟩

/-- The actual weak/reciprocal product is integrable and controlled without independence. -/
theorem parent_row_weak_reciprocal_product
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let W := parentBoundaryBandWeakProxy M n height r t
    let E := parentRowReciprocalSpatialEnergy M n height r t b L
    Integrable (fun ω => Real.sqrt (W ω)*Real.sqrt (E ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.sqrt (W ω)*Real.sqrt (E ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      Real.sqrt (theta M*parentRowWeakAllowance height t)*Real.sqrt (((3683/2500:ℝ)+1)^2*descendantsAverage (originCube 2 n) r (fun U => oldSignedFlatOscillationSize (originCube 2 n) U b L true^2)+(3683/2500:ℝ)*(1+2*parentHistorySourceEnvelope height r t+Real.sqrt (2*parentHistorySourceEnvelope height r t))*descendantsAverage (originCube 2 n) r (fun U => oldSignedFlatOscillationSize (originCube 2 n) U b L false^2)) := by
  intro W E
  have hw := parent_row_weak_expectation M h hM hg n height hheight hh16 hpast hstate r hr t ht
  have he := parent_row_reciprocal_spatial_energy M h hM hg n hpast hstate height r (by omega) hheight t ht b L
  have hh := old_signed_sqrt_product_expectation (Cutoff.cutoffSampleLaw M).toMeasure W E hw.1 he.1
    (parent_row_weak_proxy_nonneg M n height r t)
    (parent_row_reciprocal_spatial_energy_nonneg M n height r t b L)
  exact ⟨hh.1,hh.2.trans (mul_le_mul (Real.sqrt_le_sqrt hw.2) (Real.sqrt_le_sqrt he.2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))⟩

/-- The actual weak/offset product is integrable and controlled without independence. -/
theorem parent_row_weak_offset_product
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let W := parentBoundaryBandWeakProxy M n height r t
    let E := parentRowReciprocalOffsetEnergy M n height r t b L
    Integrable (fun ω => Real.sqrt (W ω)*Real.sqrt (E ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.sqrt (W ω)*Real.sqrt (E ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      Real.sqrt (theta M*parentRowWeakAllowance height t)*Real.sqrt ((Real.sqrt ((3683/2500:ℝ)*(1+2*parentHistorySourceEnvelope height r t+Real.sqrt (2*parentHistorySourceEnvelope height r t)))+1)^2*descendantsAverage (originCube 2 n) r (fun U => oldSignedFlatOscillationSize (originCube 2 n) U b L false^2)) := by
  intro W E
  have hw := parent_row_weak_expectation M h hM hg n height hheight hh16 hpast hstate r hr t ht
  have he := parent_row_reciprocal_offset_energy M h hM hg n hpast hstate height r (by omega) hheight t ht b L
  have hh := old_signed_sqrt_product_expectation (Cutoff.cutoffSampleLaw M).toMeasure W E hw.1 he.1
    (parent_row_weak_proxy_nonneg M n height r t)
    (parent_row_reciprocal_offset_energy_nonneg M n height r t b L)
  exact ⟨hh.1,hh.2.trans (mul_le_mul (Real.sqrt_le_sqrt hw.2) (Real.sqrt_le_sqrt he.2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))⟩

end
end ASDExplicitGamma.Native

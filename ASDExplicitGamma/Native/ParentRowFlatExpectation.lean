module

public import ASDExplicitGamma.Native.ParentRowFlatMoments
public import ASDExplicitGamma.Native.ParentRowSpatialProxyMoments
public import ASDExplicitGamma.Native.ParentRowReciprocalMoments

/-! The entire OLD flat-energy block after spatial and probability averaging. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Algsuperdiff.Section3
noncomputable section

/-- The actual corrector energy is nonnegative before taking its root. -/
theorem parent_row_flat_corrector_energy_nonneg (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    0≤parentRowFlatCorrectorEnergy M n height r t b L ω := by
  unfold parentRowFlatCorrectorEnergy oldSignedCellAverage
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro U _
  have hH := parent_boundary_band_max_trace_history_nonneg M n height r U.val U.property t ω
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (add_nonneg (by norm_num) inverse_history_discount_range.1.le)
      (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hH)) (Real.sqrt_nonneg _))) hH)
        (sq_nonneg _)

/-- The actual joint spatial proxy is pointwise nonnegative. -/
theorem parent_row_joint_spatial_proxy_nonneg (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    0≤parentBoundaryBandJointSpatialProxy M n height r t b L ω := by
  apply descendantsAverage_nonneg
  intro U hU
  exact add_nonneg (parent_row_cell_flat_proxy_nonneg M n height r U hU t b L ω true)
    (parent_row_cell_flat_proxy_nonneg M n height r U hU t b L ω false)

/-- The entire flat envelope is integrable and has the sharp joint affine,
corrector, inverse and matrix moment payment. -/
theorem parent_row_flat_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (height : ℕ) (hheight : 1≤height) (hh16 : height≤16) (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let op := descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2)
    let om := descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2)
    let C := parentHistorySourceEnvelope height r t
    let A := 1+2*C+Real.sqrt (2*C)
    Integrable (parentRowFlatEnvelope M n height r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,parentRowFlatEnvelope M n height r t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (2*Real.sqrt op)*Real.sqrt (theta M*parentRowWeakAllowance height t*b^2)+op*(3683/2500:ℝ)+
      (2*Real.sqrt 2*Real.sqrt om)*Real.sqrt ((theta M*((1+inverseHistoryDiscount)*A*C))*parentBoundaryDirichletEnergy Q b L)+A*om := by
  intro Q op om C A
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let J := parentBoundaryBandJointSpatialProxy M n height r t b L
  let T := parentRowFlatCorrectorEnergy M n height r t b L
  let F := parentRowFlatMatrixEnergy M n height r t b L
  let B := fun ω => (nativeSourceBandHistory M n height t ω).toReal
  have hj := parent_row_joint_spatial_proxy_payment M h hM hg n height hheight hh16 r hr t ht hpast hstate b L
  have hJ := old_signed_sqrt_expectation μ J hj.1
    (parent_row_joint_spatial_proxy_nonneg M n height r t b L)
  have hc := parent_row_flat_corrector_energy M h hM hg n hpast hstate height r (by omega) hheight t ht b L
  have hT := old_signed_sqrt_expectation μ T hc.1
    (parent_row_flat_corrector_energy_nonneg M n height r t b L)
  have hf := parent_row_flat_matrix_energy M h hM hg n hpast hstate height r (by omega) hheight t ht b L
  have hb := parent_row_bank_offset_moments M h hM hg n height hpast t ht
  have hiJ : Integrable (fun ω => (2*Real.sqrt op)*Real.sqrt (J ω)) μ := hJ.1.const_mul _
  have hiB : Integrable (fun ω => op*B ω) μ := hb.1.const_mul _
  have hiT : Integrable (fun ω => (2*Real.sqrt 2*Real.sqrt om)*Real.sqrt (T ω)) μ := hT.1.const_mul _
  have hiJB : Integrable (fun ω => (2*Real.sqrt op)*Real.sqrt (J ω)+op*B ω) μ := hiJ.add hiB
  have hiJBT : Integrable (fun ω => (2*Real.sqrt op)*Real.sqrt (J ω)+op*B ω+
    (2*Real.sqrt 2*Real.sqrt om)*Real.sqrt (T ω)) μ := hiJB.add hiT
  refine ⟨hiJBT.add hf.1,?_⟩
  change (∫ ω,(2*Real.sqrt op)*Real.sqrt (J ω)+op*B ω+
    (2*Real.sqrt 2*Real.sqrt om)*Real.sqrt (T ω)+F ω ∂μ)≤_
  rw [integral_add hiJBT hf.1,integral_add hiJB hiT,integral_add hiJ hiB,
    integral_const_mul,integral_const_mul,integral_const_mul]
  have hop : 0≤op := descendantsAverage_nonneg Q r _ (fun _ _ => sq_nonneg _)
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (hJ.2.trans (Real.sqrt_le_sqrt hj.2)) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
    (mul_le_mul_of_nonneg_left hb.2.1 hop))
    (mul_le_mul_of_nonneg_left (hT.2.trans (Real.sqrt_le_sqrt hc.2))
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))) hf.2

end
end ASDExplicitGamma.Native

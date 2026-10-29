module

public import ASDExplicitGamma.Native.OldSignedFlatHistoryEnergies
public import ASDExplicitGamma.Native.OldSignedQ1WeakContractions
public import ASDExplicitGamma.Native.OldSignedLocalHistoryMoments

/-! The entire OLD flat-energy block after spatial and probability averaging. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Algsuperdiff.Section3
noncomputable section

/-- The actual corrector energy is nonnegative before taking its root. -/
theorem old_signed_flat_corrector_energy_nonneg (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    0≤oldSignedActualFlatCorrectorEnergy M n r t b L ω := by
  unfold oldSignedActualFlatCorrectorEnergy oldSignedCellAverage
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro U _
  have hH := old_signed_actual_max_trace_history_nonneg M n r U.val U.property t ω
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (add_nonneg (by norm_num) inverse_history_discount_range.1.le)
      (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hH)) (Real.sqrt_nonneg _))) hH)
        (sq_nonneg _)

/-- Whole-partition flat block using the actual joint affine covariance
energy, common inverse bank and weighted corrector/matrix histories. -/
def oldSignedActualFlatEnvelope (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  let op := descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2)
  let om := descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2)
  (2*Real.sqrt op)*Real.sqrt (oldSignedActualJointSpatialProxy M n r t b L ω)+
    op*rawShellBandLocalHistory M n 1 t ω+
    (2*Real.sqrt 2*Real.sqrt om)*Real.sqrt (oldSignedActualFlatCorrectorEnergy M n r t b L ω)+
    oldSignedActualFlatMatrixEnergy M n r t b L ω

/-- The entire flat envelope is integrable and has the sharp joint affine,
corrector, inverse and matrix moment payment. -/
theorem old_signed_q1_flat_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let op := descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U b L true^2)
    let om := descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U b L false^2)
    let C := oldSignedQ1PanelHistory t
    let A := 1+2*C+Real.sqrt (2*C)
    Integrable (oldSignedActualFlatEnvelope M n 5 t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualFlatEnvelope M n 5 t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (2*Real.sqrt op)*Real.sqrt (theta M*oldSignedQ1PanelXi t*b^2)+op*(3683/2500:ℝ)+
      (2*Real.sqrt 2*Real.sqrt om)*Real.sqrt ((theta M*((1+inverseHistoryDiscount)*A*C))*b^2)+A*om := by
  intro Q op om C A
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let J := oldSignedActualJointSpatialProxy M n 5 t b L
  let T := oldSignedActualFlatCorrectorEnergy M n 5 t b L
  let F := oldSignedActualFlatMatrixEnergy M n 5 t b L
  let B := rawShellBandLocalHistory M n 1 t
  have hj := old_signed_q1_joint_proxy_expectation M h hM hg n hpast t ht b L
  have hJ := old_signed_sqrt_expectation μ J hj.1
    (old_signed_actual_joint_spatial_proxy_nonneg M n 5 t b L)
  have hc := old_signed_q1_flat_corrector_energy M h hM hg n hpast 5 rfl t ht b L
  have hT := old_signed_sqrt_expectation μ T hc.1
    (old_signed_flat_corrector_energy_nonneg M n 5 t b L)
  have hf := old_signed_q1_flat_matrix_energy M h hM hg n hpast 5 rfl t ht b L
  have hb := old_signed_actual_local_history_moments M h hM hg n (fun l hl => hpast l hl.le) t ht
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
  have hop : 0≤op := descendantsAverage_nonneg Q 5 _ (fun _ _ => sq_nonneg _)
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (hJ.2.trans (Real.sqrt_le_sqrt hj.2)) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
    (mul_le_mul_of_nonneg_left hb.2.1 hop))
    (mul_le_mul_of_nonneg_left (hT.2.trans (Real.sqrt_le_sqrt hc.2))
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))) hf.2

end
end ASDExplicitGamma.Native

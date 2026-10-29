module

public import ASDExplicitGamma.Native.OldSignedSourceMixedSpatial
public import ASDExplicitGamma.Native.OldSignedQ1ReciprocalContractions
public import ASDExplicitGamma.Native.OldSignedQ1BankWeightedWeak

/-! Annealed payment of the complete OLD source quadratic and mixed block. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Algsuperdiff.Section3
noncomputable section

/-- Integrable actual-law majorant of the OLD quadratic and both mixed
terms. Its three products are retained in the common probability law. -/
def oldSignedActualSourceMixedEnvelope (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let k := oldSignedSourceMultiplier (originCube 2 n) r b L
  let W := oldSignedActualTiledWeakProxy M n r t ω
  k^2*(rawShellBandLocalHistory M n 1 t ω*W)+
    (2*k)*(Real.sqrt W*Real.sqrt (oldSignedActualJointSpatialProxy M n r t b L ω))+
    (2*k)*(Real.sqrt W*Real.sqrt (oldSignedActualReciprocalSpatialEnergy M n r t b L ω))

/-- The complete quadratic/mixed OLD-source block is paid from the actual
q1 weak and bank moments, including integrability. -/
theorem old_signed_q1_source_mixed_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let k := oldSignedSourceMultiplier (originCube 2 n) 5 b L
    let X := theta M*oldSignedQ1PanelXi t
    Integrable (oldSignedActualSourceMixedEnvelope M n 5 t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualSourceMixedEnvelope M n 5 t b L ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      k^2*((3683/2500:ℝ)*X)+2*k*(X*|b|)+
        2*k*(Real.sqrt X*Real.sqrt (oldSignedQ1ReciprocalSpatialCap (originCube 2 n) 5 t b L)) := by
  intro k X
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let W := oldSignedActualTiledWeakProxy M n 5 t
  let B := rawShellBandLocalHistory M n 1 t
  let J := oldSignedActualJointSpatialProxy M n 5 t b L
  let E := oldSignedActualReciprocalSpatialEnergy M n 5 t b L
  have hb := old_signed_q1_bank_weighted_weak M h hM hg n hpast t ht 1 (by norm_num)
  simp only [pow_one] at hb
  have hj := old_signed_q1_joint_root_contraction M h hM hg n hpast t ht b L
  have he := old_signed_q1_reciprocal_root_contraction M h hM hg n hpast t ht b L
  have hiB : Integrable (fun ω => k^2*(B ω*W ω)) μ := hb.1.const_mul _
  have hiJ : Integrable (fun ω => (2*k)*(Real.sqrt (W ω)*Real.sqrt (J ω))) μ := hj.1.const_mul _
  have hiE : Integrable (fun ω => (2*k)*(Real.sqrt (W ω)*Real.sqrt (E ω))) μ := he.1.const_mul _
  have hiBJ : Integrable (fun ω => k^2*(B ω*W ω)+(2*k)*(Real.sqrt (W ω)*Real.sqrt (J ω))) μ := hiB.add hiJ
  refine ⟨hiBJ.add hiE,?_⟩
  change (∫ ω,k^2*(B ω*W ω)+(2*k)*(Real.sqrt (W ω)*Real.sqrt (J ω))+
    (2*k)*(Real.sqrt (W ω)*Real.sqrt (E ω)) ∂μ)≤_
  rw [integral_add hiBJ hiE,integral_add hiB hiJ,integral_const_mul,integral_const_mul,integral_const_mul]
  have hk := old_signed_source_multiplier_nonneg (originCube 2 n) 5 b L
  have h2k : 0≤2*k := mul_nonneg (by norm_num) hk
  have hbc : (∫ ω,B ω*W ω ∂μ)≤(3683/2500:ℝ)*X := by
    exact hb.2.trans_eq (by dsimp only [X]; ring)
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hbc (sq_nonneg k))
    (mul_le_mul_of_nonneg_left hj.2 h2k)) (mul_le_mul_of_nonneg_left he.2 h2k)

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.ParentRowRootProducts
public import ASDExplicitGamma.Native.ParentRowErrorSpatial

/-! Expectation of the complete source quadratic and mixed parent block. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Algsuperdiff.Section3
noncomputable section

/-- The exact reciprocal moment cap retains both spatial oscillation energies. -/
def parentRowReciprocalCap (n : ℤ) (height r : ℕ) (t b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  let Q := originCube 2 n
  let C := parentHistorySourceEnvelope height r t
  let A := 1+2*C+Real.sqrt (2*C)
  ((3683/2500:ℝ)+1)^2*descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2)+
    (3683/2500:ℝ)*A*descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2)

/-- All source quadratic and mixed terms are paid in the same actual law. -/
theorem parent_row_source_mixed_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let k := parentBoundaryPotentialSourceClock (originCube 2 n) r b L
    let X := theta M*parentRowWeakAllowance height t
    Integrable (parentRowSourceMixedEnvelope M n height r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,parentRowSourceMixedEnvelope M n height r t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      k^2*((3683/2500:ℝ)*X)+(2*k)*(Real.sqrt X*Real.sqrt (X*b^2))+
        (2*k)*(Real.sqrt X*Real.sqrt (parentRowReciprocalCap n height r t b L)) := by
  intro k X
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let W := parentBoundaryBandWeakProxy M n height r t
  let B := fun ω => (nativeSourceBandHistory M n height t ω).toReal
  let J := parentBoundaryBandJointSpatialProxy M n height r t b L
  let E := parentRowReciprocalSpatialEnergy M n height r t b L
  have hb := parent_weak_bank_weighted_return M h hM hg n height hheight hh16 hpast hstate r hr t ht 1 (by norm_num)
  simp only [pow_one] at hb
  have hj := parent_row_weak_joint_product M h hM hg n height hheight hh16 hpast hstate r hr t ht b L
  have he := parent_row_weak_reciprocal_product M h hM hg n height hheight hh16 hpast hstate r hr t ht b L
  have hiB : Integrable (fun ω => k^2*(B ω*W ω)) μ := hb.1.const_mul _
  have hiJ : Integrable (fun ω => (2*k)*(Real.sqrt (W ω)*Real.sqrt (J ω))) μ := hj.1.const_mul _
  have hiE : Integrable (fun ω => (2*k)*(Real.sqrt (W ω)*Real.sqrt (E ω))) μ := he.1.const_mul _
  have hid : Integrable (fun ω => k^2*(B ω*W ω)+(2*k)*(Real.sqrt (W ω)*Real.sqrt (J ω))) μ := hiB.add hiJ
  have hid' := hid.add hiE
  have hidEq : parentRowSourceMixedEnvelope M n height r t b L=
      fun ω => k^2*(B ω*W ω)+(2*k)*(Real.sqrt (W ω)*Real.sqrt (J ω))+
        (2*k)*(Real.sqrt (W ω)*Real.sqrt (E ω)) := by
    funext ω
    dsimp only [parentRowSourceMixedEnvelope,k,B,W,J,E]
    ring
  rw [hidEq]
  refine ⟨hid',?_⟩
  rw [integral_add hid hiE,integral_add hiB hiJ,integral_const_mul,integral_const_mul,integral_const_mul]
  have hk := parent_boundary_potential_source_clock_nonneg (originCube 2 n) r b L
  have h2k : 0≤2*k := mul_nonneg (by norm_num) hk
  have hbc : (∫ ω,B ω*W ω ∂μ)≤(3683/2500:ℝ)*X := by
    exact hb.2.trans_eq (by dsimp only [X,parentRowWeakAllowance]; ring)
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hbc (sq_nonneg k))
    (mul_le_mul_of_nonneg_left hj.2 h2k)) (mul_le_mul_of_nonneg_left he.2 h2k)

end
end ASDExplicitGamma.Native

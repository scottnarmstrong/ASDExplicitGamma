module

public import ASDExplicitGamma.Native.ParentRowBoundary
public import ASDExplicitGamma.Native.ParentRowWeakMoments

/-! Sharp expectation of the two separately centered parent boundary charges. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Algsuperdiff.Section3
noncomputable section

/-- The actual centered charge envelope is integrable and consumes the
sharp weak moment with the corrected two roots. -/
theorem parent_row_sharp_charge_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16) (r : ℕ) (hr : r=5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (hpast : ∀ k<n,nativeInductionState M h k)
    (hstate : nativeInductionState M h n)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let X := theta M*parentRowWeakAllowance height t
    let betaPlus := parentRowBeta n r b L true
    let betaMinus := parentRowBeta n r b L false
    Integrable (parentRowChargeEnvelope M n height r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ omega,parentRowChargeEnvelope M n height r t b L omega
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤2*betaPlus*Real.sqrt X+2*betaMinus*Real.sqrt (2*X) := by
  intro X betaPlus betaMinus
  let xi := parentBoundaryBandWeakProxy M n height r t
  have hi := parent_row_weak_expectation M h hM hg n height hheight hh16 hpast hstate r hr t ht
  have hn := parent_row_weak_proxy_nonneg M n height r t
  have h1 := old_signed_sqrt_expectation (Cutoff.cutoffSampleLaw M).toMeasure xi hi.1 hn
  have h2 := old_signed_sqrt_expectation (Cutoff.cutoffSampleLaw M).toMeasure (fun omega => 2*xi omega)
    (hi.1.const_mul 2) (fun omega => mul_nonneg (by norm_num) (hn omega))
  have hp : 0≤2*betaPlus := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hm : 0≤2*betaMinus := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have he : parentRowChargeEnvelope M n height r t b L=
      (fun omega => 2*betaPlus*Real.sqrt (xi omega)+2*betaMinus*Real.sqrt (2*xi omega)) := rfl
  rw [he]
  refine ⟨(h1.1.const_mul _).add (h2.1.const_mul _),?_⟩
  rw [integral_add (h1.1.const_mul _) (h2.1.const_mul _),integral_const_mul,integral_const_mul]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (h1.2.trans (Real.sqrt_le_sqrt hi.2)) hp
  · have hh : (∫ omega,2*xi omega ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤2*X := by
      rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left hi.2 (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)
    exact mul_le_mul_of_nonneg_left (h2.2.trans (Real.sqrt_le_sqrt hh)) hm

end
end ASDExplicitGamma.Native

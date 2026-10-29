module

public import ASDExplicitGamma.Native.ParentRowRootProducts
public import ASDExplicitGamma.Native.ParentRowDerivativeSpatial

/-! All seven parent derivative feedback terms on their common actual law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Triadic Algsuperdiff.Section3
noncomputable section

/-- Every term of the derivative envelope is integrable and paid with the
sharp actual parent moments. No estimate of a source term is assumed. -/
theorem parent_row_derivative_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (height : ℕ) (hheight : 1≤height) (hh16 : height≤16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let kd := oldSignedDerivativeKappa (cubeScaleFactor Q/3^r) b L.1
    let ka := parentBoundaryPotentialSourceClock Q r b L
    let op := Real.sqrt (descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2))
    let om := Real.sqrt (descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2))
    let C := parentHistorySourceEnvelope height r t
    let A := 1+2*C+Real.sqrt (2*C)
    let X := theta M*parentRowWeakAllowance height t
    let Ncap := ((theta M/2)*parentRowWeakAllowance height t)*parentBoundaryDirichletEnergy Q b L
    let Ecap := (Real.sqrt ((3683/2500:ℝ)*A)+1)^2*om^2
    Integrable (parentRowDerivativeEnvelope M n height r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,parentRowDerivativeEnvelope M n height r t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (2*kd*Real.sqrt 2)*(Real.sqrt X*Real.sqrt (X*b^2)+Real.sqrt X*Real.sqrt (Ncap)+Real.sqrt X*(Real.sqrt Ecap)+
        ((1+inverseHistoryDiscount)*(op+ka))*((3683/2500:ℝ)*Real.sqrt X)+
        ((1+inverseHistoryDiscount)*ka)*((3683/2500:ℝ)*X)+Real.sqrt (Ncap)+Real.sqrt Ecap) := by
  intro Q kd ka op om C A X Ncap Ecap
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let W := parentBoundaryBandWeakProxy M n height r t
  let B := fun ω => (nativeSourceBandHistory M n height t ω).toReal
  let J := parentBoundaryBandJointSpatialProxy M n height r t b L
  let N := parentRowMinusSpatialProxy M n height r t b L
  let E := parentRowReciprocalOffsetEnergy M n height r t b L
  let a₁ := (1+inverseHistoryDiscount)*(op+ka)
  let a₂ := (1+inverseHistoryDiscount)*ka
  have hj := parent_row_weak_joint_product M h hM hg n height hheight hh16 hpast hstate r hr t ht b L
  have hn := parent_row_weak_minus_product M h hM hg n height hheight hh16 hpast hstate r hr t ht b L
  have he := parent_row_weak_offset_product M h hM hg n height hheight hh16 hpast hstate r hr t ht b L
  have hb := parent_row_bank_weak_root M h hM hg n height hheight hh16 hpast hstate r hr t ht
  have hw := parent_weak_bank_weighted_return M h hM hg n height hheight hh16 hpast hstate r hr t ht 1 (by norm_num)
  simp only [pow_one] at hw
  have hNm := parent_row_minus_spatial_proxy_payment M h hM hg n height hheight hh16 r hr t ht hpast hstate b L
  have hNr := old_signed_sqrt_expectation μ N hNm.1 (parent_row_minus_spatial_proxy_nonneg M n height r t b L)
  have hrn : Integrable (fun ω => Real.sqrt (N ω)) μ ∧ (∫ ω,Real.sqrt (N ω) ∂μ)≤Real.sqrt Ncap :=
    ⟨hNr.1,hNr.2.trans (Real.sqrt_le_sqrt hNm.2)⟩
  have hEm := parent_row_reciprocal_offset_energy M h hM hg n hpast hstate height r (by omega) hheight t ht b L
  have hom : om^2=descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2) :=
    Real.sq_sqrt (descendantsAverage_nonneg Q r _ (fun _ _ => sq_nonneg _))
  have hEc : (∫ ω,E ω ∂μ)≤Ecap := by
    dsimp only [Ecap]
    rw [hom]
    exact hEm.2
  have hEr := old_signed_sqrt_expectation μ E hEm.1 (parent_row_reciprocal_offset_energy_nonneg M n height r t b L)
  have hre : Integrable (fun ω => Real.sqrt (E ω)) μ ∧ (∫ ω,Real.sqrt (E ω) ∂μ)≤Real.sqrt Ecap :=
    ⟨hEr.1,hEr.2.trans (Real.sqrt_le_sqrt hEc)⟩
  have hec : (∫ ω,Real.sqrt (W ω)*Real.sqrt (E ω) ∂μ)≤Real.sqrt X*Real.sqrt Ecap := by
    dsimp only [Ecap]
    rw [hom]
    exact he.2
  have i₁ : Integrable (fun ω => Real.sqrt (W ω)*Real.sqrt (J ω)+Real.sqrt (W ω)*Real.sqrt (N ω)) μ := hj.1.add hn.1
  have i₂ : Integrable (fun ω => Real.sqrt (W ω)*Real.sqrt (J ω)+Real.sqrt (W ω)*Real.sqrt (N ω)+
    Real.sqrt (W ω)*Real.sqrt (E ω)) μ := i₁.add he.1
  have ib : Integrable (fun ω => a₁*(B ω*Real.sqrt (W ω))) μ := hb.1.const_mul _
  have iw : Integrable (fun ω => a₂*(B ω*W ω)) μ := hw.1.const_mul _
  have i₃ : Integrable (fun ω => Real.sqrt (W ω)*Real.sqrt (J ω)+Real.sqrt (W ω)*Real.sqrt (N ω)+
    Real.sqrt (W ω)*Real.sqrt (E ω)+a₁*(B ω*Real.sqrt (W ω))) μ := i₂.add ib
  have i₄ : Integrable (fun ω => Real.sqrt (W ω)*Real.sqrt (J ω)+Real.sqrt (W ω)*Real.sqrt (N ω)+
    Real.sqrt (W ω)*Real.sqrt (E ω)+a₁*(B ω*Real.sqrt (W ω))+a₂*(B ω*W ω)) μ := i₃.add iw
  have i₅ : Integrable (fun ω => Real.sqrt (W ω)*Real.sqrt (J ω)+Real.sqrt (W ω)*Real.sqrt (N ω)+
    Real.sqrt (W ω)*Real.sqrt (E ω)+a₁*(B ω*Real.sqrt (W ω))+a₂*(B ω*W ω)+Real.sqrt (N ω)) μ := i₄.add hrn.1
  refine ⟨(i₅.add hre.1).const_mul _,?_⟩
  change (∫ ω,(2*kd*Real.sqrt 2)*(Real.sqrt (W ω)*Real.sqrt (J ω)+Real.sqrt (W ω)*Real.sqrt (N ω)+
    Real.sqrt (W ω)*Real.sqrt (E ω)+a₁*(B ω*Real.sqrt (W ω))+a₂*(B ω*W ω)+Real.sqrt (N ω)+Real.sqrt (E ω)) ∂μ)≤_
  rw [integral_const_mul,integral_add i₅ hre.1,integral_add i₄ hrn.1,integral_add i₃ iw,
    integral_add i₂ ib,integral_add i₁ he.1,integral_add hj.1 hn.1,integral_const_mul,integral_const_mul]
  have hka := parent_boundary_potential_source_clock_nonneg Q r b L
  have hD : 0≤1+inverseHistoryDiscount := add_nonneg (by norm_num) inverse_history_discount_range.1.le
  have ha₁ : 0≤a₁ := mul_nonneg hD (add_nonneg (Real.sqrt_nonneg _) hka)
  have ha₂ : 0≤a₂ := mul_nonneg hD hka
  have hw' : (∫ ω,B ω*W ω ∂μ)≤(3683/2500:ℝ)*X := hw.2.trans_eq (by dsimp only [X,parentRowWeakAllowance]; ring)
  have hh := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hj.2 hn.2) hec)
    (mul_le_mul_of_nonneg_left hb.2 ha₁)) (mul_le_mul_of_nonneg_left hw' ha₂)) hrn.2) hre.2
  exact mul_le_mul_of_nonneg_left hh (mul_nonneg (mul_nonneg (by norm_num)
    (old_signed_q1_derivative_kappa_nonneg _ _ _
      (div_nonneg (Triadic.cubeScaleFactor_pos' Q).le (by positivity))))
      (Real.sqrt_nonneg _))

end
end ASDExplicitGamma.Native

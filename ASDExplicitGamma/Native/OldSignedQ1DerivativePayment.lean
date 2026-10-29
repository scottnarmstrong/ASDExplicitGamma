module

public import ASDExplicitGamma.Native.OldSignedQ1OffsetContractions
public import ASDExplicitGamma.Native.OldSignedQ1MinusContractions
public import ASDExplicitGamma.Native.OldSignedQ1BankWeakRoot
public import ASDExplicitGamma.Native.OldSignedSourceMixedSpatial
public import ASDExplicitGamma.Native.OldSignedDerivativeConstants

/-! Annealed payment of every OLD derivative feedback term. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Triadic Algsuperdiff.Section3
noncomputable section

/-- Nonnegativity of the literal derivative-only coefficient. -/
theorem old_signed_q1_derivative_kappa_nonneg (r b L : ℝ) (hr : 0≤r) :
    0≤oldSignedDerivativeKappa r b L := by
  unfold oldSignedDerivativeKappa
  exact add_nonneg (mul_nonneg (mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) hr) (Real.sqrt_nonneg _))
    (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (sq_nonneg r)) (Real.sqrt_nonneg _))

/-- Expanded derivative envelope; all seven random factors belong to the
same actual law, including the bank-weighted weak terms. -/
def oldSignedActualDerivativeEnvelope (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  let kd := oldSignedDerivativeKappa (cubeScaleFactor Q/3^r) b L.1
  let ka := oldSignedSourceMultiplier Q r b L
  let op := Real.sqrt (descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2))
  let W := oldSignedActualTiledWeakProxy M n r t ω
  let B := rawShellBandLocalHistory M n 1 t ω
  let J := oldSignedActualJointSpatialProxy M n r t b L ω
  let N := oldSignedActualMinusSpatialProxy M n r t b L ω
  let E := oldSignedActualReciprocalOffsetEnergy M n r t b L ω
  (2*kd*Real.sqrt 2)*(Real.sqrt W*Real.sqrt J+Real.sqrt W*Real.sqrt N+Real.sqrt W*Real.sqrt E+
    ((1+inverseHistoryDiscount)*(op+ka))*(B*Real.sqrt W)+
    ((1+inverseHistoryDiscount)*ka)*(B*W)+Real.sqrt N+Real.sqrt E)

/-- Every term of the derivative envelope is integrable and paid with the
sharp actual q1 moments. No estimate of a source term is assumed. -/
theorem old_signed_q1_derivative_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let kd := oldSignedDerivativeKappa (cubeScaleFactor Q/3^5) b L.1
    let ka := oldSignedSourceMultiplier Q 5 b L
    let op := Real.sqrt (descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U b L true^2))
    let om := Real.sqrt (descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U b L false^2))
    let C := oldSignedQ1PanelHistory t
    let A := 1+2*C+Real.sqrt (2*C)
    let X := theta M*oldSignedQ1PanelXi t
    let c := Real.sqrt ((3683/2500:ℝ)*A)+1
    Integrable (oldSignedActualDerivativeEnvelope M n 5 t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualDerivativeEnvelope M n 5 t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (2*kd*Real.sqrt 2)*(X*|b|+Real.sqrt X*Real.sqrt (X*b^2/2)+Real.sqrt X*(c*om)+
        ((1+inverseHistoryDiscount)*(op+ka))*((3683/2500:ℝ)*Real.sqrt X)+
        ((1+inverseHistoryDiscount)*ka)*((3683/2500:ℝ)*X)+Real.sqrt (X*b^2/2)+c*om) := by
  intro Q kd ka op om C A X c
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let W := oldSignedActualTiledWeakProxy M n 5 t
  let B := rawShellBandLocalHistory M n 1 t
  let J := oldSignedActualJointSpatialProxy M n 5 t b L
  let N := oldSignedActualMinusSpatialProxy M n 5 t b L
  let E := oldSignedActualReciprocalOffsetEnergy M n 5 t b L
  let a₁ := (1+inverseHistoryDiscount)*(op+ka)
  let a₂ := (1+inverseHistoryDiscount)*ka
  have hj := old_signed_q1_joint_root_contraction M h hM hg n hpast t ht b L
  have hn := old_signed_q1_minus_root_contraction M h hM hg n hpast t ht b L
  have he := old_signed_q1_offset_root_contraction M h hM hg n hpast t ht b L
  have hb := old_signed_q1_bank_weak_root M h hM hg n hpast t ht
  have hw := old_signed_q1_bank_weighted_weak M h hM hg n hpast t ht 1 (by norm_num)
  simp only [pow_one] at hw
  have hrn := old_signed_q1_minus_root_expectation M h hM hg n hpast t ht b L
  have hre := old_signed_q1_offset_root_expectation M h hM hg n hpast t ht b L
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
  have hka := old_signed_source_multiplier_nonneg Q 5 b L
  have hD : 0≤1+inverseHistoryDiscount := add_nonneg (by norm_num) inverse_history_discount_range.1.le
  have ha₁ : 0≤a₁ := mul_nonneg hD (add_nonneg (Real.sqrt_nonneg _) hka)
  have ha₂ : 0≤a₂ := mul_nonneg hD hka
  have hw' : (∫ ω,B ω*W ω ∂μ)≤(3683/2500:ℝ)*X := hw.2.trans_eq (by dsimp only [X]; ring)
  have hh := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hj.2 hn.2) he.2)
    (mul_le_mul_of_nonneg_left hb.2 ha₁)) (mul_le_mul_of_nonneg_left hw' ha₂)) hrn.2) hre.2
  exact mul_le_mul_of_nonneg_left hh (mul_nonneg (mul_nonneg (by norm_num)
    (old_signed_q1_derivative_kappa_nonneg _ _ _
      (div_nonneg (Triadic.cubeScaleFactor_pos' Q).le (by positivity))))
      (Real.sqrt_nonneg _))

end
end ASDExplicitGamma.Native

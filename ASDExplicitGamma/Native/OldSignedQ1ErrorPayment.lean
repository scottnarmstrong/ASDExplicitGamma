module

public import ASDExplicitGamma.Native.OldSignedQ1FlatPayment
public import ASDExplicitGamma.Native.OldSignedQ1SourceMixedPayment
public import ASDExplicitGamma.Native.OldSignedQ1DerivativePayment
public import ASDExplicitGamma.Native.OldSignedQ1BoundaryPayment

/-! All four actual AN error blocks and their complete q1 expectation cap. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

/-- The complete actual-law envelope of the four AN error blocks. -/
def oldSignedActualErrorEnvelope (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldSignedActualFlatEnvelope M n r t b L ω+oldSignedActualSourceMixedEnvelope M n r t b L ω+
    oldSignedActualDerivativeEnvelope M n r t b L ω+oldSignedActualBoundaryEnvelope M n r t b L ω

/-- Sharp flat-block payment before the physical q1 parameter substitution. -/
def oldSignedQ1FlatCap (M : ABKModel 2) (n : ℤ) (t b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  let Q := originCube 2 n
  let op := descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U b L true^2)
  let om := descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U b L false^2)
  let C := oldSignedQ1PanelHistory t
  let A := 1+2*C+Real.sqrt (2*C)
  (2*Real.sqrt op)*Real.sqrt (theta M*oldSignedQ1PanelXi t*b^2)+op*(3683/2500:ℝ)+
    (2*Real.sqrt 2*Real.sqrt om)*Real.sqrt ((theta M*((1+inverseHistoryDiscount)*A*C))*b^2)+A*om

/-- The full source quadratic and mixed payment, including correlated
reciprocal oscillations. -/
def oldSignedQ1SourceMixedCap (M : ABKModel 2) (n : ℤ) (t b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  let k := oldSignedSourceMultiplier (originCube 2 n) 5 b L
  let X := theta M*oldSignedQ1PanelXi t
  k^2*((3683/2500:ℝ)*X)+2*k*(X*|b|)+
    2*k*(Real.sqrt X*Real.sqrt (oldSignedQ1ReciprocalSpatialCap (originCube 2 n) 5 t b L))

/-- The complete derivative-only payment, retaining the OLD source,
half-trace minus profile and reciprocal offset. -/
def oldSignedQ1DerivativeCap (M : ABKModel 2) (n : ℤ) (t b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  let Q := originCube 2 n
  let kd := oldSignedDerivativeKappa (cubeScaleFactor Q/3^5) b L.1
  let ka := oldSignedSourceMultiplier Q 5 b L
  let op := Real.sqrt (descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U b L true^2))
  let om := Real.sqrt (descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U b L false^2))
  let C := oldSignedQ1PanelHistory t
  let A := 1+2*C+Real.sqrt (2*C)
  let X := theta M*oldSignedQ1PanelXi t
  let c := Real.sqrt ((3683/2500:ℝ)*A)+1
  (2*kd*Real.sqrt 2)*(X*|b|+Real.sqrt X*Real.sqrt (X*b^2/2)+Real.sqrt X*(c*om)+
    ((1+inverseHistoryDiscount)*(op+ka))*((3683/2500:ℝ)*Real.sqrt X)+
    ((1+inverseHistoryDiscount)*ka)*((3683/2500:ℝ)*X)+Real.sqrt (X*b^2/2)+c*om)

/-- Both covariance boundary terms in the physical whole-partition form. -/
def oldSignedQ1BoundaryCap (M : ABKModel 2) (n : ℤ) (t b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  let Q := originCube 2 n
  let C := b^2+3*(cubeScaleFactor Q/3^5)*planarC1*|b| *Real.sqrt (mainFlatSigmaSq b L)
  let X := theta M*oldSignedQ1PanelXi t
  2*C*(Real.sqrt X+Real.sqrt (2*X))

/-- Complete four-block q1 error payment before the numerical panel bridge. -/
def oldSignedQ1ErrorCap (M : ABKModel 2) (n : ℤ) (t b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  oldSignedQ1FlatCap M n t b L+oldSignedQ1SourceMixedCap M n t b L+
    oldSignedQ1DerivativeCap M n t b L+oldSignedQ1BoundaryCap M n t b L

/-- The full actual AN error envelope has a finite first moment and the
complete source-derived q1 cap. No cell, history, bank or error estimate is
left as a premise. -/
theorem old_signed_q1_error_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (oldSignedActualErrorEnvelope M n 5 t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualErrorEnvelope M n 5 t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      oldSignedQ1ErrorCap M n t b L := by
  have hf := old_signed_q1_flat_payment M h hM hg n hpast t ht b L
  have hs := old_signed_q1_source_mixed_payment M h hM hg n hpast t ht b L
  have hd := old_signed_q1_derivative_payment M h hM hg n hpast t ht b L
  have hb := old_signed_q1_boundary_payment M h hM hg n hpast t ht b L
  have hfs : Integrable (fun ω => oldSignedActualFlatEnvelope M n 5 t b L ω+
    oldSignedActualSourceMixedEnvelope M n 5 t b L ω) (Cutoff.cutoffSampleLaw M).toMeasure := hf.1.add hs.1
  have hfsd : Integrable (fun ω => oldSignedActualFlatEnvelope M n 5 t b L ω+
    oldSignedActualSourceMixedEnvelope M n 5 t b L ω+oldSignedActualDerivativeEnvelope M n 5 t b L ω)
      (Cutoff.cutoffSampleLaw M).toMeasure := hfs.add hd.1
  refine ⟨hfsd.add hb.1,?_⟩
  unfold oldSignedActualErrorEnvelope
  rw [integral_add hfsd hb.1,integral_add hfs hd.1,integral_add hf.1 hs.1]
  exact add_le_add (add_le_add (add_le_add hf.2 hs.2) hd.2) hb.2

end
end ASDExplicitGamma.Native

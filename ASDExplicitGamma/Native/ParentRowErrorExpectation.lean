module

public import ASDExplicitGamma.Native.ParentRowSourceExpectation
public import ASDExplicitGamma.Native.ParentRowDerivativeExpectation
public import ASDExplicitGamma.Native.ParentRowChargeExpectation

/-! Complete first-moment payment of the actual parent error envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Algsuperdiff.Section3
noncomputable section

/-- Sharp flat error cap with the exact Dirichlet energy. -/
def parentRowFlatCap (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
    let Q := originCube 2 n
    let op := descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2)
    let om := descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2)
    let C := parentHistorySourceEnvelope height r t
    let A := 1+2*C+Real.sqrt (2*C)
    (2*Real.sqrt op)*Real.sqrt (theta M*parentRowWeakAllowance height t*b^2)+op*(3683/2500:ℝ)+
      (2*Real.sqrt 2*Real.sqrt om)*Real.sqrt ((theta M*((1+inverseHistoryDiscount)*A*C))*parentBoundaryDirichletEnergy Q b L)+A*om

/-- Complete correlated source quadratic and mixed cap. -/
def parentRowSourceMixedCap (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
    let k := parentBoundaryPotentialSourceClock (originCube 2 n) r b L
    let X := theta M*parentRowWeakAllowance height t
    k^2*((3683/2500:ℝ)*X)+(2*k)*(Real.sqrt X*Real.sqrt (X*b^2))+
        (2*k)*(Real.sqrt X*Real.sqrt (parentRowReciprocalCap n height r t b L))

/-- All seven derivative payments, including the actual minus energy. -/
def parentRowDerivativeCap (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
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
    (2*kd*Real.sqrt 2)*(Real.sqrt X*Real.sqrt (X*b^2)+Real.sqrt X*Real.sqrt (Ncap)+Real.sqrt X*(Real.sqrt Ecap)+
        ((1+inverseHistoryDiscount)*(op+ka))*((3683/2500:ℝ)*Real.sqrt X)+
        ((1+inverseHistoryDiscount)*ka)*((3683/2500:ℝ)*X)+Real.sqrt (Ncap)+Real.sqrt Ecap)

/-- The two separately centered boundary charges. -/
def parentRowChargeCap (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
    let X := theta M*parentRowWeakAllowance height t
    let betaPlus := parentRowBeta n r b L true
    let betaMinus := parentRowBeta n r b L false
    2*betaPlus*Real.sqrt X+2*betaMinus*Real.sqrt (2*X)

/-- The complete four-block cap, before the finite-shell panel comparison. -/
def parentRowErrorCap (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  parentRowFlatCap M n height r t b L+parentRowSourceMixedCap M n height r t b L+
    parentRowDerivativeCap M n height r t b L+parentRowChargeCap M n height r t b L

/-- Every error block is integrable and paid from standing source assumptions. -/
theorem parent_row_error_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (parentRowErrorEnvelope M n height r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,parentRowErrorEnvelope M n height r t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      parentRowErrorCap M n height r t b L := by
  have hf := parent_row_flat_payment M h hM hg n hpast hstate height hheight hh16 r hr t ht b L
  have hs := parent_row_source_mixed_payment M h hM hg n height hheight hh16 hpast hstate r hr t ht b L
  have hd := parent_row_derivative_payment M h hM hg n height hheight hh16 hpast hstate r hr t ht b L
  have hb := parent_row_sharp_charge_expectation M h hM hg n height hheight hh16 r hr t ht hpast hstate b L
  have hfs : Integrable (fun ω => parentRowFlatEnvelope M n height r t b L ω+
    parentRowSourceMixedEnvelope M n height r t b L ω) (Cutoff.cutoffSampleLaw M).toMeasure := hf.1.add hs.1
  have hfsd : Integrable (fun ω => parentRowFlatEnvelope M n height r t b L ω+
    parentRowSourceMixedEnvelope M n height r t b L ω+parentRowDerivativeEnvelope M n height r t b L ω)
      (Cutoff.cutoffSampleLaw M).toMeasure := hfs.add hd.1
  refine ⟨hfsd.add hb.1,?_⟩
  unfold parentRowErrorEnvelope
  rw [integral_add hfsd hb.1,integral_add hfs hd.1,integral_add hf.1 hs.1]
  exact add_le_add (add_le_add (add_le_add hf.2 hs.2) hd.2) hb.2

end
end ASDExplicitGamma.Native

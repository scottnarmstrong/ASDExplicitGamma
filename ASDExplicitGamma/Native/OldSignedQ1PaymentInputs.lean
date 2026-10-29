module

public import ASDExplicitGamma.Native.OldSignedQ1GeneratorExpectation
public import ASDExplicitGamma.Native.OldSignedQ1PaymentDegree
public import ASDExplicitGamma.Native.OldSignedQ1BoundaryProfileCap
public import ASDExplicitGamma.Native.OldSignedQ1ReciprocalProfileCap

/-! Actual physical inputs and exact frozen endpoint inputs of the q1 bill. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Cold Scalar Inverse Algsuperdiff.Section3 Numerics.Native Numerics.Mirror
noncomputable section

/-- The same history-derived matrix moment used by the actual contractions. -/
def oldSignedQ1PanelMatrix (t : ℝ) : ℝ :=
  1+2*oldSignedQ1PanelHistory t+Real.sqrt (2*oldSignedQ1PanelHistory t)

/-- Actual inputs of the positive arithmetic bill. -/
def oldSignedQ1PaymentInputs (M : ABKModel 2) (n : ℤ) (t b : ℝ)
    (L : {l : ℝ // 0<l}) : ℕ → ℝ
  | 0 => b^2
  | 1 => |b|
  | 2 => descendantsAverage (originCube 2 n) 5
      (fun U => oldSignedFlatOscillationSize (originCube 2 n) U b L true^2)
  | 3 => descendantsAverage (originCube 2 n) 5
      (fun U => oldSignedFlatOscillationSize (originCube 2 n) U b L false^2)
  | 4 => oldSignedSourceMultiplier (originCube 2 n) 5 b L
  | 5 => oldSignedDerivativeKappa (cubeScaleFactor (originCube 2 n)/3^5) b L.val
  | 6 => oldSignedQ1ReciprocalSpatialCap (originCube 2 n) 5 t b L
  | 7 => b^2+3*(cubeScaleFactor (originCube 2 n)/3^5)*planarC1*|b| *Real.sqrt (mainFlatSigmaSq b L)
  | 8 => theta M*oldSignedQ1PanelXi t
  | 9 => theta M*((1+inverseHistoryDiscount)*oldSignedQ1PanelMatrix t*oldSignedQ1PanelHistory t)
  | 10 => oldSignedQ1PanelMatrix t
  | 11 => 1+inverseHistoryDiscount
  | 12 => Real.sqrt ((3683/2500:ℝ)*oldSignedQ1PanelMatrix t)+1
  | 13 => theta M*oldSignedQ1PanelMean t
  | 14 => (cubeScaleFactor (originCube 2 n)/3^5)^2*b^2/L.val^2
  | 15 => Real.sqrt 2*oldSignedDerivativeKappa (cubeScaleFactor (originCube 2 n)/3^5) b L.val
  | _ => 0

/-- Endpoint inputs use the exact certified setup values, with no decimal rounding. -/
def oldSignedQ1PaymentEndpoint (t : ℝ) : ℕ → ℝ
  | 0 => nativeSetupQ1001FieldsR.getD 0 0
  | 1 => Real.sqrt (nativeSetupQ1001FieldsR.getD 0 0)
  | 2 => (nativeSetupQ1001FieldsR.getD 4 0)^2
  | 3 => (nativeSetupQ1001FieldsR.getD 5 0)^2
  | 4 => nativeSetupQ1001FieldsR.getD 2 0
  | 5 => nativeSetupQ1001FieldsR.getD 3 0
  | 6 => ((3683/2500:ℝ)+1)^2*(nativeSetupQ1001FieldsR.getD 4 0)^2+
      (3683/2500:ℝ)*oldSignedQ1PanelMatrix t*(nativeSetupQ1001FieldsR.getD 5 0)^2
  | 7 => nativeSetupQ1001FieldsR.getD 6 0
  | 8 => oldSignedQ1PanelXi t
  | 9 => (1+inverseHistoryDiscount)*oldSignedQ1PanelMatrix t*oldSignedQ1PanelHistory t
  | 10 => oldSignedQ1PanelMatrix t
  | 11 => 1+inverseHistoryDiscount
  | 12 => Real.sqrt ((3683/2500:ℝ)*oldSignedQ1PanelMatrix t)+1
  | 13 => oldSignedQ1PanelMean t
  | 14 => nativeSetupQ1001FieldsR.getD 1 0
  | 15 => nativeSetupQ1001FieldsR.getD 3 0
  | _ => 0

/-- The positive program is exactly the previously proved complete bill. -/
theorem old_signed_q1_payment_inputs_eval (M : ABKModel 2) (n : ℤ) (t b : ℝ)
    (L : {l : ℝ // 0<l}) :
    evalReal (oldSignedQ1PaymentInputs M n t b L) oldSignedQ1PaymentExpr=
      oldSignedQ1AffineCap M n t b L+oldSignedQ1ErrorCap M n t b L := by
  simp only [oldSignedQ1PaymentExpr,oldSignedQ1AffineExpr,oldSignedQ1FlatExpr,
    oldSignedQ1SourceExpr,oldSignedQ1DerivativeExpr,oldSignedQ1BoundaryExpr,
    evalReal,oldSignedQ1PaymentInputs,oldSignedQ1AffineCap,oldSignedQ1AffineCap',oldSignedQ1ErrorCap,
    oldSignedQ1FlatCap,oldSignedQ1SourceMixedCap,oldSignedQ1DerivativeCap,
    oldSignedQ1BoundaryCap,oldSignedQ1PanelMatrix,Rat.cast_ofNat,Rat.cast_div]
  ring

end
end ASDExplicitGamma.Native

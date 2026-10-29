module

public import ASDExplicitGamma.Native.ParentRowFlatSpatial
public import ASDExplicitGamma.Native.ParentRowSourceMixedMajorant
public import ASDExplicitGamma.Native.ParentRowDerivativeSpatial
public import ASDExplicitGamma.Native.ParentRowBoundary
public import ASDExplicitGamma.Native.ParentBoundaryDirectionalError

/-! The complete actual parent directional error has a four-block spatial envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- The complete source quadratic and mixed envelope on the actual simultaneous band. -/
def parentRowSourceMixedEnvelope (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let B := (nativeSourceBandHistory M n height t ω).toReal
  let W := parentBoundaryBandWeakProxy M n height r t ω
  let ka := parentBoundaryPotentialSourceClock (originCube 2 n) r b L
  B*ka^2*W+2*(ka*Real.sqrt W*(Real.sqrt (parentBoundaryBandJointSpatialProxy M n height r t b L ω)+
    Real.sqrt (parentRowReciprocalSpatialEnergy M n height r t b L ω)))

/-- All four blocks, retaining both separate centered covariance charges. -/
def parentRowErrorEnvelope (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  parentRowFlatEnvelope M n height r t b L ω+
    parentRowSourceMixedEnvelope M n height r t b L ω+
    parentRowDerivativeEnvelope M n height r t b L ω+
    parentRowChargeEnvelope M n height r t b L ω

/-- The literal directional error is controlled on the actual sample law.
Every source, derivative and paired-boundary term is retained in the same physical frame. -/
theorem parent_row_actual_error_spatial_majorant
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ l<n,nativeInductionState M h l) (r : ℕ) (hr : r≤5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      descendantsAverage (originCube 2 n) r (fun U => parentBoundaryDirectionalCellError (originCube 2 n) U
        M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
        (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω)) b L)≤
      parentRowErrorEnvelope M n height r t b L ω := by
  have hf := parent_row_actual_flat_spatial_majorant M h hM hg n height hpast r hr t ht b L
  have hs := parent_row_actual_source_mixed_majorant M h hM hg n height hpast r hr t ht.2 b L
  have hd := parent_row_actual_derivative_spatial_majorant M h hM hg n height hpast r hr t ht b L
  filter_upwards [hf,hs,hd] with ω hfω hsω hdω
  have hb := parent_row_actual_paired_charge M n height r t b L ω
  dsimp only at hb
  rw [←descendantsAverage_mul_left,←descendantsAverage_mul_left,←descendantsAverage_add] at hb
  have hall := add_le_add (add_le_add (add_le_add hfω hsω) hdω) hb
  dsimp only at hall
  rw [←descendantsAverage_add,←descendantsAverage_add,←descendantsAverage_add] at hall
  refine le_trans ?_ hall
  apply le_of_eq
  unfold parentBoundaryDirectionalCellError oldSignedDirectionalErrorBill descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro U _
  dsimp only [parentBoundaryBandFrameField,parentRowSourceMixedCellBill]
  ring

end
end ASDExplicitGamma.Native

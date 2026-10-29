module

public import ASDExplicitGamma.Native.ParentBoundaryBandAffineExpectation
public import ASDExplicitGamma.Native.OldSignedPartialFrameHistory

/-! Reuse of the actual simultaneous-band affine expectation on the OLD one-shell path. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- A height-one simultaneous source band is the literal OLD heat insertion. -/
theorem old_signed_single_band_scalar (n : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    nativeSourceBandScalar n 1 t ω=modelInsertedScalar (closure (cubeSet (originCube 2 n))) n t ω := by
  simp [nativeSourceBandScalar,modelBand,nativeSourceBandIndex,modelInsertedScalar]

/-- The actual starting true frame agrees on both one-shell interfaces. -/
theorem old_signed_single_band_frame (M : ABKModel 2) (n : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    parentBoundaryBandFrameField M n 1 t ω=oldSignedPartialFrameField M n 1 t ω := by
  simp only [parentBoundaryBandFrameField,old_signed_single_band_scalar,
    oldSignedPartialFrameField,oldSignedPartialResponseCoefficient,Nat.cast_one,add_sub_cancel_right]

/-- The actual signed affine contribution is integrable and retains the
two signed scalar block deviations on the same physical comparison tiling. -/
theorem old_signed_affine_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (r : ℕ) (t b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (fun ω => oldSignedFlatAffineContribution (originCube 2 n) r
      (oldSignedPartialFrameField M n 1 t ω) b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedFlatAffineContribution (originCube 2 n) r
      (oldSignedPartialFrameField M n 1 t ω) b L ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      descendantsAverage (originCube 2 n) r (fun U =>
        (parentBoundaryBandBlockMean M n 1 t U false-1)*oldSignedFlatMeanSize (originCube 2 n) U b L true^2+
        (parentBoundaryBandBlockMean M n 1 t U true-1)*oldSignedFlatMeanSize (originCube 2 n) U b L false^2) := by
  have hh := parent_boundary_band_affine_expectation M h hM n 1 (by norm_num) r t b L
  simpa only [old_signed_single_band_frame] using hh

end
end ASDExplicitGamma.Native

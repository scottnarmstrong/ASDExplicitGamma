module

public import ASDExplicitGamma.Native.ParentBoundaryBandAffineMean

/-! The literal AN affine term under the actual simultaneous-band law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- The complete signed affine contribution is genuinely integrable and
has the exact two scalar-block expectation on the SAME comparison tiling.
Neither block deviation is replaced by a positive part. -/
theorem parent_boundary_band_affine_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (height : ℕ) (hheight : 1≤height) (r : ℕ) (t b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (fun omega => oldSignedFlatAffineContribution (originCube 2 n) r
      (parentBoundaryBandFrameField M n height t omega) b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ omega,oldSignedFlatAffineContribution (originCube 2 n) r
      (parentBoundaryBandFrameField M n height t omega) b L ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      descendantsAverage (originCube 2 n) r (fun U =>
        (parentBoundaryBandBlockMean M n height t U false-1)*oldSignedFlatMeanSize (originCube 2 n) U b L true^2+
        (parentBoundaryBandBlockMean M n height t U true-1)*oldSignedFlatMeanSize (originCube 2 n) U b L false^2) := by
  have hp := parent_boundary_band_affine_family_integral M h hM n height hheight r t b L true
  have hm := parent_boundary_band_affine_family_integral M h hM n height hheight r t b L false
  have he : (fun omega => oldSignedFlatAffineContribution (originCube 2 n) r
      (parentBoundaryBandFrameField M n height t omega) b L)=
      (fun omega => parentBoundaryBandAffineFamily M n height r t b L true omega+
        parentBoundaryBandAffineFamily M n height r t b L false omega) := by
    funext omega
    exact (old_signed_flat_affine_family_sum (originCube 2 n) r
      (parentBoundaryBandFrameField M n height t omega) b L).symm
  rw [he]
  refine ⟨hp.1.add hm.1,?_⟩
  rw [integral_add hp.1 hm.1,hp.2,hm.2,←descendantsAverage_add]
  rfl

end
end ASDExplicitGamma.Native

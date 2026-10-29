module

public import ASDExplicitGamma.Native.OldSignedTrialFields

/-! AN (4.1) for the actual fixed-frame projected fields and localized
OLD-error sources. No trial membership is supplied as a premise. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
noncomputable section

/-- The actual frame's localized OLD-error source has its complete parent
physical-shear gauge variation, including the parent boundary. -/
theorem old_signed_frame_old_error_gauge_variation (Q : TriadicCube 2) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2) :
    ScalarVariation (openCubeSet Q) (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n P-
      oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2)-(fun _ => P))) :=
  old_signed_old_error_source_gauge_variation Q mesh (responseFramePlanarCoefficientField nu sigma k)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k) b L n P

/-- The actual top-load local signed trial is a genuine parent variation. -/
theorem old_signed_actual_top_trial_variation (Q : TriadicCube 2) (depth mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (i : Fin 2) :
    ScalarVariation (openCubeSet Q)
      (oldSignedPatchedPlus Q depth nu sigma hnu hsigma k b L n i+
        oldSignedPatchedOldError Q depth mesh nu sigma hnu hsigma k b L n (basisVec i,0)-
        oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
          (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (basisVec i,0))) := by
  exact old_signed_local_top_trial_variation Q depth nu sigma hnu hsigma k
    (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)))
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (basisVec i,0)) (fun _ => (basisVec i,0))
    (oldSignedFlatPlusBlock Q b L n i) (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n (basisVec i,0))
    (old_signed_flat_plus_block_memL2 Q b L n i)
    (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n (basisVec i,0))
    (old_signed_flat_plus_pointwise_shear_variation Q b L n i)
    (old_signed_frame_old_error_gauge_variation Q mesh nu sigma hnu hsigma k b L n (basisVec i,0))

/-- The actual bottom-load local trial retains the negative Z contribution
and is an admissible parent variation for the same physical shear. -/
theorem old_signed_actual_bottom_trial_variation (Q : TriadicCube 2) (depth mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (i : Fin 2) :
    ScalarVariation (openCubeSet Q)
      (oldSignedPatchedOldError Q depth mesh nu sigma hnu hsigma k b L n (0,basisVec i)-
        oldSignedPatchedMinus Q depth nu sigma hnu hsigma k b L n i-
        oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
          (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i))) := by
  have hE : oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      (fun _ => (0,basisVec i))=0 := by
    funext x
    simp [oldSignedPointwiseShear,matVecMul_zero]
  exact old_signed_local_bottom_trial_variation Q depth nu sigma hnu hsigma k
    (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)))
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i)) (fun _ => (0,basisVec i))
    (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n (0,basisVec i)) (oldSignedFlatMinusBlock Q b L n i)
    (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n (0,basisVec i))
    (old_signed_flat_minus_block_memL2 Q b L n i) hE
    (old_signed_frame_old_error_gauge_variation Q mesh nu sigma hnu hsigma k b L n (0,basisVec i))
    (old_signed_flat_minus_block_variation Q b L n i)

end
end ASDExplicitGamma.Native

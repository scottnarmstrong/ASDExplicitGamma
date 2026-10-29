module

public import ASDExplicitGamma.Native.OldSignedTrialValueFields
public import ASDExplicitGamma.Native.OldSignedFieldTrialExpansion

/-! The physical canonical Hessians bounded by the fully expanded actual
OLD trials, with every membership and class transport supplied by source data. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian
noncomputable section

/-- The complete actual top-load signed trial expansion, before estimating
any cross, covariance, or derivative-only feedback term. -/
theorem old_signed_actual_top_trial_expansion (Q : TriadicCube 2) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    let E := oldSignedEnergyPairing Q nu sigma k
    let C := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
    let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (basisVec i,0)
    let A := oldSignedPatchedPlus Q mesh nu sigma hnu hsigma k b L n i
    let R := oldSignedPatchedOldError Q mesh mesh nu sigma hnu hsigma k b L n (basisVec i,0)
    oldSignedPhysicalHessian Q nu sigma hnu hsigma k (basisVec i,0) b L n ≤
      E A A+E R R+2*E A R+2*E S (C A)+2*E S (C R) := by
  intro E C S A R
  have hA : MemBlockL2 (openCubeSet Q) A := old_signed_local_residual_memLp Q mesh nu sigma hnu hsigma k _
    (old_signed_flat_plus_block_memL2 Q b L n i)
  have hR : MemBlockL2 (openCubeSet Q) R := old_signed_local_residual_memLp Q mesh nu sigma hnu hsigma k _
    (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n (basisVec i,0))
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp S
  have hh := old_signed_actual_top_hessian_trial Q mesh mesh nu sigma hnu hsigma k b L n i
  rw [old_signed_trial_value_fields] at hh
  have he := old_signed_top_field_trial_expansion Q nu sigma hnu hsigma k b L n hS hA hR
  exact hh.trans_eq he

/-- The actual bottom-load trial retains the negative mixed cross and
negative physical feedback, ready for the exact signed inverse covariance. -/
theorem old_signed_actual_bottom_trial_expansion (Q : TriadicCube 2) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    let E := oldSignedEnergyPairing Q nu sigma k
    let C := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
    let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i)
    let R := oldSignedPatchedOldError Q mesh mesh nu sigma hnu hsigma k b L n (0,basisVec i)
    let Z := oldSignedPatchedMinus Q mesh nu sigma hnu hsigma k b L n i
    oldSignedPhysicalHessian Q nu sigma hnu hsigma k (0,basisVec i) b L n ≤
      E R R+E Z Z-2*E R Z+2*E S (C R)-2*E S (C Z) := by
  intro E C S R Z
  have hR : MemBlockL2 (openCubeSet Q) R := old_signed_local_residual_memLp Q mesh nu sigma hnu hsigma k _
    (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n (0,basisVec i))
  have hZ : MemBlockL2 (openCubeSet Q) Z := old_signed_local_residual_memLp Q mesh nu sigma hnu hsigma k _
    (old_signed_flat_minus_block_memL2 Q b L n i)
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp S
  have hh := old_signed_actual_bottom_hessian_trial Q mesh mesh nu sigma hnu hsigma k b L n i
  rw [old_signed_trial_value_fields] at hh
  have he := old_signed_bottom_field_trial_expansion Q nu sigma hnu hsigma k b L n hS hR hZ
  exact hh.trans_eq he

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Scalar.OldHessianTrialCoarsePotential
public import ASDExplicitGamma.Scalar.OldHessianTrialMixedSource
public import ASDExplicitGamma.Native.OldSignedActualHessianTrial

/-! The source-only coarse/fine bottom trial of the ten-term OLD bound.
The parent potential, coarse cell-zero potential, fine projection and fine
flat minus field are the actual fixed-frame objects. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Gaussian Main Triadic Variational
noncomputable section

/-- The literal mixed source on a bottom basis load. The two partition
parameters remain distinct: coarse selects the source potential, fine selects
both the original interpolant and complementary projection. -/
def oldHessianMixedBottomSource (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) : Vec 2 → BlockVec 2 :=
  let a := responseFramePlanarCoefficientField nu sigma k
  let ha := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  let v := oldSignedCanonicalFirstCorrector Q a ha (0,basisVec i)
  let phi := oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k (basisVec i)
  oldHessianMixedSource (diagInterpolant Q fine)
    (mainQ3DirectionW2 Q b L (whiteBasis n)).value v.toH1Function phi.toH1Function

/-- The mixed source is genuinely square integrable. -/
theorem old_hessian_mixed_bottom_source_memL2 (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    MemBlockL2 (openCubeSet Q)
      (oldHessianMixedBottomSource Q coarse fine nu sigma hnu hsigma k b L n i) :=
  old_hessian_mixed_source_memL2 Q (diagInterpolant Q fine) _ _ _
    (mainQ3DirectionW2 Q b L (whiteBasis n)).value_memLp_top
    (mainQ3DirectionW2 Q b L (whiteBasis n)).gradient_memLp_top_volume

/-- The actual mixed source differs from the physical shear of the parent
bottom minimizer by a parent variation; no source estimate is assumed. -/
theorem old_hessian_mixed_bottom_source_gauge (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    ScalarVariation (openCubeSet Q)
      (oldHessianMixedBottomSource Q coarse fine nu sigma hnu hsigma k b L n i-
        oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
          (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i))) := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let ha := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  let v := oldSignedCanonicalFirstCorrector Q a ha (0,basisVec i)
  let phi := oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k (basisVec i)
  let eta := (mainQ3DirectionW2 Q b L (whiteBasis n)).value
  have hg : v.toH1Function.grad =
      fun x => (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i) x).1 := by
    simpa only [oldSignedFrameCanonicalField,sub_zero] using
      old_signed_canonical_first_corrector_grad Q a ha (0,basisVec i)
  have he : oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i)) =
        oldSignedPhysicalPotentialShear eta v.toH1Function := by
    funext x
    change (0,-(eta x • matVecMul responsePlanarJ
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i) x).1)) =
      (0,-(eta x • matVecMul responsePlanarJ (v.toH1Function.grad x)))
    rw [hg]
  rw [he]
  exact old_hessian_mixed_source_physical_variation Q fine eta v phi
    (mainQ3DirectionW2 Q b L (whiteBasis n)).value_memLp_top
    (mainQ3DirectionW2 Q b L (whiteBasis n)).gradient_memLp_top_volume

/-- The actual fine complementary projection of the mixed source. -/
def oldHessianMixedBottomResidual (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) : Vec 2 → BlockVec 2 :=
  oldSignedLocalResidual Q fine nu sigma hnu hsigma k
    (oldHessianMixedBottomSource Q coarse fine nu sigma hnu hsigma k b L n i)
    (old_hessian_mixed_bottom_source_memL2 Q coarse fine nu sigma hnu hsigma k b L n i)

theorem old_hessian_mixed_bottom_residual_memL2 (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    MemBlockL2 (openCubeSet Q)
      (oldHessianMixedBottomResidual Q coarse fine nu sigma hnu hsigma k b L n i) :=
  old_signed_local_residual_memLp Q fine nu sigma hnu hsigma k _ _

/-- The unchanged projected fine minus field is a parent variation. -/
theorem old_hessian_fine_minus_variation (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    ScalarVariation (openCubeSet Q) (oldSignedPatchedMinus Q fine nu sigma hnu hsigma k b L n i) := by
  have hm := old_signed_flat_minus_block_variation Q b L n i
  have hr := old_signed_local_removed_variation Q fine nu sigma hnu hsigma k
    (oldSignedFlatMinusBlock Q b L n i) (old_signed_flat_minus_block_memL2 Q b L n i)
  change _ ∈ correctionFieldSubmodule (openCubeSet Q) at hm hr ⊢
  have hh := (correctionFieldSubmodule (openCubeSet Q)).sub_mem hm hr
  convert hh using 1
  funext x
  change oldSignedLocalResidual Q fine nu sigma hnu hsigma k
    (oldSignedFlatMinusBlock Q b L n i) (old_signed_flat_minus_block_memL2 Q b L n i) x =
    oldSignedFlatMinusBlock Q b L n i x-
      (oldSignedFlatMinusBlock Q b L n i x-oldSignedLocalResidual Q fine nu sigma hnu hsigma k
        (oldSignedFlatMinusBlock Q b L n i) (old_signed_flat_minus_block_memL2 Q b L n i) x)
  abel

/-- The full scalar mixed trial, with exactly the original fine Z. -/
def oldHessianMixedBottomTrial (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) (lam : ℝ) : Vec 2 → BlockVec 2 :=
  oldHessianMixedBottomResidual Q coarse fine nu sigma hnu hsigma k b L n i-
    lam • oldSignedPatchedMinus Q fine nu sigma hnu hsigma k b L n i

theorem old_hessian_mixed_bottom_trial_memL2 (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) (lam : ℝ) :
    MemBlockL2 (openCubeSet Q)
      (oldHessianMixedBottomTrial Q coarse fine nu sigma hnu hsigma k b L n i lam) :=
  (old_hessian_mixed_bottom_residual_memL2 Q coarse fine nu sigma hnu hsigma k b L n i).sub
    ((old_hessian_fine_minus_variation Q fine nu sigma hnu hsigma k b L n i).1.const_smul lam)

/-- Admissibility of the physical mixed trial is proved on the actual parent
and coefficient, including every coarse/fine interface. -/
theorem old_hessian_mixed_bottom_trial_variation (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) (lam : ℝ) :
    ScalarVariation (openCubeSet Q)
      (oldHessianMixedBottomTrial Q coarse fine nu sigma hnu hsigma k b L n i lam-
        oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
          (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i))) := by
  let F := oldHessianMixedBottomSource Q coarse fine nu sigma hnu hsigma k b L n i
  let R := oldHessianMixedBottomResidual Q coarse fine nu sigma hnu hsigma k b L n i
  let Z := oldSignedPatchedMinus Q fine nu sigma hnu hsigma k b L n i
  let CS := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i))
  have hf := old_hessian_mixed_bottom_source_gauge Q coarse fine nu sigma hnu hsigma k b L n i
  have hr := old_signed_local_removed_variation Q fine nu sigma hnu hsigma k F
    (old_hessian_mixed_bottom_source_memL2 Q coarse fine nu sigma hnu hsigma k b L n i)
  have hz := old_hessian_fine_minus_variation Q fine nu sigma hnu hsigma k b L n i
  change F-CS ∈ correctionFieldSubmodule (openCubeSet Q) at hf
  change F-R ∈ correctionFieldSubmodule (openCubeSet Q) at hr
  change Z ∈ correctionFieldSubmodule (openCubeSet Q) at hz
  change R-lam • Z-CS ∈ correctionFieldSubmodule (openCubeSet Q)
  have hh := (correctionFieldSubmodule (openCubeSet Q)).sub_mem
    ((correctionFieldSubmodule (openCubeSet Q)).sub_mem hf hr)
    ((correctionFieldSubmodule (openCubeSet Q)).smul_mem lam hz)
  convert hh using 1
  abel

/-- The physical OLD directional Hessian is bounded by the genuine mixed
trial, with no admissibility or energy estimate supplied as a premise. -/
theorem old_hessian_actual_mixed_bottom_trial (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) (lam : ℝ) :
    oldSignedPhysicalHessian Q nu sigma hnu hsigma k (0,basisVec i) b L n ≤
      oldSignedPhysicalTrialValue Q nu sigma hnu hsigma k (0,basisVec i) b L n
        (old_hessian_mixed_bottom_trial_memL2 Q coarse fine nu sigma hnu hsigma k b L n i lam) :=
  old_signed_physical_trial_bound Q nu sigma hnu hsigma k b L n (0,basisVec i)
    (old_hessian_mixed_bottom_trial_memL2 Q coarse fine nu sigma hnu hsigma k b L n i lam)
    (old_hessian_mixed_bottom_trial_variation Q coarse fine nu sigma hnu hsigma k b L n i lam)

end
end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Native.OldSignedTrialValueFields

/-! The actual parent-interpolated OLD source and fine-cell trial. The
canonical parent correction is H10; its fine-cell restrictions need not be. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

/-- Whole-parent affine interpolation is zero on the canonical H10 error.
Its localized source therefore keeps the literal parent potential. -/
def parentBoundaryOldSource (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (P : BlockVec 2) :
    Vec 2 → BlockVec 2 :=
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  oldSignedLocalizedPotentialShear 0 (mainQ3DirectionW2 Q b L (whiteBasis n)).value
    (oldSignedCanonicalFirstCorrector Q a hEll P).toH1Function

/-- The parent source has no uncentered value column: it is the actual
H10 potential times the physical column divergence. -/
theorem parent_boundary_old_source_formula (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (P : BlockVec 2) :
    parentBoundaryOldSource Q nu sigma hnu hsigma k b L n P =
      fun x => (0, -((oldSignedCanonicalFirstCorrector Q
        (responseFramePlanarCoefficientField nu sigma k)
        (responseFramePlanarCoefficientField_isElliptic
          (measurableSet_openCubeSet Q) nu sigma hnu hsigma k) P).toH1Function x •
          lemmaVPlanarWeakColumnDivergence (mainQ3DirectionW2 Q b L (whiteBasis n)).value x)) := by
  funext x
  simp [parentBoundaryOldSource, oldSignedLocalizedPotentialShear, lemmaVPlanarRowField, matVecMul_zero]

/-- Actual parent-source L2 membership follows from its physical smooth
multiplier and canonical H10 potential, without a norm premise. -/
theorem parent_boundary_old_source_memL2 (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (P : BlockVec 2) :
    MemBlockL2 (openCubeSet Q) (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n P) :=
  old_signed_localized_potential_shear_memL2 Q 0 _ _
    (mainQ3DirectionW2 Q b L (whiteBasis n)).value_memLp_top
    (mainQ3DirectionW2 Q b L (whiteBasis n)).gradient_memLp_top_volume

/-- The source change is a genuine global zero-normal gauge variation.
The physical shear and all four parent minimizers remain unchanged. -/
theorem parent_boundary_old_source_gauge (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (P : BlockVec 2) :
    ScalarVariation (openCubeSet Q)
      (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n P -
        oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
          ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) -
            (fun _ => P))) := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  let eta := (mainQ3DirectionW2 Q b L (whiteBasis n)).value
  let phi := (oldSignedCanonicalFirstCorrector Q a hEll P).toH1Function
  have hres : MemH10 (openCubeSet Q) (phi - (0 : H1Function (openCubeSet Q) →ₗ[ℝ]
      H1Function (openCubeSet Q)) phi).toFun := by
    simpa only [LinearMap.zero_apply, sub_zero] using
      (oldSignedCanonicalFirstCorrector Q a hEll P).memH10
  have ht := old_signed_localized_physical_shear_variation Q 0 eta phi hres
    (mainQ3DirectionW2 Q b L (whiteBasis n)).value_memLp_top
    (mainQ3DirectionW2 Q b L (whiteBasis n)).gradient_memLp_top_volume
  have hgrad : phi.grad = fun x => (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x).1-P.1 :=
    old_signed_canonical_first_corrector_grad Q a hEll P
  have he : oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2)-(fun _ => P)) =
      oldSignedPhysicalPotentialShear eta phi := by
    funext x
    change (0,-(eta x • matVecMul responsePlanarJ
      ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x).1-P.1))) =
      (0,-(eta x • matVecMul responsePlanarJ (phi.grad x)))
    rw [hgrad]
  rw [he]
  exact ht

/-- Actual weighted cell minimizers of the parent-interpolated source,
using the same coefficient and independent fine partition. -/
def parentBoundaryPatchedSource (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (P : BlockVec 2) :
    Vec 2 → BlockVec 2 :=
  oldSignedLocalResidual Q depth nu sigma hnu hsigma k
    (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n P)
    (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n P)

/-- The actual projected parent source remains square integrable. -/
theorem parent_boundary_patched_source_memL2 (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (P : BlockVec 2) :
    MemBlockL2 (openCubeSet Q) (parentBoundaryPatchedSource Q depth nu sigma hnu hsigma k b L n P) :=
  old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k _
    (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n P)

/-- The parent source supplies an admissible top trial on the fine cells,
without identifying any restricted parent solution with a cell minimizer. -/
theorem parent_boundary_top_trial_variation (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    ScalarVariation (openCubeSet Q)
      (oldSignedPatchedPlus Q depth nu sigma hnu hsigma k b L n i +
        parentBoundaryPatchedSource Q depth nu sigma hnu hsigma k b L n (basisVec i,0) -
        oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
          (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (basisVec i,0))) := by
  exact old_signed_local_top_trial_variation Q depth nu sigma hnu hsigma k _ _ _ _ _
    (old_signed_flat_plus_block_memL2 Q b L n i)
    (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n (basisVec i,0))
    (old_signed_flat_plus_pointwise_shear_variation Q b L n i)
    (parent_boundary_old_source_gauge Q nu sigma hnu hsigma k b L n (basisVec i,0))

/-- The parent-source bottom trial retains its negative flat contribution
on the same fine cells and is a genuine parent variation. -/
theorem parent_boundary_bottom_trial_variation (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    ScalarVariation (openCubeSet Q)
      (parentBoundaryPatchedSource Q depth nu sigma hnu hsigma k b L n (0,basisVec i) -
        oldSignedPatchedMinus Q depth nu sigma hnu hsigma k b L n i -
        oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
          (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i))) := by
  have hzero : oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      (fun _ => (0,basisVec i)) = 0 := by
    funext x
    simp [oldSignedPointwiseShear, matVecMul_zero]
  exact old_signed_local_bottom_trial_variation Q depth nu sigma hnu hsigma k _ _ _ _ _
    (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n (0,basisVec i))
    (old_signed_flat_minus_block_memL2 Q b L n i) hzero
    (parent_boundary_old_source_gauge Q nu sigma hnu hsigma k b L n (0,basisVec i))
    (old_signed_flat_minus_block_variation Q b L n i)

end
end ASDExplicitGamma.Native

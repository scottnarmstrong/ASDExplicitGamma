module

public import ASDExplicitGamma.Native.ParentBoundaryTrial

/-! Physical signed Hessian trials with the whole-parent source and an
independent fine comparison partition. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian
noncomputable section

/-- The parent-interpolated top candidate is an actual square-integrable field. -/
theorem parent_boundary_top_trial_memL2 (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    MemBlockL2 (openCubeSet Q)
      (oldSignedPatchedPlus Q depth nu sigma hnu hsigma k b L n i +
        parentBoundaryPatchedSource Q depth nu sigma hnu hsigma k b L n (basisVec i,0)) :=
  (old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k _
    (old_signed_flat_plus_block_memL2 Q b L n i)).add
    (parent_boundary_patched_source_memL2 Q depth nu sigma hnu hsigma k b L n (basisVec i,0))

/-- The parent-interpolated bottom candidate retains the negative flat tangent. -/
theorem parent_boundary_bottom_trial_memL2 (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    MemBlockL2 (openCubeSet Q)
      (parentBoundaryPatchedSource Q depth nu sigma hnu hsigma k b L n (0,basisVec i) -
        oldSignedPatchedMinus Q depth nu sigma hnu hsigma k b L n i) :=
  (parent_boundary_patched_source_memL2 Q depth nu sigma hnu hsigma k b L n (0,basisVec i)).sub
    (old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k _
      (old_signed_flat_minus_block_memL2 Q b L n i))

/-- The genuine top Hessian is bounded by the parent-source signed trial,
with all shear feedback still signed. No Hessian estimate is a premise. -/
theorem parent_boundary_top_hessian_trial (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    oldSignedPhysicalHessian Q nu sigma hnu hsigma k (basisVec i,0) b L n ≤
      oldSignedPhysicalTrialValue Q nu sigma hnu hsigma k (basisVec i,0) b L n
        (parent_boundary_top_trial_memL2 Q depth nu sigma hnu hsigma k b L n i) :=
  old_signed_physical_trial_bound Q nu sigma hnu hsigma k b L n (basisVec i,0)
    (parent_boundary_top_trial_memL2 Q depth nu sigma hnu hsigma k b L n i)
    (parent_boundary_top_trial_variation Q depth nu sigma hnu hsigma k b L n i)

/-- The genuine bottom Hessian admits the R-Z parent-source signed trial. -/
theorem parent_boundary_bottom_hessian_trial (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    oldSignedPhysicalHessian Q nu sigma hnu hsigma k (0,basisVec i) b L n ≤
      oldSignedPhysicalTrialValue Q nu sigma hnu hsigma k (0,basisVec i) b L n
        (parent_boundary_bottom_trial_memL2 Q depth nu sigma hnu hsigma k b L n i) :=
  old_signed_physical_trial_bound Q nu sigma hnu hsigma k b L n (0,basisVec i)
    (parent_boundary_bottom_trial_memL2 Q depth nu sigma hnu hsigma k b L n i)
    (parent_boundary_bottom_trial_variation Q depth nu sigma hnu hsigma k b L n i)

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.OldSignedPatchProjectionBound
public import ASDExplicitGamma.Native.OldSignedReciprocalPatchEnergy

/-! Exact-energy paired projection estimates for the same physical
canonical minimizer. The negative ordinary parent term is retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- Depth projection energy of the actual first affine defect. -/
def oldSignedPrimalProjectionEnergy (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) : ℝ :=
  ∑ i,energy Q (cubeProjection Q depth (fun x =>
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x).1 i-P.1 i))

/-- Depth projection energy of the reciprocal field about an affine datum.
For opposite pure loads this is the reciprocal defect in the paired budget. -/
def oldSignedReciprocalProjectionEnergy (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P W : BlockVec 2) : ℝ :=
  ∑ i,energy Q (cubeProjection Q depth (fun x =>
    (oldSignedDualReflection Q nu sigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P) x).1 i-W.1 i))

/-- Ordinary projection bound with the exact child-minus-parent quadratic form. -/
theorem old_signed_primal_projection_exact_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedPrimalProjectionEnergy Q depth nu sigma hnu hsigma k P ≤
      lemmaVInverseDepthMax Q a depth *
        (descendantsAverage Q depth (fun U => blockVecDot P
          (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) P))-
        blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P)) := by
  intro a
  have hh := old_signed_patch_projection_bound Q depth nu sigma hnu hsigma k P
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
    (old_signed_canonical_compatible Q nu sigma hnu hsigma k P)
  dsimp only at hh
  rw [old_signed_parent_patch_energy] at hh
  exact hh

/-- Reciprocal projection bound with the exact complementary quadratic form. -/
theorem old_signed_reciprocal_projection_exact_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P W : BlockVec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedReciprocalProjectionEnergy Q depth nu sigma hnu hsigma k P W ≤
      lemmaVInverseDepthMax Q a depth *
        (blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P)+
        descendantsAverage Q depth (fun U => blockVecDot W
          (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) W))-2*blockVecDot P W.swap) := by
  intro a
  have hh := old_signed_patch_projection_bound Q depth nu sigma hnu hsigma k W
    (oldSignedDualReflection Q nu sigma k (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P))
    (old_signed_reflected_canonical_compatible Q nu sigma hnu hsigma k P)
  dsimp only at hh
  rw [old_signed_reciprocal_patch_energy] at hh
  exact hh

/-- Combining the two genuine projection bounds cancels the parent energy
exactly, while retaining the child directional quadratic forms. -/
theorem old_signed_paired_projection_exact_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P W : BlockVec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedPrimalProjectionEnergy Q depth nu sigma hnu hsigma k P+
      oldSignedReciprocalProjectionEnergy Q depth nu sigma hnu hsigma k P W ≤
      lemmaVInverseDepthMax Q a depth *
        (descendantsAverage Q depth (fun U => blockVecDot P
          (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) P))+
        descendantsAverage Q depth (fun U => blockVecDot W
          (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) W))-2*blockVecDot P W.swap) := by
  intro a
  have hh := add_le_add (old_signed_primal_projection_exact_bound Q depth nu sigma hnu hsigma k P)
    (old_signed_reciprocal_projection_exact_bound Q depth nu sigma hnu hsigma k P W)
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Native

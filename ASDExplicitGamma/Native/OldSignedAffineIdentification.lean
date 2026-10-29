module

public import ASDExplicitGamma.Native.OldSignedCoarseMean

/-! The affine weighted residual used by OLD is the canonical physical
minimizer, so the coarse mean identities apply to that same residual. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Response
noncomputable section

/-- Weighted complementary projection of a constant is the actual affine
minimizer. The proof uses the actual correction space and first variation. -/
theorem old_signed_affine_residual_eq_minimizer (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma) (k : ResponseCoefficient (openCubeSet Q))
    (P : BlockVec 2) :
    let M := scalarFrameRealization Q nu sigma hnu hsigma k
    scalarProjectionResidual Q nu sigma hnu hsigma k (M.constantField P)=M.minimizerMap P := by
  intro M
  let D := scalarFrameEnergyData Q nu sigma hnu hsigma k
  let K := scalarFrameVariationSpace Q nu sigma hnu hsigma k
  let A := responseEnergyUp D (M.constantField P)
  let S := responseEnergyUp D (M.minimizerMap P)
  have hd : A-S ∈ K.toSubmodule := by
    change M.constantField P-M.minimizerMap P ∈ M.correctionSpace.correctionSpace
    have he : M.constantField P-M.minimizerMap P= -(M.minimizerMap P-M.constantField P) := by abel
    rw [he]
    exact M.correctionSpace.correctionSpace.neg_mem (M.sub_minimizerMap_apply_mem P)
  have hp : K.toSubmodule.starProjection A=A-S := by
    apply K.toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero hd
    intro Y hY
    have he : A-(A-S)=S := by abel
    rw [he]
    change M.energyBilin (M.minimizerMap P) Y.down=0
    exact M.minimizerMap_firstVariation P ⟨Y.down,hY⟩
  change (A-K.toSubmodule.starProjection A).down=M.minimizerMap P
  rw [hp]
  have he : A-(A-S)=S := by abel
  rw [he]
  rfl

/-- The pointwise L2 representative is the same canonical physical field
used to recover the bottom-right coarse block. -/
theorem old_signed_affine_residual_field (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma) (k : ResponseCoefficient (openCubeSet Q))
    (P : BlockVec 2) :
    scalarResidualField Q nu sigma hnu hsigma k
      ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) =
    oldSignedCanonicalAffineField Q (responseFramePlanarCoefficientField nu sigma k)
      (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
        nu sigma hnu hsigma k) P := by
  unfold scalarResidualField
  rw [old_signed_affine_residual_eq_minimizer]
  rfl

end
end ASDExplicitGamma.Native

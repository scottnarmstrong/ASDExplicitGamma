module

public import ASDExplicitGamma.Native.OldSignedPureSecondSourceEnergy
public import ASDExplicitGamma.Native.OldSignedAffineIdentification

/-! The pure-second flat energy pays both its affine cross and its centered
energy through the inverse directional construction. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic Inverse
noncomputable section

/-- Sharp flat-source energy for a pure-second field. All affine flux
estimates follow from the actual primal/reciprocal paired construction. -/
theorem old_signed_flat_projection_energy_pure_second_inverse
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (e : Vec 2)
    (hzero : ∀ x,(F x).1=0) (hmean : oldSignedBlockMean Q F=(0,e))
    (hPfst : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (F x).1 i-(oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (F x).2 i-(oldSignedBlockMean Q F).2 i)))) :
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedEnergyPairing Q nu sigma k
      (scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF))
      (scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)) ≤
      blockVecDot (oldSignedBlockMean Q F)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (oldSignedBlockMean Q F))+
      2*Real.sqrt (oldSignedDirectionalProxy Q a e)*
        oldSignedBlockPositiveNorm Q (fun x => F x-oldSignedBlockMean Q F)+
      oldSignedInverseHistory Q a*(oldSignedBlockPositiveNorm Q
        (fun x => F x-oldSignedBlockMean Q F))^2 := by
  intro a
  refine old_signed_flat_projection_energy_of_centered_energy_and_pairing
    Q nu sigma hnu hsigma k F hF _ _ ?_ ?_
  · apply old_signed_pure_second_source_energy Q nu sigma hnu hsigma k
      (fun x => F x-oldSignedBlockMean Q F) (hF.sub (memLp_const (oldSignedBlockMean Q F)))
    · intro x
      simp only [Prod.fst_sub,hzero,hmean,sub_self]
    · exact hPfst
    · exact hPsnd
  · let m := oldSignedBlockMean Q F
    let G := fun x => F x-m
    let J := scalarCoefficientFlux a (scalarResidualField Q nu sigma hnu hsigma k
      ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField m))
    let D := fun x => J x-m
    have hG : MemBlockL2 (openCubeSet Q) G := hF.sub (memLp_const m)
    have hJ : MemBlockL2 (openCubeSet Q) J := scalar_coefficient_flux_memL2 Q _
      (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
        nu sigma hnu hsigma k) (Lp.memLp _)
    have hD : MemBlockL2 (openCubeSet Q) D := hJ.sub (memLp_const m)
    have hGzero (x : Vec 2) : (G x).1=0 := by
      simp only [G,m,Prod.fst_sub,hzero,hmean,sub_self]
    have hp := old_signed_pure_second_pairing_bound Q hG hD hGzero hPfst hPsnd
    have hw : vectorWeakHaarNorm Q (fun x => (D x).2) ≤
        Real.sqrt (oldSignedDirectionalProxy Q a e) := by
      dsimp only [D,J,m]
      rw [hmean,old_signed_affine_residual_field]
      exact old_signed_bottom_reciprocal_weak_norm Q nu sigma hnu hsigma k e
    exact hp.trans (mul_le_mul_of_nonneg_left hw (Real.sqrt_nonneg _))
end
end ASDExplicitGamma.Native

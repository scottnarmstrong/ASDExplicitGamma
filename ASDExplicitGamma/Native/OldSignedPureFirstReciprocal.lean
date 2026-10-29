module

public import ASDExplicitGamma.Native.OldSignedPureSecondFeedback
public import ASDExplicitGamma.Native.OldSignedTopDirectionalNorms
public import ASDExplicitGamma.Native.OldSignedResidualReciprocalEnergy

/-! Directional reciprocal feedback for the actual top-mean OLD source. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- The reciprocal flat defect pays only its directional affine proxy;
the centered reciprocal source has the sqrt(B M) oscillation cost. -/
theorem old_signed_pure_first_reciprocal_directional (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (e : Vec 2) (hmean : oldSignedBlockMean Q F=(e,0))
    (hPfst : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (F x).1 i-(oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (F x).2 i-(oldSignedBlockMean Q F).2 i)))) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)
    vectorWeakHaarNorm Q (fun x => (scalarCoefficientFlux a Z x).2) ≤
      Real.sqrt (oldSignedDirectionalProxy Q a e)+
      Real.sqrt (oldSignedInverseHistory Q a*oldSignedResponseHistory Q a)*
        oldSignedBlockPositiveNorm Q (fun x => F x-oldSignedBlockMean Q F) := by
  intro a Z
  let m := oldSignedBlockMean Q F
  let G : Vec 2 → BlockVec 2 := fun x => F x-m
  let hG : MemBlockL2 (openCubeSet Q) G := hF.sub (memLp_const m)
  let HM := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField m
  let ZM := scalarResidualField Q nu sigma hnu hsigma k HM
  let ZG := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hG)
  let JM := scalarCoefficientFlux a ZM
  let JG := scalarCoefficientFlux a ZG
  have hc' : vectorWeakHaarNorm Q (fun x => (JG x).2) ≤
      Real.sqrt (oldSignedInverseHistory Q a*oldSignedResponseHistory Q a)*
        oldSignedBlockPositiveNorm Q G :=
    old_signed_centered_reciprocal_norm Q nu sigma hnu hsigma k G hG
      (by simpa only [G,m,Prod.fst_sub,Pi.sub_apply] using hPfst)
      (by simpa only [G,m,Prod.snd_sub,Pi.sub_apply] using hPsnd)
  have ha : vectorWeakHaarNorm Q (fun x => (JM x).2) ≤
      Real.sqrt (oldSignedDirectionalProxy Q a e) := by
    dsimp only [JM,ZM,HM,m]
    rw [hmean,old_signed_affine_residual_field]
    exact old_signed_top_reciprocal_weak_norm Q nu sigma hnu hsigma k e
  have he : (fun x => (scalarCoefficientFlux a Z x).2) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (fun x => (JM x).2+(JG x).2) := by
    filter_upwards [old_signed_residual_mean_split_ae Q nu sigma hnu hsigma k F hF] with x hx
    change (blockMatVecMul (blockCoeffField a x) (Z x)).2=_
    rw [hx,blockMatVecMul_add]
    rfl
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hJM : MemBlockL2 (openCubeSet Q) JM :=
    scalar_coefficient_flux_memL2 Q a hEll (Lp.memLp ZM)
  have hJG : MemBlockL2 (openCubeSet Q) JG :=
    scalar_coefficient_flux_memL2 Q a hEll (Lp.memLp ZG)
  have hAM := memVectorL2_snd_of_memBlockL2 hJM
  have hAG := memVectorL2_snd_of_memBlockL2 hJG
  rw [old_signed_vector_weak_congr Q he]
  exact (old_signed_vector_weak_triangle Q
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hAM i))
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hAG i))).trans
      (add_le_add ha hc')

end
end ASDExplicitGamma.Native

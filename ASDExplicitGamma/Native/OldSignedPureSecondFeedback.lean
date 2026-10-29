module

public import ASDExplicitGamma.Native.OldSignedCenteredFeedback
public import ASDExplicitGamma.Native.OldSignedAffineResidualSplit
public import ASDExplicitGamma.Native.OldSignedPureSecondPairing
public import ASDExplicitGamma.Native.OldSignedAffineIdentification
public import ASDExplicitGamma.Native.OldSignedWeakTriangle
public import ASDExplicitGamma.Native.OldSignedHaarCongr

/-! Directional affine feedback for pure-second OLD sources. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- The affine first potential and reciprocal defect share the same
actual directional proxy. -/
theorem old_signed_bottom_first_weak_norm (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,e)
    vectorWeakHaarNorm Q (fun x => (S x).1) ≤
      Real.sqrt (oldSignedDirectionalProxy Q (responseFramePlanarCoefficientField nu sigma k) e) := by
  intro S
  apply Real.sqrt_le_sqrt
  exact (le_add_of_nonneg_right (vectorWeakHaarEnergy_nonneg Q _)).trans
    (old_signed_bottom_directional_weak_bound Q nu sigma hnu hsigma k e)

/-- Pure-second residual first component: the centered cost is unchanged,
while the affine cost is its literal directional inverse proxy. -/
theorem old_signed_pure_second_first_directional (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (e : Vec 2) (hmean : oldSignedBlockMean Q F=(0,e))
    (hzero : ∀ x,(F x).1=0)
    (hPfst : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (F x).1 i-(oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (F x).2 i-(oldSignedBlockMean Q F).2 i)))) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)
    vectorWeakHaarNorm Q (fun x => (Z x).1) ≤
      Real.sqrt (oldSignedDirectionalProxy Q a e)+
      (1+inverseHistoryDiscount)*oldSignedInverseHistory Q a*
        oldSignedBlockPositiveNorm Q (fun x => F x-oldSignedBlockMean Q F) := by
  intro a Z
  let m := oldSignedBlockMean Q F
  let G : Vec 2 → BlockVec 2 := fun x => F x-m
  let hG : MemBlockL2 (openCubeSet Q) G := hF.sub (memLp_const m)
  let HM := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField m
  let ZM := scalarResidualField Q nu sigma hnu hsigma k HM
  let ZG := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hG)
  have hmG : oldSignedBlockMean Q G=0 := old_signed_centered_block_mean_zero Q hF
  have hGzero (x : Vec 2) : (G x).1=0 := by
    simp only [G,m,Prod.fst_sub,hzero,hmean,sub_self]
  have hc := old_signed_centered_pure_second_first_weak Q nu sigma hnu hsigma k G hG hmG
    (by simpa only [hmG,Prod.fst_zero,Pi.zero_apply,sub_zero,G,m,Prod.fst_sub,Pi.sub_apply] using hPfst)
    (by simpa only [hmG,Prod.snd_zero,Pi.zero_apply,sub_zero,G,m,Prod.snd_sub,Pi.sub_apply] using hPsnd)
    (Filter.Eventually.of_forall hGzero)
  dsimp only at hc
  have hc' : vectorWeakHaarNorm Q (fun x => (ZG x).1) ≤
      (1+inverseHistoryDiscount)*oldSignedInverseHistory Q a*oldSignedBlockPositiveNorm Q G := by
    simpa only [hmG,sub_zero,show (fun _ : Vec 2 => (0 : BlockVec 2))=0 from rfl] using hc
  have ha : vectorWeakHaarNorm Q (fun x => (ZM x).1) ≤
      Real.sqrt (oldSignedDirectionalProxy Q a e) := by
    dsimp only [ZM,HM,m]
    rw [hmean,old_signed_affine_residual_field]
    exact old_signed_bottom_first_weak_norm Q nu sigma hnu hsigma k e
  have he : (fun x => (Z x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun x => (ZM x).1+(ZG x).1) := by
    filter_upwards [old_signed_residual_mean_split_ae Q nu sigma hnu hsigma k F hF] with x hx
    exact congrArg Prod.fst hx
  rw [old_signed_vector_weak_congr Q he]
  exact (old_signed_vector_weak_triangle Q
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2
      (memVectorL2_fst_of_memBlockL2 (Lp.memLp ZM)) i))
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2
      (memVectorL2_fst_of_memBlockL2 (Lp.memLp ZG)) i))).trans (add_le_add ha hc')

end
end ASDExplicitGamma.Native

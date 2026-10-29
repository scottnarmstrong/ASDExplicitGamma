module

public import ASDExplicitGamma.Native.OldSignedPureSecondSharp
public import ASDExplicitGamma.Native.OldSignedPureSecondFeedback
public import ASDExplicitGamma.Native.OldSignedWeakPositiveComparison

/-! The half-gain constant `1/2 + 3^(-1/4)` in the OLD pure-second first
potential estimate (E2 R13). -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

private theorem halfgain_discount_eq : inverseHistoryDiscount = (3:ℝ)^(-(1/4:ℝ)) := by
  rw [inverse_history_discount_eq, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]

/-- Half-gain form of `old_signed_pure_second_sharp_first`. -/
theorem old_signed_pure_second_sharp_first_halfgain (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (g : Vec 2 → Vec 2)
    (hF : MemBlockL2 (openCubeSet Q) (fun x => (0,g x)))
    (hp : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => g x i))))
    (v : H10Function (openCubeSet Q))
    (hv : (fun x => (scalarResidualField Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField hF) x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)] v.toH1Function.grad) :
    vectorWeakHaarNorm Q v.toH1Function.grad ≤
      (1/2+inverseHistoryDiscount)*oldSignedInverseHistory Q
        (responseFramePlanarCoefficientField nu sigma k)*vectorPositiveHaarNorm Q g := by
  have hg : MemLp g 2 (normalizedCubeMeasure Q) := memLp_pi_iff.mpr
    (fun i => memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF) i))
  have hv' : (fun x => (projectedSourceField Q nu sigma hnu hsigma k hg x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)] v.toH1Function.grad := by
    unfold projectedSourceField
    rw [old_signed_pure_second_load_eq Q g hg hF]
    exact hv
  have hh := projectedSource_forced_feedback_bound Q nu sigma hnu hsigma k hg hp v hv'
  rw [halfgain_discount_eq]
  exact hh

/-- Centered pure-second source with the half-gain constant. -/
theorem old_signed_centered_pure_second_first_weak_halfgain (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (G : Vec 2 → BlockVec 2) (hG : MemBlockL2 (openCubeSet Q) G)
    (hGzero : (fun x => (G x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)] 0)
    (hPsnd : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (G x).2 i)))) :
    vectorWeakHaarNorm Q (fun x => (scalarResidualField Q nu sigma hnu hsigma k
        (toHilbertBlockL2OfBlockField hG) x).1) ≤
      (1/2+inverseHistoryDiscount)*oldSignedInverseHistory Q
        (responseFramePlanarCoefficientField nu sigma k)*oldSignedBlockPositiveNorm Q G := by
  let g : Vec 2 → Vec 2 := fun x => (G x).2
  have hg : MemVectorL2 (openCubeSet Q) g := memVectorL2_snd_of_memBlockL2 hG
  have hF : MemBlockL2 (openCubeSet Q) (fun x => (0, g x)) :=
    memBlockL2_blockField MemLp.zero hg
  have hGF : toHilbertBlockL2OfBlockField hG = toHilbertBlockL2OfBlockField hF := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField hG,
      coeFn_toHilbertBlockL2OfBlockField hF, hGzero] with x h1 h2 h3
    rw [h1, h2]
    have : G x = (0, g x) := Prod.ext h3 rfl
    unfold hilbertifyBlockField
    rw [this]
  have hgL : MemLp g 2 (normalizedCubeMeasure Q) := memLp_pi_iff.mpr
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hg i))
  obtain ⟨v, hv⟩ := projectedSource_firstPotential_exists Q nu sigma hnu hsigma k hgL
  have hv' : (fun x => (scalarResidualField Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField hF) x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)]
        v.toH1Function.grad := by
    unfold projectedSourceField at hv
    rw [old_signed_pure_second_load_eq Q g hgL hF] at hv
    exact hv
  have hs := old_signed_pure_second_sharp_first_halfgain Q nu sigma hnu hsigma k g hF
    hPsnd v hv'
  rw [hGF]
  have hcongr : (fun x => (scalarResidualField Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField hF) x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)]
        v.toH1Function.grad := hv'
  rw [old_signed_vector_weak_congr Q hcongr]
  have hB : 0 ≤ oldSignedInverseHistory Q (responseFramePlanarCoefficientField nu sigma k) :=
    lemmaVInverseHistory_nonneg Q _ (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hα := inverse_history_discount_range
  exact hs.trans (mul_le_mul_of_nonneg_left (old_signed_block_snd_positive_le Q G)
    (mul_nonneg (by linarith [hα.1]) hB))

/-- Pure-second residual first component: the centered cost is unchanged,
while the affine cost is its literal directional inverse proxy. -/
theorem old_signed_pure_second_first_directional_halfgain (Q : TriadicCube 2)
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
      (1/2+inverseHistoryDiscount)*oldSignedInverseHistory Q a*
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
  have hc' : vectorWeakHaarNorm Q (fun x => (ZG x).1) ≤
      (1/2+inverseHistoryDiscount)*oldSignedInverseHistory Q a*oldSignedBlockPositiveNorm Q G :=
    old_signed_centered_pure_second_first_weak_halfgain Q nu sigma hnu hsigma k G hG
      (Filter.Eventually.of_forall hGzero)
      (by simpa only [hmG,Prod.snd_zero,Pi.zero_apply,sub_zero,G,m,Prod.snd_sub,Pi.sub_apply] using hPsnd)
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

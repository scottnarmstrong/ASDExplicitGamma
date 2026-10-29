module

public import ASDExplicitGamma.Native.OldSignedFlatAffine

/-! Exact affine/centered split of the actual source and residual classes. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- The actual source class splits into its affine mean and centered field. -/
theorem old_signed_block_field_mean_split (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F) :
    let m := oldSignedBlockMean Q F
    let H := toHilbertBlockL2OfBlockField hF
    let HM := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField m
    let HG := toHilbertBlockL2OfBlockField
      (hF.sub (memLp_const (oldSignedBlockMean Q F)))
    H = HM + HG := by
  dsimp
  let m := oldSignedBlockMean Q F
  let hConst : MemBlockL2 (openCubeSet Q) (fun _ : Vec 2 => m) := memLp_const m
  let hG : MemBlockL2 (openCubeSet Q) (fun x => F x - m) := hF.sub (memLp_const m)
  let HM := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField m
  let HG := toHilbertBlockL2OfBlockField hG
  have hConstRaw : toHilbertBlockL2OfBlockField hConst =
      blockVecToHilbertBlockL2Const m := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField hConst,
      coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet Q) m] with x hx hy
    exact hx.trans hy.symm
  have hSource : toHilbertBlockL2OfBlockField hF = HM + HG := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField hF,
      coeFn_toHilbertBlockL2OfBlockField hConst,
      coeFn_toHilbertBlockL2OfBlockField hG,
      MeasureTheory.Lp.coeFn_add HM HG] with x hF' hConst' hG' hsum
    have hmConst : HM x = HilbertBlockVec.ofBlockVec m := by
      have hpoint := congrArg (fun H : HilbertBlockL2 (openCubeSet Q) => H x) hConstRaw
      exact hpoint.symm.trans hConst'
    have hGpoint : HG x = HilbertBlockVec.ofBlockVec (F x - m) := by
      simpa [HG, hilbertifyBlockField] using hG'
    calc
      toHilbertBlockL2OfBlockField hF x = hilbertifyBlockField F x := hF'
      _ = Function.const (Vec 2) (HilbertBlockVec.ofBlockVec m) x +
          hilbertifyBlockField (fun x => F x - m) x := by
        apply (HilbertBlockVec.continuousLinearEquivBlockVec 2).injective
        change F x = m + (F x - m)
        abel
      _ = HM x + HG x := by
        change HilbertBlockVec.ofBlockVec m +
          HilbertBlockVec.ofBlockVec (F x - m) = HM x + HG x
        rw [← hmConst, ← hGpoint]
      _ = (HM + HG) x := by simpa [Pi.add_apply] using hsum.symm
  exact hSource

/-- Centering removes precisely the actual block mean. -/
theorem old_signed_centered_block_mean_zero (Q : TriadicCube 2)
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F) :
    oldSignedBlockMean Q (fun x => F x - oldSignedBlockMean Q F) = 0 := by
  let m := oldSignedBlockMean Q F
  let G : Vec 2 → BlockVec 2 := fun x => F x - m
  apply Prod.ext
  · funext i
    have hFi : MemLp (fun x => (F x).1 i) 2 (normalizedCubeMeasure Q) :=
      memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hF) i)
    change cubeAverage Q (fun x => (F x).1 i - cubeAverage Q (fun x => (F x).1 i)) = 0
    rw [cubeAverage_sub_const_of_memLp_two Q hFi (cubeAverage Q (fun x => (F x).1 i))]
    simp
  · funext i
    have hFi : MemLp (fun x => (F x).2 i) 2 (normalizedCubeMeasure Q) :=
      memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF) i)
    change cubeAverage Q (fun x => (F x).2 i - cubeAverage Q (fun x => (F x).2 i)) = 0
    rw [cubeAverage_sub_const_of_memLp_two Q hFi (cubeAverage Q (fun x => (F x).2 i))]
    simp

/-- Residual projection preserves the same affine/centered split as an
almost-everywhere identity of the actual physical representatives. -/
theorem old_signed_residual_mean_split_ae (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) :
    let m := oldSignedBlockMean Q F
    let HM := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField m
    let HG := toHilbertBlockL2OfBlockField (hF.sub (memLp_const m))
    (scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF) : Vec 2 → BlockVec 2) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (fun x => scalarResidualField Q nu sigma hnu hsigma k HM x+
        scalarResidualField Q nu sigma hnu hsigma k HG x) := by
  intro m HM HG
  have he := old_signed_block_field_mean_split Q nu sigma hnu hsigma k F hF
  dsimp only at he
  have hclass : scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)=
      scalarResidualField Q nu sigma hnu hsigma k HM+scalarResidualField Q nu sigma hnu hsigma k HG := by
    rw [he]
    exact scalar_residual_field_add Q nu sigma hnu hsigma k HM HG
  filter_upwards [Lp.ext_iff.mp hclass,Lp.coeFn_add
    (scalarResidualField Q nu sigma hnu hsigma k HM)
    (scalarResidualField Q nu sigma hnu hsigma k HG)] with x hx hy
  exact hx.trans hy

end
end ASDExplicitGamma.Native

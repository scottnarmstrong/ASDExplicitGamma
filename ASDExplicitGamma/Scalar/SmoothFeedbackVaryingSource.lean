module

public import ASDExplicitGamma.Scalar.SmoothFeedbackGapIdentity
public import ASDExplicitGamma.Scalar.SmoothFeedbackResponse
public import ASDExplicitGamma.Scalar.TopSourceResidual
public import ASDExplicitGamma.Native.OldSignedLocalData
public import ASDExplicitGamma.Native.OldSignedHistoryBounds
public import ASDExplicitGamma.Native.OldSignedFlatAffine
public import ASDExplicitGamma.Native.OldSignedCompatibleFullMean
public import ASDExplicitGamma.Native.OldSignedDirectionalDepthPositivity
public import ASDExplicitGamma.Native.OldSignedAffineCorrectorBounds
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetBottomResidual

/-! Linear source identities on the actual OLD depth-cell residual carrier.

These identities let the Λ8 patch split use the literal varying source and
its cell-mean/oscillation decomposition. They are identities for the actual
weighted projection, not assumptions about an abstract response operator. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native

noncomputable section

/-- The actual cell solve preserves the average of the first source block.
This identifies the constant part in the mean/oscillation split with the
literal source average on the cell. -/
theorem smooth_feedback_old_signed_cell_residual_first_mean
    (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (i : Fin 2) :
    cubeAverage R (fun x =>
      (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF x).1 i) =
      cubeAverage R (fun x => (F x).1 i) := by
  let Z : Vec 2 → BlockVec 2 := oldSignedCellResidual Q R hRQ
    nu sigma hnu hsigma k F hF
  let hFR : MemBlockL2 (openCubeSet R) F :=
    hF.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hZ : MemBlockL2 (openCubeSet R) Z :=
    (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF).property
  have hFcoord : MemLp (fun x => (F x).1 i) 2 (normalizedCubeMeasure R) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hFR) i)
  have hZcoord : MemLp (fun x => (Z x).1 i) 2 (normalizedCubeMeasure R) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hZ) i)
  have hRemoved := old_signed_cell_removed_variation Q R hRQ
    nu sigma hnu hsigma k F hF
  have hPotential : IsPotentialZeroTraceOn (openCubeSet R)
      (fun x => (F x - Z x).1) := by
    simpa [Z] using hRemoved.2.1
  have hIntegral := IsPotentialZeroTraceOn.integral_eq_zero hPotential
  have hzero : cubeAverage R (fun x => (F x).1 i - (Z x).1 i) = 0 := by
    rw [← Cold.square_volumeAverage_eq_cubeAverage]
    apply volumeAverage_eq_zero_of_integral_eq_zero
    exact congrFun hIntegral i
  have hsub : cubeAverage R (fun x => (F x).1 i - (Z x).1 i) =
      cubeAverage R (fun x => (F x).1 i) -
        cubeAverage R (fun x => (Z x).1 i) := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_sub (hFcoord.integrable (by norm_num))
      (hZcoord.integrable (by norm_num))
  rw [hsub] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- The varying top source splits in the actual OLD energy norm into its
constant cell mean response and the residual of its centered source. This
keeps the centered term as the literal local solve needed by the Λ8 patch. -/
theorem smooth_feedback_scalar_top_source_cell_energy_triangle
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (f : Vec 2 → Vec 2) (hf : ScalarPositiveHaarAdmissible Q f)
    (hfcenter : ScalarPositiveHaarAdmissible Q
      (fun x => f x - fun i => cubeAverage Q (fun y => f y i))) :
    let mean : Vec 2 := fun i => cubeAverage Q (fun x => f x i)
    let P : BlockVec 2 := (mean, 0)
    let Y := scalarResidualField Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField (scalar_source_block_memL2 Q hf.memLp))
    let YC := scalarResidualField Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField (scalar_source_block_memL2 Q hfcenter.memLp))
    oldSignedEnergyPairing Q nu sigma k Y Y ≤
      (Real.sqrt (blockVecDot P
        (blockMatVecMul
          (coarseBlockMatrix (openCubeSet Q)
            (responseFramePlanarCoefficientField nu sigma k)) P)) +
        Real.sqrt (oldSignedEnergyPairing Q nu sigma k YC YC)) ^ 2 := by
  classical
  dsimp only
  let mean : Vec 2 := fun i => cubeAverage Q (fun x => f x i)
  let P : BlockVec 2 := (mean, 0)
  let Fmean : Vec 2 → BlockVec 2 := fun _ => P
  let Fcenter : Vec 2 → BlockVec 2 := fun x => (f x - mean, 0)
  let htotal : HilbertBlockL2 (openCubeSet Q) :=
    toHilbertBlockL2OfBlockField (scalar_source_block_memL2 Q hf.memLp)
  let hmeanBlock : MemBlockL2 (openCubeSet Q) Fmean := memLp_const P
  let hmean : HilbertBlockL2 (openCubeSet Q) :=
    (scalarFrameRealization Q nu sigma hnu hsigma k).constantField P
  let hcenterBlock : MemBlockL2 (openCubeSet Q) Fcenter :=
    scalar_source_block_memL2 Q hfcenter.memLp
  let hcenter : HilbertBlockL2 (openCubeSet Q) :=
    toHilbertBlockL2OfBlockField hcenterBlock
  let a := responseFramePlanarCoefficientField nu sigma k
  let Y : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k htotal
  let YM : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k hmean
  let YC : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k hcenter
  have hmeanLoad : toHilbertBlockL2OfBlockField hmeanBlock = hmean := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField hmeanBlock,
      coeFn_blockVecToHilbertBlockL2Const P] with x hleft hright
    calc
      (toHilbertBlockL2OfBlockField hmeanBlock) x =
          HilbertBlockVec.ofBlockVec (Fmean x) := by
        simpa [hilbertifyBlockField] using hleft
      _ = HilbertBlockVec.ofBlockVec P := by simp [Fmean]
      _ = hmean x := by exact hright.symm.trans (by rfl)
  have hload : htotal = hmean + hcenter := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField
        (scalar_source_block_memL2 Q hf.memLp),
      coeFn_toHilbertBlockL2OfBlockField hmeanBlock,
      coeFn_toHilbertBlockL2OfBlockField hcenterBlock,
      Lp.coeFn_add hmean hcenter] with x htotalx hmeanBlockx hcenterx hadd
    have hmeanx : hmean x = HilbertBlockVec.ofBlockVec P := by
      rw [← hmeanLoad]
      simpa [hilbertifyBlockField, Fmean] using hmeanBlockx
    have hcenterx' : hcenter x =
        HilbertBlockVec.ofBlockVec (f x - mean, 0) := by
      simpa [hilbertifyBlockField, Fcenter] using hcenterx
    calc
      htotal x = HilbertBlockVec.ofBlockVec (f x, 0) := by
        simpa [hilbertifyBlockField, scalar_source_block_memL2] using htotalx
      _ = HilbertBlockVec.ofBlockVec P +
          HilbertBlockVec.ofBlockVec (f x - mean, 0) := by
        apply HilbertBlockVec.ext <;> simp [P, mean]
      _ = (hmean + hcenter) x := by
        rw [← hmeanx, ← hcenterx']
        exact hadd.symm
  have hYadd : Y =ᵐ[volumeMeasureOn (openCubeSet Q)] (YM + YC) := by
    dsimp only [Y, YM, YC]
    rw [hload]
    have hRadd := smooth_feedback_scalar_residual_field_add Q nu sigma hnu hsigma k
      hmean hcenter
    have hfun := congrArg (fun Z : BlockL2 (openCubeSet Q) =>
      (Z : Vec 2 → BlockVec 2)) hRadd
    filter_upwards [Lp.coeFn_add
      (scalarResidualField Q nu sigma hnu hsigma k hmean)
      (scalarResidualField Q nu sigma hnu hsigma k hcenter)] with x hx
    rw [hfun]
    exact hx
  have hYMenergy : oldSignedEnergyPairing Q nu sigma k YM YM =
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) := by
    exact old_signed_affine_energy Q nu sigma hnu hsigma k P
  have hYMmem : MemBlockL2 (openCubeSet Q) YM := Lp.memLp _
  have hYCmem : MemBlockL2 (openCubeSet Q) YC := Lp.memLp _
  have hYmem : MemBlockL2 (openCubeSet Q) Y := Lp.memLp _
  have hEYM : 0 ≤ oldSignedEnergyPairing Q nu sigma k YM YM :=
    old_signed_energy_pairing_nonneg Q nu sigma hnu hsigma k YM
  have hEYC : 0 ≤ oldSignedEnergyPairing Q nu sigma k YC YC :=
    old_signed_energy_pairing_nonneg Q nu sigma hnu hsigma k YC
  have hcross := old_signed_energy_pairing_sq_le_product Q nu sigma hnu hsigma k
    hYMmem hYCmem
  have hcrossAbs : |oldSignedEnergyPairing Q nu sigma k YM YC| ≤
      Real.sqrt (oldSignedEnergyPairing Q nu sigma k YM YM) *
        Real.sqrt (oldSignedEnergyPairing Q nu sigma k YC YC) := by
    have hsq := Real.sqrt_le_sqrt hcross
    rw [Real.sqrt_sq_eq_abs] at hsq
    rw [Real.sqrt_mul hEYM] at hsq
    exact hsq
  have hExpand : oldSignedEnergyPairing Q nu sigma k Y Y =
      oldSignedEnergyPairing Q nu sigma k YM YM +
        2 * oldSignedEnergyPairing Q nu sigma k YM YC +
          oldSignedEnergyPairing Q nu sigma k YC YC := by
    calc
      oldSignedEnergyPairing Q nu sigma k Y Y =
          oldSignedEnergyPairing Q nu sigma k (YM + YC) (YM + YC) :=
        old_signed_energy_pairing_congr_ae Q nu sigma k hYadd hYadd
      _ = _ := by
        rw [old_signed_energy_pairing_add_left Q nu sigma hnu hsigma k
          hYMmem hYCmem (hYMmem.add hYCmem),
          old_signed_energy_pairing_add_right Q nu sigma hnu hsigma k
            hYMmem hYMmem hYCmem,
          old_signed_energy_pairing_add_right Q nu sigma hnu hsigma k
            hYCmem hYMmem hYCmem,
          old_signed_energy_pairing_symm Q nu sigma k YC YM]
        ring
  let Emean := blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P)
  let Ecenter := oldSignedEnergyPairing Q nu sigma k YC YC
  have hMeanEq : oldSignedEnergyPairing Q nu sigma k YM YM = Emean := by
    simpa [Emean, a, P] using hYMenergy
  have hEmean : 0 ≤ Emean := by rw [← hMeanEq]; exact hEYM
  have hsqrtMeanSq : Real.sqrt Emean ^ 2 = Emean := Real.sq_sqrt hEmean
  have hsqrtCenterSq : Real.sqrt Ecenter ^ 2 = Ecenter := Real.sq_sqrt hEYC
  have hcrossUpper : oldSignedEnergyPairing Q nu sigma k YM YC ≤
      Real.sqrt Emean * Real.sqrt Ecenter := by
    simpa [Emean, Ecenter, hMeanEq] using
      (le_abs_self (oldSignedEnergyPairing Q nu sigma k YM YC)).trans hcrossAbs
  rw [hExpand, hMeanEq] at ⊢
  change Emean + 2 * oldSignedEnergyPairing Q nu sigma k YM YC + Ecenter ≤
    (Real.sqrt Emean + Real.sqrt Ecenter) ^ 2
  nlinarith [hcrossUpper, hsqrtMeanSq, hsqrtCenterSq]

end

end ASDExplicitGamma.Scalar

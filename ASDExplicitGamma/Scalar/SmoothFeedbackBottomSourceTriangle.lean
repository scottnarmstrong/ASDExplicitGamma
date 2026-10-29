/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackVaryingSource

/-! Actual RESET-bottom source energy split into its affine mean response and
its literal centered bottom-source residual. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native

noncomputable section

/-- The actual bottom-load cell energy is controlled by its constant mean
response and the exact centered RESET-bottom residual energy. -/
theorem smooth_feedback_scalar_bottom_source_cell_energy_triangle
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (f : Vec 2 → Vec 2) (hf : ScalarPositiveHaarAdmissible Q f)
    (hfcenter : ScalarPositiveHaarAdmissible Q
      (fun x => f x - fun i => cubeAverage Q (fun y => f y i))) :
    let mean : Vec 2 := fun i => cubeAverage Q (fun x => f x i)
    let P : BlockVec 2 := (0, mean)
    let Y := scalarResidualField Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField (upper_cell_reset_bottom_load_memL2 Q hf.memLp))
    let YC := scalarResidualField Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField (upper_cell_reset_bottom_load_memL2 Q hfcenter.memLp))
    oldSignedEnergyPairing Q nu sigma k Y Y ≤
      (Real.sqrt (blockVecDot P
        (blockMatVecMul
          (coarseBlockMatrix (openCubeSet Q)
            (responseFramePlanarCoefficientField nu sigma k)) P)) +
        Real.sqrt (oldSignedEnergyPairing Q nu sigma k YC YC)) ^ 2 := by
  classical
  dsimp only
  let mean : Vec 2 := fun i => cubeAverage Q (fun x => f x i)
  let P : BlockVec 2 := (0, mean)
  let Fmean : Vec 2 → BlockVec 2 := fun _ => P
  let Fcenter : Vec 2 → BlockVec 2 := fun x => (0, f x - mean)
  let htotal : HilbertBlockL2 (openCubeSet Q) :=
    toHilbertBlockL2OfBlockField (upper_cell_reset_bottom_load_memL2 Q hf.memLp)
  let hmeanBlock : MemBlockL2 (openCubeSet Q) Fmean := memLp_const P
  let hmean : HilbertBlockL2 (openCubeSet Q) :=
    (scalarFrameRealization Q nu sigma hnu hsigma k).constantField P
  let hcenterBlock : MemBlockL2 (openCubeSet Q) Fcenter :=
    upper_cell_reset_bottom_load_memL2 Q hfcenter.memLp
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
        (upper_cell_reset_bottom_load_memL2 Q hf.memLp),
      coeFn_toHilbertBlockL2OfBlockField hmeanBlock,
      coeFn_toHilbertBlockL2OfBlockField hcenterBlock,
      Lp.coeFn_add hmean hcenter] with x htotalx hmeanBlockx hcenterx hadd
    have hmeanx : hmean x = HilbertBlockVec.ofBlockVec P := by
      rw [← hmeanLoad]
      simpa [hilbertifyBlockField, Fmean] using hmeanBlockx
    have hcenterx' : hcenter x =
        HilbertBlockVec.ofBlockVec (0, f x - mean) := by
      simpa [hilbertifyBlockField, Fcenter] using hcenterx
    calc
      htotal x = HilbertBlockVec.ofBlockVec (0, f x) := by
        simpa [hilbertifyBlockField, upper_cell_reset_bottom_load_memL2] using htotalx
      _ = HilbertBlockVec.ofBlockVec P +
          HilbertBlockVec.ofBlockVec (0, f x - mean) := by
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

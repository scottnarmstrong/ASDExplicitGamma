module

public import ASDExplicitGamma.Native.OldSignedFlatAffine

/-! Affine/oscillatory energy split with the physical-flux norm kept
explicit, so the sharp directional payment can be inserted. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

private theorem old_signed_residual_pairing_hilbert_sharp_aux (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F G : HilbertBlockL2 (openCubeSet Q)) :
    oldSignedEnergyPairing Q nu sigma k
        (scalarResidualField Q nu sigma hnu hsigma k F)
        (scalarResidualField Q nu sigma hnu hsigma k G) =
      (scalarFrameRealization Q nu sigma hnu hsigma k).energyBilin
        (scalarProjectionResidual Q nu sigma hnu hsigma k G)
        (scalarProjectionResidual Q nu sigma hnu hsigma k F) := by
  let ZF := scalarResidualField Q nu sigma hnu hsigma k F
  let ZG := scalarResidualField Q nu sigma hnu hsigma k G
  have hZFrebuild : toHilbertBlockL2OfBlockField (Lp.memLp ZF) =
      scalarProjectionResidual Q nu sigma hnu hsigma k F := hilbert_field_rebuild _
  have hZGrebuild : toHilbertBlockL2OfBlockField (Lp.memLp ZG) =
      scalarProjectionResidual Q nu sigma hnu hsigma k G := hilbert_field_rebuild _
  have hbil := scalar_frame_bilinear_field Q nu sigma hnu hsigma k
    (Lp.memLp ZG) (Lp.memLp ZF)
  rw [hZGrebuild, hZFrebuild] at hbil
  unfold oldSignedEnergyPairing
  simpa [ZF, ZG, scalarCoefficientFlux] using hbil.symm

private theorem old_signed_affine_centered_cross_source_sharp_aux (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    {G : Vec 2 → BlockVec 2} (hG : MemBlockL2 (openCubeSet Q) G) :
    oldSignedEnergyPairing Q nu sigma k
        (scalarResidualField Q nu sigma hnu hsigma k
          ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P))
        (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hG)) =
      volumeAverage (openCubeSet Q) (fun x => blockVecDot (G x)
        (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
          (scalarResidualField Q nu sigma hnu hsigma k
            ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)) x)) := by
  let M := scalarFrameRealization Q nu sigma hnu hsigma k
  let HP := M.constantField P
  let RP := scalarProjectionResidual Q nu sigma hnu hsigma k HP
  let RG := scalarProjectionResidual Q nu sigma hnu hsigma k
    (toHilbertBlockL2OfBlockField hG)
  let ZP : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k HP
  have hPair := old_signed_residual_pairing_hilbert_sharp_aux Q nu sigma hnu hsigma k HP
    (toHilbertBlockL2OfBlockField hG)
  have hRemoved := scalar_projection_removed_mem Q nu sigma hnu hsigma k
    (toHilbertBlockL2OfBlockField hG)
  have hOrth := scalar_projection_residual_orthogonal Q nu sigma hnu hsigma k HP
    (toHilbertBlockL2OfBlockField hG - RG) hRemoved
  rw [map_sub] at hOrth
  have hOrth' : M.energyBilin RP (toHilbertBlockL2OfBlockField hG) =
      M.energyBilin RP RG := by
    have hsub : M.energyBilin RP (toHilbertBlockL2OfBlockField hG) -
        M.energyBilin RP RG = 0 := by
      simpa [M, RP, RG] using hOrth
    linarith
  have hSymm := M.energySymm RG RP
  have hZP : MemBlockL2 (openCubeSet Q) ZP := Lp.memLp _
  have hRebuild : toHilbertBlockL2OfBlockField hZP = RP := hilbert_field_rebuild _
  have hField := scalar_frame_bilinear_field Q nu sigma hnu hsigma k hZP hG
  rw [hRebuild] at hField
  calc
    oldSignedEnergyPairing Q nu sigma k ZP
        (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hG)) = M.energyBilin RG RP := by
      simpa [M, RP, RG, ZP] using hPair
    _ = M.energyBilin RP RG := hSymm
    _ = M.energyBilin RP (toHilbertBlockL2OfBlockField hG) := hOrth'.symm
    _ = volumeAverage (openCubeSet Q) (fun x => blockVecDot (G x)
        (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k) ZP x)) := by
      simpa [M, RP, ZP, scalarCoefficientFlux] using hField

private theorem old_signed_centered_mean_zero_sharp_aux (Q : TriadicCube 2)
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

private theorem old_signed_block_pairing_integrable_sharp_aux (Q : TriadicCube 2)
    {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    IntegrableOn (fun x => blockVecDot (F x) (G x)) (openCubeSet Q) := by
  have h₁ := integrableOn_vecDot_of_memVectorL2
    (memVectorL2_fst_of_memBlockL2 hF) (memVectorL2_fst_of_memBlockL2 hG)
  have h₂ := integrableOn_vecDot_of_memVectorL2
    (memVectorL2_snd_of_memBlockL2 hF) (memVectorL2_snd_of_memBlockL2 hG)
  have hsplit : (fun x => blockVecDot (F x) (G x)) =
      (fun x => vecDot (F x).1 (G x).1) + (fun x => vecDot (F x).2 (G x).2) := by
    funext x
    rfl
  rw [hsplit]
  exact h₁.add h₂

/-- The actual affine/oscillatory split pays its cross by the supplied
physical-flux norm. Sharp directional bounds are inserted by consumers. -/
theorem old_signed_flat_projection_energy_of_centered_energy_and_pairing
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F)
    (R : ℝ)
    (C : ℝ)
    (hCenteredEnergy :
      let HG := toHilbertBlockL2OfBlockField (hF.sub (memLp_const (oldSignedBlockMean Q F)))
      let ZG := scalarResidualField Q nu sigma hnu hsigma k HG
      oldSignedEnergyPairing Q nu sigma k ZG ZG ≤
        C*oldSignedBlockPositiveNorm Q (fun x => F x-oldSignedBlockMean Q F)^2)
    (hPair : |volumeAverage (openCubeSet Q) (fun x =>
      blockVecDot (F x-oldSignedBlockMean Q F)
        (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
          (scalarResidualField Q nu sigma hnu hsigma k
            ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField
              (oldSignedBlockMean Q F))) x-oldSignedBlockMean Q F))| ≤
      oldSignedBlockPositiveNorm Q (fun x => F x-oldSignedBlockMean Q F)*R) :
    oldSignedEnergyPairing Q nu sigma k
        (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hF))
        (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hF)) ≤
      blockVecDot (oldSignedBlockMean Q F)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q)
          (responseFramePlanarCoefficientField nu sigma k)) (oldSignedBlockMean Q F)) +
      2 * R *
        oldSignedBlockPositiveNorm Q
          (fun x => F x - oldSignedBlockMean Q F) +
      C *
        oldSignedBlockPositiveNorm Q
          (fun x => F x - oldSignedBlockMean Q F) ^ 2 := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let M := scalarFrameRealization Q nu sigma hnu hsigma k
  let m := oldSignedBlockMean Q F
  let G : Vec 2 → BlockVec 2 := fun x => F x - m
  let HG := toHilbertBlockL2OfBlockField (hF.sub (memLp_const m))
  let HF := toHilbertBlockL2OfBlockField hF
  let HM := M.constantField m
  let ZM : Vec 2 → BlockVec 2 :=
    scalarResidualField Q nu sigma hnu hsigma k HM
  let ZG : Vec 2 → BlockVec 2 :=
    scalarResidualField Q nu sigma hnu hsigma k HG
  let J : Vec 2 → BlockVec 2 := scalarCoefficientFlux a ZM
  let D : Vec 2 → BlockVec 2 := fun x => J x - m
  let O := oldSignedBlockPositiveNorm Q G
  have hG : MemBlockL2 (openCubeSet Q) G := hF.sub (memLp_const m)
  have hGzero : oldSignedBlockMean Q G = 0 := by
    simpa [G, m] using old_signed_centered_mean_zero_sharp_aux Q hF
  have hConstRaw : toHilbertBlockL2OfBlockField
      (U := openCubeSet Q) (F := fun _ : Vec 2 => m) (memLp_const m) = HM := by
    have hconst : toHilbertBlockL2OfBlockField
        (U := openCubeSet Q) (F := fun _ : Vec 2 => m) (memLp_const m) =
        blockVecToHilbertBlockL2Const m := by
      apply Lp.ext
      filter_upwards [coeFn_toHilbertBlockL2OfBlockField (memLp_const m),
        coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet Q) m] with x hx hy
      exact hx.trans hy.symm
    have hMConst : HM = blockVecToHilbertBlockL2Const m := by rfl
    exact hconst.trans hMConst.symm
  have hSource : HF = HM + HG := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField hF,
      coeFn_toHilbertBlockL2OfBlockField (memLp_const m),
      coeFn_toHilbertBlockL2OfBlockField (hF.sub (memLp_const m)),
      MeasureTheory.Lp.coeFn_add HM HG] with x hF' hrawConst hG' hsum
    have hmConst : HM x = HilbertBlockVec.ofBlockVec m := by
      have hpoint := congrArg (fun H : HilbertBlockL2 (openCubeSet Q) => H x) hConstRaw
      exact hpoint.symm.trans hrawConst
    have hGpoint : HG x = HilbertBlockVec.ofBlockVec (G x) := by
      simpa [HG, hilbertifyBlockField] using hG'
    calc
      HF x = hilbertifyBlockField F x := hF'
      _ = Function.const (Vec 2) (HilbertBlockVec.ofBlockVec m) x +
          hilbertifyBlockField G x := by
        apply (HilbertBlockVec.continuousLinearEquivBlockVec 2).injective
        change F x = m + (F x - m)
        abel
      _ = HM x + HG x := by
        change HilbertBlockVec.ofBlockVec m + HilbertBlockVec.ofBlockVec (G x) =
          HM x + HG x
        rw [← hmConst, ← hGpoint]
      _ = (HM + HG) x := by simpa [Pi.add_apply] using hsum.symm
  have hsplit := old_signed_residual_energy_split Q nu sigma hnu hsigma k HM HG
  rw [← hSource] at hsplit
  have hsplit' : oldSignedEnergyPairing Q nu sigma k
      (scalarResidualField Q nu sigma hnu hsigma k HF)
      (scalarResidualField Q nu sigma hnu hsigma k HF) =
    oldSignedEnergyPairing Q nu sigma k ZM ZM +
      2 * oldSignedEnergyPairing Q nu sigma k ZM ZG +
      oldSignedEnergyPairing Q nu sigma k ZG ZG := by
    simpa [ZM, ZG] using hsplit
  have hAffEnergy := old_signed_affine_energy Q nu sigma hnu hsigma k m
  have hCross := old_signed_affine_centered_cross_source_sharp_aux Q nu sigma hnu hsigma k m
    (hG := hG)
  have hCrossSource : oldSignedEnergyPairing Q nu sigma k ZM ZG =
      volumeAverage (openCubeSet Q) (fun x => blockVecDot (G x) (J x)) := by
    simpa [ZM, ZG, J, HM, HG] using hCross
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hJM : MemBlockL2 (openCubeSet Q) J := by
    apply scalar_coefficient_flux_memL2 Q a hEll
    exact Lp.memLp (scalarResidualField Q nu sigma hnu hsigma k HM)
  have hD : MemBlockL2 (openCubeSet Q) D := hJM.sub (memLp_const m)
  have hIntGM : IntegrableOn (fun x => blockVecDot (G x) m) (openCubeSet Q) := by
    exact old_signed_block_pairing_integrable_sharp_aux Q hG (memLp_const m)
  have hIntGD : IntegrableOn (fun x => blockVecDot (G x) (D x)) (openCubeSet Q) := by
    exact old_signed_block_pairing_integrable_sharp_aux Q hG hD
  have hPairZero : volumeAverage (openCubeSet Q)
      (fun x => blockVecDot (G x) m) = 0 := by
    have h := old_signed_constant_block_pairing_mean Q hG m
    have hsymm : (fun x => blockVecDot (G x) m) =
        fun x => blockVecDot m (G x) := by
      funext x
      exact blockVecDot_comm _ _
    rw [hsymm, h, hGzero]
    simp [blockVecDot, vecDot_zero_right]
  have hCrossShift : oldSignedEnergyPairing Q nu sigma k ZM ZG =
      volumeAverage (openCubeSet Q) (fun x => blockVecDot (G x) (D x)) := by
    have hpoint : (fun x => blockVecDot (G x) (J x)) =
        fun x => blockVecDot (G x) (D x) + blockVecDot (G x) m := by
      funext x
      have hsub := blockVecDot_sub_right (G x) (J x) m
      have hsubD : blockVecDot (G x) (D x) =
          blockVecDot (G x) (J x) - blockVecDot (G x) m := by
        simpa [D] using hsub
      linarith
    calc
      _ = volumeAverage (openCubeSet Q) (fun x => blockVecDot (G x) (J x)) := hCrossSource
      _ = volumeAverage (openCubeSet Q)
          (fun x => blockVecDot (G x) (D x) + blockVecDot (G x) m) := by rw [hpoint]
      _ = volumeAverage (openCubeSet Q) (fun x => blockVecDot (G x) (D x)) := by
        calc
          _ = volumeAverage (openCubeSet Q)
              ((fun x => blockVecDot (G x) (D x)) +
                (fun x => blockVecDot (G x) m)) := by
            congr 1
          _ = volumeAverage (openCubeSet Q) (fun x => blockVecDot (G x) (D x)) +
                volumeAverage (openCubeSet Q) (fun x => blockVecDot (G x) m) :=
            volumeAverage_add hIntGD hIntGM
          _ = _ := by rw [hPairZero, add_zero]
  have hCrossBound : oldSignedEnergyPairing Q nu sigma k ZM ZG ≤ O * R := by
    rw [hCrossShift]
    exact (le_abs_self _).trans hPair
  rw [hAffEnergy] at hsplit'
  have hOEq : O = oldSignedBlockPositiveNorm Q G := rfl
  have hCentered : oldSignedEnergyPairing Q nu sigma k ZG ZG ≤
      C * O ^ 2 := by
    simpa [O, G, a] using hCenteredEnergy
  nlinarith [hsplit', hCentered, hCrossBound]

/-- The general source energy estimate specializes the affine split to
its full-response coefficient, preserving the original API. -/
theorem old_signed_flat_projection_energy_of_flux_pairing
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F)
    (R : ℝ)
    (hPfst : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).1 i - (oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).2 i - (oldSignedBlockMean Q F).2 i))))
    (hPair : |volumeAverage (openCubeSet Q) (fun x =>
      blockVecDot (F x-oldSignedBlockMean Q F)
        (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
          (scalarResidualField Q nu sigma hnu hsigma k
            ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField
              (oldSignedBlockMean Q F))) x-oldSignedBlockMean Q F))| ≤
      oldSignedBlockPositiveNorm Q (fun x => F x-oldSignedBlockMean Q F)*R) :
    oldSignedEnergyPairing Q nu sigma k
        (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hF))
        (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hF)) ≤
      blockVecDot (oldSignedBlockMean Q F)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q)
          (responseFramePlanarCoefficientField nu sigma k)) (oldSignedBlockMean Q F)) +
      2 * R *
        oldSignedBlockPositiveNorm Q
          (fun x => F x - oldSignedBlockMean Q F) +
      oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k) *
        oldSignedBlockPositiveNorm Q
          (fun x => F x - oldSignedBlockMean Q F) ^ 2 := by
  apply old_signed_flat_projection_energy_of_centered_energy_and_pairing
    Q nu sigma hnu hsigma k F hF R
    (oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k)) _ hPair
  exact old_signed_flat_source_energy Q nu sigma hnu hsigma k
    (fun x => F x-oldSignedBlockMean Q F) (hF.sub (memLp_const (oldSignedBlockMean Q F))) hPfst hPsnd

/-- The full physical-flux weak norm supplies the affine cross estimate. -/
theorem old_signed_flat_projection_energy_of_flux_norm
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F)
    (R : ℝ)
    (hPfst : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).1 i - (oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).2 i - (oldSignedBlockMean Q F).2 i))))
    (hAffine : oldSignedBlockWeakNorm Q (fun x =>
      scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
        (scalarResidualField Q nu sigma hnu hsigma k
          ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField
            (oldSignedBlockMean Q F))) x - oldSignedBlockMean Q F) ≤
      R) :
    oldSignedEnergyPairing Q nu sigma k
        (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hF))
        (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hF)) ≤
      blockVecDot (oldSignedBlockMean Q F)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q)
          (responseFramePlanarCoefficientField nu sigma k)) (oldSignedBlockMean Q F)) +
      2 * R *
        oldSignedBlockPositiveNorm Q
          (fun x => F x - oldSignedBlockMean Q F) +
      oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k) *
        oldSignedBlockPositiveNorm Q
          (fun x => F x - oldSignedBlockMean Q F) ^ 2 := by
  apply old_signed_flat_projection_energy_of_flux_pairing Q nu sigma hnu hsigma k F hF R hPfst hPsnd
  let m := oldSignedBlockMean Q F
  let G := fun x => F x-m
  let J := scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
    (scalarResidualField Q nu sigma hnu hsigma k
      ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField m))
  have hG : MemBlockL2 (openCubeSet Q) G := hF.sub (memLp_const m)
  have hJ : MemBlockL2 (openCubeSet Q) J := scalar_coefficient_flux_memL2 Q _
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) (Lp.memLp _)
  have hD : MemBlockL2 (openCubeSet Q) (fun x => J x-m) := hJ.sub (memLp_const m)
  exact (old_signed_block_pairing_bound Q hG hD hPfst hPsnd).trans
    (mul_le_mul_of_nonneg_left hAffine (Real.sqrt_nonneg _))

end
end ASDExplicitGamma.Native

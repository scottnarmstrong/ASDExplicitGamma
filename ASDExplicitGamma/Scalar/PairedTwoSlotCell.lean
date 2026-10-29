module

public import ASDExplicitGamma.Scalar.PairedTwoSlotCellData

/-! Cellwise two-slot joint weak estimate of a function-level two-slot solution. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational

noncomputable section

/-- On a tiling cell `U` of `Q`, the two-slot solution `(φ, η)` obeys the joint forced
weak estimate with the cell's own inverse history. -/
theorem two_slot_cell_bound {Q : TriadicCube 2} (n : ℕ) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q))
    (φ : H10Function (openCubeSet Q)) (η : H1Function (openCubeSet Q))
    {F G : Vec 2 → Vec 2}
    (hGQ : MemVectorL2 (openCubeSet Q) G)
    (hc : IsSolenoidalOn (openCubeSet Q) (fun z =>
      (ν / σ) • η.grad z + shear' σ k z (φ.toH1Function.grad z) - F z))
    (hd : IsSolenoidalOn (openCubeSet Q) (fun z =>
      (ν / σ) • φ.toH1Function.grad z + shear' σ k z (η.grad z) - G z))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q n)
    (hFU : MemLp F 2 (normalizedCubeMeasure U))
    (hFposU : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy U (cubeIncrement U (j + 1) (fun x => F x i))))
    (hGU : MemLp G 2 (normalizedCubeMeasure U))
    (hGposU : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy U (cubeIncrement U (j + 1) (fun x => G x i)))) :
    let a := responseFramePlanarCoefficientField ν σ k
    let B := lemmaVInverseHistory U a ((3 : ℝ) ^ (1 / 4 : ℝ))
    let E := volumeAverage (openCubeSet U) (fun z => (ν / σ) *
      (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z)))
    ∃ X Y : ℝ, 0 ≤ X ∧ 0 ≤ Y ∧ X + Y ≤ B * E ∧
      Real.sqrt (vectorWeakHaarEnergy U φ.toH1Function.grad) ≤ Real.sqrt X +
        (3 : ℝ) ^ (-(1 / 4 : ℝ)) * B * Real.sqrt (forcedSourceCircleEnergy U F) ∧
      Real.sqrt (vectorWeakHaarEnergy U η.grad) ≤ Real.sqrt Y +
        (3 : ℝ) ^ (-(1 / 4 : ℝ)) * B * Real.sqrt (forcedSourceCircleEnergy U G) := by
  intro a B E
  letI instQ : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  letI instU : IsFiniteMeasure (volumeMeasureOn (openCubeSet U)) :=
    (isOpenBoundedConvexDomain_openCubeSet U).isFiniteMeasure_restrict_volume
  have hUQ : openCubeSet U ⊆ openCubeSet Q := openCubeSet_subset_of_mem_descendantsAtDepth hU
  have hEllQ := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    ν σ hν hσ k
  have hEllU : IsEllipticFieldOn (ν / σ) _ (openCubeSet U) a :=
    hEllQ.mono (measurableSet_openCubeSet U) hUQ
  let W : BlockState 2 := twoSlotState ν σ k φ.toH1Function.grad η.grad
  have hx : MemVectorL2 (openCubeSet Q) φ.toH1Function.grad := φ.toH1Function.grad_memVectorL2
  have hy : MemVectorL2 (openCubeSet Q) η.grad := η.grad_memVectorL2
  have hsub : Measure.restrict volume (openCubeSet U) ≤ Measure.restrict volume (openCubeSet Q) :=
    Measure.restrict_mono_set volume hUQ
  have hxU : MemVectorL2 (openCubeSet U) φ.toH1Function.grad := hx.mono_measure hsub
  have hyU : MemVectorL2 (openCubeSet U) η.grad := hy.mono_measure hsub
  have hflux : MemVectorL2 (openCubeSet Q) W.flux :=
    (hy.const_smul (ν / σ)).add (shear_memL2 hν hσ k hx)
  have hfluxU : MemVectorL2 (openCubeSet U) W.flux := hflux.mono_measure hsub
  have hFvecU : MemVectorL2 (openCubeSet U) F :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure U hFU
  have hWpot : IsBlockPotentialOn (openCubeSet U) W := by
    change IsPotentialOn (openCubeSet U) φ.toH1Function.grad
    exact (φ.toH1Function.isPotentialOn).restrict_of_isOpen_of_memVectorL2
      (isOpen_openCubeSet Q) (isOpen_openCubeSet U) hUQ hxU
  have hWsol : IsSolenoidalOn (openCubeSet U) (fun z => W.flux z - F z) :=
    hc.restrict_of_isOpen_of_memVectorL2 (isOpen_openCubeSet Q)
      (isOpen_openCubeSet U) hUQ (hfluxU.sub hFvecU)
  have hWmem : MemBlockL2 (openCubeSet U) W.eval := by
    change MemBlockL2 (openCubeSet U) (fun z => (W.potential z, W.flux z))
    exact memBlockL2_blockField hxU hfluxU
  have hWlower : MemVectorL2 (openCubeSet U)
      (fun z => (blockMatVecMul (blockCoeffField a z) (W.eval z)).2) := by
    have hfun : (fun z => (blockMatVecMul (blockCoeffField a z) (W.eval z)).2) = η.grad := by
      funext z; exact twoSlot_lower hν hσ k _ _ z
    rw [hfun]; exact hyU
  have hforcedQ := two_slot_hforced hν hσ k φ η hGQ hd
  have hforcedU := fun T hT => forcedSource_weakEquation_onDescendant Q n U hU
    (a := a) W G hforcedQ T hT
  obtain ⟨u, hu⟩ := (η.isPotentialOn).restrict_of_isOpen_of_memVectorL2
    (isOpen_openCubeSet Q) (isOpen_openCubeSet U) hUQ hyU
  have hu' : (fun z => (blockMatVecMul (blockCoeffField a z) (W.eval z)).2) =ᵐ[
      volumeMeasureOn (openCubeSet U)] u.grad :=
    Filter.Eventually.of_forall fun z => by
      exact (twoSlot_lower hν hσ k φ.toH1Function.grad η.grad z).trans (congrFun hu z).symm
  obtain ⟨X, Y, hX, hY, hXY, h1, h2⟩ := forced_two_slot_joint_bound U hEllU W hWpot hFU hFposU
    hWsol hWmem hWlower hGU hGposU hforcedU u hu'
  have hE : blockPairingAverage (openCubeSet U) a W W = E := by
    unfold blockPairingAverage
    congr 1
    funext z
    exact twoSlot_pairing hν hσ k _ _ z
  rw [hE] at hXY
  rw [hu] at h2
  exact ⟨X, Y, hX, hY, hXY, h1, h2⟩

end

end ASDExplicitGamma.Scalar

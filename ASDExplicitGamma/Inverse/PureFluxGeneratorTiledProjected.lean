module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorTiledFeedback

/-! Broken source estimates for the actual global pure-flux projection. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators
noncomputable section

theorem pureFlux_projectedSource_tiled_bound (Q : TriadicCube 2) (m : ℕ)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hFpos : ∀ R ∈ descendantsAtDepth Q m, ∀ i : Fin 2,
      Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy R (cubeIncrement R (j + 1) (fun x => F x i))))
    (v : H10Function (openCubeSet Q))
    (hv : (fun x => (projectedSourceField Q ν σ hν hσ k hF x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)] v.toH1Function.grad)
    (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ R ∈ descendantsAtDepth Q m,
      lemmaVInverseHistory R (responseFramePlanarCoefficientField ν σ k)
        ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    (scalarFrameRealization Q ν σ hν hσ k).energyBilin
      (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
      (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) ≤
        B * lemmaVTiledPositiveEnergy Q m F ∧
    Real.sqrt (lemmaVTiledWeakEnergy Q m v.toH1Function.grad) ≤
      (1/2+(3:ℝ)^(-(1/4:ℝ)))*B*Real.sqrt (lemmaVTiledPositiveEnergy Q m F) := by
  let U := openCubeSet Q
  letI pureFluxTiledProjectionFiniteMeasure : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let a := responseFramePlanarCoefficientField ν σ k
  let Y := projectedSourceCompatibleState Q ν σ hν hσ k hF
  let Z := projectedSourceField Q ν σ hν hσ k hF
  let W : BlockState 2 := ⟨fun x => (Z x).1, fun x => (Z x).2⟩
  let D := scalarFrameRealization Q ν σ hν hσ k
  let E0 := D.energyBilin
    (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
    (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
  let E := blockPairingAverage U a Y Y
  let G := Y.potential
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hCompat := projectedSourceCompatibleState_compatible Q ν σ hν hσ k hF
  have hYmem : MemBlockL2 U Y.eval := by
    simpa [Y] using hCompat.1
  have hYpot : IsPotentialOn U Y.potential := by
    change IsPotentialOn U (fun x => (Y.eval x).1)
    simpa [Y, projectedSourceCompatibleState, projectedSourceField, Z, W, a, U,
      BlockState.eval] using hCompat.2.1
  have hYsol : IsSolenoidalOn U Y.flux := by
    change IsSolenoidalOn U (fun x => (Y.eval x).2)
    simpa [Y, projectedSourceCompatibleState, projectedSourceField, Z, W, a, U,
      BlockState.eval] using hCompat.2.2
  obtain ⟨g, hg⟩ := hYpot
  have hGcoord (i : Fin 2) :
      MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q) := by
    simpa [G, hg] using g.grad_memL2_normalizedCubeMeasure i
  have hZmem : MemBlockL2 U (fun x => Z x) := Lp.memLp Z
  have hZeq : toHilbertBlockL2OfBlockField hZmem =
      scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF) := by
    change toHilbertBlockL2OfBlockField
      (Lp.memLp (hilbertBlockL2ToBlockL2
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)))) = _
    exact hilbert_field_rebuild _
  have hWeval : W.eval = fun x => Z x := by
    funext x
    exact Prod.eta _
  have hbil := scalar_frame_bilinear_field Q ν σ hν hσ k hZmem hZmem
  rw [hZeq] at hbil
  have hblockE : blockPairingAverage U a W W = E0 := by
    change volumeAverage U (fun x => blockVecDot (W.eval x)
      (blockMatVecMul (blockCoeffField a x) (W.eval x))) = _
    rw [hWeval]
    exact hbil.symm
  have hreflectE : E = blockPairingAverage U a W W := by
    dsimp [E]
    change blockPairingAverage U a (pairedReflectState a W)
      (pairedReflectState a W) = blockPairingAverage U a W W
    exact pairedReflect_pairingAverage_isometry hEll W W
  have hsourcePair := projectedSource_energy_eq_pairing Q ν σ hν hσ k hF
  have hsourcePair' : E0 = vectorPairing Q F G := by
    simpa [E0, D, G, Y] using hsourcePair
  have hEpair : E = vectorPairing Q F G := hreflectE.trans (hblockE.trans hsourcePair')

  have hImageAE : (fun x => (blockMatVecMul (blockCoeffField a x) (Y.eval x)).2) =ᵐ[
      volumeMeasureOn U] fun x => (Z x).1 := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    have ha := pairedReflectState_action hEll W hx
    exact congrArg Prod.snd ha
  have hImageMem : MemVectorL2 U
      (fun x => (blockMatVecMul (blockCoeffField a x) (Y.eval x)).2) :=
    (memLp_congr_ae hImageAE).2 (memVectorL2_fst_of_memBlockL2 hZmem)
  have hImageGrad : (fun x => (blockMatVecMul (blockCoeffField a x) (Y.eval x)).2) =ᵐ[
      volumeMeasureOn U] v.toH1Function.grad := hImageAE.trans hv
  have hforced (T : BlockState 2) (hT : ScalarVariation U T.eval) :
      volumeAverage U (blockPairingIntegrand a T Y) =
        volumeAverage U (fun x => vecDot (T.potential x) (F x)) := by
    have hi := projectedSource_forcedResponse_onDescendant Q 0 ν σ hν hσ k hF
      Q (by simp) T hT
    unfold volumeAverage
    exact congrArg (fun z : ℝ => (volume U).toReal⁻¹*z) hi
  have htest : E = cubeAverage Q (fun x => vecDot (Y.potential x) (F x)) := by
    rw [hEpair, ← lemmaV_cubeAverage_vecDot_eq_vectorPairing Q]
    · congr 1
      funext x
      exact vecDot_comm _ _
    · intro i
      exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2
        (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF) i)
    · exact hGcoord
  have hh := pureFlux_forced_pair_tiled_bound Q m hEll Y ⟨g, hg⟩ hYsol hYmem
    hImageMem hF hFpos hforced v.toH1Function hImageGrad htest B hB hhist
  have hEE0 : E = E0 := hreflectE.trans hblockE
  change E ≤ B * lemmaVTiledPositiveEnergy Q m F ∧
    Real.sqrt (lemmaVTiledWeakEnergy Q m v.toH1Function.grad) ≤
      (1/2+(3:ℝ)^(-(1/4:ℝ)))*B*Real.sqrt (lemmaVTiledPositiveEnergy Q m F) at hh
  rw [hEE0] at hh
  exact hh

end
end ASDExplicitGamma.Inverse

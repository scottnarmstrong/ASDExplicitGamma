module

public import ASDExplicitGamma.Main.InverseLowerRowPairing
public import ASDExplicitGamma.Variational.LemmaVMinimizer

/-! Recover H10 first-potential representatives for response variations. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

namespace ASDExplicitGamma.Main

theorem main_response_variation_first_potential
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n)))
    (Y : (responseFrameEnergyVariationSpace
      (measurableSet_openCubeSet (originCube 2 n))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k).toSubmodule) :
    ∃ z : H10Function (openCubeSet (originCube 2 n)),
      (fun x => (hilbertBlockL2ToBlockL2 (Y : EnergyCarrier
        (responseFrameEnergyData (measurableSet_openCubeSet (originCube 2 n))
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k)).down x).1) =ᵐ[
        volumeMeasureOn (openCubeSet (originCube 2 n))] z.toH1Function.grad := by
  let Q := originCube 2 n
  let U := openCubeSet Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let D := responseFrameEnergyData (measurableSet_openCubeSet Q) hv ν σ hν hσ k
  let M := responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
    hv ν σ hν hσ k
  let R := (lemmaVRecoveryData hU).toMuCorrectionSpaceRecoveryData
  have hmem : (Y : EnergyCarrier D).down ∈
      M.toMuHilbertRealization.correctionSpace.correctionSpace := by
    change (Y : EnergyCarrier D) ∈ responseEnergyCorrectionSpace
      M.toMuHilbertRealization D
    exact Y.property
  let F := R.repr ⟨(Y : EnergyCarrier D).down, hmem⟩
  obtain ⟨z, hz⟩ := F.isPotentialZeroTrace
  have hrepr := R.repr_eq (⟨(Y : EnergyCarrier D).down, hmem⟩)
  have hblock : hilbertBlockL2ToBlockL2 (U := U) F.toHilbertBlockL2 =
      hilbertBlockL2ToBlockL2 (Y : EnergyCarrier D).down := by
    exact congrArg (hilbertBlockL2ToBlockL2 (U := U)) hrepr
  have hblock' : toBlockL2OfComponents F.potential_memL2 F.flux_memL2 =
      hilbertBlockL2ToBlockL2 (Y : EnergyCarrier D).down := by
    calc
      toBlockL2OfComponents F.potential_memL2 F.flux_memL2 =
          hilbertBlockL2ToBlockL2 F.toHilbertBlockL2 := by
        symm
        exact Homogenization.PotentialSolenoidalL2Data.hilbertBlockL2ToBlockL2_toHilbertBlockL2OfComponents
          F.potential_memL2 F.flux_memL2
      _ = hilbertBlockL2ToBlockL2 (Y : EnergyCarrier D).down := hblock
  have hblockAE := (Lp.ext_iff.mp hblock')
  have hfieldAE := coeFn_toBlockL2OfComponents F.potential_memL2 F.flux_memL2
  refine ⟨z, ?_⟩
  filter_upwards [hblockAE, hfieldAE] with x hblockFn hfieldFn
  have hfirst : (hilbertBlockL2ToBlockL2 (Y : EnergyCarrier D).down x).1 =
      F.potential x := by
    rw [← hblockFn, hfieldFn]
    rfl
  rw [hfirst, hz]

end ASDExplicitGamma.Main

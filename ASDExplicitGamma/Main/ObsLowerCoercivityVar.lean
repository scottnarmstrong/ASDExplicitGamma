module

public import ASDExplicitGamma.Main.ObsLowerCoercivityCell
public import ASDExplicitGamma.Main.InverseLowerRowBound

/-! Observer-level coercivity for response variations through the cell history `B` (source (1.2)),
replacing the ellipticity-based first-potential bound: the tiled weak energy of the zero-trace
first potential of a variation is at most `B` times its response energy. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Native ASDExplicitGamma.Scalar

namespace ASDExplicitGamma.Main

theorem obs_variation_first_potential_weak_energy_bound
    (n : ℤ) (m : ℕ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n)))
    (Y : (responseFrameEnergyVariationSpace
      (measurableSet_openCubeSet (originCube 2 n))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k).toSubmodule)
    (B : ℝ)
    (hhist : ∀ U ∈ descendantsAtDepth (originCube 2 n) m,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ B) :
    ∃ z : H10Function (openCubeSet (originCube 2 n)),
      (fun x => (hilbertBlockL2ToBlockL2 (Y : EnergyCarrier
        (responseFrameEnergyData (measurableSet_openCubeSet (originCube 2 n))
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k)).down x).1) =ᵐ[
        volumeMeasureOn (openCubeSet (originCube 2 n))] z.toH1Function.grad ∧
      lemmaVTiledWeakEnergy (originCube 2 n) m z.toH1Function.grad ≤
        B * ‖(Y : EnergyCarrier (responseFrameEnergyData
          (measurableSet_openCubeSet (originCube 2 n))
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k))‖ ^ 2 := by
  classical
  let Q := originCube 2 n
  let U := openCubeSet Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let a := responseFramePlanarCoefficientField ν σ k
  letI : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
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
  have hY : ∀ᵐ x ∂volumeMeasureOn U,
      hilbertBlockL2ToBlockL2 (Y : EnergyCarrier D).down x = (F.potential x, F.flux x) := by
    filter_upwards [hblockAE, hfieldAE] with x hblockFn hfieldFn
    rw [← hblockFn, hfieldFn]
    rfl
  refine ⟨z, ?_, ?_⟩
  · filter_upwards [hY] with x hx
    rw [hx]
    exact (congrFun hz x).symm
  · let Dc : Unit → Vec 2 → BlockVec 2 := fun _ x => (F.potential x, F.flux x)
    have hcomp : ∀ c, ScalarCompatible (openCubeSet Q) (Dc c) := by
      intro c
      refine ⟨?_, ?_, ?_⟩
      · exact memBlockL2_blockField F.potential_memL2 F.flux_memL2
      · exact F.isPotentialZeroTrace.isPotentialOn
      · exact fun φ => F.isSolenoidalZeroNormalTrace φ.toH1Function
    have hEll := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) ν σ hν hσ k
    have hK := obs_compat_family_weak_tiled Q m hEll Dc hcomp B hhist
    simp only [Finset.univ_unique, Finset.sum_singleton] at hK
    have hnorm : D.energy (Y : EnergyCarrier D).down (Y : EnergyCarrier D).down =
        ‖(Y : EnergyCarrier D)‖ ^ 2 := by
      change D.energy _ _ = ‖responseEnergyUp D (Y : EnergyCarrier D).down‖ ^ 2
      rw [energyCarrier_norm_sq, responseEnergyUp_down]
    have hE : obsCellEnergy Q a (Dc ()) = ‖(Y : EnergyCarrier D)‖ ^ 2 := by
      rw [← hnorm]
      change _ = M.toMuHilbertRealization.energyBilin _ _
      rw [lemmaV_muSystem_bilinear_eq_volumeAverage]
      unfold obsCellEnergy
      rw [cubeAverage_eq_integralAverage_openCubeSet Q]
      change volumeAverage U _ = _
      unfold volumeAverage
      congr 1
      apply integral_congr_ae
      filter_upwards [hY] with x hx
      rw [hx]
      rfl
    have : (fun x => (Dc () x).1) = z.toH1Function.grad := by
      funext x; exact (congrFun hz x).symm
    rw [this] at hK
    rw [hE] at hK
    exact hK

end ASDExplicitGamma.Main

module

public import ASDExplicitGamma.Native.HeatVHEATDriftBankIdentity
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransportGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBankGen

/-! The `ns`-shell generalization of `HeatVHEATDriftBankIdentity`. -/

@[expose] public section


namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Triadic Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

variable (ns : ℕ)

theorem heatVHEATDrift_bank_eq_root_max_Gen
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (g : ℝ) (d : Fin ns) :
    (heatVHEATDriftBankGen ns) M n height t ω g d=
      Book.Ch02.finsetSupReal (descendantsAtDepth (originCube 2 (n-1)) (pureFluxBankSourceDepth (d.val+2)))
        (fun U => (bankRootInverseHistory U M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω).toReal) := by
  let Q := originCube 2 (n-1)
  let j := pureFluxBankSourceDepth (d.val+2)
  let k := pureFluxOpenResponseRestriction (n-1) (heatRefinedObserverShear (n-1) n height t ω g)
  have hq : Q∈descendantsAtDepth (originCube 2 n) 1 := by
    simpa only [Nat.cast_one] using originCube_mem_descendantsAtDepth' 2 n 1
  have hm := tile_history_le_source_history Q j M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 k
  change max _ _=_
  rw [max_eq_right hm]
  apply Book.Ch02.finsetSupReal_congr
  intro U hU
  change lemmaVInverseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
    (pureFluxOpenResponseRestriction (n-1)
      (parentBoundaryObserverBandScalar (n-1) n height t ω+ContinuousMap.const _ g))) _=_
  rw [parent_boundary_inverse_history_gauge (n-1) M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 _ g U j hU,
    heat_refined_observer_history_eq_parent M (n-1) n 1 hq height t ω U j hU]
  exact heatVHEATDrift_inverse_history_eq_bank M n height t ω (1+j) U (mem_descendantsAtDepth_add hq hU)

/-- Every auxiliary shear gives the same bank, on EVERY sample. -/
theorem heatVHEATDrift_bank_gauge_Gen
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (g : ℝ) (d : Fin ns) :
    (heatVHEATDriftBankGen ns) M n height t ω g d=(heatVHEATDriftBankGen ns) M n height t ω 0 d := by
  rw [heatVHEATDrift_bank_eq_root_max_Gen,heatVHEATDrift_bank_eq_root_max_Gen]

end
end ASDExplicitGamma.Native

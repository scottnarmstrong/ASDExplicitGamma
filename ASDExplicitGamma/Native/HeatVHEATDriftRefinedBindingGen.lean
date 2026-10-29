module

public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedBinding
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransportGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBankGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankMeasurableGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceIntegrandGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNormsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedProfileGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedPhysicalGen

/-! The `ns`-shell generalization of `HeatVHEATDriftRefinedBinding`. -/

@[expose] public section


namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Algsuperdiff.Section3
noncomputable section

variable (ns : ℕ)

/-- The physical trace is the canonical translated trace after the exact
observer identity. Only that geometric identity is an input here. -/
theorem heatVHEATDrift_refined_physical_trace_eq_of_observer_Gen
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) (i : nativeHeatQ3RefinedCarrierIndex)
    (hf : nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i)
      ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i)=
      heatRefinedObserverShear (nativeHeatQ3RefinedCarrierChild m i).scale (m+1) ns t
        (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2)) :
    (heatVHEATDriftRefinedPhysicalTraceGen ns) M m t g z i=
      heatRefinedTranslatedTrace M (m+1) ns t (heatVHEATDriftRefinedShift m i) (g i) z := by
  have hq : m+1-1=(nativeHeatQ3RefinedCarrierChild m i).scale := by
    rw [nativeHeatQ3RefinedCarrierChild_scale]
    ring
  have ht (q n : ℤ) (hq : n-1=q) (ω : Cutoff.CutoffSample 2) (a : ℝ) :
      modelTraceObservable q M.nu (Annealed.sigmaBar M n)
        (heatRefinedObserverShear q n ns t ω a)=(heatVHEATDriftObserverTraceGen ns) M n t ω a := by
    subst q
    rfl
  unfold heatVHEATDriftRefinedPhysicalTraceGen
  rw [nativeHeatQ3RefinedCarrierChildTraceObservable_toOrigin,hf,ht _ _ hq]
  rfl

/-- The complete physical centered signed row is exactly the source bank
row once the owner's observer identity is supplied. -/
theorem heatVHEATDrift_refined_physical_profile_eq_of_observer_Gen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin ns)
    (hf : nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i)
      ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i)=
      heatRefinedObserverShear (nativeHeatQ3RefinedCarrierChild m i).scale (m+1) ns t
        (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2)) :
    (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d (Annealed.sigmaBar M (m+1))
      ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i)=
      (2*(heatVHEATDriftVarianceGen ns) M h (m+1) d*(heatVHEATDriftKappaGen ns) (m+1) d*
        (heatVHEATDriftBankGen ns) M (m+1) ns t
          (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2) d+
       (heatVHEATDriftVarianceGen ns) M h (m+1) d*(heatVHEATDriftMuGen ns) d*
        ((heatVHEATDriftBankGen ns) M (m+1) ns t
          (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2) d)^2)*
      (heatRefinedTranslatedTrace M (m+1) ns t (heatVHEATDriftRefinedShift m i) (g i) z+4) := by
  have hn : (nativeHeatQ3RefinedCarrierChild m i).scale+1=m+1 := by
    rw [nativeHeatQ3RefinedCarrierChild_scale]
  have hf' : nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i)
      ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i)=
      heatRefinedObserverShear (nativeHeatQ3RefinedCarrierChild m i).scale
        ((nativeHeatQ3RefinedCarrierChild m i).scale+1) ns t
        (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2) := by
    rw [hn]
    exact hf
  have hp := (heatVHEATDrift_refined_profile_eq_of_observer_Gen ns) M h m i d t
    (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2)
    ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i) hf'
  dsimp only at hp
  rw [hn] at hp
  exact hp

/-- All physical children and shells are aggregated before integration.
The input is the exact transport identity, never a drift estimate. -/
theorem heatVHEATDrift_refined_physical_family_eq_of_observer_Gen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ))
    (hf : ∀ i,nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i)
      ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i)=
      heatRefinedObserverShear (nativeHeatQ3RefinedCarrierChild m i).scale (m+1) ns t
        (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2)) :
    (heatVHEATDriftRefinedPhysicalAverageGen ns) M m t g z=(heatVHEATDriftRefinedAverageGen ns) M m t g z ∧
    (heatVHEATDriftRefinedPhysicalDriftGen ns) M h m t k g z=(heatVHEATDriftRefinedSourceGen ns) M h m t k g z := by
  have hA : (heatVHEATDriftRefinedPhysicalAverageGen ns) M m t g z=
      (heatVHEATDriftRefinedAverageGen ns) M m t g z := by
    dsimp only [heatVHEATDriftRefinedPhysicalAverageGen,heatVHEATDriftRefinedAverageGen,heatRefinedTraceAverage]
    apply Finset.sum_congr rfl
    intro i _
    rw [(heatVHEATDrift_refined_physical_trace_eq_of_observer_Gen ns) M m t g z i (hf i)]
  refine ⟨hA,?_⟩
  unfold heatVHEATDriftRefinedPhysicalDriftGen heatVHEATDriftRefinedSourceGen heatVHEATDriftSourceGen
  rw [hA]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [(heatVHEATDrift_refined_physical_profile_eq_of_observer_Gen ns) M h m t g z i _ (hf i)]
  rw [←Finset.sum_mul]
  dsimp only [heatVHEATDriftRefinedAverageGen]
  ring

end
end ASDExplicitGamma.Native

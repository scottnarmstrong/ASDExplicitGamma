module

public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedPhysical

/-! Consumption of the exact source-observer transport identity, keeping
all physical signed rows and the actual polynomial average. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Algsuperdiff.Section3
noncomputable section

/-- The physical trace is the canonical translated trace after the exact
observer identity. Only that geometric identity is an input here. -/
theorem heatVHEATDrift_refined_physical_trace_eq_of_observer
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) (i : nativeHeatQ3RefinedCarrierIndex)
    (hf : nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i)
      (heatVHEATDriftRefinedChildField m t g z i)=
      heatRefinedObserverShear (nativeHeatQ3RefinedCarrierChild m i).scale (m+1) 9 t
        (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2)) :
    heatVHEATDriftRefinedPhysicalTrace M m t g z i=
      heatRefinedTranslatedTrace M (m+1) 9 t (heatVHEATDriftRefinedShift m i) (g i) z := by
  have hq : m+1-1=(nativeHeatQ3RefinedCarrierChild m i).scale := by
    rw [nativeHeatQ3RefinedCarrierChild_scale]
    ring
  have ht (q n : ℤ) (hq : n-1=q) (ω : Cutoff.CutoffSample 2) (a : ℝ) :
      modelTraceObservable q M.nu (Annealed.sigmaBar M n)
        (heatRefinedObserverShear q n 9 t ω a)=heatVHEATDriftObserverTrace M n t ω a := by
    subst q
    rfl
  unfold heatVHEATDriftRefinedPhysicalTrace
  rw [nativeHeatQ3RefinedCarrierChildTraceObservable_toOrigin,hf,ht _ _ hq]
  rfl

/-- The complete physical centered signed row is exactly the source bank
row once the owner's observer identity is supplied. -/
theorem heatVHEATDrift_refined_physical_profile_eq_of_observer
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin 9)
    (hf : nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i)
      (heatVHEATDriftRefinedChildField m t g z i)=
      heatRefinedObserverShear (nativeHeatQ3RefinedCarrierChild m i).scale (m+1) 9 t
        (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2)) :
    nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile M h m i d (Annealed.sigmaBar M (m+1))
      (heatVHEATDriftRefinedChildField m t g z i)=
      (2*heatVHEATDriftVariance M h (m+1) d*heatVHEATDriftKappa (m+1) d*
        heatVHEATDriftBank M (m+1) 9 t
          (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2) d+
       heatVHEATDriftVariance M h (m+1) d*heatVHEATDriftMu d*
        (heatVHEATDriftBank M (m+1) 9 t
          (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2) d)^2)*
      (heatRefinedTranslatedTrace M (m+1) 9 t (heatVHEATDriftRefinedShift m i) (g i) z+4) := by
  have hn : (nativeHeatQ3RefinedCarrierChild m i).scale+1=m+1 := by
    rw [nativeHeatQ3RefinedCarrierChild_scale]
  have hf' : nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i)
      (heatVHEATDriftRefinedChildField m t g z i)=
      heatRefinedObserverShear (nativeHeatQ3RefinedCarrierChild m i).scale
        ((nativeHeatQ3RefinedCarrierChild m i).scale+1) 9 t
        (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2) := by
    rw [hn]
    exact hf
  have hp := heatVHEATDrift_refined_profile_eq_of_observer M h m i d t
    (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2)
    (heatVHEATDriftRefinedChildField m t g z i) hf'
  dsimp only at hp
  rw [hn] at hp
  exact hp

/-- All physical children and shells are aggregated before integration.
The input is the exact transport identity, never a drift estimate. -/
theorem heatVHEATDrift_refined_physical_family_eq_of_observer
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ))
    (hf : ∀ i,nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i)
      (heatVHEATDriftRefinedChildField m t g z i)=
      heatRefinedObserverShear (nativeHeatQ3RefinedCarrierChild m i).scale (m+1) 9 t
        (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2)) :
    heatVHEATDriftRefinedPhysicalAverage M m t g z=heatVHEATDriftRefinedAverage M m t g z ∧
    heatVHEATDriftRefinedPhysicalDrift M h m t k g z=heatVHEATDriftRefinedSource M h m t k g z := by
  have hA : heatVHEATDriftRefinedPhysicalAverage M m t g z=
      heatVHEATDriftRefinedAverage M m t g z := by
    dsimp only [heatVHEATDriftRefinedPhysicalAverage,heatVHEATDriftRefinedAverage,heatRefinedTraceAverage]
    apply Finset.sum_congr rfl
    intro i _
    rw [heatVHEATDrift_refined_physical_trace_eq_of_observer M m t g z i (hf i)]
  refine ⟨hA,?_⟩
  unfold heatVHEATDriftRefinedPhysicalDrift heatVHEATDriftRefinedSource heatVHEATDriftSource
  rw [hA]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [heatVHEATDrift_refined_physical_profile_eq_of_observer M h m t g z i _ (hf i)]
  rw [←Finset.sum_mul]
  dsimp only [heatVHEATDriftRefinedAverage]
  ring

end
end ASDExplicitGamma.Native

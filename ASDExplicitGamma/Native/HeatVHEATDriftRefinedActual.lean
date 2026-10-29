module

public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedBinding
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceObserver

/-! The actual refined physical drift expectation, with all owner transport
and Gaussian-law inputs supplied by their proved declarations. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Algsuperdiff.Section3 Numerics.Native
open scoped ENNReal NNReal
noncomputable section

/-- The actual sheared child field satisfies the owner's source-observer
identity; no transport equality remains as a premise. -/
theorem heatVHEATDrift_refined_child_observer
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) (i : nativeHeatQ3RefinedCarrierIndex) :
    nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i)
      (heatVHEATDriftRefinedChildField m t g z i)=
      heatRefinedObserverShear (nativeHeatQ3RefinedCarrierChild m i).scale (m+1) 9 t
        (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2) := by
  have hc : nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i)
      (ContinuousMap.const _ (g i z.2))=ContinuousMap.const _ (g i z.2) := by
    ext x
    rfl
  unfold heatVHEATDriftRefinedChildField
  rw [map_add,hc]
  exact nativeHeatQ3RefinedCarrierShearedField_translate M m i t (g i z.2) z.1

/-- Exact physical-to-canonical equality for the entire actual family. -/
theorem heatVHEATDrift_refined_physical_family_eq
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) :
    heatVHEATDriftRefinedPhysicalAverage M m t g z=heatVHEATDriftRefinedAverage M m t g z ∧
    heatVHEATDriftRefinedPhysicalDrift M h m t k g z=heatVHEATDriftRefinedSource M h m t k g z :=
  heatVHEATDrift_refined_physical_family_eq_of_observer M h m t k g z
    (heatVHEATDrift_refined_child_observer M m t g z)

/-- Intrinsic L20 norm of the actual physical child traces, still extended. -/
def heatVHEATDriftRefinedPhysicalXExtended (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ) : ℝ≥0∞ :=
  heatVHEATDriftXExtended (nativeHeatRemainderJointLaw M) Finset.univ
    (fun i z => heatVHEATDriftRefinedPhysicalTrace M m t g z i)

/-- The physical and canonical extended heat norms are exactly equal,
before any conversion to a real number. -/
theorem heatVHEATDrift_refined_physical_norm_eq
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ) :
    heatVHEATDriftRefinedPhysicalXExtended M m t g=
      heatVHEATDriftSourceXExtended Finset.univ M (m+1) t (heatVHEATDriftRefinedShift m) g := by
  have hT : (fun i z => heatVHEATDriftRefinedPhysicalTrace M m t g z i)=
      (fun i => heatRefinedTranslatedTrace M (m+1) 9 t (heatVHEATDriftRefinedShift m i) (g i)) := by
    funext i z
    exact heatVHEATDrift_refined_physical_trace_eq_of_observer M m t g z i
      (heatVHEATDrift_refined_child_observer M m t g z i)
  exact congrArg (heatVHEATDriftXExtended (nativeHeatRemainderJointLaw M) Finset.univ) hT

end
end ASDExplicitGamma.Native

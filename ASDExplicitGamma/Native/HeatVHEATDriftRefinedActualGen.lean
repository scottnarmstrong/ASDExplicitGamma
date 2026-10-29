module

public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedActual
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
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedBindingGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceObserverGen

/-! The `ns`-shell generalization of `HeatVHEATDriftRefinedActual`. -/

@[expose] public section


namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Algsuperdiff.Section3 Numerics.Native
open scoped ENNReal NNReal
noncomputable section

variable (ns : ℕ)

/-- The actual sheared child field satisfies the owner's source-observer
identity; no transport equality remains as a premise. -/
theorem heatVHEATDrift_refined_child_observer_Gen
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) (i : nativeHeatQ3RefinedCarrierIndex) :
    nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i)
      ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i)=
      heatRefinedObserverShear (nativeHeatQ3RefinedCarrierChild m i).scale (m+1) ns t
        (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1) (g i z.2) := by
  have hc : nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i)
      (ContinuousMap.const _ (g i z.2))=ContinuousMap.const _ (g i z.2) := by
    ext x
    rfl
  unfold heatVHEATDriftRefinedChildFieldGen
  rw [map_add,hc]
  exact (nativeHeatQ3RefinedCarrierShearedField_translate_Gen ns) M m i t (g i z.2) z.1

/-- Exact physical-to-canonical equality for the entire actual family. -/
theorem heatVHEATDrift_refined_physical_family_eq_Gen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) :
    (heatVHEATDriftRefinedPhysicalAverageGen ns) M m t g z=(heatVHEATDriftRefinedAverageGen ns) M m t g z ∧
    (heatVHEATDriftRefinedPhysicalDriftGen ns) M h m t k g z=(heatVHEATDriftRefinedSourceGen ns) M h m t k g z :=
  (heatVHEATDrift_refined_physical_family_eq_of_observer_Gen ns) M h m t k g z
    ((heatVHEATDrift_refined_child_observer_Gen ns) M m t g z)

/-- Intrinsic L20 norm of the actual physical child traces, still extended. -/
def heatVHEATDriftRefinedPhysicalXExtendedGen (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ) : ℝ≥0∞ :=
  heatVHEATDriftXExtended (nativeHeatRemainderJointLaw M) Finset.univ
    (fun i z => (heatVHEATDriftRefinedPhysicalTraceGen ns) M m t g z i)

/-- The physical and canonical extended heat norms are exactly equal,
before any conversion to a real number. -/
theorem heatVHEATDrift_refined_physical_norm_eq_Gen
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ) :
    (heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t g=
      (heatVHEATDriftSourceXExtendedGen ns) Finset.univ M (m+1) t (heatVHEATDriftRefinedShift m) g := by
  have hT : (fun i z => (heatVHEATDriftRefinedPhysicalTraceGen ns) M m t g z i)=
      (fun i => heatRefinedTranslatedTrace M (m+1) ns t (heatVHEATDriftRefinedShift m i) (g i)) := by
    funext i z
    exact (heatVHEATDrift_refined_physical_trace_eq_of_observer_Gen ns) M m t g z i
      ((heatVHEATDrift_refined_child_observer_Gen ns) M m t g z i)
  exact congrArg (heatVHEATDriftXExtended (nativeHeatRemainderJointLaw M) Finset.univ) hT


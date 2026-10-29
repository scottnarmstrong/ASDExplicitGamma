module

public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedExpectation

/-! Literal physical heat-path objects consumed by the drift aggregation.
These assemble the owner's existing carrier maps without replacing its law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Algsuperdiff.Section3
noncomputable section

local instance heatVHEATDriftRefinedPhysicalChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- The actual physical OLD-plus-fresh-band field on a refined child, with
its auxiliary scalar added only to that child's test. -/
def heatVHEATDriftRefinedChildField (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) (i : nativeHeatQ3RefinedCarrierIndex) :
    C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)),ℝ) :=
  nativeHeatQ3RefinedCarrierOldMap m
    (olderField (nativeHeatQ3RefinedCarrierDomain m) (m+1) z.1+
      Real.sqrt t • modelBand (nativeHeatQ3RefinedCarrierDomain m)
        (nativeHeatQ3RefinedCarrierPhysicalShells m) z.1) i+
    ContinuousMap.const _ (g i z.2)

/-- Actual common-frame physical child trace on the same two noises. -/
def heatVHEATDriftRefinedPhysicalTrace (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) (i : nativeHeatQ3RefinedCarrierIndex) : ℝ :=
  childTraceObservable (measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i)) M.nu
    (Annealed.sigmaBar M (m+1)) M.nu_pos (Annealed.sigmaBar_characterization M (m+1)).1
    (heatVHEATDriftRefinedChildField m t g z i)

/-- The actual physical trace average on the depth-ten carrier. -/
def heatVHEATDriftRefinedPhysicalAverage (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : ℝ :=
  ∑ i : nativeHeatQ3RefinedCarrierIndex,
    heatVHEATDriftRefinedWeight*heatVHEATDriftRefinedPhysicalTrace M m t g z i

/-- Literal sum of the owner's centered signed drift/mixed profiles on the
actual sheared physical child fields, with the actual polynomial power weight. -/
def heatVHEATDriftRefinedPhysicalDrift (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : ℝ :=
  ∑ i : nativeHeatQ3RefinedCarrierIndex,heatVHEATDriftRefinedWeight*
    ((k:ℝ)*(heatVHEATDriftRefinedPhysicalAverage M m t g z)^(k-1)*
      ∑ d : Fin 9,nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile M h m i d
        (Annealed.sigmaBar M (m+1)) (heatVHEATDriftRefinedChildField m t g z i))

end
end ASDExplicitGamma.Native

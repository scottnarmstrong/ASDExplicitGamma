module

public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceObserver
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

/-! The `ns`-shell generalization of `HeatVHEATRefinedSourceObserver`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Model
open scoped Topology

variable (ns : ℕ)

local instance nativeHeatRefinedSourceObserverOriginCompactGenRefinedSourceObserver (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet (originCube 2 Q.scale))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (originCube 2 Q.scale)).isCompact_closure

theorem nativeHeatQ3RefinedCarrierFreshBand_translate_Gen
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex)
    (ω : Cutoff.CutoffSample 2) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let E : nativeHeatQ3RefinedCarrierIndex → Type := fun j =>
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)
    let P := (ContinuousLinearMap.proj (R := ℝ) (φ := E) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
    nativeHeat_translateTriadicFieldToOrigin Q
      (P (modelBand (nativeHeatQ3RefinedCarrierDomain m)
        (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) ω)) =
    modelBand (closure (cubeSet (originCube 2 Q.scale)))
      (nativeSourceBandIndex (m + 1) ns)
      (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) := by
  classical
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let K := nativeHeatQ3RefinedCarrierDomain m
  let U0 := closure (cubeSet (originCube 2 Q.scale))
  let E : nativeHeatQ3RefinedCarrierIndex → Type := fun j =>
    C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)
  let P : C(K, ℝ) →L[ℝ] E i :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := E) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
  let A := nativeHeat_translateTriadicFieldToOrigin Q
  let z := triadicCubeShift Q
  have hlabels : nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns =
      nativeSourceBandIndex (m + 1) ns := by
    funext d
    simp [nativeHeatQ3RefinedCarrierPhysicalShellsGen, nativeSourceBandIndex]
    omega
  have hterm (d : Fin ns) :
      A (P (shellFieldScalarRestriction K
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d)))) =
        shellFieldScalarRestriction U0
          ((Cutoff.translateCutoffSample z ω).1
            (nativeSourceBandIndex (m + 1) ns d)) := by
    let j := nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d
    have hrestrict : P (shellFieldScalarRestriction K
        (ω.1 j)) =
        shellFieldScalarRestriction
          (closure (cubeSet Q)) (ω.1 j) := by
      apply ContinuousMap.ext
      intro y
      change shellFieldScalarRestriction K (ω.1 j)
          ⟨y.1, nativeHeatQ3RefinedCarrierChild_closure_subset m i y.2⟩ = _
      rfl
    rw [hrestrict, nativeHeat_translateTriadicFieldToOrigin_shellRestriction]
    rw [show nativeSourceBandIndex (m + 1) ns d = j from (congrFun hlabels d).symm]
    change shellFieldScalarRestriction U0 (ShellField.translate z (ω.1 j)) =
      shellFieldScalarRestriction U0 (ShellField.translate z (ω.1 j))
    rfl
  change A (P (∑ d : Fin ns,
      shellFieldScalarRestriction K
        (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d)))) =
    ∑ d : Fin ns, shellFieldScalarRestriction U0
      ((Cutoff.translateCutoffSample z ω).1
        (nativeSourceBandIndex (m + 1) ns d))
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact hterm d

/-- The full OLD-plus-band source field is exactly the canonical observer
after translating the cutoff sample. -/
theorem nativeHeatQ3RefinedCarrierField_translate_Gen
    (M : ABKModel 2) (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let E : nativeHeatQ3RefinedCarrierIndex → Type := fun j =>
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)
    let P := (ContinuousLinearMap.proj (R := ℝ) (φ := E) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
    nativeHeat_translateTriadicFieldToOrigin Q
      (P (olderField (nativeHeatQ3RefinedCarrierDomain m) (m + 1) ω +
        Real.sqrt t • modelBand (nativeHeatQ3RefinedCarrierDomain m)
          (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) ω)) =
    parentBoundaryObserverBandScalar Q.scale (m + 1) ns t
      (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) := by
  classical
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let K := nativeHeatQ3RefinedCarrierDomain m
  let E : nativeHeatQ3RefinedCarrierIndex → Type := fun j =>
    C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)
  let P := (ContinuousLinearMap.proj (R := ℝ) (φ := E) i).comp
    (nativeHeatQ3RefinedCarrierOldMap m)
  let A := nativeHeat_translateTriadicFieldToOrigin Q
  have hold := nativeHeatQ3RefinedCarrierOldField_translate M m i ω
  have hband := (nativeHeatQ3RefinedCarrierFreshBand_translate_Gen ns) m i ω
  have hold' :
      A (P (olderField K (m + 1) ω)) =
        olderField (closure (cubeSet (originCube 2 Q.scale))) (m + 1)
          (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) := by
    simpa [Q, E, P, A, K] using hold
  have hband' :
      A (P (modelBand K (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) ω)) =
        modelBand (closure (cubeSet (originCube 2 Q.scale)))
          (nativeSourceBandIndex (m + 1) ns)
          (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) := by
    simpa [Q, E, P, A, K] using hband
  calc
    A (P (olderField K (m + 1) ω + Real.sqrt t •
        modelBand K (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) ω)) =
      A (P (olderField K (m + 1) ω)) + Real.sqrt t •
        A (P (modelBand K (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) ω)) := by
          simp only [map_add, map_smul]
    _ = parentBoundaryObserverBandScalar Q.scale (m + 1) ns t
        (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) := by
          rw [hold', hband']
          rfl

/-- Adding the independent auxiliary scalar after the pointwise carrier
transport gives exactly its sheared refined observer. -/
theorem nativeHeatQ3RefinedCarrierShearedField_translate_Gen
    (M : ABKModel 2) (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex)
    (t g : ℝ) (ω : Cutoff.CutoffSample 2) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let E : nativeHeatQ3RefinedCarrierIndex → Type := fun j =>
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)
    let P := (ContinuousLinearMap.proj (R := ℝ) (φ := E) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
    nativeHeat_translateTriadicFieldToOrigin Q
      (P (olderField (nativeHeatQ3RefinedCarrierDomain m) (m + 1) ω +
        Real.sqrt t • modelBand (nativeHeatQ3RefinedCarrierDomain m)
          (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) ω)) +
      ContinuousMap.const _ g =
    heatRefinedObserverShear Q.scale (m + 1) ns t
      (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) g := by
  dsimp only
  rw [(nativeHeatQ3RefinedCarrierField_translate_Gen ns) M m i t ω]
  rw [heatRefinedObserverShear]

end ASDExplicitGamma.Native

end

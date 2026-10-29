module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanObservation
public import ASDExplicitGamma.Native.HeatVHEATFamily
import ASDExplicitGamma.Gaussian.GaussCentering

/-! The actual child remainder map becomes the origin-cube centered field
after translating the child to its model coordinates. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
open ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped Topology

/-- Translation intertwines the physical child remainder with centering at
the origin cube's parent center. -/
theorem nativeHeatQ3RefinedCarrierChildRemainder_translate_eq_centered
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex)
    (f : C(nativeHeatQ3RefinedCarrierDomain m, ℝ)) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
      fun j => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j))
    let hU : ∀ j, U j ⊆ nativeHeatQ3RefinedCarrierDomain m :=
      nativeHeatQ3RefinedCarrierChild_closure_subset m
    let R₀ := childRemainderMap U hU (nativeHeatQ3RefinedCarrierCenter m)
    let P := (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
    let A := nativeHeat_translateTriadicFieldToOrigin Q
    let C₀ := centeringMap (pureFluxParentCenter Q.scale)
    A (R₀ f i) = C₀ (A (P f)) := by
  classical
  dsimp only
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
    fun j => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j))
  let hU : ∀ j, U j ⊆ nativeHeatQ3RefinedCarrierDomain m :=
    nativeHeatQ3RefinedCarrierChild_closure_subset m
  let R₀ := childRemainderMap U hU (nativeHeatQ3RefinedCarrierCenter m)
  let P := (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
    (nativeHeatQ3RefinedCarrierOldMap m)
  let A := nativeHeat_translateTriadicFieldToOrigin Q
  let C₀ := centeringMap (pureFluxParentCenter Q.scale)
  have hcenter : (pureFluxParentCenter Q.scale).1 + triadicCubeShift Q =
      cubeCenter Q := by
    funext a
    simp [pureFluxParentCenter, triadicCubeShift, cubeCenter, originCube]
  ext y
  simp only [nativeHeat_translateTriadicFieldToOrigin,
    ContinuousMap.compCLM_apply, ContinuousMap.comp_apply,
    nativeHeatQ3RefinedCarrierOldMap,
    childRemainderMap_apply, centeringMap_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply,
    nativeHeatQ3RefinedCarrierCenter]
  simp only [ContinuousMap.compCLM_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  congr 1
  exact congrArg f (Subtype.ext hcenter.symm)

end ASDExplicitGamma.Native

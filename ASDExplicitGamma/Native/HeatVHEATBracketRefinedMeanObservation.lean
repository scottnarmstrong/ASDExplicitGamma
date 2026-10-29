module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSourceMap
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransport
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! The mean-gradient observation written in the translated child coordinates
used by the local SHEAR bracket row. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
open ASDExplicitGamma.Response ASDExplicitGamma.Variational ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

local instance nativeHeatQ3RefinedObservationCubeCompact (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

/-- The derivative observation for one physical child, expressed on the
rectangle carrier of its actual source remainder factor. -/
noncomputable def nativeHeatQ3RefinedChildMeanTraceObservation
    (M : ABKModel 2) (σ : ℝ) (m : ℤ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ))
    (i : nativeHeatQ3RefinedCarrierIndex) :
    C(nativeHeatQ3RefinedCarrierChildRectangle m i, ℝ) →L[ℝ] ℝ := by
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let A := nativeHeat_translateTriadicFieldToOrigin Q
  let O := fderiv ℝ (modelTraceObservable Q.scale M.nu σ) (A (x i))
  exact O.comp (A.comp
    (nativeHeatQ3RefinedCarrierChildRectangleToCube m i))

/-- Translation of the actual child trace commutes with its first derivative.
This identifies the derivative used in the product mean with the origin-cube
derivative used by the sharp per-child bracket estimate. -/
theorem nativeHeatQ3RefinedCarrierChildTrace_fderiv_toOrigin
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet Q), ℝ)) :
    fderiv ℝ
        (childTraceObservable
          (measurableSet_cubeSet Q) (volume_cubeSet_toReal_pos Q)
          ν σ hν hσ) x =
      (fderiv ℝ (modelTraceObservable Q.scale ν σ)
        (nativeHeat_translateTriadicFieldToOrigin Q x)).comp
        (nativeHeat_translateTriadicFieldToOrigin Q) := by
  let A := nativeHeat_translateTriadicFieldToOrigin Q
  let φ := childTraceObservable
    (measurableSet_cubeSet Q) (volume_cubeSet_toReal_pos Q) ν σ hν hσ
  let Φ := modelTraceObservable Q.scale ν σ
  have hobs : φ = fun y => Φ (A y) := by
    funext y
    simpa [φ, Φ, A] using
      (nativeHeatQ3RefinedCarrierChildTraceObservable_toOrigin
        Q ν σ hν hσ y)
  have hΦ : DifferentiableAt ℝ Φ (A x) := by
    exact (ContDiff.contDiffAt
      (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives
        Q.scale ν σ hν hσ).1).differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ A x := A.differentiableAt
  change fderiv ℝ φ x = (fderiv ℝ Φ (A x)).comp A
  rw [hobs]
  simpa only [Function.comp_def, ContinuousLinearMap.fderiv] using
    (fderiv_comp x hΦ hA)

end ASDExplicitGamma.Native

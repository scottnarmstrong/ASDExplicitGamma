module

public import ASDExplicitGamma.Native.HeatVHEATCarrierRow
public import ASDExplicitGamma.Native.HeatVHEATFamily
public import ASDExplicitGamma.Native.HeatVHEATSourceTransport
public import ASDExplicitGamma.Native.HeatVHEATResponseTranslation
public import ASDExplicitGamma.Native.HeatVHEATShellTranslation

/-! Actual carrier factors in origin coordinates, ready for the source signed
generator row. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3 ASDExplicitGamma.Model
open ASDExplicitGamma.Inverse ASDExplicitGamma.Response
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open ProbabilityTheory

/-- A C² covariance trace commutes with an arbitrary continuous linear
coordinate map, with no bijectivity assumption. -/
theorem nativeHeat_modelCovarianceTrace_comp_continuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (H : ℕ → E) (hH : Summable (fun j => ‖H j‖ ^ 2))
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (x : E) :
    modelCovarianceTrace (f ∘ A) H x =
      modelCovarianceTrace f (fun j => A (H j)) (A x) := by
  classical
  let C : (F →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E F ℝ).flip A
  have hfderiv : ContDiff ℝ 1 (fun y : F => fderiv ℝ f y) :=
    hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hfirst (y : E) :
      fderiv ℝ (f ∘ A) y = C (fderiv ℝ f (A y)) := by
    rw [fderiv_comp (f := A) (g := f) y
      (hf.differentiable (by norm_num) (A y)) A.differentiableAt]
    rw [A.fderiv]
    simp [C, ContinuousLinearMap.compL_apply]
  have hinnerDiff : DifferentiableAt ℝ
      (fun y : E => fderiv ℝ f (A y)) x := by
    exact (hfderiv.differentiable (by norm_num) (A x)).comp x A.differentiableAt
  have hCDiff : DifferentiableAt ℝ C (fderiv ℝ f (A x)) := C.differentiableAt
  have hsecond :
      fderiv ℝ (fderiv ℝ (f ∘ A)) x =
        C.comp ((fderiv ℝ (fun y : F => fderiv ℝ f y) (A x)).comp A) := by
    have hgrad : fderiv ℝ (f ∘ A) = C ∘ (fun y : E => fderiv ℝ f (A y)) := by
      funext y
      exact hfirst y
    rw [hgrad]
    rw [fderiv_comp (f := fun y : E => fderiv ℝ f (A y)) (g := C) x
      hCDiff hinnerDiff]
    have hinner : (fun y : E => fderiv ℝ f (A y)) =
        (fun y : F => fderiv ℝ f y) ∘ A := rfl
    rw [hinner]
    rw [fderiv_comp (f := A) (g := fun y : F => fderiv ℝ f y) x
      (hfderiv.differentiable (by norm_num) (A x)) A.differentiableAt]
    rw [C.fderiv, A.fderiv]
  let H' : ℕ → F := fun j => A (H j)
  have hH' : Summable (fun j => ‖H' j‖ ^ 2) :=
    summable_sq_norm_gaussianDirections hH A
  have hleft := modelCovarianceTrace_eq_bilinearTraceMap H hH
    (hf.comp_continuousLinearMap (g := A)) x
  have hright := modelCovarianceTrace_eq_bilinearTraceMap H' hH' hf (A x)
  rw [hleft, hright]
  rw [bilinearTraceMap_apply, bilinearTraceMap_apply]
  apply tsum_congr
  intro j
  rw [hsecond]
  simp [C, H', ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]

end ASDExplicitGamma.Native

end

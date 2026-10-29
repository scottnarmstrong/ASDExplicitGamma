module

public import ASDExplicitGamma.Gaussian.RealizationMeasurability
public import ASDExplicitGamma.Model.CutoffAction
public import Homogenization.Geometry.TriadicCubeTranslation

/-! Translation of actual shell restrictions to the origin coordinates of a
triadic observation cube. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions

/-- Pull a continuous shell field on a triadic cube back to the origin cube
at the same scale. -/
noncomputable def nativeHeat_translateTriadicFieldToOrigin (Q : TriadicCube 2) :
    C(closure (cubeSet Q), ℝ) →L[ℝ]
      C(closure (cubeSet (originCube 2 Q.scale)), ℝ) := by
  let z := triadicCubeShift Q
  let K := closure (cubeSet Q)
  let K0 := closure (cubeSet (originCube 2 Q.scale))
  have himage : (fun y : Vec 2 => y + z) '' K0 ⊆ K := by
    change (fun y : Vec 2 => y + z) ''
        closure (cubeSet (originCube 2 Q.scale)) ⊆ closure (cubeSet Q)
    rw [cubeSet_eq_translateSet_originCube_of_triadicCube Q]
    rw [← image_addRight_eq_translateSet z (cubeSet (originCube 2 Q.scale))]
    exact image_closure_subset_closure_image (by fun_prop)
  let incl : C(K0, K) :=
    ⟨fun x => ⟨x.1 + z, himage ⟨x.1, x.2, rfl⟩⟩,
      (continuous_subtype_val.add continuous_const).subtype_mk _⟩
  exact ContinuousMap.compCLM ℝ ℝ incl

/-- The translated restriction is pointwise the original shell evaluated at
the translated coordinate. -/
theorem nativeHeat_translateTriadicFieldToOrigin_shellRestriction
    (Q : TriadicCube 2) (j : ShellField 2) :
    nativeHeat_translateTriadicFieldToOrigin Q
        (shellFieldScalarRestriction (closure (cubeSet Q)) j) =
      shellFieldScalarRestriction
        (closure (cubeSet (originCube 2 Q.scale)))
        (ShellField.translate (triadicCubeShift Q) j) := by
  apply ContinuousMap.ext
  intro x
  simp [nativeHeat_translateTriadicFieldToOrigin,
    shellFieldScalarRestriction, planarShellScalarStream,
    ContinuousMap.compCLM_apply, ShellField.translate_apply]

/-- The actual cutoff-law shell restriction on a triadic cube, pulled back to
origin coordinates, has exactly the actual shell restriction law there. -/
theorem nativeHeat_shellRestrictionLaw_translateTriadicCube_toOrigin
    (M : ABKModel 2) (k : ℤ) (Q : TriadicCube 2) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 =>
          nativeHeat_translateTriadicFieldToOrigin Q
            (shellFieldScalarRestriction (closure (cubeSet Q)) (ω.1 k))) =
      (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 =>
          shellFieldScalarRestriction
            (closure (cubeSet (originCube 2 Q.scale))) (ω.1 k)) := by
  let z := triadicCubeShift Q
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let K0 := closure (cubeSet (originCube 2 Q.scale))
  let g := fun ω : Cutoff.CutoffSample 2 =>
    shellFieldScalarRestriction K0 (ω.1 k)
  have hg : Measurable g :=
    (measurable_shellFieldScalarRestriction K0).comp
      ((measurable_pi_apply k).comp measurable_subtype_coe)
  have hpoint (ω : Cutoff.CutoffSample 2) :
      nativeHeat_translateTriadicFieldToOrigin Q
          (shellFieldScalarRestriction (closure (cubeSet Q)) (ω.1 k)) =
        g (Cutoff.translateCutoffSample z ω) := by
    rw [nativeHeat_translateTriadicFieldToOrigin_shellRestriction]
    rfl
  have hfunctions :
      (fun ω : Cutoff.CutoffSample 2 =>
        nativeHeat_translateTriadicFieldToOrigin Q
          (shellFieldScalarRestriction (closure (cubeSet Q)) (ω.1 k))) =
        g ∘ Cutoff.translateCutoffSample z := by
    funext ω
    exact hpoint ω
  change μ.map (fun ω : Cutoff.CutoffSample 2 =>
      nativeHeat_translateTriadicFieldToOrigin Q
        (shellFieldScalarRestriction (closure (cubeSet Q)) (ω.1 k))) =
    μ.map g
  rw [hfunctions, ← Measure.map_map hg
    (Cutoff.measurable_translateCutoffSample z)]
  rw [Cutoff.map_translateCutoffSample_cutoffSampleLaw]

end ASDExplicitGamma.Native

end

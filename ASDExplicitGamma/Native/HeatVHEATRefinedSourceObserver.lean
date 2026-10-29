module

public import ASDExplicitGamma.Native.HeatRefinedObserverShear
public import ASDExplicitGamma.Native.HeatVHEATRefinedAssembly

/-! Pointwise identification of the refined carrier heat field with the
canonical translated source observer. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Model
open scoped Topology

local instance nativeHeatRefinedSourceObserverOriginCompact (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet (originCube 2 Q.scale))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (originCube 2 Q.scale)).isCompact_closure

/-- The completed old field on the refined carrier, restricted to one child
and translated to origin coordinates, is the old field of the translated
cutoff sample. -/
theorem nativeHeatQ3RefinedCarrierOldField_translate
    (M : ABKModel 2) (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex)
    (ω : Cutoff.CutoffSample 2) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let E : nativeHeatQ3RefinedCarrierIndex → Type := fun j =>
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)
    let P := (ContinuousLinearMap.proj (R := ℝ) (φ := E) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
    nativeHeat_translateTriadicFieldToOrigin Q
      (P (olderField (nativeHeatQ3RefinedCarrierDomain m) (m + 1) ω)) =
    olderField (closure (cubeSet (originCube 2 Q.scale))) (m + 1)
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
  have himage : (fun y : Vec 2 => y + z) '' U0 ⊆ closure (cubeSet Q) := by
    change (fun y : Vec 2 => y + z) ''
        closure (cubeSet (originCube 2 Q.scale)) ⊆ closure (cubeSet Q)
    rw [cubeSet_eq_translateSet_originCube_of_triadicCube Q]
    rw [← image_addRight_eq_translateSet z (cubeSet (originCube 2 Q.scale))]
    exact image_closure_subset_closure_image (by fun_prop)
  obtain ⟨ellK, hK⟩ := exists_originCube_containing_compact K
    (isCompact_iff_compactSpace.mpr inferInstance)
  obtain ⟨ell0, h0⟩ := exists_originCube_containing_compact U0
    (isCompact_iff_compactSpace.mpr inferInstance)
  have hcoef := Cutoff.coefficientCutoff_translateCutoffSample
    M.nu (m + 1) z ω
  apply ContinuousMap.ext
  intro x
  have hxQ : x.1 + z ∈ closure (cubeSet Q) :=
    himage ⟨x.1, x.2, rfl⟩
  have hxK : x.1 + z ∈ K :=
    nativeHeatQ3RefinedCarrierChild_closure_subset m i hxQ
  change olderField K (m + 1) ω ⟨x.1 + z, hxK⟩ =
    olderField U0 (m + 1) (Cutoff.translateCutoffSample z ω) x
  have hentry := congrArg (fun a : RegCoeffField 2 => a x.1 1 0) hcoef
  have hvalue :
      Cutoff.coefficientCutoff M.nu (m + 1) (Cutoff.translateCutoffSample z ω)
          x.1 1 0 =
        Cutoff.coefficientCutoff M.nu (m + 1) ω (x.1 + z) 1 0 := by
    simpa only [translateReg] using hentry
  rw [olderField_apply_eq_coefficientCutoff K M ellK (m + 1) hK ω
      ⟨x.1 + z, hxK⟩,
    olderField_apply_eq_coefficientCutoff U0 M ell0 (m + 1) h0
      (Cutoff.translateCutoffSample z ω) x]
  exact hvalue.symm

/-- The complete nine-shell fresh field on the refined carrier, restricted
to a child and translated to origin coordinates, is the canonical source
band field for the translated cutoff sample. -/
theorem nativeHeatQ3RefinedCarrierFreshBand_translate
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex)
    (ω : Cutoff.CutoffSample 2) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let E : nativeHeatQ3RefinedCarrierIndex → Type := fun j =>
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)
    let P := (ContinuousLinearMap.proj (R := ℝ) (φ := E) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
    nativeHeat_translateTriadicFieldToOrigin Q
      (P (modelBand (nativeHeatQ3RefinedCarrierDomain m)
        (nativeHeatQ3RefinedCarrierPhysicalShells m) ω)) =
    modelBand (closure (cubeSet (originCube 2 Q.scale)))
      (nativeSourceBandIndex (m + 1) 9)
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
  have hlabels : nativeHeatQ3RefinedCarrierPhysicalShells m =
      nativeSourceBandIndex (m + 1) 9 := by
    funext d
    simp [nativeHeatQ3RefinedCarrierPhysicalShells, nativeSourceBandIndex]
    omega
  have hterm (d : Fin 9) :
      A (P (shellFieldScalarRestriction K
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d)))) =
        shellFieldScalarRestriction U0
          ((Cutoff.translateCutoffSample z ω).1
            (nativeSourceBandIndex (m + 1) 9 d)) := by
    let j := nativeHeatQ3RefinedCarrierPhysicalShells m d
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
    rw [show nativeSourceBandIndex (m + 1) 9 d = j from (congrFun hlabels d).symm]
    change shellFieldScalarRestriction U0 (ShellField.translate z (ω.1 j)) =
      shellFieldScalarRestriction U0 (ShellField.translate z (ω.1 j))
    rfl
  change A (P (∑ d : Fin 9,
      shellFieldScalarRestriction K
        (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d)))) =
    ∑ d : Fin 9, shellFieldScalarRestriction U0
      ((Cutoff.translateCutoffSample z ω).1
        (nativeSourceBandIndex (m + 1) 9 d))
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact hterm d

/-- The full OLD-plus-band source field is exactly the canonical observer
after translating the cutoff sample. -/
theorem nativeHeatQ3RefinedCarrierField_translate
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
          (nativeHeatQ3RefinedCarrierPhysicalShells m) ω)) =
    parentBoundaryObserverBandScalar Q.scale (m + 1) 9 t
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
  have hband := nativeHeatQ3RefinedCarrierFreshBand_translate m i ω
  have hold' :
      A (P (olderField K (m + 1) ω)) =
        olderField (closure (cubeSet (originCube 2 Q.scale))) (m + 1)
          (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) := by
    simpa [Q, E, P, A, K] using hold
  have hband' :
      A (P (modelBand K (nativeHeatQ3RefinedCarrierPhysicalShells m) ω)) =
        modelBand (closure (cubeSet (originCube 2 Q.scale)))
          (nativeSourceBandIndex (m + 1) 9)
          (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) := by
    simpa [Q, E, P, A, K] using hband
  calc
    A (P (olderField K (m + 1) ω + Real.sqrt t •
        modelBand K (nativeHeatQ3RefinedCarrierPhysicalShells m) ω)) =
      A (P (olderField K (m + 1) ω)) + Real.sqrt t •
        A (P (modelBand K (nativeHeatQ3RefinedCarrierPhysicalShells m) ω)) := by
          simp only [map_add, map_smul]
    _ = parentBoundaryObserverBandScalar Q.scale (m + 1) 9 t
        (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) := by
          rw [hold', hband']
          rfl

/-- Adding the independent auxiliary scalar after the pointwise carrier
transport gives exactly its sheared refined observer. -/
theorem nativeHeatQ3RefinedCarrierShearedField_translate
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
          (nativeHeatQ3RefinedCarrierPhysicalShells m) ω)) +
      ContinuousMap.const _ g =
    heatRefinedObserverShear Q.scale (m + 1) 9 t
      (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) g := by
  dsimp only
  rw [nativeHeatQ3RefinedCarrierField_translate M m i t ω]
  rw [heatRefinedObserverShear]

end ASDExplicitGamma.Native

end

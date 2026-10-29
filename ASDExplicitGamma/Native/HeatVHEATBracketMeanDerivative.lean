module

public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszSupport

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

local instance nativeHeatQ3RefinedMeanApplyIndexNeZero :
    NeZero (3 ^ 10 * 3 ^ 10) := ⟨by norm_num⟩

local instance nativeHeatQ3RefinedMeanApplyChildCompact (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

local instance nativeHeatQ3RefinedMeanApplyChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn
      (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

noncomputable section

/-- The derivative row of the common child mean, evaluated on the actual
centered parent-source remainder, is the corresponding physical child
observation. This keeps the row identity separate from the symbolic finite
sum in the mean derivative. -/
theorem nativeHeatQ3RefinedCarrierParentMeanDerivative_row
    (M : ABKModel 2) (h : ℝ)
    (m : ℤ) (d : Fin 9) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ))
    (i : nativeHeatQ3RefinedCarrierIndex) (u : WhiteNoise) :
    fderiv ℝ
        (childTraceObservable
          (measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
          (volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
          M.nu σ M.nu_pos hσ)
        (x i)
        ((nativeHeatQ3RefinedCarrierRemainderMap m
          (nativeHeatQ3RefinedCarrierParentRestrict m
            (nativeHeatQ3RefinedCarrierParentSource' M h m d u))) i) =
      nativeHeatQ3RefinedChildMeanTraceObservation M σ m x i
        (q3RemainderValueFactor
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
          (q3ModelAmplitude M h (m + ((d.val + 2 : ℕ) : ℤ)))
          (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ)))
          ⟨cubeCenter (nativeHeatQ3RefinedCarrierChild m i),
            nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
              (subset_closure
                (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet
                  (nativeHeatQ3RefinedCarrierChild m i)))⟩ u) := by
  classical
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let s : ℕ := d.val + 2
  let β := q3ModelAmplitude M h (m + (s : ℤ))
  let L := q3ModelLength (m + (s : ℤ))
  have hsource := nativeHeatQ3RefinedCarrierParentCenteredSource_eq_childRemainders
    M h m d u
  have hsourcei := congrFun hsource i
  have hobs := nativeHeatQ3RefinedCarrierChildTrace_fderiv_toOrigin
    Q M.nu σ M.nu_pos hσ (x i)
  dsimp only [nativeHeatQ3RefinedCarrierRemainderMap,
    nativeHeatQ3RefinedCarrierParentSource']
  rw [hsourcei]
  simp only [nativeHeatQ3RefinedChildMeanTraceObservation]
  exact congrArg (fun D : C(closure (cubeSet Q), ℝ) →L[ℝ] ℝ =>
    D (nativeHeatQ3RefinedCarrierChildRectangleToCube m i
      (q3RemainderValueFactor
        (cubeCorner Q 0) (cubeCorner Q 0 + cubeScaleFactor Q)
        (cubeCorner Q 1) (cubeCorner Q 1 + cubeScaleFactor Q)
        β L
        ⟨cubeCenter Q,
          nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
            (subset_closure
              (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet Q))⟩ u))) hobs

/-- Evaluating the derivative of the common child mean on the centered
restriction of one parent q3 source is the normalized sum of the actual
physical child remainder observations. -/
theorem nativeHeatQ3RefinedCarrierParentMeanDerivative_eq_remainderObservations
    (M : ABKModel 2) (h : ℝ)
    (m : ℤ) (d : Fin 9) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ))
    (u : WhiteNoise) :
    fderiv ℝ (nativeHeatQ3RefinedCarrierMeanTrace M m σ hσ) x
      (nativeHeatQ3RefinedCarrierRemainderMap m
        (nativeHeatQ3RefinedCarrierParentRestrict m
          (nativeHeatQ3RefinedCarrierParentSource' M h m d u))) =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          nativeHeatQ3RefinedCarrierChildRemainderMeanObservation
            M h m d σ x i u := by
  classical
  dsimp only [nativeHeatQ3RefinedCarrierMeanTrace,
    nativeHeatQ3RefinedCarrierRemainderMap,
    nativeHeatQ3RefinedCarrierParentSource']
  let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
    fun i => nativeHeatQ3RefinedCarrierChild m i
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
  let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
  let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos (Q i)
  let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
  let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
    nativeHeatQ3RefinedCarrierChild_closure_subset m
  let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
  let R₀ := childRemainderMap V hV (nativeHeatQ3RefinedCarrierCenter m)
  let s : ℕ := d.val + 2
  let β := q3ModelAmplitude M h (m + (s : ℤ))
  let L := q3ModelLength (m + (s : ℤ))
  let parent := mainCubeH3Value (m + 10) β L ∘L
    q3H3RangeFactor (-mainCubeHalfSide (m + 10)) (mainCubeHalfSide (m + 10))
      (-mainCubeHalfSide (m + 10)) (mainCubeHalfSide (m + 10)) β L
  let source := nativeHeatQ3RefinedCarrierParentRestrict m (parent u)
  let hsource := nativeHeatQ3RefinedCarrierParentCenteredSource_eq_childRemainders
    M h m d u
  have hderiv := nativeHeat_childMeanTrace_fderiv_apply
    (n := 3 ^ 10 * 3 ^ 10) Q M.nu σ M.nu_pos hσ x (R₀ source)
  rw [hderiv]
  have hsum :
      (∑ i : nativeHeatQ3RefinedCarrierIndex,
        fderiv ℝ (childTraceObservable (hU i) (hvol i) M.nu σ M.nu_pos hσ)
          (x i) ((R₀ source) i)) =
      ∑ i : nativeHeatQ3RefinedCarrierIndex,
        nativeHeatQ3RefinedCarrierChildRemainderMeanObservation
          M h m d σ x i u := by
    apply Finset.sum_congr rfl
    intro i hi
    change fderiv ℝ
        (childTraceObservable (hU i) (hvol i) M.nu σ M.nu_pos hσ)
        (x i)
        ((nativeHeatQ3RefinedCarrierRemainderMap m
          (nativeHeatQ3RefinedCarrierParentRestrict m
            (nativeHeatQ3RefinedCarrierParentSource' M h m d u))) i) =
      nativeHeatQ3RefinedCarrierChildRemainderMeanObservation
        M h m d σ x i u
    rw [nativeHeatQ3RefinedCarrierParentMeanDerivative_row
      M h m d σ hσ x i u]
    rfl
  rw [hsum]
  rw [show Fintype.card nativeHeatQ3RefinedCarrierIndex = 3 ^ 10 * 3 ^ 10 by
    simp [nativeHeatQ3RefinedCarrierIndex]]

end

end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszIdentity

/-! The common-shell mean-gradient trace as the Riesz energy of the actual
finite average of physical child observations. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped RealInnerProductSpace Topology

local instance nativeHeatQ3RefinedMeanRieszIdentityChildCompact (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

local instance nativeHeatQ3RefinedMeanRieszIdentityChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn
      (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- One actual common-shell global mean-gradient trace is the squared norm
of the normalized average of its physical child-observation Riesz vectors. -/
theorem nativeHeatQ3RefinedCarrierMeanRieszAverageIdentity
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (d : Fin 9) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
      fun i => cubeSet (nativeHeatQ3RefinedCarrierChild m i)
    let hU : ∀ i, MeasurableSet (U i) :=
      fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal :=
      fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
      fun i => closure (U i)
    let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
      nativeHeatQ3RefinedCarrierChild_closure_subset m
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let R₀ := childRemainderMap V hV
      (nativeHeatQ3RefinedCarrierCenter m)
    let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
    let s : ℕ := d.val + 2
    let β := q3ModelAmplitude M h (m + (s : ℤ))
    let L := q3ModelLength (m + (s : ℤ))
    let obs : nativeHeatQ3RefinedCarrierIndex → WhiteNoise →L[ℝ] ℝ := fun i =>
      (nativeHeatQ3RefinedChildMeanTraceObservation M σ m x i).comp
        (q3RemainderValueFactor
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
          β L
          ⟨cubeCenter (nativeHeatQ3RefinedCarrierChild m i),
            nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
              (subset_closure
                (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet
                  (nativeHeatQ3RefinedCarrierChild m i)))⟩)
    modelGradientSquareTrace μ
      (fun j => R₀ (F.factor d (F.direction d j))) x =
      ‖(Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ •
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          (InnerProductSpace.toDual ℝ WhiteNoise).symm (obs i)‖ ^ 2 := by
  classical
  dsimp only
  let C := nativeHeatQ3RefinedCarrierIndex
  let I := Fin (3 ^ 10) × Fin (3 ^ 10)
  let e : I ≃ C := finProdFinEquiv
  let U : C → Set (Vec 2) := fun i => cubeSet (nativeHeatQ3RefinedCarrierChild m i)
  let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet _
  let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos _
  let V : C → Set (Vec 2) := fun i => closure (U i)
  let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
    nativeHeatQ3RefinedCarrierChild_closure_subset m
  let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
  let R₀ := childRemainderMap V hV (nativeHeatQ3RefinedCarrierCenter m)
  let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
  let s : ℕ := d.val + 2
  let β := q3ModelAmplitude M h (m + (s : ℤ))
  let L := q3ModelLength (m + (s : ℤ))
  let obs : C → WhiteNoise →L[ℝ] ℝ := fun i =>
    (nativeHeatQ3RefinedChildMeanTraceObservation M σ m x i).comp
      (q3RemainderValueFactor
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
          cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
          cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
        β L
        ⟨cubeCenter (nativeHeatQ3RefinedCarrierChild m i),
          nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
            (subset_closure
              (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet
                (nativeHeatQ3RefinedCarrierChild m i)))⟩)
  let Riesz : (WhiteNoise →L[ℝ] ℝ) → WhiteNoise :=
    fun T => (InnerProductSpace.toDual ℝ WhiteNoise).symm T
  have htrace := nativeHeatQ3RefinedCarrierMeanRemainderGradient_eq_averageRiesz
    M h hM m d σ hσ x
  have htrace' : modelGradientSquareTrace μ
      (fun j => R₀ (F.factor d (F.direction d j))) x =
      ‖nativeHeatQ3RefinedCarrierMeanRieszAverage M h m d σ x‖ ^ 2 := by
    simpa only [μ, R₀, F, nativeHeatQ3RefinedCarrierMeanTrace,
      nativeHeatQ3RefinedCarrierRemainderMap,
      nativeHeatQ3RefinedCarrierFreshShellVector,
      nativeHeatQ3RefinedCarrierMeanRieszAverage] using htrace
  have hcard : (Fintype.card C : ℝ) =
      ((Finset.univ : Finset I).card : ℝ) := by
    rw [Finset.card_univ]
    exact_mod_cast (Fintype.card_congr e).symm
  have hobs (i : C) :
      nativeHeatQ3RefinedCarrierChildRemainderMeanObservation
        M h m d σ x i = obs i := by
    simp only [nativeHeatQ3RefinedCarrierChildRemainderMeanObservation,
      obs, s, β, L]
  have hsum :
      (∑ i : C, Riesz (obs i)) =
        ∑ ij : I, Riesz
          (nativeHeatQ3RefinedCarrierChildRemainderMeanObservation
            M h m d σ x (e ij)) := by
    calc
      _ = ∑ i : C, Riesz
          (nativeHeatQ3RefinedCarrierChildRemainderMeanObservation
            M h m d σ x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hobs]
      _ = _ := (Equiv.sum_comp e fun i : C => Riesz
        (nativeHeatQ3RefinedCarrierChildRemainderMeanObservation
          M h m d σ x i)).symm
  have havg : nativeHeatQ3RefinedCarrierMeanRieszAverage M h m d σ x =
      (Fintype.card C : ℝ)⁻¹ • ∑ i : C, Riesz (obs i) := by
    dsimp only [nativeHeatQ3RefinedCarrierMeanRieszAverage]
    rw [← hcard]
    rw [hsum.symm]
  calc
    _ = ‖nativeHeatQ3RefinedCarrierMeanRieszAverage M h m d σ x‖ ^ 2 := htrace'
    _ = ‖(Fintype.card C : ℝ)⁻¹ • ∑ i : C, Riesz (obs i)‖ ^ 2 := by rw [havg]

end ASDExplicitGamma.Native

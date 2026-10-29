module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanRieszIdentity
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
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedActualGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedAssemblyGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedRowGen
public import ASDExplicitGamma.Native.Q3GridOverlapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSupportGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedObservationGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedParentLawGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSourceMapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanVarianceGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedRemainderGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanChildBoundGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszSupportGen
public import ASDExplicitGamma.Native.HeatVHEATBracketParentRieszGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanDerivativeGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanDerivativeCLMGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszIdentityGen

/-! The `ns`-shell generalization of `HeatVHEATBracketRefinedMeanRieszIdentity`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped RealInnerProductSpace Topology

variable (ns : ℕ) [NeZero ns]

local instance nativeHeatQ3RefinedMeanRieszIdentityChildCompact_GenBracketRefinedMeanRieszIdentity (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

local instance nativeHeatQ3RefinedMeanRieszIdentityChildFinite_GenBracketRefinedMeanRieszIdentity (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn
      (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- One actual common-shell global mean-gradient trace is the squared norm
of the normalized average of its physical child-observation Riesz vectors. -/
theorem nativeHeatQ3RefinedCarrierMeanRieszAverageIdentity_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (d : Fin ns) (σ : ℝ) (hσ : 0 < σ)
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
      (fun j => R₀ (Ffam.factor d (Ffam.direction d j))) x =
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
  have htrace := (nativeHeatQ3RefinedCarrierMeanRemainderGradient_eq_averageRiesz_Gen ns)
    M h hM m Ffam d σ hσ x
  have htrace' : modelGradientSquareTrace μ
      (fun j => R₀ (Ffam.factor d (Ffam.direction d j))) x =
      ‖(nativeHeatQ3RefinedCarrierMeanRieszAverageGen ns) M h m d σ x‖ ^ 2 := by
    simpa only [μ, R₀, nativeHeatQ3RefinedCarrierMeanTrace,
      nativeHeatQ3RefinedCarrierRemainderMap,
      nativeHeatQ3RefinedCarrierFreshShellVectorGen,
      nativeHeatQ3RefinedCarrierMeanRieszAverageGen] using htrace
  have hcard : (Fintype.card C : ℝ) =
      ((Finset.univ : Finset I).card : ℝ) := by
    rw [Finset.card_univ]
    exact_mod_cast (Fintype.card_congr e).symm
  have hobs (i : C) :
      (nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
        M h m d σ x i = obs i := by
    simp only [nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen,
      obs, s, β, L]
  have hsum :
      (∑ i : C, Riesz (obs i)) =
        ∑ ij : I, Riesz
          ((nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
            M h m d σ x (e ij)) := by
    calc
      _ = ∑ i : C, Riesz
          ((nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
            M h m d σ x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hobs]
      _ = _ := (Equiv.sum_comp e fun i : C => Riesz
        ((nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
          M h m d σ x i)).symm
  have havg : (nativeHeatQ3RefinedCarrierMeanRieszAverageGen ns) M h m d σ x =
      (Fintype.card C : ℝ)⁻¹ • ∑ i : C, Riesz (obs i) := by
    dsimp only [nativeHeatQ3RefinedCarrierMeanRieszAverageGen]
    rw [← hcard]
    rw [hsum.symm]
  calc
    _ = ‖(nativeHeatQ3RefinedCarrierMeanRieszAverageGen ns) M h m d σ x‖ ^ 2 := htrace'
    _ = ‖(Fintype.card C : ℝ)⁻¹ • ∑ i : C, Riesz (obs i)‖ ^ 2 := by rw [havg]

end ASDExplicitGamma.Native

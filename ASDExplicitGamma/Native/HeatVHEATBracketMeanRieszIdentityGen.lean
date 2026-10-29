module

public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszIdentity
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

/-! The `ns`-shell generalization of `HeatVHEATBracketMeanRieszIdentity`. -/

@[expose] public section

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ProbabilityTheory
open scoped RealInnerProductSpace Topology

namespace ASDExplicitGamma.Native

noncomputable section

variable (ns : ℕ) [NeZero ns]

/-- The fixed-shell squared gradient of the actual child mean, composed with
the pure centered remainder, is exactly the squared norm of the normalized
average of the physical child remainder-observation Riesz vectors. -/
theorem nativeHeatQ3RefinedCarrierMeanRemainderGradient_eq_averageRiesz_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (d : Fin ns) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    modelGradientSquareTrace
      (nativeHeatQ3RefinedCarrierMeanTrace M m σ hσ)
      (fun j => nativeHeatQ3RefinedCarrierRemainderMap m
        ((nativeHeatQ3RefinedCarrierFreshShellVectorGen ns) M h hM m Ffam d j)) x =
      ‖((Finset.univ : Finset (Fin (3 ^ 10) × Fin (3 ^ 10))).card : ℝ)⁻¹ •
        ∑ ij : Fin (3 ^ 10) × Fin (3 ^ 10),
          (InnerProductSpace.toDual ℝ WhiteNoise).symm
            ((nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
              M h m d σ x (finProdFinEquiv ij))‖ ^ 2 := by
  classical
  let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
    fun i => nativeHeatQ3RefinedCarrierChild m i
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
  let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
  let hvol : ∀ i, 0 < (volume (U i)).toReal :=
    fun i => volume_cubeSet_toReal_pos (Q i)
  let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
  let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
    nativeHeatQ3RefinedCarrierChild_closure_subset m
  let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
  let R₀ := childRemainderMap V hV (nativeHeatQ3RefinedCarrierCenter m)
  let I := Fin (3 ^ 10) × Fin (3 ^ 10)
  let e : I ≃ nativeHeatQ3RefinedCarrierIndex := finProdFinEquiv
  let A := (fderiv ℝ μ x).comp R₀
  let r := nativeHeatQ3RefinedCarrierParentRestrict m
  let s : ℕ := d.val + 2
  let β := q3ModelAmplitude M h (m + (s : ℤ))
  let L := q3ModelLength (m + (s : ℤ))
  let p := (mainCubeH3Value (m + 10) β L).comp
    (q3H3RangeFactor (-mainCubeHalfSide (m + 10))
      (mainCubeHalfSide (m + 10)) (-mainCubeHalfSide (m + 10))
      (mainCubeHalfSide (m + 10)) β L)
  have hvar := (nativeHeatQ3RefinedCarrierParentObservationRiesz_eq_Gen' ns)
    M h hM m Ffam d A
  have hderivative' :=
    (nativeHeatQ3RefinedCarrierParentMeanDerivativeCLM_eq_remainderObservations_Gen ns)
      M h m d σ hσ x
  change (A.comp r).comp p =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ •
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          (nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
            M h m d σ x i at hderivative'
  have hcard : (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ) =
      ((Finset.univ : Finset I).card : ℝ) := by
    rw [Finset.card_univ]
    exact_mod_cast (Fintype.card_congr e).symm
  have hsumRiesz :
      (∑ i : nativeHeatQ3RefinedCarrierIndex,
        (InnerProductSpace.toDual ℝ WhiteNoise).symm
          ((nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
            M h m d σ x i)) =
        ∑ ij : I,
          (InnerProductSpace.toDual ℝ WhiteNoise).symm
            ((nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
              M h m d σ x (e ij)) := by
    exact (Equiv.sum_comp e (fun i : nativeHeatQ3RefinedCarrierIndex =>
      (InnerProductSpace.toDual ℝ WhiteNoise).symm
        ((nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
          M h m d σ x i))).symm
  have hRiesz :
      (InnerProductSpace.toDual ℝ WhiteNoise).symm ((A.comp r).comp p) =
        ((Finset.univ : Finset I).card : ℝ)⁻¹ •
          ∑ ij : I,
            (InnerProductSpace.toDual ℝ WhiteNoise).symm
              ((nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
                M h m d σ x (e ij)) := by
    calc
      _ = (InnerProductSpace.toDual ℝ WhiteNoise).symm
          ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ •
            ∑ i : nativeHeatQ3RefinedCarrierIndex,
              (nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
                M h m d σ x i) := by rw [hderivative']
      _ = (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ •
          ∑ i : nativeHeatQ3RefinedCarrierIndex,
            (InnerProductSpace.toDual ℝ WhiteNoise).symm
              ((nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
                M h m d σ x i) :=
        nativeHeatQ3WhiteNoiseRiesz_smul_sum _ _
      _ = _ := by rw [hcard, hsumRiesz]
  change (∑' j,
      ((fderiv ℝ μ x) (R₀ (Ffam.factor d (Ffam.direction d j)))) ^ 2) = _
  calc
    _ = ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
        ((A.comp r).comp p)‖ ^ 2 := hvar
    _ = _ := by rw [hRiesz]

end

end ASDExplicitGamma.Native

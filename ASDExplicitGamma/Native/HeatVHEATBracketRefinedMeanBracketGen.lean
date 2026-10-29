module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanBracket
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
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanRieszIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanAverageProfilesGen

/-! The `ns`-shell generalization of `HeatVHEATBracketRefinedMeanBracket`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped RealInnerProductSpace Topology

variable (ns : ℕ) [NeZero ns]

/-- The global mean-gradient bracket for one actual refined common shell. -/
theorem nativeHeatQ3RefinedCarrierMeanRemainderBracket_le_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (d : Fin ns) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
      fun i => nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
      fun i => cubeSet (Q i)
    let hU : ∀ i, MeasurableSet (U i) :=
      fun i => measurableSet_cubeSet (Q i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal :=
      fun i => volume_cubeSet_toReal_pos (Q i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
      fun i => closure (U i)
    let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
      nativeHeatQ3RefinedCarrierChild_closure_subset m
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let R₀ := childRemainderMap V hV
      (nativeHeatQ3RefinedCarrierCenter m)
    let s : ℕ := d.val + 2
    let L := q3ModelLength (m + (s : ℤ))
    let profile : nativeHeatQ3RefinedCarrierIndex → ℝ := fun i =>
      let Q := nativeHeatQ3RefinedCarrierChild m i
      let A := nativeHeat_translateTriadicFieldToOrigin Q
      let k := pureFluxOpenResponseRestriction Q.scale (A (x i))
      let B := lemmaVTileHistory (originCube 2 Q.scale) (pureFluxBankSourceDepth s)
        (responseFramePlanarCoefficientField M.nu σ k)
      let T := modelTraceObservable Q.scale M.nu σ (A (x i))
      B ^ 2 * T * (T + 4)
    modelGradientSquareTrace μ
      (fun j => R₀ (Ffam.factor d (Ffam.direction d j))) x ≤
      4 * (q3ModelAmplitude M h (m + (s : ℤ)) ^ 2 / σ ^ 2) *
        q3GridOverlapFactor 10 s *
        (lemmaVH2Bn
          (cubeScaleFactor (originCube 2 m) / L.1)
          (diagMeshRadius (originCube 2 m) (pureFluxBankSourceDepth s) / L.1)) ^ 2 *
        ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
          ∑ i, profile i) := by
  calc
    _ = _ := (nativeHeatQ3RefinedCarrierMeanRieszAverageIdentity_Gen ns)
      M h hM m Ffam d σ hσ x
    _ ≤ _ := (nativeHeatQ3RefinedCarrierMeanRieszAverage_sq_le_profiles_Gen ns)
      M h hM m Ffam d σ hσ x

end ASDExplicitGamma.Native

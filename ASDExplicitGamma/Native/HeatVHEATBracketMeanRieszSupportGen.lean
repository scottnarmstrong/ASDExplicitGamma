module

public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszSupport
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

/-! The `ns`-shell generalization of `HeatVHEATBracketMeanRieszSupport`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

noncomputable section

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ProbabilityTheory
open scoped RealInnerProductSpace Topology

variable (ns : ℕ) [NeZero ns]

noncomputable def nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (d : Fin ns) (σ : ℝ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ))
    (i : nativeHeatQ3RefinedCarrierIndex) : WhiteNoise →L[ℝ] ℝ := by
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let s : ℕ := d.val + 2
  exact (nativeHeatQ3RefinedChildMeanTraceObservation M σ m x i).comp
    (q3RemainderValueFactor
      (cubeCorner Q 0) (cubeCorner Q 0 + cubeScaleFactor Q)
      (cubeCorner Q 1) (cubeCorner Q 1 + cubeScaleFactor Q)
      (q3ModelAmplitude M h (m + (s : ℤ)))
      (q3ModelLength (m + (s : ℤ)))
      ⟨cubeCenter Q,
        nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
          (subset_closure
            (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet Q))⟩)

/-- The normalized average of the actual child remainder-observation Riesz
vectors, indexed symbolically by the Cartesian refined grid. -/
noncomputable def nativeHeatQ3RefinedCarrierMeanRieszAverageGen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (d : Fin ns) (σ : ℝ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) : WhiteNoise :=
  ((Finset.univ : Finset (Fin (3 ^ 10) × Fin (3 ^ 10))).card : ℝ)⁻¹ •
    ∑ ij : Fin (3 ^ 10) × Fin (3 ^ 10),
      (InnerProductSpace.toDual ℝ WhiteNoise).symm
        ((nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
          M h m d σ x (finProdFinEquiv ij))

/-- The actual fresh-shell vector sequence, named once so theorem statements
do not repeatedly elaborate the full carrier-family structure. -/
noncomputable def nativeHeatQ3RefinedCarrierFreshShellVectorGen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (d : Fin ns) : ℕ → C(nativeHeatQ3RefinedCarrierDomain m, ℝ) :=
  fun j => Ffam.factor d (Ffam.direction d j)

noncomputable def nativeHeatQ3RefinedCarrierParentSourceGen'
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (d : Fin ns) :
    WhiteNoise →L[ℝ]
      C(closure (cubeSet (originCube 2 (m + 10))), ℝ) := by
  let s : ℕ := d.val + 2
  let β := q3ModelAmplitude M h (m + (s : ℤ))
  let L := q3ModelLength (m + (s : ℤ))
  exact (mainCubeH3Value (m + 10) β L).comp
    (q3H3RangeFactor (-mainCubeHalfSide (m + 10))
      (mainCubeHalfSide (m + 10)) (-mainCubeHalfSide (m + 10))
      (mainCubeHalfSide (m + 10)) β L)

end

end ASDExplicitGamma.Native

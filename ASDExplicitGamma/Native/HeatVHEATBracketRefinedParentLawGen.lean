module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedParentLaw
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
import ASDExplicitGamma.Triadic.PoincareCell

/-! The `ns`-shell generalization of `HeatVHEATBracketRefinedParentLaw`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ProbabilityTheory
open scoped Topology

variable (ns : ℕ) [NeZero ns]

set_option linter.constructorNameAsVariable false in
/- Every depth-ten carrier child lies in the containing parent cube. -/

/-- The actual factor for one physical refined shell has the law of the
canonical q3 source field restricted from the parent cube. This is a joint
law on the whole carrier, so restrictions to different children keep their
actual common-noise correlations. -/
theorem nativeHeatQ3RefinedCarrierFreshShellParentLaw_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (d : Fin ns) :
    (standardGaussianInfinitePi.map
      (gaussianSeriesLimitE (Ffam.squareSummable d) (Ffam.factor d))) =
      (standardGaussianInfinitePi.map
        (mainCubeQ3Series (m + 10)
          (q3ModelAmplitude M h
            (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d))
          (q3ModelLength
            (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d)))).map
        (nativeHeatQ3RefinedCarrierParentRestrict m) := by
  classical
  let parent := closure (cubeSet (originCube 2 (m + 10)))
  let K := nativeHeatQ3RefinedCarrierDomain m
  let label := nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d
  let r := nativeHeatQ3RefinedCarrierParentRestrict m
  have hF := Ffam.law d
  have hparent : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction parent (ω.1 label)) =
      standardGaussianInfinitePi.map
        (mainCubeQ3Series (m + 10)
          (q3ModelAmplitude M h label) (q3ModelLength label)) := by
    simpa [parent, label, Int.sub_add_cancel] using
      (main_actual_fresh_cube_factor_law (m + 10) M h hM (label - 1))
  have hparentK := congrArg (Measure.map r) hparent
  have hm : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction parent (ω.1 label)) :=
    (measurable_shellFieldScalarRestriction parent).comp
      ((measurable_pi_apply label).comp measurable_subtype_coe)
  rw [Measure.map_map r.continuous.measurable hm] at hparentK
  have hsame : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        r (shellFieldScalarRestriction parent (ω.1 label))) =
      (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 =>
          shellFieldScalarRestriction K (ω.1 label)) := by
    congr 1
  change (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction K (ω.1 label)) = _ at hF
  dsimp only [label, K, r] at hF hparentK ⊢
  exact hF.symm.trans (hsame.symm.trans hparentK)

end ASDExplicitGamma.Native

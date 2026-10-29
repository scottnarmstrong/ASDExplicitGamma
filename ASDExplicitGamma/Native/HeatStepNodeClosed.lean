module

public import ASDExplicitGamma.Native.HeatStepAllTimeCap

/-! NA-REFINED-HEAT, closed: the main step without the all-time child-cap hypothesis. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal

/-- The all-time actual child cap of the refined heat step, proved from the states at `m+1` and
below. -/
theorem nativeHeatStep_childAllTime (ns : ℕ) (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m + 1, nativeInductionState M h j) :
    NativeHeatStepChildAllTimeCap M m ns (nativeHeatY0Gen ns : ℝ) := by
  have hfr := nativeHeatStepFrameNum_Gen ns hns9 hns160
  have hind := nativeHeatStepIndivNum_Gen ns hns9 hns160
  intro t ht
  exact nativeHeatStep_childAllTime_core ns hns9 hns160 hind hfr M h hM hg (m + 1 - 1) (m + 1)
    (by omega) (fun j hj => hpast j (by omega)) (hpast (m + 1 - 1) (by omega)) t ht

theorem nativeRefinedHeatStep_Gen_closed (ns : ℕ) [NeZero ns] (hns9 : 9 ≤ ns)
    (hns160 : ns ≤ 160) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m + 1, nativeInductionState M h j)
    (hstate : nativeInductionState M h (m + 1)) :
    eLpNorm (nativeHeatStepParentTrace M m ns) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (((nativeHeatResultGen ns).1 : ℚ) : ℝ) ∧
      ∫ ω, nativeHeatStepParentTrace M m ns ω ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        (((nativeHeatResultGen ns).2 : ℚ) : ℝ) :=
  nativeRefinedHeatStep_Gen ns hns9 hns160 M h hM hg m hpast hstate
    (nativeHeatStep_childAllTime ns hns9 hns160 M h hM hg m hpast)

end ASDExplicitGamma.Native

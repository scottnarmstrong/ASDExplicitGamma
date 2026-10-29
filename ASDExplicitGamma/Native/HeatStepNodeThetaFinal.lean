module

public import ASDExplicitGamma.Native.HeatStepNodeTheta
public import ASDExplicitGamma.Native.HeatInitialRefinedStartTheta
public import ASDExplicitGamma.Native.HeatStepNodeClosed
public import ASDExplicitGamma.Native.ReturnsY48TableTheta

/-! NA-REFINED-HEAT at smaller gamma: for `9 ≤ ns ≤ 160` the physical parent trace is bounded in
`L^20` by `θ · min(Y₄₈, y₀)` and in mean by `θ ·` the producer's mean return, for every
`0 < γ ≤ γ₀`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal

theorem nativeRefinedHeatStep_theta (ns : ℕ) [NeZero ns] (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m + 1, nativeInductionState M h j)
    (hstate : nativeInductionState M h (m + 1)) :
    eLpNorm (nativeHeatStepParentTrace M m ns) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (theta M * (((nativeHeatResultGen ns).1 : ℚ) : ℝ)) ∧
      ∫ ω, nativeHeatStepParentTrace M m ns ω ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        theta M * (((nativeHeatResultGen ns).2 : ℚ) : ℝ) := by
  have hk := nativeRefinedHeatStep_theta_of_start ns M h hM m hns9 hns160 hg hpast hstate
    (nativeHeatStep_curve_start_theta ns M h hM m hns9 hns160 hg hpast hstate)
  have h1 := nativeHeatResultGen_fst_eq_Y48 ns hns9 hns160
  have hmin : (nativeHeatResultGen ns).2 = nativeHeatMeanGen ns := rfl
  rw [h1, hmin]
  exact hk

end ASDExplicitGamma.Native

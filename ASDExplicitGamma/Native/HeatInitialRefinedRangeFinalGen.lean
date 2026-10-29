module

public import ASDExplicitGamma.Native.HeatInitialRefinedFinalGen
public import ASDExplicitGamma.Native.HeatInitialNumericsGen
public import ASDExplicitGamma.Numerics.Native.Heat009Initial

/-! The h-general refined start-time heat moment bound, for every shell count
`9 ≤ ns ≤ 160`, and its nine-shell specialization. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native

/-- NA-INITIAL-HEAT-MOMENTS, refined, for every `9 ≤ ns ≤ 160` inserted shells: at the
carrier's source start (scale-`m` cells, cutoff `m + 1`, frame `sigmaBar (m + 1)`,
shells `m + 2, …, m + 1 + ns`) every moment row through degree twenty is bounded by
the configured `initial` row built from `nativeHeatVariance ns` (old row of gap
`ns + 1`) and its Gaussian moment list. -/
theorem nativeHeatQ3RefinedCarrierSourceInitialMoment_gen
    (ns : ℕ) [NeZero ns] (hns : 9 ≤ ns) (hns' : ns ≤ 160)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hstate : nativeInductionState M h (m + 1))
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (k : ℕ) (hk20 : k ≤ 20) :
    nativeHeatQ3RefinedCarrierSourceMomentGen M m ns
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        k (nativeHeatTheta : ℝ) 0 ≤
      ((nativeHeatInitialAt nativeHeatParametersData
        (nativeGaussianMoments (nativeHeatVariance ns (nativeHeatOldRowGen ns)).1
          (nativeHeatVariance ns (nativeHeatOldRowGen ns)).2)
        (nativeHeatVariance ns (nativeHeatOldRowGen ns)).1 k : ℚ) : ℝ) := by
  have key := nativeHeatQ3RefinedCarrierSourceInitialMoment_of_numerics_Gen ns
    (nativeHeatGenNum_of_range ns hns hns') M h hM hg m
    (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns) hstate hpast k hk20
  rw [nativeHeatGenQm_eq] at key
  unfold nativeHeatGenVariance nativeHeatGenSpectral at key
  exact key

/-- The old row used for `9` shells is the accepted gap-`10` row. -/
theorem nativeHeatOldRowGen_nine : nativeHeatOldRowGen 9 = nativeGap010Old := by
  unfold nativeHeatOldRowGen
  rfl

/-- The `ns = 9` instance, for the Gaussian-series family of the nine-shell carrier, is the
accepted nine-shell refined start-time moment bound. -/
theorem nativeHeatQ3RefinedCarrierSourceInitialMoment_le_009_of_gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hstate : nativeInductionState M h (m + 1))
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (k : ℕ) (hk20 : k ≤ 20) :
    nativeHeatQ3RefinedCarrierSourceMoment M h hM m k (nativeHeatTheta : ℝ) 0 ≤
      ((nativeHeatInitialAt nativeHeatParametersData nativeHeat009Qm
        nativeHeat009Variance k : ℚ) : ℝ) := by
  have key := nativeHeatQ3RefinedCarrierSourceInitialMoment_of_numerics_Gen 9
    (nativeHeatGenNum_of_range 9 (by norm_num) (by norm_num)) M h hM hg m
    (nativeHeatQ3RefinedCarrierFreshShellFamilyGen_of M h hM m) hstate hpast k hk20
  rw [nativeHeatGenQm_eq] at key
  unfold nativeHeatGenVariance nativeHeatGenSpectral at key
  rw [nativeHeatOldRowGen_nine, nativeHeat009Variance_formula] at key
  rw [nativeHeat009Qm_formula] at key
  exact key

end ASDExplicitGamma.Native

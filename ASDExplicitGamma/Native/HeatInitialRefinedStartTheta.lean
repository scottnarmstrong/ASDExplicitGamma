module

public import ASDExplicitGamma.Native.HeatInitialRefinedAssemblyThetaPartD
public import ASDExplicitGamma.Native.HeatInitialRefinedFinalGen
public import ASDExplicitGamma.Native.HeatInitialNumericsGen
public import ASDExplicitGamma.Native.HeatStepCurves2

/-! The theta-scaled refined start-time heat moment bound, premise-free, for `9 ≤ ns ≤ 160`
shells: every moment row of degree `≤ 20` at heat time zero is at most `θ^k` times the configured
`initial` row, and the same for the pass-lemma curves. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native

theorem nativeHeatQ3RefinedCarrierSourceInitialMoment_of_numerics_Theta
    (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns)
    (hstate : nativeInductionState M h (m + 1))
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (k : ℕ) (hk20 : k ≤ 20) :
    nativeHeatQ3RefinedCarrierSourceMomentGen M m ns Ffam k (nativeHeatTheta : ℝ) 0 ≤
      theta M ^ k * ((nativeHeatInitialAt nativeHeatParametersData (nativeHeatGenQm ns)
        (nativeHeatGenVariance ns) k : ℚ) : ℝ) :=
  nativeHeatQ3RefinedCarrierSourceInitialMoment_of_providers_Theta ns hnum
    M h hM hg m Ffam hpast
    (fun j hj1 hj20 =>
      nativeHeatQ3RefinedCarrierSourceCenterQuadraticMoment_theta ns hnum
        M h hM hg m hstate j hj20)
    (fun j hj2 hj20 =>
      nativeHeatQ3RefinedCarrierSourceShearCrossMoment_theta ns hnum
        M h hM m hg hstate hpast j hj2 hj20)
    (fun j hj1 hj20 =>
      nativeHeatQ3RefinedCarrierSourceRareQuadraticMoment_le_009_depth4_Theta ns hnum
        M h hM m hg hstate hpast j hj1 hj20)
    k hk20

theorem nativeHeatStep_curve_start_theta (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m : ℤ) (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hg : M.gamma ≤ gammaZero) (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1)) :
    ∀ j ≤ 20, nativeHeatStepCurve ns M h hM m j 0 ≤
      theta M ^ j * ((nativeHeatInitGen ns).getD j 0 : ℚ) := by
  intro j hj
  by_cases h0 : j = 0
  · subst j
    simp [nativeHeatStepCurve, nativeHeatInitGen, nativeHeatInitial, nativeHeatInitialAt]
  · have key := nativeHeatQ3RefinedCarrierSourceInitialMoment_of_numerics_Theta ns
      (nativeHeatGenNum_of_range ns hns9 hns160) M h hM hg m
      (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns) hstate hpast j hj
    have hget : (nativeHeatInitGen ns).getD j 0 =
        nativeHeatInitialAt nativeHeatParametersData (nativeHeatGenQm ns)
          (nativeHeatGenVariance ns) j := by
      unfold nativeHeatInitGen nativeHeatInitial
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
    rw [hget, nativeHeatStep_curve_eq_moment ns M h hM m j h0]
    exact key

end ASDExplicitGamma.Native

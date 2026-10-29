module

public import ASDExplicitGamma.Native.HeatStepCurves
public import ASDExplicitGamma.Native.HeatVHEATSourceExpectationGen
public import ASDExplicitGamma.Native.HeatMomentBackwardPair
public import ASDExplicitGamma.Native.HeatMomentTransition
public import ASDExplicitGamma.Native.HeatMomentGreenKernel

/-! Integrability of the backward pairing derivative, the moment/average-norm identities on
`(0,1)` and the time-zero start row for the `ns`-shell curves. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal Topology

section Curves2

variable (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)

theorem nativeHeatStep_curve_eq_moment (j : ℕ) (h0 : j ≠ 0) :
    nativeHeatStepCurve ns M h hM m j = nativeHeatStepMoment ns M h hM m j := by
  funext t
  unfold nativeHeatStepCurve
  rw [if_neg h0]

theorem nativeHeatStep_curveDeriv_eq_generator (j : ℕ) (h0 : j ≠ 0) :
    nativeHeatStepCurveDeriv ns M h hM m j = nativeHeatStepGenerator ns M h hM m j := by
  funext t
  unfold nativeHeatStepCurveDeriv
  rw [if_neg h0]

theorem nativeHeatStep_curve_contOn (j : ℕ) (hj : j ≤ 20) :
    ContinuousOn (nativeHeatStepCurve ns M h hM m j) (Icc (0 : ℝ) 1) := by
  by_cases h0 : j = 0
  · subst j
    have : nativeHeatStepCurve ns M h hM m 0 = fun _ => (1 : ℝ) := by
      funext t; simp [nativeHeatStepCurve]
    rw [this]
    exact continuousOn_const
  · rw [nativeHeatStep_curve_eq_moment ns M h hM m j h0]
    exact (nativeHeatStep_regular ns M h hM m j (by omega)).1

theorem nativeHeatStep_curveDeriv_contOn (j : ℕ) (hj : j ≤ 20) :
    ContinuousOn (nativeHeatStepCurveDeriv ns M h hM m j) (Icc (0 : ℝ) 1) := by
  by_cases h0 : j = 0
  · subst j
    have : nativeHeatStepCurveDeriv ns M h hM m 0 = fun _ => (0 : ℝ) := by
      funext t; simp [nativeHeatStepCurveDeriv]
    rw [this]
    exact continuousOn_const
  · rw [nativeHeatStep_curveDeriv_eq_generator ns M h hM m j h0]
    exact (nativeHeatStep_regular ns M h hM m j (by omega)).2.1

theorem nativeHeatStep_curve_hasDerivAt :
    ∀ s ∈ Ioo (0 : ℝ) 1, ∀ j ≤ 20,
      HasDerivAt (nativeHeatStepCurve ns M h hM m j)
        (nativeHeatStepCurveDeriv ns M h hM m j s) s := by
  intro s hs j hj
  by_cases h0 : j = 0
  · subst j
    have e1 : nativeHeatStepCurve ns M h hM m 0 = fun _ => (1 : ℝ) := by
      funext t; simp [nativeHeatStepCurve]
    have e2 : nativeHeatStepCurveDeriv ns M h hM m 0 s = 0 := by
      simp [nativeHeatStepCurveDeriv]
    rw [e1, e2]
    exact hasDerivAt_const s (1 : ℝ)
  · rw [nativeHeatStep_curve_eq_moment ns M h hM m j h0,
      nativeHeatStep_curveDeriv_eq_generator ns M h hM m j h0]
    exact (nativeHeatStep_regular ns M h hM m j (by omega)).2.2 s hs

/-- The backward pairing derivative is continuous on `[0,1]`, hence interval integrable on
every `[0,T]`, `T ≤ 1`, for every top degree `k ≤ 20`. -/
theorem nativeHeatStep_curve_hint (c : ℝ) (k : ℕ) (hk : k ≤ 20) (T : ℝ)
    (hT : T ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (heatMomentBackwardDerivative c k T
      (nativeHeatStepCurve ns M h hM m) (nativeHeatStepCurveDeriv ns M h hM m))
      volume 0 T := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hT.1]
  have hsub : Icc (0 : ℝ) T ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hT.2
  unfold heatMomentBackwardDerivative
  apply continuousOn_finset_sum
  intro j hj
  have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
  have hj20 : j ≤ 20 := hjk.trans hk
  have hkern (a : ℕ) : Continuous (fun s : ℝ => heatMomentTransition c k a (T - s)) := by
    unfold heatMomentTransition heatMomentGreenKernel
    fun_prop
  have hm := (nativeHeatStep_curve_contOn ns M h hM m j hj20).mono hsub
  have hmp := (nativeHeatStep_curveDeriv_contOn ns M h hM m j hj20).mono hsub
  refine ContinuousOn.sub ?_ ?_
  · exact ((hkern j).continuousOn).mul hmp
  · refine ContinuousOn.mul ?_ hm
    exact (((continuous_const.mul (hkern j)).add
      (continuous_const.mul (hkern (j + 1)))).continuousOn)

/-- The start row of the curves. -/
theorem nativeHeatStep_curve_start (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hg : M.gamma ≤ gammaZero) (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1)) :
    ∀ j ≤ 20, nativeHeatStepCurve ns M h hM m j 0 ≤ ((nativeHeatInitGen ns).getD j 0 : ℚ) := by
  intro j hj
  by_cases h0 : j = 0
  · subst j
    simp [nativeHeatStepCurve, nativeHeatInitGen, nativeHeatInitial, nativeHeatInitialAt]
  · have key := nativeHeatQ3RefinedCarrierSourceInitialMoment_gen ns hns9 hns160 M h hM hg m
      hstate hpast j hj
    have hget : (nativeHeatInitGen ns).getD j 0 =
        nativeHeatInitialAt nativeHeatParametersData
          (nativeGaussianMoments (nativeHeatVariance ns (nativeHeatOldRowGen ns)).1
            (nativeHeatVariance ns (nativeHeatOldRowGen ns)).2)
          (nativeHeatVariance ns (nativeHeatOldRowGen ns)).1 j := by
      unfold nativeHeatInitGen nativeHeatInitial
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
      rw [nativeHeatGenQm_eq]
      unfold nativeHeatGenVariance nativeHeatGenSpectral
      rfl
    rw [hget, nativeHeatStep_curve_eq_moment ns M h hM m j h0]
    exact key

end Curves2

end ASDExplicitGamma.Native

end

module

public import ASDExplicitGamma.Native.HeatStepRows2
public import ASDExplicitGamma.Native.HeatFinitePasses
public import ASDExplicitGamma.Native.HeatPassBudget
public import ASDExplicitGamma.Numerics.Native.Heat009Passes

/-! The 48 finite passes and the first-moment (mean) bound for the `ns`-shell carrier: each
pass improves the uniform average cap by the rows of `HeatStepRows2` at the previous cap;
no fixed point is assumed. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ProbabilityTheory
open scoped ENNReal Topology

section Passes

variable (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)

/-- A cap on the average norm on `(0,1)` is a uniform twentieth-moment cap on `[0,1]`. -/
theorem nativeHeatStep_cap_of_avgNorm (hns : ns ≤ 1331) (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l) (y : ℚ) (hy : 0 ≤ y)
    (hA : ∀ t ∈ Ioo (0 : ℝ) 1,
      (nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t ≤ (y : ℝ)) :
    HeatUniformMomentCap (nativeHeatStepCurve ns M h hM m) y := by
  refine ⟨hy, ?_⟩
  have hcont := nativeHeatStep_curve_contOn ns M h hM m 20 le_rfl
  have hopen : ∀ t ∈ Ioo (0 : ℝ) 1,
      nativeHeatStepCurve ns M h hM m 20 t ≤ (fun _ : ℝ => (y : ℝ) ^ 20) t := by
    intro t ht
    rw [nativeHeatStep_curve_eq_moment ns M h hM m 20 (by norm_num)]
    exact nativeHeatStep_moment_le_of_avgNorm_le ns M h hM m hns hg hpast t ht (y : ℝ) (hA t ht)
  exact nativeHeatStep_le_on_Icc_of_Ioo hcont continuousOn_const hopen

/-- The rows hold at every cap already proved. -/
theorem nativeHeatStep_passes_cap (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hnum : NativeHeatStepPassNum ns) (hgen : NativeHeatGenNum ns)
    (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (hX : ∀ t ∈ Ioo (0 : ℝ) 1,
      ((heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t
        (nativeHeatStepAux ns M h hM m t)).toReal ≤ ((nativeHeatFramesGen ns).x : ℝ))
    (hF : ∀ t ∈ Ioo (0 : ℝ) 1,
      heatRefinedRawEnvelope ns
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
            (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
            (nativeHeatTheta : ℝ) t)) ≤ ((nativeHeatFramesGen ns).raw : ℝ))
    (hY0 : HeatUniformMomentCap (nativeHeatStepCurve ns M h hM m) (nativeHeatFramesGen ns).y) :
    HeatUniformMomentCap (nativeHeatStepCurve ns M h hM m) (nativeHeatY48Gen ns) := by
  have hns1331 : ns ≤ 1331 := by omega
  have hfixedlen : (nativeHeatInitGen ns).length = 21 := by
    simp [nativeHeatInitGen, nativeHeatInitial]
  have key := heat_finite_passes_uniform_cap (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
    (nativeHeatFixedGen ns) (nativeHeatInitGen ns) (nativeHeatFramesGen ns).y
    (nativeHeatExpArgGen ns) (nativeHeatExpGen ns) 48 hnum.c_nonneg hnum.exp_check
    hnum.old_e_nonneg hnum.x_pos.le hnum.fixed_nonneg hfixedlen hnum.init_nonneg
    (nativeHeatStepCurve ns M h hM m) (nativeHeatStepCurveDeriv ns M h hM m) hY0
    (fun j hj => nativeHeatStep_curve_contOn ns M h hM m j hj)
    (nativeHeatStep_curve_hasDerivAt ns M h hM m)
    (fun T hT => nativeHeatStep_curve_hint ns M h hM m _ 20 le_rfl T hT)
    (nativeHeatStep_curve_start ns M h hM m hns9 hns160 hg hpast hstate)
    (by
      intro y hy _ s hs j hj
      refine nativeHeatStep_row ns M h hM m hns9 hns160 hnum hgen hg hpast hstate hX hF y hy.1
        (fun t ht => hy.2 t ⟨ht.1.le, ht.2.le⟩) s hs j hj)
    (fun n hn => hnum.pass_roots n hn)
  exact key

omit [NeZero ns] in
/-- At every nonnegative cap the first forcing row is the first fixed row. -/
theorem nativeHeatStep_forcing_one (y : ℚ) :
    nativeHeatForcingAt (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
      (nativeHeatFixedGen ns) y 1 = (nativeHeatFixedGen ns).getD 0 0 := by
  have h1 := nativeHeatFixedGen_getD ns 1 le_rfl (by norm_num)
  simp only [Nat.sub_self] at h1
  rw [h1]
  simp only [nativeHeatForcingAt, show ¬ (1 ≥ 2) by norm_num, if_false]
  rw [h1, nativeHeatFixedAt_eq_explicit_remainder]
  exact nativeUp_idem _

/-- The first moment at time one: the producer's mean return. -/
theorem nativeHeatStep_mean (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hnum : NativeHeatStepPassNum ns) (hgen : NativeHeatGenNum ns)
    (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (hX : ∀ t ∈ Ioo (0 : ℝ) 1,
      ((heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t
        (nativeHeatStepAux ns M h hM m t)).toReal ≤ ((nativeHeatFramesGen ns).x : ℝ))
    (hF : ∀ t ∈ Ioo (0 : ℝ) 1,
      heatRefinedRawEnvelope ns
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
            (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
            (nativeHeatTheta : ℝ) t)) ≤ ((nativeHeatFramesGen ns).raw : ℝ))
    (hY48 : HeatUniformMomentCap (nativeHeatStepCurve ns M h hM m) (nativeHeatY48Gen ns)) :
    nativeHeatStepMoment ns M h hM m 1 1 ≤ (nativeHeatMeanGen ns : ℝ) := by
  classical
  set c : ℝ := (nativeHeatExpArgGen ns : ℝ) with hc
  set y : ℚ := nativeHeatY48Gen ns with hy
  have hc0 : 0 ≤ c := Rat.cast_nonneg.mpr hnum.c_nonneg
  have hrow := nativeHeatStep_row ns M h hM m hns9 hns160 hnum hgen hg hpast hstate hX hF y
    hY48.1 (fun t ht => hY48.2 t ⟨ht.1.le, ht.2.le⟩)
  have hfix0 : ∀ j < 20, 0 ≤ (nativeHeatFixedGen ns).getD j 0 := hnum.fixed_nonneg
  have hE : ∀ j ≤ 1, 0 ≤ (if j = 0 then (0 : ℝ) else
      (nativeHeatForcingAt (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
        (nativeHeatFixedGen ns) y j : ℝ)) := by
    intro j hj
    by_cases hj0 : j = 0
    · simp [hj0]
    · rw [if_neg hj0]
      have := heat_pass_forcing_nonneg (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
        (nativeHeatFixedGen ns) y j hnum.old_e_nonneg hnum.x_pos.le hY48.1
        (hfix0 (j - 1) (by omega))
      exact_mod_cast this
  have hinitR : ∀ j ≤ 1, 0 ≤ ((nativeHeatInitGen ns).getD j 0 : ℝ) := by
    intro j hj
    exact_mod_cast hnum.init_nonneg j (by omega)
  have hstart := nativeHeatStep_curve_start ns M h hM m hns9 hns160 hg hpast hstate
  have hu := heat_moment_uniform_bound c hc0 1 1 (by norm_num) le_rfl
    (nativeHeatStepCurve ns M h hM m) (nativeHeatStepCurveDeriv ns M h hM m)
    (fun j => if j = 0 then (0 : ℝ) else
      (nativeHeatForcingAt (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
        (nativeHeatFixedGen ns) y j : ℝ))
    (fun j => ((nativeHeatInitGen ns).getD j 0 : ℝ))
    (fun j hj => (nativeHeatStep_curve_contOn ns M h hM m j (by omega)).mono
      (Icc_subset_Icc le_rfl le_rfl))
    (fun s hs j hj => nativeHeatStep_curve_hasDerivAt ns M h hM m s
      ⟨hs.1, hs.2⟩ j (by omega))
    (nativeHeatStep_curve_hint ns M h hM m c 1 (by norm_num) 1 ⟨by norm_num, le_rfl⟩)
    (fun s hs j hj => hrow s ⟨hs.1, hs.2⟩ j (by omega))
    (fun j hj => hstart j (by omega)) hinitR hE
  have hcurve1 : nativeHeatStepCurve ns M h hM m 1 1 =
      nativeHeatStepMoment ns M h hM m 1 1 := by
    rw [nativeHeatStep_curve_eq_moment ns M h hM m 1 (by norm_num)]
  rw [hcurve1] at hu
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    heatMomentTransition, heatMomentGreenKernel] at hu
  have hexp : Real.exp c ≤ (nativeHeatExpGen ns : ℝ) := nativeHeatExpCheck_sound hnum.exp_check
  have hi1 : 0 ≤ ((nativeHeatInitGen ns).getD 1 0 : ℝ) := hinitR 1 le_rfl
  have hf0 : 0 ≤ (((nativeHeatFixedGen ns).getD 0 0 : ℚ) : ℝ) := by
    exact_mod_cast hfix0 0 (by norm_num)
  have hinit0 : (nativeHeatInitGen ns).getD 0 0 = 1 := by
    simp [nativeHeatInitGen, nativeHeatInitial, nativeHeatInitialAt]
  rw [hinit0, nativeHeatStep_forcing_one] at hu
  have hmean : (nativeHeatExpGen ns * (nativeHeatInitGen ns).getD 1 0 +
      4 * (nativeHeatExpGen ns - 1) +
      nativeHeatExpGen ns * (nativeHeatFixedGen ns).getD 0 0 : ℚ) ≤
      nativeHeatMeanGen ns := nativeUp_ge _
  have hmeanR := (Rat.cast_le (K := ℝ)).2 hmean
  push_cast at hmeanR
  have e1 := mul_le_mul_of_nonneg_right hexp hi1
  have e2 := mul_le_mul_of_nonneg_right hexp hf0
  norm_num [List.getD_eq_getElem?_getD] at hu e1 e2 hmeanR
  linarith

end Passes

end ASDExplicitGamma.Native

end

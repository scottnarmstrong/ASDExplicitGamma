module

public import ASDExplicitGamma.Native.HeatStepThetaRow
public import ASDExplicitGamma.Native.HeatStepPasses

/-! The 48 passes and the mean bound for the theta-normalized curves of the `ns`-shell refined
heat step.  The start row and the caps `X`, `y₀` are the theta-scaled inputs. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ProbabilityTheory
open scoped ENNReal Topology

section ThetaPasses

variable (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)

theorem nativeHeatStep_curveN_contOn (hg : M.gamma ≤ gammaZero) (j : ℕ) (hj : j ≤ 20) :
    ContinuousOn (nativeHeatStepCurveN ns M h hM m j) (Icc (0 : ℝ) 1) := by
  unfold nativeHeatStepCurveN
  exact (nativeHeatStep_curve_contOn ns M h hM m j hj).div_const _

theorem nativeHeatStep_curveN_hasDerivAt :
    ∀ s ∈ Ioo (0 : ℝ) 1, ∀ j ≤ 20,
      HasDerivAt (nativeHeatStepCurveN ns M h hM m j)
        (nativeHeatStepCurveDerivN ns M h hM m j s) s := by
  intro s hs j hj
  unfold nativeHeatStepCurveN nativeHeatStepCurveDerivN
  exact (nativeHeatStep_curve_hasDerivAt ns M h hM m s hs j hj).div_const _

theorem nativeHeatStep_curveN_hint (hg : M.gamma ≤ gammaZero) (c : ℝ) (k : ℕ) (hk : k ≤ 20)
    (T : ℝ) (hT : T ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (heatMomentBackwardDerivative c k T
      (nativeHeatStepCurveN ns M h hM m) (nativeHeatStepCurveDerivN ns M h hM m))
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
  have hm := (nativeHeatStep_curveN_contOn ns M h hM m hg j hj20).mono hsub
  have hmp : ContinuousOn (nativeHeatStepCurveDerivN ns M h hM m j) (Icc (0 : ℝ) T) := by
    unfold nativeHeatStepCurveDerivN
    exact ((nativeHeatStep_curveDeriv_contOn ns M h hM m j hj20).div_const _).mono hsub
  refine ContinuousOn.sub ?_ ?_
  · exact ((hkern j).continuousOn).mul hmp
  · refine ContinuousOn.mul ?_ hm
    exact (((continuous_const.mul (hkern j)).add
      (continuous_const.mul (hkern (j + 1)))).continuousOn)

/-- A normalized uniform cap is a `θ`-scaled cap on the actual moment. -/
theorem nativeHeatStep_moment_le_of_curveN_cap (hg : M.gamma ≤ gammaZero) (y : ℚ)
    (hy : HeatUniformMomentCap (nativeHeatStepCurveN ns M h hM m) y) :
    ∀ t ∈ Ioo (0 : ℝ) 1, nativeHeatStepMoment ns M h hM m 20 t ≤ (theta M * (y : ℝ)) ^ 20 := by
  intro t ht
  obtain ⟨hθ0, _⟩ := theta_pos_le_one M hg
  have h1 := hy.2 t ⟨ht.1.le, ht.2.le⟩
  unfold nativeHeatStepCurveN at h1
  rw [div_le_iff₀ (pow_pos hθ0 20)] at h1
  rw [mul_pow, mul_comm]
  have e : nativeHeatStepCurve ns M h hM m 20 t = nativeHeatStepMoment ns M h hM m 20 t := by
    rw [nativeHeatStep_curve_eq_moment ns M h hM m 20 (by norm_num)]
  rw [e] at h1
  exact h1

/-- The theta-normalized finite passes: no fixed point assumed. -/
theorem nativeHeatStep_passesTheta_cap (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hnum : NativeHeatStepPassNum ns) (hgen : NativeHeatGenNum ns)
    (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (hX : ∀ t ∈ Ioo (0 : ℝ) 1,
      ((heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t
        (nativeHeatStepAux ns M h hM m t)).toReal ≤ theta M * ((nativeHeatFramesGen ns).x : ℝ))
    (hF : ∀ t ∈ Ioo (0 : ℝ) 1,
      heatRefinedRawEnvelope ns
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
            (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
            (nativeHeatTheta : ℝ) t)) ≤ ((nativeHeatFramesGen ns).raw : ℝ))
    (hstart : ∀ j ≤ 20, nativeHeatStepCurve ns M h hM m j 0 ≤
      theta M ^ j * ((nativeHeatInitGen ns).getD j 0 : ℚ))
    (hY0 : HeatUniformMomentCap (nativeHeatStepCurveN ns M h hM m)
      (nativeHeatFramesGen ns).y) :
    HeatUniformMomentCap (nativeHeatStepCurveN ns M h hM m) (nativeHeatY48Gen ns) := by
  obtain ⟨hθ0, hθ1⟩ := theta_pos_le_one M hg
  have hfixedlen : (nativeHeatInitGen ns).length = 21 := by
    simp [nativeHeatInitGen, nativeHeatInitial]
  refine heat_finite_passes_uniform_cap (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
    (nativeHeatFixedGen ns) (nativeHeatInitGen ns) (nativeHeatFramesGen ns).y
    (nativeHeatExpArgGen ns) (nativeHeatExpGen ns) 48 hnum.c_nonneg hnum.exp_check
    hnum.old_e_nonneg hnum.x_pos.le hnum.fixed_nonneg hfixedlen hnum.init_nonneg
    (nativeHeatStepCurveN ns M h hM m) (nativeHeatStepCurveDerivN ns M h hM m) hY0
    (fun j hj => nativeHeatStep_curveN_contOn ns M h hM m hg j hj)
    (nativeHeatStep_curveN_hasDerivAt ns M h hM m)
    (fun T hT => nativeHeatStep_curveN_hint ns M h hM m hg _ 20 le_rfl T hT)
    ?_ ?_ (fun n hn => hnum.pass_roots n hn)
  · intro j hj
    unfold nativeHeatStepCurveN
    rw [div_le_iff₀ (pow_pos hθ0 j), mul_comm]
    exact hstart j hj
  · intro y hy _ s hs j hj
    exact nativeHeatStep_rowTheta ns M h hM m hns9 hns160 hnum hgen hg hpast hstate hX hF y hy.1
      (nativeHeatStep_moment_le_of_curveN_cap ns M h hM m hg y hy) s hs j hj

/-- The normalized first moment at time one is below the producer's mean return. -/
theorem nativeHeatStep_meanTheta (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hnum : NativeHeatStepPassNum ns) (hgen : NativeHeatGenNum ns)
    (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (hX : ∀ t ∈ Ioo (0 : ℝ) 1,
      ((heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t
        (nativeHeatStepAux ns M h hM m t)).toReal ≤ theta M * ((nativeHeatFramesGen ns).x : ℝ))
    (hF : ∀ t ∈ Ioo (0 : ℝ) 1,
      heatRefinedRawEnvelope ns
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
            (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
            (nativeHeatTheta : ℝ) t)) ≤ ((nativeHeatFramesGen ns).raw : ℝ))
    (hstart : ∀ j ≤ 20, nativeHeatStepCurve ns M h hM m j 0 ≤
      theta M ^ j * ((nativeHeatInitGen ns).getD j 0 : ℚ))
    (hY48 : HeatUniformMomentCap (nativeHeatStepCurveN ns M h hM m) (nativeHeatY48Gen ns)) :
    nativeHeatStepCurveN ns M h hM m 1 1 ≤ (nativeHeatMeanGen ns : ℝ) := by
  classical
  obtain ⟨hθ0, hθ1⟩ := theta_pos_le_one M hg
  set c : ℝ := (nativeHeatExpArgGen ns : ℝ) with hc
  set y : ℚ := nativeHeatY48Gen ns with hy
  have hc0 : 0 ≤ c := Rat.cast_nonneg.mpr hnum.c_nonneg
  have hrow := nativeHeatStep_rowTheta ns M h hM m hns9 hns160 hnum hgen hg hpast hstate hX hF y
    hY48.1 (nativeHeatStep_moment_le_of_curveN_cap ns M h hM m hg y hY48)
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
  have hstartN : ∀ j ≤ 20, nativeHeatStepCurveN ns M h hM m j 0 ≤
      ((nativeHeatInitGen ns).getD j 0 : ℝ) := by
    intro j hj
    unfold nativeHeatStepCurveN
    rw [div_le_iff₀ (pow_pos hθ0 j), mul_comm]
    exact hstart j hj
  have hu := heat_moment_uniform_bound c hc0 1 1 (by norm_num) le_rfl
    (nativeHeatStepCurveN ns M h hM m) (nativeHeatStepCurveDerivN ns M h hM m)
    (fun j => if j = 0 then (0 : ℝ) else
      (nativeHeatForcingAt (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
        (nativeHeatFixedGen ns) y j : ℝ))
    (fun j => ((nativeHeatInitGen ns).getD j 0 : ℝ))
    (fun j hj => (nativeHeatStep_curveN_contOn ns M h hM m hg j (by omega)).mono
      (Icc_subset_Icc le_rfl le_rfl))
    (fun s hs j hj => nativeHeatStep_curveN_hasDerivAt ns M h hM m s
      ⟨hs.1, hs.2⟩ j (by omega))
    (nativeHeatStep_curveN_hint ns M h hM m hg c 1 (by norm_num) 1 ⟨by norm_num, le_rfl⟩)
    (fun s hs j hj => hrow s ⟨hs.1, hs.2⟩ j (by omega))
    (fun j hj => hstartN j (by omega)) hinitR hE
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

end ThetaPasses

end ASDExplicitGamma.Native

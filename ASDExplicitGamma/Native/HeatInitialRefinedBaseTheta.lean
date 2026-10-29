module

public import ASDExplicitGamma.Native.HeatInitialRefinedBase
public import ASDExplicitGamma.Native.HeatInitialRefinedChildCapTheta
public import ASDExplicitGamma.Native.HeatStepThetaRow

/-! Theta-scaled old average of the refined children at cutoff `m + 1`: child cap, mean, centered
`L^20` decay and moment table, all proportional to `θ`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal BigOperators

noncomputable section

local instance nativeHeatRefinedBaseThetaNeZero : NeZero (3 ^ 10 * 3 ^ 10) :=
  ⟨by norm_num⟩

/-- Each refined child trace has L20 norm at most `3` under the carrier law. -/
theorem nativeHeatRefinedCell_L20_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    MemLp (Cold.coldNativeCellTrace M (m + 1) (nativeHeatQ3RefinedCarrierChild m i)) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (Cold.coldNativeCellTrace M (m + 1)
        (nativeHeatQ3RefinedCarrierChild m i)) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ theta M * 3 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  have hroot := nativeRefinedChild_L20_le_theta M h hM hg (m + 1) hpast
  have e : (m + 1 - 1 : ℤ) = m := by ring
  rw [e] at hroot
  have hf : AEStronglyMeasurable (cutoffTraceDefect M (m + 1) m) μ :=
    (Variational.cutoffTraceDefect_measurable M (m + 1) m).aestronglyMeasurable
  have h20 : eLpNorm (cutoffTraceDefect M (m + 1) m) (20 : ℝ≥0∞) μ ≤ ENNReal.ofReal (theta M * 3) := by
    have : eLpNorm (cutoffTraceDefect M (m + 1) m) (20 : ℝ≥0∞) μ =
        eLpNorm' (cutoffTraceDefect M (m + 1) m) 20 μ := by
      simpa using (eLpNorm_eq_eLpNorm' (p := (20 : ℝ≥0∞)) (by norm_num) (by norm_num) hf)
    rw [this]
    exact hroot
  have hscale := nativeHeatQ3RefinedCarrierChild_scale m i
  have hid := Cold.coldNativeCellTrace_identDistrib M (m + 1)
    (nativeHeatQ3RefinedCarrierChild m i)
  rw [hscale] at hid
  have hEq := hid.eLpNorm_eq (p := 20)
  have hcell : eLpNorm (Cold.coldNativeCellTrace M (m + 1)
      (nativeHeatQ3RefinedCarrierChild m i)) 20 μ ≤ ENNReal.ofReal (theta M * 3) := by
    rw [hEq]; exact h20
  refine ⟨?_, ?_⟩
  · rw [memLp_iff]
    exact lt_of_le_of_lt hcell ENNReal.ofReal_lt_top
  · change (eLpNorm _ 20 μ).toReal ≤ theta M * 3
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcell
    rw [ENNReal.toReal_ofReal (mul_nonneg (theta_pos_le_one M hg).1.le (by norm_num))] at this
    exact this


/-- The completed q1 mean (the source AMEAN) bounds the refined old average. -/
theorem nativeHeatRefinedOldAverage_mean_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n) :
    Integrable (nativeHeatRefinedOldAverage M m)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      ∫ ω, nativeHeatRefinedOldAverage M m ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure =
        ∫ ω, cutoffTraceDefect M (m + 1) m ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ∧
      ∫ ω, cutoffTraceDefect M (m + 1) m ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ theta M * (nativeQstar : ℝ) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  have hint (i : nativeHeatQ3RefinedCarrierIndex) :
      Integrable (Cold.coldNativeCellTrace M (m + 1)
        (nativeHeatQ3RefinedCarrierChild m i)) μ :=
    Cold.coldNativeCellTrace_integrable M (m + 1) _
  have hmean (i : nativeHeatQ3RefinedCarrierIndex) :
      ∫ ω, Cold.coldNativeCellTrace M (m + 1)
        (nativeHeatQ3RefinedCarrierChild m i) ω ∂μ =
        ∫ ω, cutoffTraceDefect M (m + 1) m ω ∂μ := by
    rw [Cold.coldNativeCellTrace_integral, nativeHeatQ3RefinedCarrierChild_scale]
  have hAint : Integrable (nativeHeatRefinedOldAverage M m) μ := by
    unfold nativeHeatRefinedOldAverage
    exact (integrable_finset_sum _ fun i _ => hint i).const_mul _
  refine ⟨hAint, ?_, ?_⟩
  · unfold nativeHeatRefinedOldAverage
    rw [integral_const_mul, integral_finset_sum _ fun i _ => hint i]
    simp only [hmean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ) ≠ 0 := by
      have := Fintype.card_pos (α := nativeHeatQ3RefinedCarrierIndex)
      positivity
    field_simp
    rfl
  · have hq := native_completed_q1_integral_carried M h hM hg (m + 1) hpast
    have e : (m + 1 - 1 : ℤ) = m := by ring
    rw [e] at hq
    exact hq

/-- The centered refined old average has the sixteen-colour L20 decay, so its
L20 norm is within `1/1000` of the AMEAN cap. -/
theorem nativeHeatRefinedOldAverage_L20_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n) :
    MemLp (nativeHeatRefinedOldAverage M m) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (nativeHeatRefinedOldAverage M m) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ theta M * ((nativeQstar : ℝ) + 1 / 1000) := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let cell : nativeHeatQ3RefinedCarrierIndex → Cutoff.CutoffSample 2 → ℝ :=
    fun i => Cold.coldNativeCellTrace M (m + 1) (nativeHeatQ3RefinedCarrierChild m i)
  let mean : ℝ := ∫ ω, cutoffTraceDefect M (m + 1) m ω ∂μ
  let Y : nativeHeatQ3RefinedCarrierIndex → Cutoff.CutoffSample 2 → ℝ :=
    fun i ω => cell i ω - mean
  have hmeanq := (nativeHeatRefinedOldAverage_mean_theta M h hM hg m hpast).2.2
  have hcell := nativeHeatRefinedCell_L20_theta M h hM hg m hpast
  have hmeanNonneg : 0 ≤ mean :=
    integral_nonneg (fun ω => Variational.cutoffTraceDefect_nonneg M (m + 1) m ω)
  have hmean_i (i : nativeHeatQ3RefinedCarrierIndex) : ∫ ω, cell i ω ∂μ = mean := by
    change ∫ ω, Cold.coldNativeCellTrace M (m + 1)
      (nativeHeatQ3RefinedCarrierChild m i) ω ∂μ = _
    rw [Cold.coldNativeCellTrace_integral, nativeHeatQ3RefinedCarrierChild_scale]
  have hY (i : nativeHeatQ3RefinedCarrierIndex) : MemLp (Y i) 20 μ :=
    (hcell i).1.sub (memLp_const mean)
  have hzero (i : nativeHeatQ3RefinedCarrierIndex) : ∫ ω, Y i ω ∂μ = 0 := by
    change ∫ ω, cell i ω - mean ∂μ = 0
    rw [integral_sub ((hcell i).1.integrable (by norm_num)) (integrable_const _),
      integral_const, probReal_univ, one_smul, hmean_i i, sub_self]
  have hcap (i : nativeHeatQ3RefinedCarrierIndex) : lpNorm (Y i) 20 μ ≤ theta M * 3 := by
    have hh := Cold.lpNorm_sub_mean_le μ (by norm_num : (2 : ℝ) ≤ 20)
      (show MemLp (cell i) (ENNReal.ofReal 20) μ by simpa using (hcell i).1)
      (Filter.Eventually.of_forall (Cold.coldNativeCellTrace_nonneg M (m + 1) _))
    rw [hmean_i i] at hh
    have hh' : lpNorm (Y i) 20 μ ≤ lpNorm (cell i) 20 μ := by
      simpa only [ENNReal.ofReal_ofNat] using hh
    exact hh'.trans (hcell i).2
  have hInd := Cold.cold_refined_color_independent M h hM m
    (nativeHeatQ3RefinedCarrierChild m) (nativeHeatRefinedChild_injective m)
    (nativeHeatQ3RefinedCarrierChild_scale m) (X := Y)
    (fun i => (Cold.coldNativeCellTrace_local M (m + 1)
      (nativeHeatQ3RefinedCarrierChild m i)).sub_const mean)
  have hsum := Cold.color_twenty_centered_sum
    (fun i => Cold.coldRefinedColor (nativeHeatQ3RefinedCarrierChild m i))
    hY hInd hzero (mul_nonneg hτ0.le (by norm_num : (0 : ℝ) ≤ 3)) hcap
  have hn : Fintype.card nativeHeatQ3RefinedCarrierIndex ≠ 0 := Fintype.card_ne_zero
  have hN : (0 : ℝ) < Fintype.card nativeHeatQ3RefinedCarrierIndex :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hcenter : lpNorm (fun ω => nativeHeatRefinedOldAverage M m ω - mean) 20 μ ≤
      theta M * (1 / 1000) := by
    have he : (fun ω => nativeHeatRefinedOldAverage M m ω - mean) =
        fun ω => (∑ i, Y i ω) / (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ) := by
      funext ω
      unfold nativeHeatRefinedOldAverage
      simp only [Y, cell, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      field_simp
    rw [he, lpNorm_fun_div_natCast hn]
    have hs : (fun ω => ∑ i, Y i ω) = ∑ i, Y i := by
      funext ω; simp only [Finset.sum_apply]
    rw [hs]
    have hc16 : Real.sqrt (Fintype.card (Fin 4 × Fin 4) : ℝ) = 4 := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [show ((4 * 4 : ℕ) : ℝ) = 4 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    have hcI : Real.sqrt (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ) = 3 ^ 10 := by
      rw [Fintype.card_fin]
      rw [show (((3 ^ 10 * 3 ^ 10 : ℕ)) : ℝ) = (3 ^ 10) ^ 2 by push_cast; ring]
      exact Real.sqrt_sq (by norm_num)
    rw [hc16, hcI] at hsum
    have hcard : (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ) = 3 ^ 10 * 3 ^ 10 := by
      rw [Fintype.card_fin]; push_cast; ring
    rw [div_le_iff₀ hN, hcard]
    have h19 : Real.sqrt 19 ≤ 44 / 10 := by
      apply Real.sqrt_le_iff.mpr; constructor <;> norm_num
    have hsq : 0 ≤ Real.sqrt 19 := Real.sqrt_nonneg _
    nlinarith [hsum, h19, hsq, mul_le_mul_of_nonneg_left h19 hτ0.le, mul_nonneg hτ0.le hsq]
  have hAmem : MemLp (nativeHeatRefinedOldAverage M m) 20 μ := by
    have h1 := (memLp_finsetSum' Finset.univ (fun i _ => (hcell i).1)).const_mul
      ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹)
    have e : (fun ω => (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        (∑ i, cell i) ω) = nativeHeatRefinedOldAverage M m := by
      funext ω
      simp [nativeHeatRefinedOldAverage, Finset.sum_apply, cell]
    rw [← e]
    exact h1
  refine ⟨hAmem, ?_⟩
  have hsumPi : (nativeHeatRefinedOldAverage M m - fun _ => mean) + (fun _ => mean) =
      nativeHeatRefinedOldAverage M m := by
    ext ω; simp
  have htri := lpNorm_add_le (hAmem.sub (memLp_const mean)) (g := fun _ => mean)
    (by norm_num : (1 : ℝ≥0∞) ≤ 20)
  rw [hsumPi] at htri
  rw [lpNorm_const' (by norm_num : (20 : ℝ≥0∞) ≠ 0)
    (by norm_num : (20 : ℝ≥0∞) ≠ ⊤)] at htri
  simp only [Real.norm_eq_abs, abs_of_nonneg hmeanNonneg, probReal_univ,
    Real.one_rpow, mul_one] at htri
  have hc' : lpNorm (nativeHeatRefinedOldAverage M m - fun _ => mean) 20 μ ≤ theta M * (1 / 1000) :=
    hcenter
  nlinarith [htri, hc', hmeanq]


end

end ASDExplicitGamma.Native

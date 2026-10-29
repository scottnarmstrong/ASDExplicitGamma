module

public import ASDExplicitGamma.Native.HeatInitialRefinedSplit
public import ASDExplicitGamma.Native.HeatInitialRefinedChildCap
public import ASDExplicitGamma.Native.HeatInitialRefinedColor
public import ASDExplicitGamma.Native.HeatInitialMoments
public import ASDExplicitGamma.Native.HeatFiniteBandCenters
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Native.HeatInitialProduct
public import ASDExplicitGamma.Native.OldSignedCompletedQ1

/-! The old average of the refined children at cutoff `m + 1`: its mean
(the source AMEAN, from the completed q1 row), its centered L20 decay, and
its moment table. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal BigOperators

noncomputable section

theorem nativeHeatRefinedChild_injective (m : ℤ) :
    Function.Injective (nativeHeatQ3RefinedCarrierChild m) := by
  intro i j hij
  have h1 := Triadic.diagMeshCell_injective (originCube 2 (m + 10)) 10 hij
  have h0 := congrFun h1 0
  have h1' := congrFun h1 1
  simp only [nativeHeatQ3RefinedChildDigits, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1'
  have : finProdFinEquiv.symm i = finProdFinEquiv.symm j := Prod.ext h0 h1'
  exact finProdFinEquiv.symm.injective this

/-- Each refined child trace has L20 norm at most `3` under the carrier law. -/
theorem nativeHeatRefinedCell_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    MemLp (Cold.coldNativeCellTrace M (m + 1) (nativeHeatQ3RefinedCarrierChild m i)) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (Cold.coldNativeCellTrace M (m + 1)
        (nativeHeatQ3RefinedCarrierChild m i)) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ 3 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  have hroot := nativeRefinedChild_L20_le M h hM hg (m + 1) hpast
  have e : (m + 1 - 1 : ℤ) = m := by ring
  rw [e] at hroot
  have hf : AEStronglyMeasurable (cutoffTraceDefect M (m + 1) m) μ :=
    (Variational.cutoffTraceDefect_measurable M (m + 1) m).aestronglyMeasurable
  have h20 : eLpNorm (cutoffTraceDefect M (m + 1) m) (20 : ℝ≥0∞) μ ≤ ENNReal.ofReal 3 := by
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
      (nativeHeatQ3RefinedCarrierChild m i)) 20 μ ≤ ENNReal.ofReal 3 := by
    rw [hEq]; exact h20
  refine ⟨?_, ?_⟩
  · rw [memLp_iff]
    exact lt_of_le_of_lt hcell ENNReal.ofReal_lt_top
  · change (eLpNorm _ 20 μ).toReal ≤ 3
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcell
    simpa using this


local instance nativeHeatRefinedBaseNeZero : NeZero (3 ^ 10 * 3 ^ 10) :=
  ⟨by norm_num⟩

theorem nativeHeatRefinedOldAverage_nonneg
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ nativeHeatRefinedOldAverage M m ω := by
  unfold nativeHeatRefinedOldAverage
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ =>
      Cold.coldNativeCellTrace_nonneg M (m + 1) _ ω)

theorem nativeHeatRefinedOldAverage_measurable
    (M : ABKModel 2) (m : ℤ) :
    Measurable (nativeHeatRefinedOldAverage M m) := by
  unfold nativeHeatRefinedOldAverage
  exact measurable_const.mul
    (Finset.measurable_sum _ fun i _ =>
      Cold.coldNativeCellTrace_measurable M (m + 1) _)

/-- The completed q1 mean (the source AMEAN) bounds the refined old average. -/
theorem nativeHeatRefinedOldAverage_mean
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
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ (nativeQstar : ℝ) := by
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
    have ht0 : 0 ≤ theta M := by
      rw [theta]; exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
    have ht1 : theta M ≤ 1 := by
      rw [theta]; exact (div_le_one₀ (by norm_num [gammaZero])).2 hg
    have hqs : (0 : ℝ) ≤ nativeQstar := by norm_num [nativeQstar]
    exact hq.trans (by nlinarith)


/-- The centered refined old average has the sixteen-colour L20 decay, so its
L20 norm is within `1/1000` of the AMEAN cap. -/
theorem nativeHeatRefinedOldAverage_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n) :
    MemLp (nativeHeatRefinedOldAverage M m) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (nativeHeatRefinedOldAverage M m) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ (nativeQstar : ℝ) + 1 / 1000 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let cell : nativeHeatQ3RefinedCarrierIndex → Cutoff.CutoffSample 2 → ℝ :=
    fun i => Cold.coldNativeCellTrace M (m + 1) (nativeHeatQ3RefinedCarrierChild m i)
  let mean : ℝ := ∫ ω, cutoffTraceDefect M (m + 1) m ω ∂μ
  let Y : nativeHeatQ3RefinedCarrierIndex → Cutoff.CutoffSample 2 → ℝ :=
    fun i ω => cell i ω - mean
  have hmeanq := (nativeHeatRefinedOldAverage_mean M h hM hg m hpast).2.2
  have hcell := nativeHeatRefinedCell_L20 M h hM hg m hpast
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
  have hcap (i : nativeHeatQ3RefinedCarrierIndex) : lpNorm (Y i) 20 μ ≤ 3 := by
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
    hY hInd hzero (by norm_num : (0 : ℝ) ≤ 3) hcap
  have hn : Fintype.card nativeHeatQ3RefinedCarrierIndex ≠ 0 := Fintype.card_ne_zero
  have hN : (0 : ℝ) < Fintype.card nativeHeatQ3RefinedCarrierIndex :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hcenter : lpNorm (fun ω => nativeHeatRefinedOldAverage M m ω - mean) 20 μ ≤
      1 / 1000 := by
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
    nlinarith [hsum, h19, hsq]
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
  have hc' : lpNorm (nativeHeatRefinedOldAverage M m - fun _ => mean) 20 μ ≤ 1 / 1000 :=
    hcenter
  linarith [htri, hc', hmeanq]


private theorem nativeHeatRefined_meanMoment_rat (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    (nativeQstar + 1 / 1000) ^ (20 * (k - 1)) * nativeQstar ^ (20 - k) ≤
      (nativeInitialMeanMoment nativeHeatParametersData k) ^ 19 := by
  interval_cases k <;> decide +kernel

/-- Every moment of the refined old average, through degree twenty, is bounded
by the configured native mean-moment row. -/
theorem nativeHeatRefinedOldAverage_moment_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (k : ℕ) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatRefinedOldAverage M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeInitialMeanMoment nativeHeatParametersData k : ℝ) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  by_cases hk0 : k = 0
  · subst k
    simp [nativeInitialMeanMoment]
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  let A := nativeHeatRefinedOldAverage M m
  have hmeas := nativeHeatRefinedOldAverage_measurable M m
  have hnonneg := nativeHeatRefinedOldAverage_nonneg M m
  obtain ⟨hmem, hlp⟩ := nativeHeatRefinedOldAverage_L20 M h hM hg m hpast
  obtain ⟨hint, hmeanEq, hmeanLe⟩ := nativeHeatRefinedOldAverage_mean M h hM hg m hpast
  have hq0 : (0 : ℝ) ≤ nativeQstar := by norm_num [nativeQstar]
  have h20 : eLpNorm A 20 μ ≤ ENNReal.ofReal ((nativeQstar : ℝ) + 1 / 1000) := by
    have hfin : eLpNorm A 20 μ ≠ ∞ := hmem.eLpNorm_ne_top
    have : ENNReal.ofReal (lpNorm A 20 μ) = eLpNorm A 20 μ :=
      ENNReal.ofReal_toReal hfin
    rw [← this]
    exact ENNReal.ofReal_le_ofReal hlp
  have hfirst : ∫⁻ ω, ‖A ω‖ₑ ∂μ ≤ ENNReal.ofReal (nativeQstar : ℝ) := by
    have e : ∫⁻ ω, ‖A ω‖ₑ ∂μ = ENNReal.ofReal (∫ ω, A ω ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnonneg)]
      apply lintegral_congr
      intro ω
      exact Real.enorm_eq_ofReal (hnonneg ω)
    rw [e]
    exact ENNReal.ofReal_le_ofReal (hmeanEq ▸ hmeanLe)
  have htable := lintegral_enorm_natPow_le_holder20_of_caps hmeas.aestronglyMeasurable
    k hk1 hk20 h20 hfirst
  refine htable.trans ?_
  set c : ℝ := (nativeQstar : ℝ) + 1 / 1000 with hc
  set q : ℝ := (nativeQstar : ℝ) with hq
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hα : 0 ≤ ((k : ℝ) - 1) / 19 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    exact div_nonneg (by linarith) (by norm_num)
  have hβ : 0 ≤ (20 - (k : ℝ)) / 19 := by
    have : (k : ℝ) ≤ 20 := by exact_mod_cast hk20
    exact div_nonneg (by linarith) (by norm_num)
  rw [ENNReal.ofReal_rpow_of_nonneg hc0 (by norm_num : (0 : ℝ) ≤ 20),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hc0 _) hα,
    ENNReal.ofReal_rpow_of_nonneg hq0 hβ,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_nonneg hc0 _) _)]
  apply ENNReal.ofReal_le_ofReal
  set R1 : ℝ := (c ^ (20 : ℝ)) ^ (((k : ℝ) - 1) / 19) * q ^ ((20 - (k : ℝ)) / 19) with hR1
  have hR10 : 0 ≤ R1 := by
    rw [hR1]; exact mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hc0 _) _)
      (Real.rpow_nonneg hq0 _)
  have hpow19 : R1 ^ 19 = (c ^ (20 * (k - 1))) * q ^ (20 - k) := by
    have hk1' : 1 ≤ k := hk1
    have c20 : c ^ (20 : ℝ) = c ^ (20 : ℕ) := by
      exact_mod_cast Real.rpow_natCast c 20
    have e1 : ((c ^ (20 : ℝ)) ^ (((k : ℝ) - 1) / 19)) ^ 19 = c ^ (20 * (k - 1)) := by
      rw [c20, ← Real.rpow_natCast, ← Real.rpow_mul (pow_nonneg hc0 20)]
      rw [show (((k : ℝ) - 1) / 19 * ((19 : ℕ) : ℝ)) = ((k - 1 : ℕ) : ℝ) by
        push_cast [Nat.cast_sub hk1']; ring]
      rw [Real.rpow_natCast, ← pow_mul]
    have e2 : (q ^ ((20 - (k : ℝ)) / 19)) ^ 19 = q ^ (20 - k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0]
      rw [show ((20 - (k : ℝ)) / 19 * ((19 : ℕ) : ℝ)) = ((20 - k : ℕ) : ℝ) by
        push_cast [Nat.cast_sub hk20]; ring]
      rw [Real.rpow_natCast]
    rw [hR1, mul_pow, e1, e2]
  have hrat := nativeHeatRefined_meanMoment_rat k hk1 hk20
  have hratR : c ^ (20 * (k - 1)) * q ^ (20 - k) ≤
      ((nativeInitialMeanMoment nativeHeatParametersData k : ℚ) : ℝ) ^ 19 := by
    have := (Rat.cast_le (K := ℝ)).2 hrat
    push_cast at this
    simpa [hc, hq] using this
  have h19 : R1 ^ 19 ≤ ((nativeInitialMeanMoment nativeHeatParametersData k : ℚ) : ℝ) ^ 19 := by
    rw [hpow19]; exact hratR
  have hodd : (0 : ℝ) ≤ ((nativeInitialMeanMoment nativeHeatParametersData k : ℚ) : ℝ) := by
    have h0 : (0 : ℝ) ≤ ((nativeInitialMeanMoment nativeHeatParametersData k : ℚ) : ℝ) ^ 19 :=
      le_trans (pow_nonneg hR10 19) h19
    exact (Odd.pow_nonneg_iff (by decide : Odd 19)).1 h0
  exact le_of_pow_le_pow_left₀ (by norm_num : (19 : ℕ) ≠ 0) hodd h19

end

end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.HeatInitialRefinedBaseTheta

/-! Theta-scaled moment table of the refined old average. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal BigOperators

noncomputable section

private theorem nativeHeatRefined_meanMomentTheta_rat (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    (nativeQstar + 1 / 1000) ^ (20 * (k - 1)) * nativeQstar ^ (20 - k) ≤
      (nativeInitialMeanMoment nativeHeatParametersData k) ^ 19 := by
  interval_cases k <;> decide +kernel

theorem nativeHeatRefined_meanMoment_of_caps {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A : Ω → ℝ} (hmeas : AEStronglyMeasurable A μ) (k : ℕ)
    (hk1 : 1 ≤ k) (hk20 : k ≤ 20)
    (h20 : eLpNorm A 20 μ ≤ ENNReal.ofReal ((nativeQstar : ℝ) + 1 / 1000))
    (hfirst : ∫⁻ ω, ‖A ω‖ₑ ∂μ ≤ ENNReal.ofReal (nativeQstar : ℝ)) :
    ∫⁻ ω, ‖A ω‖ₑ ^ (k : ℝ) ∂μ ≤
      ENNReal.ofReal (nativeInitialMeanMoment nativeHeatParametersData k : ℝ) := by
  have hq0 : (0 : ℝ) ≤ nativeQstar := by norm_num [nativeQstar]
  have htable := lintegral_enorm_natPow_le_holder20_of_caps hmeas
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
  have hrat := nativeHeatRefined_meanMomentTheta_rat k hk1 hk20
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


/-- Every moment of the refined old average is below `θ^k` times the configured native
mean-moment row. -/
theorem nativeHeatRefinedOldAverage_moment_le_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (k : ℕ) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatRefinedOldAverage M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M ^ k * (nativeInitialMeanMoment nativeHeatParametersData k : ℝ)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  by_cases hk0 : k = 0
  · subst k
    simp [nativeInitialMeanMoment]
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  let A := nativeHeatRefinedOldAverage M m
  have hmeas := nativeHeatRefinedOldAverage_measurable M m
  have hnonneg := nativeHeatRefinedOldAverage_nonneg M m
  obtain ⟨hmem, hlp⟩ := nativeHeatRefinedOldAverage_L20_theta M h hM hg m hpast
  obtain ⟨hint, hmeanEq, hmeanLe⟩ := nativeHeatRefinedOldAverage_mean_theta M h hM hg m hpast
  have hq0 : (0 : ℝ) ≤ nativeQstar := by norm_num [nativeQstar]
  have h20 : eLpNorm A 20 μ ≤ ENNReal.ofReal (theta M * ((nativeQstar : ℝ) + 1 / 1000)) := by
    have hfin : eLpNorm A 20 μ ≠ ∞ := hmem.eLpNorm_ne_top
    have : ENNReal.ofReal (lpNorm A 20 μ) = eLpNorm A 20 μ :=
      ENNReal.ofReal_toReal hfin
    rw [← this]
    exact ENNReal.ofReal_le_ofReal hlp
  have hfirst : ∫⁻ ω, ‖A ω‖ₑ ∂μ ≤ ENNReal.ofReal (theta M * (nativeQstar : ℝ)) := by
    have e : ∫⁻ ω, ‖A ω‖ₑ ∂μ = ENNReal.ofReal (∫ ω, A ω ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnonneg)]
      apply lintegral_congr
      intro ω
      exact Real.enorm_eq_ofReal (hnonneg ω)
    rw [e]
    exact ENNReal.ofReal_le_ofReal (hmeanEq ▸ hmeanLe)
  -- normalize by `θ`
  have hτ0' : 0 ≤ theta M := hτ0.le
  let g : Cutoff.CutoffSample 2 → ℝ := (theta M)⁻¹ • A
  have hg : AEStronglyMeasurable g μ := hmeas.aestronglyMeasurable.const_smul (theta M)⁻¹
  have hfg : A = theta M • g := by
    funext ω; simp [g, hτ0.ne']
  have hfactor : ENNReal.ofReal (theta M) ≠ 0 := (ENNReal.ofReal_pos.mpr hτ0).ne'
  have hrootScale : eLpNorm A 20 μ = ENNReal.ofReal (theta M) * eLpNorm g 20 μ := by
    conv_lhs => rw [hfg]
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hτ0']
  have h20g : eLpNorm g 20 μ ≤ ENNReal.ofReal ((nativeQstar : ℝ) + 1 / 1000) := by
    apply (ENNReal.mul_le_mul_iff_right hfactor ENNReal.ofReal_ne_top).mp
    calc ENNReal.ofReal (theta M) * eLpNorm g 20 μ = eLpNorm A 20 μ := hrootScale.symm
      _ ≤ ENNReal.ofReal (theta M * ((nativeQstar : ℝ) + 1 / 1000)) := h20
      _ = ENNReal.ofReal (theta M) * ENNReal.ofReal ((nativeQstar : ℝ) + 1 / 1000) :=
        ENNReal.ofReal_mul hτ0'
  have hfirstScale : ∫⁻ ω, ‖A ω‖ₑ ∂μ = ENNReal.ofReal (theta M) * ∫⁻ ω, ‖g ω‖ₑ ∂μ := by
    calc _ = ∫⁻ ω, ‖g ω‖ₑ * ENNReal.ofReal (theta M) ∂μ := by
          apply lintegral_congr; intro ω
          rw [show A ω = (theta M • g) ω by rw [← hfg], Pi.smul_apply, enorm_smul,
            Real.enorm_eq_ofReal hτ0', mul_comm]
      _ = (∫⁻ ω, ‖g ω‖ₑ ∂μ) * ENNReal.ofReal (theta M) := lintegral_mul_const'' _ (hg.enorm)
      _ = _ := by rw [mul_comm]
  have hfirstg : ∫⁻ ω, ‖g ω‖ₑ ∂μ ≤ ENNReal.ofReal (nativeQstar : ℝ) := by
    apply (ENNReal.mul_le_mul_iff_right hfactor ENNReal.ofReal_ne_top).mp
    calc ENNReal.ofReal (theta M) * ∫⁻ ω, ‖g ω‖ₑ ∂μ = ∫⁻ ω, ‖A ω‖ₑ ∂μ := hfirstScale.symm
      _ ≤ ENNReal.ofReal (theta M * (nativeQstar : ℝ)) := hfirst
      _ = ENNReal.ofReal (theta M) * ENNReal.ofReal (nativeQstar : ℝ) :=
        ENNReal.ofReal_mul hτ0'
  have hgm := nativeHeatRefined_meanMoment_of_caps hg k hk1 hk20 h20g hfirstg
  have hmomentScale : (∫⁻ ω, ‖A ω‖ₑ ^ (k : ℝ) ∂μ) =
      ENNReal.ofReal (theta M) ^ k * ∫⁻ ω, ‖g ω‖ₑ ^ (k : ℝ) ∂μ := by
    calc _ = ∫⁻ ω, ENNReal.ofReal (theta M) ^ k * ‖g ω‖ₑ ^ (k : ℝ) ∂μ := by
          apply lintegral_congr; intro ω
          calc _ = (ENNReal.ofReal (theta M) * ‖g ω‖ₑ) ^ (k : ℝ) := by
                rw [show A ω = (theta M • g) ω by rw [← hfg], Pi.smul_apply, enorm_smul,
                  Real.enorm_eq_ofReal hτ0']
            _ = ENNReal.ofReal (theta M) ^ (k : ℝ) * ‖g ω‖ₑ ^ (k : ℝ) :=
                ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
            _ = _ := by rw [ENNReal.rpow_natCast]
      _ = _ := lintegral_const_mul'' _ (hg.enorm.pow_const (k : ℝ))
  rw [hmomentScale, ENNReal.ofReal_mul (pow_nonneg hτ0' k), ENNReal.ofReal_pow hτ0']
  exact mul_le_mul' le_rfl hgm

end

end ASDExplicitGamma.Native

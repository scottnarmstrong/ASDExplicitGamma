module

public import ASDExplicitGamma.Native.HeatRemainderControlHolder

/-! The bounded-bank part of the heat bracket retains the improved average
Lp envelope Y independently of the individual-trace envelope X. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

private theorem heat_norm_moment20 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) :
    (∫⁻ ω, ‖f ω‖ₑ ^ (20 : ℕ) ∂μ) = eLpNorm f 20 μ ^ (20 : ℕ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Holder bounds the baseline mixed bracket with the separate average and
individual envelopes. The total trace degree, rather than each exponent
separately, is required to be at most twenty. -/
theorem nativeHeat_trace_mixed_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A T : Ω → ℝ) (hA : AEStronglyMeasurable A μ) (hT : AEStronglyMeasurable T μ)
    (Y X : ℝ) (hY : 0 ≤ Y) (hX : 0 ≤ X)
    (hAcap : eLpNorm A 20 μ ≤ ENNReal.ofReal Y)
    (hTcap : eLpNorm T 20 μ ≤ ENNReal.ofReal X)
    (a b : ℕ) (hab : a + b ≤ 20) :
    (∫⁻ ω, ‖A ω‖ₑ ^ a * ‖T ω‖ₑ ^ b ∂μ) ≤ ENNReal.ofReal (Y ^ a * X ^ b) := by
  let u : Fin 3 → Ω → ℝ≥0∞ := ![fun ω => ‖A ω‖ₑ ^ (20 : ℕ),
    fun ω => ‖T ω‖ₑ ^ (20 : ℕ), fun _ => 1]
  let w : Fin 3 → ℝ := ![(a : ℝ) / 20, (b : ℝ) / 20, 1 - (a : ℝ) / 20 - (b : ℝ) / 20]
  have habR : (a : ℝ) + (b : ℝ) ≤ 20 := by exact_mod_cast hab
  have hw : ∑ i : Fin 3, w i = 1 := by simp [w, Fin.sum_univ_three]
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i hi
    fin_cases i
    · dsimp [w]; positivity
    · dsimp [w]; positivity
    · dsimp [w]; linarith
  have hu : ∀ i ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable (u i) μ := by
    intro i hi
    fin_cases i
    · exact hA.enorm.pow_const _
    · exact hT.enorm.pow_const _
    · exact aemeasurable_const
  have hh := ENNReal.lintegral_prod_norm_pow_le Finset.univ hu hw hw0
  simp only [Fin.prod_univ_three] at hh
  change (∫⁻ ω, (‖A ω‖ₑ ^ (20 : ℕ)) ^ ((a : ℝ) / 20) *
      (‖T ω‖ₑ ^ (20 : ℕ)) ^ ((b : ℝ) / 20) *
      1 ^ (1 - (a : ℝ) / 20 - (b : ℝ) / 20) ∂μ) ≤
    (∫⁻ ω, ‖A ω‖ₑ ^ (20 : ℕ) ∂μ) ^ ((a : ℝ) / 20) *
      (∫⁻ ω, ‖T ω‖ₑ ^ (20 : ℕ) ∂μ) ^ ((b : ℝ) / 20) *
      (∫⁻ _ : Ω, 1 ∂μ) ^ (1 - (a : ℝ) / 20 - (b : ℝ) / 20) at hh
  have he (x : ℝ≥0∞) (j : ℕ) : (x ^ (20 : ℕ)) ^ ((j : ℝ) / 20) = x ^ j := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num only [Nat.cast_ofNat]
    rw [mul_div_cancel₀ _ (by norm_num : (20 : ℝ) ≠ 0), ENNReal.rpow_natCast]
  simp only [ENNReal.one_rpow, mul_one, lintegral_const, measure_univ, mul_one, he] at hh
  rw [heat_norm_moment20 μ A hA, heat_norm_moment20 μ T hT] at hh
  simp only [he] at hh
  exact hh.trans (by
    calc
      eLpNorm A 20 μ ^ a * eLpNorm T 20 μ ^ b ≤
          ENNReal.ofReal Y ^ a * ENNReal.ofReal X ^ b :=
        mul_le_mul' (pow_le_pow_left' hAcap a) (pow_le_pow_left' hTcap b)
      _ = ENNReal.ofReal (Y ^ a * X ^ b) := by
        rw [← ENNReal.ofReal_pow hY, ← ENNReal.ofReal_pow hX,
          ENNReal.ofReal_mul (pow_nonneg hY a)])

/-- The bounded part of the VHEAT bracket in real integral form, with genuine
integrability and no independence assumption. In the recurrence use
`a=k-2`, and `b=1` or `b=2`. -/
theorem nativeHeat_trace_mixed_product
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A T : Ω → ℝ) (hA : AEStronglyMeasurable A μ) (hT : AEStronglyMeasurable T μ)
    (hA0 : ∀ ω, 0 ≤ A ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (Y X : ℝ) (hY : 0 ≤ Y) (hX : 0 ≤ X)
    (hAcap : eLpNorm A 20 μ ≤ ENNReal.ofReal Y)
    (hTcap : eLpNorm T 20 μ ≤ ENNReal.ofReal X)
    (a b : ℕ) (hab : a + b ≤ 20) :
    Integrable (fun ω => A ω ^ a * T ω ^ b) μ ∧
      (∫ ω, A ω ^ a * T ω ^ b ∂μ) ≤ Y ^ a * X ^ b := by
  have hn := nativeHeat_trace_mixed_lintegral μ A T hA hT Y X hY hX hAcap hTcap a b hab
  have he (ω : Ω) : ENNReal.ofReal (A ω ^ a * T ω ^ b) = ‖A ω‖ₑ ^ a * ‖T ω‖ₑ ^ b := by
    rw [ENNReal.ofReal_mul (pow_nonneg (hA0 ω) a), ENNReal.ofReal_pow (hA0 ω),
      ENNReal.ofReal_pow (hT0 ω), Real.enorm_eq_ofReal (hA0 ω), Real.enorm_eq_ofReal (hT0 ω)]
  have hsm : AEStronglyMeasurable (fun ω => A ω ^ a * T ω ^ b) μ := (hA.pow a).mul (hT.pow b)
  have hnn (ω : Ω) : 0 ≤ A ω ^ a * T ω ^ b := mul_nonneg (pow_nonneg (hA0 ω) a) (pow_nonneg (hT0 ω) b)
  have hn' : (∫⁻ ω, ENNReal.ofReal (A ω ^ a * T ω ^ b) ∂μ) ≤ ENNReal.ofReal (Y ^ a * X ^ b) := by
    simpa only [he] using hn
  have hmem : MemLp (fun ω => A ω ^ a * T ω ^ b) 1 μ := by
    rw [memLp_iff, eLpNorm_one_eq_lintegral_enorm hsm]
    simp only [Real.enorm_eq_ofReal (hnn _)]
    exact lt_of_le_of_lt hn' ENNReal.ofReal_lt_top
  refine ⟨memLp_one_iff_integrable.mp hmem, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all μ hnn) hsm]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hn').trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hY a) (pow_nonneg hX b)))

end
end ASDExplicitGamma.Native

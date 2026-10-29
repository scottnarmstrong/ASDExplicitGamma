module

public import ASDExplicitGamma.Inverse.StoppedRareMomentLayerBound

/-! Exact rare moments derived from both tail envelopes before taking Lp norms. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- Layer cake for a positive integer moment, with its exact derivative kernel. -/
theorem nat_moment_layercake {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (X ω^(n+1)) ∂μ) =
      ∫⁻ u in Ioi 0, μ {ω | u < X ω}*ENNReal.ofReal ((n+1:ℝ)*u^n) := by
  have hc : Continuous (fun u : ℝ => (n+1:ℝ)*u^n) := continuous_const.mul (continuous_id.pow n)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] (fun u : ℝ => (n+1:ℝ)*u^n) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    exact mul_nonneg (by positivity) (pow_nonneg hu0.le n)
  have hh := lintegral_comp_eq_lintegral_meas_lt_mul μ (Filter.Eventually.of_forall hX0)
    hX.aemeasurable (fun t _ => hc.intervalIntegrable 0 t) hn
  simpa only [power_layer_kernel_interval] using! hh

/-- Exact source rare-moment bound a R_m(T), from the two tail envelopes
and B exp(-T/4)<=a. Integrability is a conclusion, including on the full space. -/
theorem nat_moment_of_two_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (n : ℕ) (a B T : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hcut : B*Real.exp (-T/4) ≤ a)
    (hrare : ∀ u > 0, μ.real {ω | u < X ω} ≤ a)
    (hexp : ∀ u > 0, μ.real {ω | u < X ω} ≤ B*Real.exp (-u/4)) :
    Integrable (fun ω => X ω^(n+1)) μ ∧
      (∫ ω, X ω^(n+1) ∂μ) ≤ a*rareMomentPolynomial (n+1) T := by
  have hP := rare_moment_polynomial_nonneg n T hT
  have hfactor : 0 ≤ (n+1:ℝ)*4*rareMomentPolynomial n T := by positivity
  have hpaid := mul_le_mul_of_nonneg_right hcut hfactor
  have halg : a*T^(n+1)+B*((n+1:ℝ)*4*rareMomentPolynomial n T*Real.exp (-T/4)) ≤
      a*rareMomentPolynomial (n+1) T := by
    simp only [rareMomentPolynomial]
    nlinarith only [hpaid]
  have hL := tail_moment_lintegral_bound (fun u => μ {ω | u < X ω}) n a B T ha hB hT
    (fun u hu => (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) ha).mpr (hrare u hu))
    (fun u hu => (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (mul_nonneg hB (Real.exp_pos _).le)).mpr (hexp u hu))
  have hb : (∫⁻ ω, ENNReal.ofReal (X ω^(n+1)) ∂μ) ≤
      ENNReal.ofReal (a*rareMomentPolynomial (n+1) T) := by
    rw [nat_moment_layercake μ X hX hX0 n]
    exact hL.trans (ENNReal.ofReal_le_ofReal halg)
  have hn (ω : Ω) : 0 ≤ X ω^(n+1) := pow_nonneg (hX0 ω) _
  have hi : Integrable (fun ω => X ω^(n+1)) μ := by
    refine ⟨(hX.pow_const (n+1)).aestronglyMeasurable,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hn)).mpr
      (hb.trans_lt ENNReal.ofReal_lt_top)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn),
    ENNReal.toReal_ofReal (integral_nonneg hn),
    ENNReal.toReal_ofReal (mul_nonneg ha (rare_moment_polynomial_nonneg (n+1) T hT))] at hr
  exact ⟨hi,hr⟩

end
end ASDExplicitGamma.Inverse

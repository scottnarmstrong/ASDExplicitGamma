module

public import ASDExplicitGamma.Model.SpectralGraphNorm
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

open MeasureTheory Filter Complex
open scoped Topology

namespace ASDExplicitGamma.Model

private theorem phase_hasDerivAt (a : ℝ) (z : ℂ) :
    HasDerivAt (fun t : ℝ => exp (((t * a : ℝ) : ℂ) * I) * z)
      (((a : ℂ) * I) * z) 0 := by
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 :=
    Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  have h := ((ht.mul_const (a : ℂ)).mul_const I).cexp.mul_const z
  simpa only [ofReal_mul, ofReal_zero, zero_mul, exp_zero, one_mul] using h

private theorem norm_phase_sub_one_le (s : ℝ) :
    ‖exp ((s : ℂ) * I) - 1‖ ≤ |s| := by
  rw [mul_comm (s : ℂ), norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |Real.sin (s / 2)| ≤ 2 * |s / 2| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |s| := by rw [abs_div]; norm_num; ring

private theorem norm_phase_slope_mul_le (a t : ℝ) (z : ℂ) :
    ‖t⁻¹ • ((exp (((t * a : ℝ) : ℂ) * I) - 1) * z)‖ ≤ |a| * ‖z‖ := by
  by_cases ht : t = 0
  · simp only [ht, inv_zero, zero_smul, norm_zero]
    exact mul_nonneg (abs_nonneg _) (norm_nonneg _)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, norm_mul]
  calc
    |t|⁻¹ * (‖exp (((t * a : ℝ) : ℂ) * I) - 1‖ * ‖z‖) ≤
        |t|⁻¹ * (|t * a| * ‖z‖) := by
      gcongr
      exact norm_phase_sub_one_le _
    _ = |a| * ‖z‖ := by
      rw [abs_mul]
      field_simp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem modulated_slope_coeFn
    (F : ℝ → Lp ℂ 2 μ) (f : Lp ℂ 2 μ) (a : α → ℝ)
    (hF : ∀ t, (F t : α → ℂ) =ᵐ[μ]
      fun x => exp (((t * a x : ℝ) : ℂ) * I) * f x) (t : ℝ) :
    (slope F 0 t : α → ℂ) =ᵐ[μ]
      fun x => t⁻¹ • ((exp (((t * a x : ℝ) : ℂ) * I) - 1) * f x) := by
  rw [slope_def_module, sub_zero]
  filter_upwards [Lp.coeFn_smul t⁻¹ (F t - F 0), Lp.coeFn_sub (F t) (F 0),
    hF t, hF 0] with x hs hd ht h0
  simp only [Pi.smul_apply] at hs
  simp only [Pi.sub_apply] at hd
  rw [hs, hd, ht, h0]
  simp only [zero_mul, ofReal_zero, exp_zero, one_mul, sub_mul]

/-- Strong `L²` differentiation of a spectral multiplication orbit can only
have the pointwise multiplier as its derivative. -/
theorem spectral_strong_derivative_ae
    {F : ℝ → Lp ℂ 2 μ} {f g : Lp ℂ 2 μ} {a : α → ℝ}
    (hF : ∀ t, (F t : α → ℂ) =ᵐ[μ]
      fun x => exp (((t * a x : ℝ) : ℂ) * I) * f x)
    (hd : HasDerivAt F g 0) :
    (g : α → ℂ) =ᵐ[μ] fun x => ((a x : ℂ) * I) * f x := by
  obtain ⟨ts, hts, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hd.tendsto_slope).exists_seq_tendsto_ae'
  have hcoe := ae_all_iff.mpr (fun n : ℕ => modulated_slope_coeFn F f a hF (ts n))
  filter_upwards [hae, hcoe] with x hx hxeq
  have hp := (phase_hasDerivAt (a x) (f x)).tendsto_slope.comp hts
  have heq (t : ℝ) : slope
      (fun s : ℝ => exp (((s * a x : ℝ) : ℂ) * I) * f x) 0 t =
      t⁻¹ • ((exp (((t * a x : ℝ) : ℂ) * I) - 1) * f x) := by
    simp only [slope_def_module, sub_zero, zero_mul, ofReal_zero, exp_zero,
      one_mul, sub_mul]
  simp only [Function.comp_def, heq] at hp
  exact tendsto_nhds_unique hx (hp.congr' (Filter.Eventually.of_forall fun n => (hxeq n).symm))

/-- A square-integrable pointwise multiplier is the strong derivative of the
spectral multiplication orbit. This is the converse domain inclusion. -/
theorem hasDerivAt_spectral_of_ae
    {F : ℝ → Lp ℂ 2 μ} {f g : Lp ℂ 2 μ} {a : α → ℝ}
    (ha : Measurable a)
    (hF : ∀ t, (F t : α → ℂ) =ᵐ[μ]
      fun x => exp (((t * a x : ℝ) : ℂ) * I) * f x)
    (hg : (g : α → ℂ) =ᵐ[μ] fun x => ((a x : ℂ) * I) * f x) :
    HasDerivAt F g 0 := by
  let r : ℝ → α → ℂ := fun t x =>
    t⁻¹ • ((exp (((t * a x : ℝ) : ℂ) * I) - 1) * f x) - g x
  have hm (t : ℝ) : AEStronglyMeasurable (r t) μ := by
    have hf := (Lp.memLp f).aestronglyMeasurable
    have hg := (Lp.memLp g).aestronglyMeasurable
    dsimp [r]
    fun_prop
  have hi : Integrable (fun x => 4 * ‖g x‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp g).aestronglyMeasurable).mp
      (Lp.memLp g)).const_mul 4
  have hbound (t : ℝ) : ∀ᵐ x ∂μ, ‖‖r t x‖ ^ 2‖ ≤ 4 * ‖g x‖ ^ 2 := by
    filter_upwards [hg] with x hx
    have hnorm : |a x| * ‖f x‖ = ‖g x‖ := by
      rw [hx, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
      rfl
    have hq := norm_phase_slope_mul_le (a x) t (f x)
    rw [hnorm] at hq
    have hb : ‖r t x‖ ≤ 2 * ‖g x‖ := by
      exact (norm_sub_le _ _).trans (by linarith only [hq])
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      ‖r t x‖ ^ 2 ≤ (2 * ‖g x‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).mpr hb
      _ = 4 * ‖g x‖ ^ 2 := by ring
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun t => ‖r t x‖ ^ 2) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [hg] with x hx
    have hp := (phase_hasDerivAt (a x) (f x)).tendsto_slope
    have heq (t : ℝ) : slope
        (fun s : ℝ => exp (((s * a x : ℝ) : ℂ) * I) * f x) 0 t =
        t⁻¹ • ((exp (((t * a x : ℝ) : ℂ) * I) - 1) * f x) := by
      simp only [slope_def_module, sub_zero, zero_mul, ofReal_zero, exp_zero,
        one_mul, sub_mul]
    have hpr : Tendsto (fun t => r t x) (𝓝[≠] 0) (𝓝 (0 : ℂ)) := by
      have h := hp.sub_const (g x)
      rw [← hx, sub_self] at h
      convert h using 1
      funext t
      exact congrArg (fun z => z - g x) (heq t).symm
    simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using hpr.norm.pow 2
  have hint := tendsto_integral_filter_of_dominated_convergence
    (fun x => 4 * ‖g x‖ ^ 2)
    (Filter.Eventually.of_forall fun t => (hm t).norm.pow 2)
    (Filter.Eventually.of_forall hbound) hi hlim
  simp only [Pi.pow_apply, integral_zero] at hint
  have hsq (t : ℝ) : ‖slope F 0 t - g‖ ^ 2 = ∫ x, ‖r t x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (slope F 0 t) g,
      modulated_slope_coeFn F f a hF t] with x hd hs
    simp only [Pi.sub_apply] at hd
    rw [hd, hs]
  have hsqt : Tendsto (fun t => ‖slope F 0 t - g‖ ^ 2) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    simpa only [hsq] using hint
  have hnorm : Tendsto (fun t => ‖slope F 0 t - g‖) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsqt
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h
  apply hasDerivAt_iff_tendsto_slope.mpr
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- On a spectral orbit the strong derivative domain is exactly the multiplier domain. -/
theorem hasDerivAt_spectral_iff
    {F : ℝ → Lp ℂ 2 μ} {f g : Lp ℂ 2 μ} {a : α → ℝ}
    (ha : Measurable a)
    (hF : ∀ t, (F t : α → ℂ) =ᵐ[μ]
      fun x => exp (((t * a x : ℝ) : ℂ) * I) * f x) :
    HasDerivAt F g 0 ↔ (g : α → ℂ) =ᵐ[μ] fun x => ((a x : ℂ) * I) * f x :=
  ⟨spectral_strong_derivative_ae hF, hasDerivAt_spectral_of_ae ha hF⟩

end ASDExplicitGamma.Model

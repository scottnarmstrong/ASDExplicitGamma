module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # The one-dimensional estimates used by the rectangular C¹ bound -/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- Cauchy–Schwarz on a finite interval, with ordinary Lebesgue normalization. -/
theorem interval_integral_sq_le {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  let I := ∫ x in a..b, f x
  let c := I / (b - a)
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hc : I = c * (b - a) := by dsimp only [c]; field_simp
  have hi := hf.intervalIntegrable (μ := volume) a b
  have hi2 : IntervalIntegrable (fun x => f x ^ 2) volume a b := (hf.pow 2).intervalIntegrable a b
  have hpos : 0 ≤ ∫ x in a..b, (f x - c) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun _ _ => sq_nonneg _
  have hexp : (∫ x in a..b, (f x - c) ^ 2) =
      (∫ x in a..b, f x ^ 2) - 2 * c * I + c ^ 2 * (b - a) := by
    have heq : (fun x => (f x - c) ^ 2) = fun x => f x ^ 2 - 2 * c * f x + c ^ 2 := by
      funext x
      ring
    have hisub : IntervalIntegrable (fun x => f x ^ 2 - 2 * c * f x) volume a b := hi2.sub (hi.const_mul (2 * c))
    have hiconst : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume a b := intervalIntegrable_const
    rw [heq, intervalIntegral.integral_add hisub hiconst,
      intervalIntegral.integral_sub hi2 (hi.const_mul (2 * c)), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    dsimp only [I]
    ring
  have hmul := mul_nonneg hlen.le hpos
  rw [hexp] at hmul
  have he : (b - a) * ((∫ x in a..b, f x ^ 2) - 2 * c * I + c ^ 2 * (b - a)) =
      (b - a) * (∫ x in a..b, f x ^ 2) - I ^ 2 := by rw [hc]; ring
  rw [he] at hmul
  linarith only [hmul]

/-- The oscillation between any two interval points is controlled by the derivative's L² norm. -/
theorem interval_sub_sq_le {a b x y : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (f x - f y) ^ 2 ≤ (b - a) * ∫ t in a..b, deriv f t ^ 2 := by
  wlog hyx : y ≤ x generalizing x y
  · simpa only [sub_sq_comm] using this hy hx (le_of_not_ge hyx)
  have hc : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hyx
    (hf.continuous.continuousOn : ContinuousOn f (Icc y x))
    (fun t _ => (hf.differentiable_one t).hasDerivAt) (hc.intervalIntegrable y x)
  have hd : |f x - f y| ≤ ∫ t in a..b, |deriv f t| := by
    rw [← hsub, ← Real.norm_eq_abs]
    exact (intervalIntegral.norm_integral_le_integral_norm hyx).trans
      (intervalIntegral.integral_mono_interval hy.1 hyx hx.2
        (ae_of_all _ fun _ => abs_nonneg _) (hc.abs.intervalIntegrable a b))
  have hsq : (f x - f y) ^ 2 ≤ (∫ t in a..b, |deriv f t|) ^ 2 := by
    simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg _) hd
  exact hsq.trans (by simpa only [sq_abs] using interval_integral_sq_le hab hc.abs)

/-- The scalar interval Sobolev bound used twice in each coordinate of a square. -/
theorem interval_value_sq_le {a b x : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hx : x ∈ Icc a b) :
    f x ^ 2 ≤ (2 / (b - a)) * (∫ t in a..b, f t ^ 2) +
      2 * (b - a) * ∫ t in a..b, deriv f t ^ 2 := by
  obtain ⟨y, hy, he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (a := a) (b := b) (μ := volume) ((hf.continuous.pow 2).continuousOn)
    (g := fun _ => (1 : ℝ)) intervalIntegrable_const (fun _ _ => zero_le_one)
  rw [uIcc_of_le hab.le] at hy
  have hval : (∫ t in a..b, f t ^ 2) = f y ^ 2 * (b - a) := by
    simpa only [mul_one, Pi.pow_apply, intervalIntegral.integral_const, smul_eq_mul] using he
  have hdist := interval_sub_sq_le hab hf hx hy
  have hcoef : (2 / (b - a)) * (∫ t in a..b, f t ^ 2) = 2 * f y ^ 2 := by
    rw [hval]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
  rw [hcoef]
  nlinarith only [hdist, sq_nonneg (f x - 2 * f y)]

/-- The same bound in the set-integral spelling of the Sobolev jet norm. -/
theorem interval_value_sq_le_setIntegral {a b x : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hx : x ∈ Icc a b) :
    f x ^ 2 ≤ (2 / (b - a)) * (∫ t in Icc a b, f t ^ 2) +
      2 * (b - a) * ∫ t in Icc a b, deriv f t ^ 2 := by
  simpa only [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc] using
    interval_value_sq_le hab hf hx

end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Inverse.WeightedLocalizationMGF
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Real-order moment bounds from both exponential tilts, without integer rounding. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The normalized real power is bounded by its exponential envelope. -/
theorem localization_rpow_exp_envelope (x p : ℝ) (hx : 0 ≤ x) (hp : 0 < p) :
    x ^ p ≤ Real.exp (p * (x - 1)) := by
  rcases hx.eq_or_lt with he | hx
  · rw [← he, Real.zero_rpow hp.ne']
    exact (Real.exp_pos _).le
  · rw [Real.rpow_def_of_pos hx]
    exact Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) hp.le
      nlinarith only [hh])

/-- Two exponential moments at a positive tilt control every real p>=1.
The factor exp(p) is canceled before taking the p-th root. -/
theorem localization_moment_of_exp_bounds {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (S : Ω → ℝ) (hm : AEMeasurable S mu) (p lam : ℝ)
    (hp : 1 ≤ p) (hlam : 0 < lam)
    (hiP : Integrable (fun ω => Real.exp (lam * S ω)) mu)
    (hiN : Integrable (fun ω => Real.exp (-lam * S ω)) mu)
    (hP : (∫ ω, Real.exp (lam * S ω) ∂mu) ≤ Real.exp p)
    (hN : (∫ ω, Real.exp (-lam * S ω) ∂mu) ≤ Real.exp p) :
    Integrable (fun ω => |S ω| ^ p) mu ∧
      (∫ ω, |S ω| ^ p ∂mu) ≤ (2 * (p / lam)) ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let c := p / lam
  have hc : 0 < c := div_pos hp0 hlam
  let D (ω : Ω) := c ^ p * Real.exp (-p) *
    (Real.exp (lam * S ω) + Real.exp (-lam * S ω))
  have hiD : Integrable D mu := (hiP.add hiN).const_mul _
  have hpoint (ω : Ω) : |S ω| ^ p ≤ D ω := by
    have hbase := localization_rpow_exp_envelope (|S ω| / c) p (by positivity) hp0
    have he : |S ω| ^ p ≤ c ^ p * Real.exp (lam * |S ω| - p) := by
      have hh := mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hc.le p)
      have hid : c ^ p * (|S ω| / c) ^ p = |S ω| ^ p := by
        rw [← Real.mul_rpow hc.le (by positivity), mul_div_cancel₀ _ hc.ne']
      rw [hid] at hh
      convert hh using 2
      congr 1
      dsimp only [c]
      field_simp
    have hsum : Real.exp (lam * |S ω|) ≤ Real.exp (lam * S ω) + Real.exp (-lam * S ω) := by
      by_cases hs : 0 ≤ S ω
      · rw [abs_of_nonneg hs]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [abs_of_neg (lt_of_not_ge hs), mul_neg, neg_mul]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
    calc
      _ ≤ c ^ p * Real.exp (lam * |S ω| - p) := he
      _ = c ^ p * Real.exp (-p) * Real.exp (lam * |S ω|) := by rw [sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ D ω := mul_le_mul_of_nonneg_left hsum (by positivity)
  have hint : Integrable (fun ω => |S ω| ^ p) mu := by
    have hpowm : AEMeasurable (fun ω => |S ω| ^ p) mu := by
      simpa only [Real.norm_eq_abs] using hm.norm.pow_const p
    apply hiD.mono' hpowm.aestronglyMeasurable
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)] using hpoint ω
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ ω, D ω ∂mu := integral_mono hint hiD hpoint
    _ = c ^ p * Real.exp (-p) *
        ((∫ ω, Real.exp (lam * S ω) ∂mu) + ∫ ω, Real.exp (-lam * S ω) ∂mu) := by
      rw [integral_const_mul, integral_add hiP hiN]
    _ ≤ c ^ p * Real.exp (-p) * (Real.exp p + Real.exp p) :=
      mul_le_mul_of_nonneg_left (add_le_add hP hN) (by positivity)
    _ = 2 * c ^ p := by
      calc
        _ = (2 * c ^ p) * (Real.exp (-p) * Real.exp p) := by ring
        _ = _ := by rw [← Real.exp_add]; simp only [neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ (2 * c) ^ p := by
      rw [Real.mul_rpow (by norm_num) hc.le]
      exact mul_le_mul_of_nonneg_right (Real.self_le_rpow_of_one_le (by norm_num) hp) (by positivity)

end ASDExplicitGamma.Inverse

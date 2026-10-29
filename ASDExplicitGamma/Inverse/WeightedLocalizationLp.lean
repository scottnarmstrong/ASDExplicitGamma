module

public import ASDExplicitGamma.Inverse.WeightedLocalizationMoment

/-! Real Lp estimates with no ceiling of the source exponent. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The two-tilt envelope gives a genuine real-order Lp bound. -/
theorem localization_eLpNorm_of_exp_bounds {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (S : Ω → ℝ) (hm : AEMeasurable S mu) (p lam : ℝ)
    (hp : 1 ≤ p) (hlam : 0 < lam)
    (hiP : Integrable (fun ω => Real.exp (lam * S ω)) mu)
    (hiN : Integrable (fun ω => Real.exp (-lam * S ω)) mu)
    (hP : (∫ ω, Real.exp (lam * S ω) ∂mu) ≤ Real.exp p)
    (hN : (∫ ω, Real.exp (-lam * S ω) ∂mu) ≤ Real.exp p) :
    eLpNorm S (ENNReal.ofReal p) mu ≤ ENNReal.ofReal (2 * (p / lam)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpE : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hh := localization_moment_of_exp_bounds mu S hm p lam hp hlam hiP hiN hP hN
  have hint : Integrable (fun ω => ‖S ω‖ ^ (ENNReal.ofReal p).toReal) mu := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using hh.1
  have hmem := (integrable_norm_rpow_iff hm.aestronglyMeasurable hpE ENNReal.ofReal_ne_top).mp hint
  rw [hmem.eLpNorm_eq_integral_rpow_norm hpE ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  apply ENNReal.ofReal_le_ofReal
  have hroot := Real.rpow_le_rpow (integral_nonneg (fun ω => by positivity)) hh.2
    (inv_nonneg.mpr hp0.le)
  rw [← Real.rpow_mul (by positivity : 0 ≤ 2 * (p / lam)),
    mul_inv_cancel₀ hp0.ne', Real.rpow_one] at hroot
  simpa only [Real.norm_eq_abs] using hroot

/-- The MGF tilt balances the exact variance proxy and boundedness scale. -/
theorem localization_Lp_parameters (b V p : ℝ) (hb : 0 < b) (hV : 0 < V) (hp : 0 < p) :
    ∃ lam : ℝ, 0 < lam ∧ lam * b ≤ 1 ∧ lam ^ 2 * V ≤ p ∧
      p / lam = Real.sqrt V * Real.sqrt p + b * p := by
  let r := Real.sqrt V
  let z := Real.sqrt p
  have hr : 0 < r := Real.sqrt_pos.mpr hV
  have hz : 0 < z := Real.sqrt_pos.mpr hp
  have hd : 0 < r + b * z := by positivity
  have hrs : r ^ 2 = V := Real.sq_sqrt hV.le
  have hzs : z ^ 2 = p := Real.sq_sqrt hp.le
  let lam := z / (r + b * z)
  have hl : 0 < lam := div_pos hz hd
  refine ⟨lam, hl, ?_, ?_, ?_⟩
  · change z / (r + b * z) * b ≤ 1
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    linarith only [hr]
  · have hle : lam * r ≤ z := by
      dsimp only [lam]
      rw [div_mul_eq_mul_div, div_le_iff₀ hd]
      nlinarith only [mul_nonneg hb.le (sq_nonneg z)]
    have hs := mul_self_le_mul_self (mul_nonneg hl.le hr.le) hle
    nlinarith only [hs, hrs, hzs]
  · change p / (z / (r + b * z)) = r * z + b * p
    rw [← hzs]
    field_simp

end ASDExplicitGamma.Inverse

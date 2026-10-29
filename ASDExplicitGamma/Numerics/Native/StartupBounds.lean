module
public import ASDExplicitGamma.Numerics.Inverse.RealBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Standalone NU-NA-MOLECULAR-STARTUP.
Its only project dependency is the inverse root API.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

noncomputable def startupHistoryConstant : ℝ :=
  (1-(3 : ℝ)^(-1/4 : ℝ))/(1-(3 : ℝ)^(-3/20 : ℝ))

private theorem startup_ratio_upper : (3 : ℝ)^(-3/20 : ℝ) < 84807022/100000000 := by
  have h := ASDExplicitGamma.Numerics.Inverse.inv_root_upper
    (x := (1/27 : ℚ)) (u := 84807022/100000000) (n := 20)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
  have he : (3 : ℝ)^(-3/20 : ℝ) = (1/27 : ℝ)^((20 : ℝ)⁻¹) := by
    have hb : (3 : ℝ)^(-3 : ℝ) = 1/27 := by norm_num [Real.rpow_neg,Real.rpow_natCast]
    rw [← hb,← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
  rw [he]
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
  convert h using 1 <;> norm_num [one_div]

private theorem startup_numerator_upper : 1-(3 : ℝ)^(-1/4 : ℝ) < 241/1000 := by
  have h := ASDExplicitGamma.Numerics.Inverse.inv_root_lower
    (x := (1/3 : ℚ)) (l := 759/1000) (n := 4)
    (by decide +kernel) (by decide) (by decide +kernel)
  have he : (3 : ℝ)^(-1/4 : ℝ) = (1/3 : ℝ)^((4 : ℝ)⁻¹) := by
    have hb : (3 : ℝ)^(-1 : ℝ) = 1/3 := by norm_num [Real.rpow_neg]
    rw [← hb,← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
  rw [he]
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
  have hh : (759/1000 : ℝ) < (1/3 : ℝ)^((4 : ℝ)⁻¹) := by
    simpa only [one_div] using h
  linarith only [hh]

theorem native_startup_history_coefficient_lt : startupHistoryConstant < 8/5 := by
  have hd : (0 : ℝ) < 1-(3 : ℝ)^(-3/20 : ℝ) := by
    linarith only [startup_ratio_upper]
  unfold startupHistoryConstant
  apply (div_lt_iff₀ hd).2
  linarith only [startup_numerator_upper,startup_ratio_upper]

theorem native_startup_variance_polynomials (x θ : ℝ) (hx : 0 ≤ x) (hθ1 : θ ≤ 1)
    (hxθ : x ≤ θ/400) :
    x^2/2+78*x ≤ θ*(62401/320000) ∧ x^2/2+2*x ≤ θ*(1601/320000) := by
  have hx1 : x ≤ 1/400 := by linarith only [hxθ,hθ1]
  have hs : x^2 ≤ θ/160000 := by
    nlinarith only [mul_nonneg hx (sub_nonneg.mpr hx1),hxθ]
  constructor <;> nlinarith only [hs,hxθ]

theorem native_molecular_startup_scalar_caps (x θ : ℝ) (hx : 0 ≤ x) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hxθ : x ≤ θ/400) :
    x^2/2+78*x < (2013/10000)*θ ∧
    (8/5)*(x^2/2+78*x) < (2379/2500)*θ ∧
    (8/5)*(x^2/2+78*x) < (61/10)*θ ∧
    x^2/2+2*x < (3/50)*θ ∧ x^2/2+2*x < (8/25)*θ := by
  have hp := native_startup_variance_polynomials x θ hx hθ1 hxθ
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith only [hp.1,hp.2,hθ]

theorem native_molecular_startup_gate (x θ : ℝ) (hx : 0 ≤ x) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hxθ : x ≤ θ/400) :
    x^2/2+78*x < (2013/10000)*θ ∧
    startupHistoryConstant*(x^2/2+78*x) < (2379/2500)*θ ∧
    startupHistoryConstant*(x^2/2+78*x) < (61/10)*θ ∧
    x^2/2+2*x < (3/50)*θ ∧ x^2/2+2*x < (8/25)*θ := by
  have hs := native_molecular_startup_scalar_caps x θ hx hθ hθ1 hxθ
  have hr : 0 ≤ x^2/2+78*x := by positivity
  have hm := mul_le_mul_of_nonneg_right native_startup_history_coefficient_lt.le hr
  exact ⟨hs.1,hm.trans_lt hs.2.1,hm.trans_lt hs.2.2.1,hs.2.2.2⟩

end ASDExplicitGamma.Numerics.Native

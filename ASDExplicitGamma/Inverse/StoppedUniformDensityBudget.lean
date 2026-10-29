module

public import ASDExplicitGamma.Inverse.StoppedUniformCoefficients

/-! The source all-depth 3^(-R/2) density payment, using actual uniform rare moments. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The uniform moment cap used only for concentration, separately from the
producer-specific rare mean in the baseline. -/
def uniformDensityVariance (m : ℕ) : ℝ := if m=2 then 8 else 1000000000

/-- Full uniform concentration budget, including both localization errors. -/
def uniformDensityBudget (m : ℕ) (p : ℝ) (M : ℕ) (a v : ℝ) : ℝ :=
  4*Real.sqrt (p*21^2*uniformDensityVariance m*(3:ℝ)^(2*M)*a*v)+
  4*p*21^2*4^m*(3:ℝ)^(M*(m+2))*a+2*localizationErrorBudget m p M*v

/-- A retained coefficient is paid at all later depths by its entrance power. -/
theorem retained_power_payment (c ν d R : ℝ)
    (hc : c ≤ (3:ℝ)^d/4) (hd : d ≤ (ν-1/2)*R) :
    c*(3:ℝ)^(-ν*R) ≤ (3:ℝ)^(-R/2)/4 := by
  calc
    _ ≤ ((3:ℝ)^d/4)*(3:ℝ)^(-ν*R) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by norm_num) _)
    _ = (3:ℝ)^(d-ν*R)/4 := by
      rw [sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ) < 3)]
      ring_nf
    _ ≤ _ := div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hd])) (by norm_num)

/-- All three error terms together obey the source bound at every later depth.
The actual volume appears in the budget and is paid only in the error. -/
theorem uniform_density_budget_le (m : ℕ) (hm : m ≤ 4)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) (R : ℕ) (hR : 60 ≤ R)
    (v : ℝ) (hv1 : v ≤ 1) :
    uniformDensityBudget m p (R/6+1) ((1/9:ℝ)^R) v ≤ (3:ℝ)^(-(R:ℝ)/2) := by
  have hp0 : 0 < p := by linarith only [hp]
  have hβ0 : 0 ≤ uniformDensityVariance m := by unfold uniformDensityVariance; split <;> norm_num
  have hβ : uniformDensityVariance m ≤ 1000000000 := by unfold uniformDensityVariance; split <;> norm_num
  have hRr : (60:ℝ) ≤ R := by exact_mod_cast hR
  have hmr : (m:ℝ) ≤ 4 := by exact_mod_cast hm
  have hc1 : 4*Real.sqrt (p*63^2*uniformDensityVariance m) ≤ (3:ℝ)^20/4 := by
    apply le_trans _ uniform_variance_coefficient
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    have hh := mul_le_mul hp256 hβ hβ0 (by norm_num : (0:ℝ) ≤ 256)
    nlinarith only [hh]
  have hc2 : 4*p*63^2*12^m ≤ (3:ℝ)^30/4 := by
    apply le_trans _ uniform_linear_coefficient
    have hh := mul_le_mul hp256 (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 12) hm)
      (by positivity : (0:ℝ) ≤ 12^m) (by norm_num : (0:ℝ) ≤ 256)
    nlinarith only [hh]
  have hvs : Real.sqrt v ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num,by simpa only [one_pow] using hv1⟩
  have hvar := density_variance_power_bound p (uniformDensityVariance m) v hp0.le hβ0 R
  have hvar' : 4*Real.sqrt (p*21^2*uniformDensityVariance m*(3:ℝ)^(2*(R/6+1))*(1/9:ℝ)^R*v) ≤
      (3:ℝ)^(-(R:ℝ)/2)/4 := by
    apply hvar.trans
    apply le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hvs (by positivity : 0 ≤ 4*Real.sqrt (p*63^2*uniformDensityVariance m)))
      (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _))
    simpa only [mul_one] using retained_power_payment _ (5/6) 20 R
      (by simpa only [Real.rpow_ofNat] using hc1) (by linarith only [hRr])
  have hlin := density_linear_power_bound p hp0.le m R
  have hlin' : 4*p*21^2*4^m*(3:ℝ)^((R/6+1)*(m+2))*(1/9:ℝ)^R ≤
      (3:ℝ)^(-(R:ℝ)/2)/4 := by
    apply hlin.trans
    apply retained_power_payment _ ((10-(m:ℝ))/6) 30 R
      (by simpa only [Real.rpow_ofNat] using hc2)
    have hh := mul_le_mul_of_nonneg_right hmr (show 0 ≤ (R:ℝ) by positivity)
    nlinarith only [hh,hRr]
  have hmis := localization_retained_mismatch_bound m p hp0 hp256 R hR
  have herr : 2*localizationErrorBudget m p (R/6+1)*v ≤ (3:ℝ)^(-(R:ℝ)/2)/4 := by
    have hnon := localization_error_budget_nonneg m p hp0.le (R/6+1)
    apply (mul_le_mul_of_nonneg_left hv1 (show 0 ≤ 2*localizationErrorBudget m p (R/6+1) by positivity)).trans
    rw [mul_one]
    apply le_trans _ (retained_power_payment _ 2 90 R
      (by simpa only [Real.rpow_ofNat] using uniform_mismatch_coefficient m hm p hp hp256)
      (by linarith only [hRr]))
    simpa only [localizationErrorBudget,localizationCutoffRadius,Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using! hmis
  unfold uniformDensityBudget
  have hh := add_le_add (add_le_add hvar' hlin') herr
  have hpos : 0 ≤ (3:ℝ)^(-(R:ℝ)/2) := Real.rpow_nonneg (by norm_num) _
  linarith only [hh,hpos]

end
end ASDExplicitGamma.Inverse

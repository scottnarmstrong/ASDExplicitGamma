module

public import ASDExplicitGamma.Inverse.FullResponseRetainedResetBounds

/-! The three literal D4 retained powers and their complete first moments. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- Dropping only the favorable leading 3^-ρ factor gives a reusable
positive retained sum comparison at the fixed full-response entrance. -/
theorem full_response_positive_retained_bounds (a ρ β c : ℝ) (N : ℕ)
    (hdecay : a < ρ) (hρ : 0 ≤ ρ) (hβ : β ≤ ρ-a) (hβ0 : 0 ≤ β)
    (hN : (N:ℝ) ≤ β*340) (hc : 0 ≤ c) (hc1 : c < 1)
    (hq : (3:ℝ)^(-β) ≤ c) :
    densityResetPowerSum a ρ 339 ≤ (3:ℝ)^(-(N:ℝ))*(1/(1-c))^2 ∧
    densityResetFirstPowerSum a ρ 339 ≤ (3:ℝ)^(-(N:ℝ))*
      ((341:ℝ)*(1/(1-c))^2+3*c/(1-c)^3) := by
  have hh := full_response_retained_reset_bounds a ρ β c 339 N
    hdecay hβ hβ0 (by simpa using hN) hc hc1 hq
  have hsmall : (3:ℝ)^(-ρ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr hρ)
  constructor
  · apply hh.1.trans
    have hmul := mul_le_mul_of_nonneg_right hsmall
      (show 0 ≤ (3:ℝ)^(-(N:ℝ))*(1/(1-c))^2 by positivity)
    convert hmul using 1 <;> ring
  · apply hh.2.trans
    have hden : 0 < 1-c := sub_pos.mpr hc1
    have hmul := mul_le_mul_of_nonneg_right hsmall
      (show 0 ≤ (3:ℝ)^(-(N:ℝ))*((341:ℝ)*(1/(1-c))^2+3*c/(1-c)^3) by positivity)
    convert hmul using 1 <;> norm_num
    ring

/-- Literal complete geometric source cap for each of the three D4 powers. -/
def fullResponseD4ResetCap (i : Fin 3) : ℝ :=
  ![(3:ℝ)^(-(136:ℝ))/(35/100)^2,
    (3:ℝ)^(-(166:ℝ))/(41/100)^2,
    (3:ℝ)^(-(336:ℝ))/(66/100)^2] i

/-- The three actual D4 retained powers fit the literal coded cap, and their
first moments fit 350 times the same cap. -/
theorem full_response_D4_reset_endpoint (γ : ℝ) (hg : γ ≤ gammaZero) (i : Fin 3) :
    densityResetPowerSum (4*γ) (densityPERate 4 i/2) 339 ≤ fullResponseD4ResetCap i ∧
    densityResetFirstPowerSum (4*γ) (densityPERate 4 i/2) 339 ≤ 350*fullResponseD4ResetCap i := by
  have hg' : γ ≤ 17/50000 := hg
  fin_cases i
  · have hh := full_response_positive_retained_bounds (4*γ) (5/12) (2/5) (65/100) 136
      (by linarith only [hg']) (by norm_num) (by linarith only [hg']) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) full_response_three_neg_40_le
    norm_num [densityPERate,fullResponseD4ResetCap] at hh ⊢
    constructor
    · exact hh.1
    · apply hh.2.trans
      norm_num [Real.rpow_neg,Real.rpow_natCast]

  · have hh := full_response_positive_retained_bounds (4*γ) (1/2) (49/100) (59/100) 166
      (by linarith only [hg']) (by norm_num) (by linarith only [hg']) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) full_response_three_neg_49_le
    norm_num [densityPERate,fullResponseD4ResetCap] at hh ⊢
    constructor
    · exact hh.1
    · apply hh.2.trans
      norm_num [Real.rpow_neg,Real.rpow_natCast]

  · have hh := full_response_positive_retained_bounds (4*γ) 1 (99/100) (34/100) 336
      (by linarith only [hg']) (by norm_num) (by linarith only [hg']) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) full_response_three_neg_99_le
    norm_num [densityPERate]
    change densityResetPowerSum (4*γ) 1 339 ≤ (3:ℝ)^(-(336:ℝ))/(66/100)^2 ∧
      densityResetFirstPowerSum (4*γ) 1 339 ≤ 350*((3:ℝ)^(-(336:ℝ))/(66/100)^2)
    generalize ht : (3:ℝ)^(-(336:ℝ))=t at hh ⊢
    have ht0 : 0 ≤ t := by rw [← ht]; positivity
    norm_num at hh ⊢
    constructor
    · nlinarith only [hh.1]
    · nlinarith only [hh.2,ht0]

end
end ASDExplicitGamma.Inverse

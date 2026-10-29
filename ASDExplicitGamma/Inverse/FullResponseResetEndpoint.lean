module

public import ASDExplicitGamma.Inverse.FullResponseRetainedResetBounds
public import ASDExplicitGamma.Numerics.Inverse.Full128
public import ASDExplicitGamma.Inverse.StoppedResetDensityEZ

/-! Literal M0/Z0 endpoint payments for complete reset powers and moments. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- Both matrix reset powers fit M0, and the first depth moment fits 350 M0. -/
theorem full_response_matrix_reset_endpoint (a : ℝ) (ha : a ≤ 4*gammaZero) :
    densityResetPowerSum a 1 339 ≤ (invFull128M0:ℝ) ∧
      densityResetFirstPowerSum a 1 339 ≤ 350*(invFull128M0:ℝ) := by
  have hh := full_response_retained_reset_bounds a 1 (99/100) (34/100) 339 336
    (by change a ≤ 4*(17/50000) at ha; linarith only [ha])
    (by change a ≤ 4*(17/50000) at ha; linarith only [ha])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) full_response_three_neg_99_le
  have hM0 : (invFull128M0:ℝ)=(2/3:ℝ)*(3:ℝ)^(-(336:ℝ))/(66/100)^2 := by
    unfold invFull128M0
    push_cast
    rw [Real.rpow_neg_ofNat (3:ℝ) 336]
    simp only [zpow_neg,zpow_ofNat,one_div]
  rw [hM0]
  generalize ht : (3:ℝ)^(-(336:ℝ))=t at hh ⊢
  have ht0 : 0 ≤ t := by rw [← ht]; positivity
  norm_num at hh ⊢
  constructor
  · nlinarith only [hh.1,ht0]
  · nlinarith only [hh.2,ht0]

/-- The complete coarse density reset power fits the literal Z0 supplier. -/
theorem full_response_density_reset_endpoint (γ : ℝ) (hg : γ ≤ gammaZero) :
    densityResetPowerSum (2*γ) (1/2) 339 ≤ (invFull128Z0:ℝ) := by
  have hh := (full_response_retained_reset_bounds (2*γ) (1/2) (49/100) (59/100) 339 166
    (by change γ ≤ 17/50000 at hg; linarith only [hg])
    (by change γ ≤ 17/50000 at hg; linarith only [hg])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) full_response_three_neg_49_le).1
  have hsmall : (3:ℝ)^(-(1/2:ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  apply hh.trans
  have hfactor : (0:ℝ) ≤ (3:ℝ)^(-(166:ℝ))*(1/(1-(59/100:ℝ)))^2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hsmall hfactor
  calc
    _ = (3:ℝ)^(-(1/2:ℝ))*((3:ℝ)^(-(166:ℝ))*(1/(1-(59/100:ℝ)))^2) := by norm_num; ring
    _ ≤ _ := hmul
    _ = _ := by
      norm_num [invFull128Z0,Real.rpow_neg,Real.rpow_natCast]

/-- The source coarse e_Z cap consumes precisely 3*C*Z0, with C=3(S_b+1). -/
theorem full_response_density_EZ_endpoint (γ : ℝ) (hg : γ ≤ gammaZero) (S : ℝ) (hS : 0 ≤ S) :
    densityEZ γ S 339 ≤ 9*(S+1)*(invFull128Z0:ℝ) := by
  have hreset := full_response_density_reset_endpoint γ hg
  have hpower : (3:ℝ)^(1/2:ℝ) ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 3) (by norm_num : (1/2:ℝ) ≤ 1)
  have hc : (S+1)*(1+(3:ℝ)^(1/2:ℝ)+(3:ℝ)^(2*(1/2:ℝ))) ≤ 9*(S+1) := by
    norm_num at hpower ⊢
    nlinarith only [hS,hpower]
  have hnonneg : 0 ≤ densityResetPowerSum (2*γ) (1/2) 339 := by
    have hs := density_reset_power_hasSum (2*γ) (1/2)
      (by change γ ≤ 17/50000 at hg; linarith only [hg]) 339
    rw [← hs.tsum_eq]
    exact tsum_nonneg (fun _ => by positivity)
  unfold densityEZ
  exact mul_le_mul hc hreset hnonneg (by positivity)

end
end ASDExplicitGamma.Inverse

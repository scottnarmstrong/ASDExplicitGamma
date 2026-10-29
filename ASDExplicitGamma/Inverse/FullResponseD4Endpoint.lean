module

public import ASDExplicitGamma.Inverse.FullResponseD4ResetEndpoint
public import ASDExplicitGamma.Inverse.FullResponseD4CoefficientEndpoint

/-! Complete analytic-to-certified full-response D40/D41 endpoints. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- Corrected weighted coefficient caps, with the third resolution sum 13. -/
def fullResponseD4CoefficientCap (V D : ℝ) (i : Fin 3) : ℝ := ![9*V,9*D,9] i

/-- The first two offset factors are ≤9; the third uses its actual 13 payment. -/
theorem full_response_D4_offset_coefficient_le (p V D : ℝ) (hV : 0 ≤ V) (hD : 0 ≤ D)
    (h0 : Real.sqrt (densityPECoefficient (rootQ .full) 4 p 1232 0) ≤ V)
    (h1 : Real.sqrt (densityPECoefficient (rootQ .full) 4 p 1232 1) ≤ D)
    (h2 : 13*Real.sqrt (densityPECoefficient (rootQ .full) 4 p 1232 2) ≤ 9)
    (i : Fin 3) :
    Real.sqrt (densityPECoefficient (rootQ .full) 4 p 1232 i)*
      (1+(3:ℝ)^(densityPERate 4 i/2)+(3:ℝ)^(densityPERate 4 i)) ≤
        fullResponseD4CoefficientCap V D i := by
  have hp (r : ℝ) (hr : r ≤ 1) : (3:ℝ)^r ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 3) hr
  fin_cases i
  · have ho : 1+(3:ℝ)^(5/12:ℝ)+(3:ℝ)^(5/6:ℝ) ≤ 9 := by
      linarith only [hp (5/12) (by norm_num),hp (5/6) (by norm_num)]
    have hh := mul_le_mul h0 ho (by positivity) hV
    convert hh using 1 <;> norm_num [densityPERate,fullResponseD4CoefficientCap]
    ring
  · have ho : 1+(3:ℝ)^(1/2:ℝ)+(3:ℝ)^(1:ℝ) ≤ 9 := by
      linarith only [hp (1/2) (by norm_num),hp 1 le_rfl]
    have hh := mul_le_mul h1 ho (by positivity) hD
    convert hh using 1 <;> norm_num [densityPERate,fullResponseD4CoefficientCap]
    ring
  · convert h2 using 1 <;> norm_num [densityPERate,fullResponseD4CoefficientCap]
    ring

/-- Both full retained D4 series consume the same literal positive cap and
its source factor 350 for the first abscissa moment. -/
theorem full_response_D4_generic_endpoint (γ p V D : ℝ) (hg : γ ≤ gammaZero)
    (hV : 0 ≤ V) (hD : 0 ≤ D)
    (h0 : Real.sqrt (densityPECoefficient (rootQ .full) 4 p 1232 0) ≤ V)
    (h1 : Real.sqrt (densityPECoefficient (rootQ .full) 4 p 1232 1) ≤ D)
    (h2 : 13*Real.sqrt (densityPECoefficient (rootQ .full) 4 p 1232 2) ≤ 9) :
    let cap := (planarGradientCharge 40+1)*9*
      (V*fullResponseD4ResetCap 0+D*fullResponseD4ResetCap 1+fullResponseD4ResetCap 2)
    densityD40 (rootQ .full) p 1232 γ (planarGradientCharge 40) 339 ≤ cap ∧
      densityD41 (rootQ .full) p 1232 γ (planarGradientCharge 40) 339 ≤ 350*cap := by
  dsimp only
  let c := fun i : Fin 3 => Real.sqrt (densityPECoefficient (rootQ .full) 4 p 1232 i)*
    (1+(3:ℝ)^(densityPERate 4 i/2)+(3:ℝ)^(densityPERate 4 i))
  have hc (i : Fin 3) : c i ≤ fullResponseD4CoefficientCap V D i :=
    full_response_D4_offset_coefficient_le p V D hV hD h0 h1 h2 i
  have hcap0 (i : Fin 3) : 0 ≤ fullResponseD4CoefficientCap V D i := by
    fin_cases i <;> simp [fullResponseD4CoefficientCap] <;> positivity
  have hR (i : Fin 3) : 0 ≤ densityResetPowerSum (4*γ) (densityPERate 4 i/2) 339 := by
    have hs := density_reset_power_hasSum (4*γ) _ (density_rates_decay γ hg 4 (Or.inr rfl) i).2 339
    rw [← hs.tsum_eq]
    exact tsum_nonneg (fun _ => by positivity)
  have hR1 (i : Fin 3) : 0 ≤ densityResetFirstPowerSum (4*γ) (densityPERate 4 i/2) 339 := by
    have hs := density_reset_first_power_hasSum (4*γ) _ (density_rates_decay γ hg 4 (Or.inr rfl) i).2 339
    rw [← hs.tsum_eq]
    exact tsum_nonneg (fun _ => by positivity)
  have hh0 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => mul_le_mul (hc i)
    (full_response_D4_reset_endpoint γ hg i).1 (hR i) (hcap0 i))
  have hh1 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => mul_le_mul (hc i)
    (full_response_D4_reset_endpoint γ hg i).2 (hR1 i) (hcap0 i))
  have hS : 0 ≤ planarGradientCharge 40+1 := by unfold planarGradientCharge; positivity
  constructor
  · apply (mul_le_mul_of_nonneg_left hh0 hS).trans_eq
    simp [Fin.sum_univ_succ,fullResponseD4CoefficientCap]
    ring
  · apply (mul_le_mul_of_nonneg_left hh1 hS).trans_eq
    simp [Fin.sum_univ_succ,fullResponseD4CoefficientCap]
    ring

/-- Literal order-64 D40 and D41 source endpoint. -/
theorem full_response_D4_endpoint64 (γ : ℝ) (hg : γ ≤ gammaZero) :
    densityD40 (rootQ .full) 64 1232 γ (planarGradientCharge 40) 339 ≤ (invFull64D4:ℝ) ∧
      densityD41 (rootQ .full) 64 1232 γ (planarGradientCharge 40) 339 ≤ 350*(invFull64D4:ℝ) := by
  have hh := full_response_D4_generic_endpoint γ 64 (invFull64Vroot:ℝ) (invFull64Droot:ℝ) hg
    (by exact_mod_cast invFull64_radicals.2.2.2.2.1.le) (by exact_mod_cast invFull64_radicals.2.2.1.le)
    full_response_D4_coefficients64.1 full_response_D4_coefficients64.2.1 full_response_D4_coefficients64.2.2
  have he : (planarGradientCharge 40+1)*9*
      ((invFull64Vroot:ℝ)*fullResponseD4ResetCap 0+(invFull64Droot:ℝ)*fullResponseD4ResetCap 1+
        fullResponseD4ResetCap 2)=(invFull64D4:ℝ) := by
    change (planarGradientCharge 40+1)*9*
      ((invFull64Vroot:ℝ)*((3:ℝ)^(-(136:ℝ))/(35/100)^2)+
        (invFull64Droot:ℝ)*((3:ℝ)^(-(166:ℝ))/(41/100)^2)+
          (3:ℝ)^(-(336:ℝ))/(66/100)^2)=(invFull64D4:ℝ)
    unfold invFull64D4
    push_cast
    rw [Real.rpow_neg_ofNat (3:ℝ) 136,Real.rpow_neg_ofNat (3:ℝ) 166,
      Real.rpow_neg_ofNat (3:ℝ) 336]
    simp only [zpow_neg,zpow_ofNat,one_div]
    unfold planarGradientCharge
    generalize ht : ((3:ℝ)^(336:ℕ))⁻¹=t
    ring
  simpa only [he] using hh

/-- Literal order-128 D40 and D41 source endpoint. -/
theorem full_response_D4_endpoint128 (γ : ℝ) (hg : γ ≤ gammaZero) :
    densityD40 (rootQ .full) 128 1232 γ (planarGradientCharge 40) 339 ≤ (invFull128D4:ℝ) ∧
      densityD41 (rootQ .full) 128 1232 γ (planarGradientCharge 40) 339 ≤ 350*(invFull128D4:ℝ) := by
  have hh := full_response_D4_generic_endpoint γ 128 (invFull128Vroot:ℝ) (invFull128Droot:ℝ) hg
    (by exact_mod_cast invFull128_radicals.2.2.2.2.1.le) (by exact_mod_cast invFull128_radicals.2.2.1.le)
    full_response_D4_coefficients128.1 full_response_D4_coefficients128.2.1 full_response_D4_coefficients128.2.2
  have he : (planarGradientCharge 40+1)*9*
      ((invFull128Vroot:ℝ)*fullResponseD4ResetCap 0+(invFull128Droot:ℝ)*fullResponseD4ResetCap 1+
        fullResponseD4ResetCap 2)=(invFull128D4:ℝ) := by
    change (planarGradientCharge 40+1)*9*
      ((invFull128Vroot:ℝ)*((3:ℝ)^(-(136:ℝ))/(35/100)^2)+
        (invFull128Droot:ℝ)*((3:ℝ)^(-(166:ℝ))/(41/100)^2)+
          (3:ℝ)^(-(336:ℝ))/(66/100)^2)=(invFull128D4:ℝ)
    unfold invFull128D4
    push_cast
    rw [Real.rpow_neg_ofNat (3:ℝ) 136,Real.rpow_neg_ofNat (3:ℝ) 166,
      Real.rpow_neg_ofNat (3:ℝ) 336]
    simp only [zpow_neg,zpow_ofNat,one_div]
    unfold planarGradientCharge
    generalize ht : ((3:ℝ)^(336:ℕ))⁻¹=t
    ring
  simpa only [he] using hh

end
end ASDExplicitGamma.Inverse

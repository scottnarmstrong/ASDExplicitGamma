module

public import ASDExplicitGamma.Inverse.FullResponseSelectedClockNumerics

/-! Analytic selected-height profiles consume the rational endpoint clocks. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- Every retained positive physical clock has the source rational exponential endpoint. -/
theorem full_response_clock_endpoint (γ : ℝ) (_hγ : 0 ≤ γ) (hg : γ ≤ gammaZero)
    (t : ℚ) (ht : 0 ≤ t) (hdom : (11/10:ℚ)*(invGamma*t) < 1) :
    (3:ℝ)^(γ*(t:ℝ)) ≤ (invE ((11/10)*invGamma*t):ℝ) := by
  have hg' : γ ≤ (invGamma:ℝ) := by
    simpa only [gammaZero,invGamma,Rat.cast_div,Rat.cast_ofNat] using hg
  have ht' : (0:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hdom' : (11/10:ℝ)*((invGamma:ℝ)*(t:ℝ)) < 1 := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hdom
    norm_num only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] at hh
    exact hh
  have hh := inv_three_power_bound ((invGamma:ℝ)*(t:ℝ))
    (mul_nonneg (by norm_num [invGamma]) ht') hdom'
  apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
    (mul_le_mul_of_nonneg_right hg' ht')).trans
  apply hh.trans_eq
  unfold invE
  push_cast
  congr 1
  ring

/-- The bounded selected-wave payment at the source clock z_s=350. -/
def fullResponseSelectedBase (p R : ℝ) : ℝ :=
  40*(2*p+2)*R*(invE ((22/5)*invGamma*350):ℝ)

/-- Both W₀/W₁ endpoints retain their exact finite-candidate and tiny-tail
coefficients. The root comparison is a reusable scalar comparison discharged
by the rational order-64/order-128 root certificates at its consumers. -/
theorem full_response_selected_wave_endpoint (γ p R : ℝ) (hγ : 0 ≤ γ)
    (hg : γ ≤ gammaZero) (hp : 64 ≤ p) (hp128 : p ≤ 128)
    (hroot : (12:ℝ)^(1/p:ℝ) ≤ R) :
    physicalSelectedWaveBudget γ p 377 0 ≤ fullResponseSelectedBase p R+(1/10^100:ℝ) ∧
    physicalSelectedWaveBudget γ p 377 1 ≤ 350*fullResponseSelectedBase p R+351*(1/10^100:ℝ) := by
  have hclock : (3:ℝ)^(4*γ*350) ≤ (invE ((22/5)*invGamma*350):ℝ) := by
    have hh := full_response_clock_endpoint γ hγ hg 1400 (by norm_num)
      (by norm_num [invGamma])
    norm_num only [Rat.cast_ofNat] at hh
    rw [show γ*(1400:ℝ)=4*γ*350 by ring] at hh
    convert hh using 1
    norm_num [invE,invGamma]
  have hR : 0 ≤ R := (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 12) _).trans hroot
  have hFin : physicalSelectedWaveFiniteBudget γ p 377 0 ≤ fullResponseSelectedBase p R := by
    unfold physicalSelectedWaveFiniteBudget fullResponseSelectedBase
    norm_num only [Fin.val_zero,pow_zero,mul_one,Nat.cast_ofNat]
    have hh := mul_le_mul hroot hclock (by positivity) hR
    have hp0 : 0 ≤ 40*(2*p+2) := by linarith only [hp]
    convert mul_le_mul_of_nonneg_left hh hp0 using 1 <;> ring
  have hFin1 : physicalSelectedWaveFiniteBudget γ p 377 1 =
      350*physicalSelectedWaveFiniteBudget γ p 377 0 := by
    norm_num [physicalSelectedWaveFiniteBudget]
    ring
  constructor
  · exact add_le_add hFin (full_response_wave_tail_tiny γ p hg hp hp128)
  · unfold physicalSelectedWaveBudget
    rw [hFin1]
    exact add_le_add (mul_le_mul_of_nonneg_left hFin (by norm_num))
      (full_response_wave_first_tail_tiny γ p hg hp hp128)

/-- The exact full-row selected Jp consumes its rational clock plus tiny tail. -/
theorem full_response_selected_Jp_endpoint (γ p : ℝ) (hγ : 0 ≤ γ)
    (hg : γ ≤ gammaZero) (hp : 64 ≤ p) (hp128 : p ≤ 128) :
    selectedJp γ p 377 ≤ (invE ((11/5)*invGamma*350):ℝ)+(1/10^100:ℝ) := by
  have hclock : (3:ℝ)^(2*γ*350) ≤ (invE ((11/5)*invGamma*350):ℝ) := by
    have hh := full_response_clock_endpoint γ hγ hg 700 (by norm_num)
      (by norm_num [invGamma])
    norm_num only [Rat.cast_ofNat] at hh
    rw [show γ*(700:ℝ)=2*γ*350 by ring] at hh
    convert hh using 1
    norm_num [invE,invGamma]
  exact (full_response_selected_Jp_le γ p hg hp hp128).trans (add_le_add hclock le_rfl)

end
end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Inverse.StoppedSelectedSeries
public import ASDExplicitGamma.Inverse.StoppedSelectedCandidates

/-! Complete selected-height root and wave tails with the exact physical gamma clocks. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- First unbounded height's source clock z_f=Hs+3-40. -/
def selectedFirstClock (H0 : ℕ) : ℝ := (H0:ℝ)-26

/-- The root moment clock has consecutive ratio less than three on the full
source order interval. Gamma remains the physical model parameter. -/
theorem selected_root_clock_ratio (γ p : ℝ) (hg : γ ≤ gammaZero)
    (hp : 0 ≤ p) (hp256 : p ≤ 256) : (3:ℝ)^(2*p*γ) ≤ 3 := by
  have hg' : γ ≤ 17/50000 := hg
  have h1 := mul_le_mul_of_nonneg_left hg' hp
  have h2 := mul_le_mul_of_nonneg_left hp256 (by norm_num : (0:ℝ) ≤ 17/50000)
  have he : 2*p*γ ≤ (1:ℝ) := by nlinarith only [h1,h2]
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) he

/-- Even after paying the linear z_h factor by doubling, the wave clock's
consecutive ratio is at most three. -/
theorem selected_wave_clock_ratio (γ : ℝ) (hg : γ ≤ gammaZero) :
    2*(3:ℝ)^(4*γ) ≤ 3 := by
  have hg' : γ ≤ 17/50000 := hg
  have hroot : (3:ℝ)^(1/4:ℝ) ≤ 3/2 := by
    rw [one_div,Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < 4)]
    norm_num
  have hh := (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
    (show 4*γ ≤ (1/4:ℝ) by linarith only [hg'])).trans hroot
  linarith only [hh]

/-- The entrance supergeometric argument remains above 10000 after the
source tail-event Holder exponent 1/(2p), including p=256. -/
theorem selected_first_argument_lower (H0 : ℕ) (hH : 333 ≤ H0)
    (p : ℝ) (hp : 0 < p) (hp256 : p ≤ 256) :
    (10000:ℝ) ≤ (heightExponent (H0+11)/32)/(2*p) := by
  have hh := height_exponent_lower (H0+11) (by omega)
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*p)).mpr
  have hnum : (10000:ℝ)*(2*p) ≤ (3:ℝ)^43/32 := by norm_num; linarith only [hp256]
  exact hnum.trans (div_le_div_of_nonneg_right hh (by norm_num))

/-- Exact factorization of the actual source root-tail moment summand. -/
theorem selected_root_tail_factor (γ p : ℝ) (H0 n : ℕ) :
    (3:ℝ)^(2*p*γ*(selectedFirstClock H0+(n:ℝ)))*selectedTailProbability H0 n =
      (3:ℝ)^(2*p*γ*selectedFirstClock H0)*
        (((3:ℝ)^(2*p*γ))^n*Real.exp (-(heightExponent (H0+11)/32)*((3:ℝ)^(1/4:ℝ))^n)) := by
  rw [selected_tail_probability_eq,
    show 2*p*γ*(selectedFirstClock H0+(n:ℝ)) =
      2*p*γ*selectedFirstClock H0+(2*p*γ)*(n:ℝ) by ring,
    Real.rpow_add (by norm_num : (0:ℝ) < 3),
    Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]
  ring

/-- Complete root selected tail (9.2), with the first exponent reading Hs. -/
theorem selected_root_tail_series (γ p : ℝ) (hg : γ ≤ gammaZero)
    (hp : 0 < p) (hp256 : p ≤ 256) (H0 : ℕ) (hH : 333 ≤ H0) :
    Summable (fun n : ℕ => (3:ℝ)^(2*p*γ*(selectedFirstClock H0+(n:ℝ)))*selectedTailProbability H0 n) ∧
      (∑' n : ℕ, (3:ℝ)^(2*p*γ*(selectedFirstClock H0+(n:ℝ)))*selectedTailProbability H0 n) ≤
        (1000/999)*(3:ℝ)^(2*p*γ*selectedFirstClock H0)*Real.exp (-heightExponent (H0+11)/32) := by
  have hx : (10000:ℝ) ≤ heightExponent (H0+11)/32 := by
    have hh := height_exponent_lower (H0+11) (by omega)
    norm_num at hh ⊢
    linarith only [hh]
  have hh := selected_clock_series ((3:ℝ)^(2*p*γ)) (heightExponent (H0+11)/32)
    ((3:ℝ)^(1/4:ℝ)) (by positivity) (selected_root_clock_ratio γ p hg hp.le hp256)
    hx Numerics.Inverse.inv_quarter_growth.le
  have hs := hh.1.mul_left ((3:ℝ)^(2*p*γ*selectedFirstClock H0))
  simp_rw [← selected_root_tail_factor γ p H0] at hs
  refine ⟨hs,?_⟩
  simp_rw [selected_root_tail_factor γ p H0]
  rw [tsum_mul_left]
  have hb := mul_le_mul_of_nonneg_left hh.2
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) (2*p*γ*selectedFirstClock H0))
  simpa only [neg_div,mul_assoc,mul_left_comm,mul_comm] using! hb

/-- Exact wave tail probability power, before combining with its physical clock. -/
theorem selected_wave_tail_probability (H0 n : ℕ) (p : ℝ) :
    (selectedTailProbability H0 n)^(1/(2*p):ℝ) =
      Real.exp (-((heightExponent (H0+11)/32)/(2*p))*((3:ℝ)^(1/4:ℝ))^n) := by
  rw [selected_tail_probability_eq,← Real.exp_mul]
  congr 1
  ring

end
end ASDExplicitGamma.Inverse

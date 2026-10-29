module

public import ASDExplicitGamma.Inverse.StoppedSelectedPhysicalClock

/-! Complete selected-height tails of W₀ and W₁, retaining physical gamma and Holder order. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The complete first-term majorant of each source wave tail, j=0,1. -/
def selectedWaveTailBudget (γ p : ℝ) (H0 : ℕ) (j : Fin 2) : ℝ :=
  (1000/999)*(selectedFirstClock H0)^j.val*(3:ℝ)^(4*γ*selectedFirstClock H0)*
    (selectedTailProbability H0 0)^(1/(2*p):ℝ)

/-- The exact summand factorization preserves both z_h and physical gamma. -/
theorem selected_wave_tail_factor (γ p : ℝ) (H0 n : ℕ) (j : Fin 2) :
    (selectedFirstClock H0+(n:ℝ))^j.val*(3:ℝ)^(4*γ*(selectedFirstClock H0+(n:ℝ)))*
      (selectedTailProbability H0 n)^(1/(2*p):ℝ) =
      (3:ℝ)^(4*γ*selectedFirstClock H0)*
        ((selectedFirstClock H0+(n:ℝ))^j.val*((3:ℝ)^(4*γ))^n*
          Real.exp (-((heightExponent (H0+11)/32)/(2*p))*((3:ℝ)^(1/4:ℝ))^n)) := by
  rw [selected_wave_tail_probability,
    show 4*γ*(selectedFirstClock H0+(n:ℝ)) = 4*γ*selectedFirstClock H0+(4*γ)*(n:ℝ) by ring,
    Real.rpow_add (by norm_num : (0:ℝ) < 3),Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]
  ring

/-- Both infinite wave tails from (9.4), including the first z_h moment, are
bounded by 1000/999 times their exact first terms. -/
theorem selected_wave_tail_series (γ p : ℝ) (hg : γ ≤ gammaZero)
    (hp : 0 < p) (hp256 : p ≤ 256) (H0 : ℕ) (hH : 333 ≤ H0) (j : Fin 2) :
    Summable (fun n : ℕ => (selectedFirstClock H0+(n:ℝ))^j.val*
      (3:ℝ)^(4*γ*(selectedFirstClock H0+(n:ℝ)))*(selectedTailProbability H0 n)^(1/(2*p):ℝ)) ∧
      (∑' n : ℕ, (selectedFirstClock H0+(n:ℝ))^j.val*
      (3:ℝ)^(4*γ*(selectedFirstClock H0+(n:ℝ)))*(selectedTailProbability H0 n)^(1/(2*p):ℝ)) ≤
        selectedWaveTailBudget γ p H0 j := by
  let a := (3:ℝ)^(4*γ)
  let x := (heightExponent (H0+11)/32)/(2*p)
  let r := (3:ℝ)^(1/4:ℝ)
  let z := selectedFirstClock H0
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have ha3 : 2*a ≤ 3 := selected_wave_clock_ratio γ hg
  have hx : (10000:ℝ) ≤ x := selected_first_argument_lower H0 hH p hp hp256
  have hr : (13/10:ℝ) ≤ r := Numerics.Inverse.inv_quarter_growth.le
  have hz : 1 ≤ z := by
    have hc : (333:ℝ) ≤ H0 := by exact_mod_cast hH
    dsimp only [z,selectedFirstClock]
    linarith only [hc]
  have hinner : Summable (fun n : ℕ => (z+n)^j.val*a^n*Real.exp (-x*r^n)) ∧
      (∑' n : ℕ, (z+n)^j.val*a^n*Real.exp (-x*r^n)) ≤ z^j.val*(1000/999)*Real.exp (-x) := by
    fin_cases j
    · simpa only [Fin.val_zero,pow_zero,one_mul] using!
        selected_clock_series a x r ha (by linarith only [ha,ha3]) hx hr
    · simpa only [Fin.val_one,pow_one] using! selected_linear_clock_series a x r z ha ha3 hx hr hz
  have hs := hinner.1.mul_left ((3:ℝ)^(4*γ*selectedFirstClock H0))
  dsimp only [a,x,r,z] at hs
  simp_rw [← selected_wave_tail_factor γ p H0] at hs
  refine ⟨hs,?_⟩
  simp_rw [selected_wave_tail_factor γ p H0]
  rw [tsum_mul_left]
  have hh := mul_le_mul_of_nonneg_left hinner.2
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) (4*γ*selectedFirstClock H0))
  unfold selectedWaveTailBudget
  rw [selected_wave_tail_probability]
  norm_num only [pow_zero,mul_one]
  simpa only [z,x,r,a,mul_assoc,mul_left_comm,mul_comm] using! hh

end
end ASDExplicitGamma.Inverse

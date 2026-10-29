module

public import ASDExplicitGamma.Inverse.WeightedLocalizationResetSeries
public import ASDExplicitGamma.Inverse.StoppedDensityResetPowers

/-! Complete reset power and first-moment comparisons for full-response numerics. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The actual reset profile is controlled pointwise by the same double
geometric envelope as in the inverse-bank arithmetic. -/
theorem full_response_reset_term_le (C N : ℕ) (rate c : ℝ)
    (hN : (N:ℝ) ≤ rate*((C+1:ℕ):ℝ)) (hrate : 0 ≤ rate)
    (hc : 0 ≤ c) (hq : (3:ℝ)^(-rate) ≤ c) (hk : ℕ × ℕ) :
    (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ)) ≤
      (3:ℝ)^(-(N:ℝ))*(c^hk.1*c^hk.2) := by
  let g : ℕ → ℝ := fun n => c^n
  have hx (hk : ℕ × ℕ) :
      (C+1:ℕ)+hk.1+hk.2 ≤ localizationResetAbscissa C hk.1 hk.2 := by
    rw [localizationResetAbscissa]
    unfold localizationProfileDepth
    omega
  have hterm (hk : ℕ × ℕ) :
      (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ)) ≤
        (3:ℝ)^(-(N:ℝ))*(g hk.1*g hk.2) := by
    have hcast : (((C+1:ℕ)+hk.1+hk.2:ℕ):ℝ) ≤
        (localizationResetAbscissa C hk.1 hk.2:ℝ) := by exact_mod_cast hx hk
    have hexp : -(rate*(localizationResetAbscissa C hk.1 hk.2:ℝ)) ≤
        -(N:ℝ)-rate*(hk.1:ℝ)-rate*(hk.2:ℝ) := by
      have hsum : (N:ℝ)+hk.1*rate+hk.2*rate ≤
          rate*(localizationResetAbscissa C hk.1 hk.2:ℝ) := by
        have hmore := mul_le_mul_of_nonneg_left hcast hrate
        have hN' : (N:ℝ)+rate*((hk.1+hk.2:ℕ):ℝ) ≤
            rate*((C+1:ℕ):ℝ)+rate*((hk.1+hk.2:ℕ):ℝ) := by
          have hN0 := hN
          push_cast at hN0
          push_cast
          linarith [hN0]
        have hcastsum : ((hk.1+hk.2:ℕ):ℝ) = (hk.1:ℝ)+(hk.2:ℝ) := by norm_num
        rw [hcastsum] at hN'
        push_cast at hmore
        push_cast at hN'
        nlinarith only [hmore, hN']
      nlinarith only [hsum]
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hexp
    have hpowNat (n : ℕ) : (3:ℝ)^(-rate*(n:ℝ)) = ((3:ℝ)^(-rate))^n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    have hfactor :
        (3:ℝ)^(-(N:ℝ)-rate*(hk.1:ℝ)-rate*(hk.2:ℝ)) =
          (3:ℝ)^(-(N:ℝ))*((3:ℝ)^(-rate))^hk.1*((3:ℝ)^(-rate))^hk.2 := by
      calc
        _ = (3:ℝ)^(-(N:ℝ))*(3:ℝ)^(-rate*(hk.1:ℝ))*(3:ℝ)^(-rate*(hk.2:ℝ)) := by
          rw [show -(N:ℝ)-rate*(hk.1:ℝ)-rate*(hk.2:ℝ) =
            (-(N:ℝ)+(-rate*(hk.1:ℝ)))+(-rate*(hk.2:ℝ)) by ring]
          rw [Real.rpow_add (by norm_num : (0:ℝ)<3),
            Real.rpow_add (by norm_num : (0:ℝ)<3)]
        _ = _ := by rw [hpowNat, hpowNat]
    have hfactor_le : (3:ℝ)^(-(N:ℝ))*((3:ℝ)^(-rate))^hk.1*((3:ℝ)^(-rate))^hk.2 ≤
        (3:ℝ)^(-(N:ℝ))*(g hk.1*g hk.2) := by
      dsimp [g]
      have hq1 := pow_le_pow_left₀ (by positivity : 0 ≤ (3:ℝ)^(-rate)) hq hk.1
      have hq2 := pow_le_pow_left₀ (by positivity : 0 ≤ (3:ℝ)^(-rate)) hq hk.2
      have hfront : 0 ≤ (3:ℝ)^(-(N:ℝ)) := by positivity
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left
          (mul_le_mul hq1 hq2 (by positivity) (by positivity)) hfront)
    have hpow' : (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ)) ≤
        (3:ℝ)^(-(N:ℝ)-rate*(hk.1:ℝ)-rate*(hk.2:ℝ)) := by
      simpa only [neg_mul] using hpow
    exact hpow'.trans (hfactor.trans_le hfactor_le)
  exact hterm hk

end
end ASDExplicitGamma.Inverse

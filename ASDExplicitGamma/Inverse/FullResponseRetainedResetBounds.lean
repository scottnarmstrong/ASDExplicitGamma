module

public import ASDExplicitGamma.Inverse.FullResponseDecayNumerics

/-! Retained reset powers and first moments consume the complete geometric envelopes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- Both actual retained reset sums fit the same explicit positive geometric
majorants, with the leading resolution factor 3^-ρ kept exactly. -/
theorem full_response_retained_reset_bounds (a ρ β c : ℝ) (C N : ℕ)
    (hdecay : a < ρ) (hβ : β ≤ ρ-a) (hβ0 : 0 ≤ β)
    (hN : (N:ℝ) ≤ β*((C+1:ℕ):ℝ)) (hc : 0 ≤ c) (hc1 : c < 1)
    (hq : (3:ℝ)^(-β) ≤ c) :
    densityResetPowerSum a ρ C ≤ (3:ℝ)^(-ρ)*(3:ℝ)^(-(N:ℝ))*(1/(1-c))^2 ∧
    densityResetFirstPowerSum a ρ C ≤ (3:ℝ)^(-ρ)*(3:ℝ)^(-(N:ℝ))*
      (((C:ℝ)+2)*(1/(1-c))^2+3*c/(1-c)^3) := by
  have hraw := full_response_reset_moment_bounds C N β c hN hβ0 hc hc1 hq
  let x := fun hk : ℕ × ℕ => (localizationResetAbscissa C hk.1 hk.2:ℝ)
  let f := fun hk : ℕ × ℕ => (3:ℝ)^(a*x hk)*(3:ℝ)^(-ρ*(x hk+1))
  let g := fun hk : ℕ × ℕ => (3:ℝ)^(-ρ)*(3:ℝ)^(-β*x hk)
  have hp (hk : ℕ × ℕ) : f hk ≤ g hk := by
    have hx : 0 ≤ x hk := Nat.cast_nonneg _
    have he : (3:ℝ)^(a*x hk)*(3:ℝ)^(-ρ*(x hk+1)) =
        (3:ℝ)^(-ρ)*(3:ℝ)^(-(ρ-a)*x hk) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<3),← Real.rpow_add (by norm_num : (0:ℝ)<3)]
      congr 1
      ring
    dsimp only [f,g]
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
    have hh := mul_le_mul_of_nonneg_right hβ hx
    linarith only [hh]
  have hf := density_reset_power_hasSum a ρ hdecay C
  have hf1 := density_reset_first_power_hasSum a ρ hdecay C
  have hg : Summable g := hraw.1.1.mul_left ((3:ℝ)^(-ρ))
  have hg1 : Summable (fun hk => x hk*g hk) := by
    have hh := hraw.2.1.mul_left ((3:ℝ)^(-ρ))
    convert hh using 1
    funext hk
    dsimp only [g,x]
    ring
  constructor
  · have hh := hf.summable.tsum_le_tsum hp hg
    rw [hf.tsum_eq] at hh
    have he : (∑' hk : ℕ × ℕ, g hk) =
        (3:ℝ)^(-ρ)*(∑' hk : ℕ × ℕ, (3:ℝ)^(-β*x hk)) := tsum_mul_left
    rw [he] at hh
    have hb := mul_le_mul_of_nonneg_left hraw.1.2 (by positivity : (0:ℝ) ≤ (3:ℝ)^(-ρ))
    exact hh.trans (hb.trans_eq (by ring))
  · have hp1 (hk : ℕ × ℕ) : x hk*f hk ≤ x hk*g hk :=
      mul_le_mul_of_nonneg_left (hp hk) (Nat.cast_nonneg _)
    have hh := hf1.summable.tsum_le_tsum hp1 hg1
    rw [hf1.tsum_eq] at hh
    have he : (∑' hk : ℕ × ℕ, x hk*g hk) =
        (3:ℝ)^(-ρ)*(∑' hk : ℕ × ℕ, x hk*(3:ℝ)^(-β*x hk)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro hk
      dsimp only [g]
      ring
    rw [he] at hh
    have hb := mul_le_mul_of_nonneg_left hraw.2.2 (by positivity : (0:ℝ) ≤ (3:ℝ)^(-ρ))
    exact hh.trans (hb.trans_eq (by ring))

end
end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Inverse.BankProfileArithmetic
public import ASDExplicitGamma.Inverse.FullResponseTrace

/-! The certified full-response arithmetic profiles in source form. This
module records the outward constants and the attenuated p=128 profile; it does
not assert the analytic full-response bank estimate. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open ASDExplicitGamma.Numerics.Inverse

noncomputable section

/-- The outward source profile used for the attenuated p=128 response. -/
def fullResponseAttenuatedOutwardProfile (γ : ℝ) (h : ℕ) : ℝ :=
  4 * (2018618 / 1000000 + γ *
    (32474 * ((h : ℝ) + 1) + 11483216)) *
      (3 : ℝ) ^ ((2 * (h : ℝ) + 4) * γ)

/-- The p=64 constants in (11.7) are bounded by their audited outward caps. -/
theorem full_response_profile_64_outward (γ D : ℝ)
    (hγ : 0 ≤ γ) (hD : 0 ≤ D) :
    ((invFull64Bt : ℚ) : ℝ) + γ *
      (((invFull64KD : ℚ) : ℝ) * D + ((invFull64K0 : ℚ) : ℝ)) ≤
      2018618 / 1000000 + γ * (16684 * D + 5899542) := by
  have hc := bank_full_response_64_caps
  have hB : (invFull64Bt : ℝ) ≤ 2018618 / 1000000 := by
    exact hc.1.le.trans (by norm_num)
  have hDcap : (invFull64KD : ℝ) ≤ 16684 := by
    exact hc.2.1.le
  have h0 : (invFull64K0 : ℝ) ≤ 5899542 := by
    exact hc.2.2.le
  have hlinear : (invFull64KD : ℝ) * D + (invFull64K0 : ℝ) ≤
      16684 * D + 5899542 := by
    exact add_le_add (mul_le_mul_of_nonneg_right hDcap hD) h0
  calc
    (invFull64Bt : ℝ) + γ * ((invFull64KD : ℝ) * D + (invFull64K0 : ℝ))
        ≤ 2018618 / 1000000 + γ * (16684 * D + 5899542) :=
      add_le_add hB (mul_le_mul_of_nonneg_left hlinear hγ)

/-- The p=128 constants in (11.7) are bounded by their audited outward caps. -/
theorem full_response_profile_128_outward (γ D : ℝ)
    (hγ : 0 ≤ γ) (hD : 0 ≤ D) :
    ((invFull128Bt : ℚ) : ℝ) + γ *
      (((invFull128KD : ℚ) : ℝ) * D + ((invFull128K0 : ℚ) : ℝ)) ≤
      2018618 / 1000000 + γ * (32474 * D + 11483216) := by
  have hc := bank_full_response_128_caps
  have hB : (invFull128Bt : ℝ) ≤ 2018618 / 1000000 := by
    exact hc.1.le.trans (by norm_num)
  have hDcap : (invFull128KD : ℝ) ≤ 32474 := by
    exact hc.2.1.le
  have h0 : (invFull128K0 : ℝ) ≤ 11483216 := by
    exact hc.2.2.le
  have hlinear : (invFull128KD : ℝ) * D + (invFull128K0 : ℝ) ≤
      32474 * D + 11483216 := by
    exact add_le_add (mul_le_mul_of_nonneg_right hDcap hD) h0
  calc
    (invFull128Bt : ℝ) + γ * ((invFull128KD : ℝ) * D + (invFull128K0 : ℝ))
        ≤ 2018618 / 1000000 + γ * (32474 * D + 11483216) :=
      add_le_add hB (mul_le_mul_of_nonneg_left hlinear hγ)

end
end ASDExplicitGamma.Inverse

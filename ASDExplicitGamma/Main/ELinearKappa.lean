module

public import ASDExplicitGamma.Main.ErrorCoefficients
public import ASDExplicitGamma.Native.OldSignedQ1MultiplierCaps

/-! The derivative-only row coefficient of a depth-five source cell is below
the common coefficient `mainKd`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Native ASDExplicitGamma.Triadic Numerics.Native

/-- If the source cell side is at most `3⁻⁶` times the flat length, the
actual derivative coefficient is below `mainKd (b²)`. -/
theorem old_signed_derivative_kappa_le_mainKd (r b : ℝ) (L : {l : ℝ // 0 < l})
    (hr0 : 0 ≤ r) (hr : r ≤ (3 : ℝ) ^ (-6 : ℤ) * L.1) :
    oldSignedDerivativeKappa r b L.1 ≤ mainKd (b ^ 2) := by
  have hL := L.2
  have key : ∀ c X : ℝ, 0 ≤ c → c * Real.sqrt X = Real.sqrt (c ^ 2 * X) := by
    intro c X hc
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  have hs : r / L.1 ≤ (3 : ℝ) ^ (-6 : ℤ) := by
    rw [div_le_iff₀ hL]; exact hr
  have hs0 : 0 ≤ r / L.1 := div_nonneg hr0 hL.le
  have hs2 : (r / L.1) ^ 2 ≤ (3 : ℝ) ^ (-12 : ℤ) := by
    calc (r / L.1) ^ 2 ≤ ((3 : ℝ) ^ (-6 : ℤ)) ^ 2 := pow_le_pow_left₀ hs0 hs 2
      _ = _ := by rw [← zpow_natCast, ← zpow_mul]; norm_num
  have hs4 : (r / L.1) ^ 4 ≤ (3 : ℝ) ^ (-24 : ℤ) := by
    calc (r / L.1) ^ 4 ≤ ((3 : ℝ) ^ (-12 : ℤ)) ^ 2 := by
          rw [show (r / L.1) ^ 4 = ((r / L.1) ^ 2) ^ 2 by ring]
          exact pow_le_pow_left₀ (sq_nonneg _) hs2 2
      _ = _ := by rw [← zpow_natCast, ← zpow_mul]; norm_num
  have h1 : r * Real.sqrt ((78 / 5) * b ^ 2 / L.1 ^ 2) ≤
      Real.sqrt ((156 / 5) * mainA2 (b ^ 2)) := by
    rw [key r _ hr0, show r ^ 2 * ((78 / 5) * b ^ 2 / L.1 ^ 2) =
        (78 / 5) * b ^ 2 * (r / L.1) ^ 2 by field_simp]
    apply Real.sqrt_le_sqrt
    unfold mainA2
    have := mul_le_mul_of_nonneg_left hs2 (by positivity : (0:ℝ) ≤ (78 / 5) * b ^ 2)
    nlinarith [sq_nonneg b, zpow_pos (by norm_num : (0:ℝ) < 3) (-12 : ℤ)]
  have h2 : r ^ 2 * Real.sqrt ((23244 / 25) * b ^ 2 / L.1 ^ 4) ≤
      Real.sqrt ((46488 / 25) * mainA4 (b ^ 2)) := by
    rw [key (r ^ 2) _ (sq_nonneg r), show (r ^ 2) ^ 2 * ((23244 / 25) * b ^ 2 / L.1 ^ 4) =
        (23244 / 25) * b ^ 2 * (r / L.1) ^ 4 by field_simp]
    apply Real.sqrt_le_sqrt
    unfold mainA4
    have := mul_le_mul_of_nonneg_left hs4 (by positivity : (0:ℝ) ≤ (23244 / 25) * b ^ 2)
    nlinarith [sq_nonneg b, zpow_pos (by norm_num : (0:ℝ) < 3) (-24 : ℤ)]
  have hc : planarC0 * planarC1 ≤ (418 / 3125 : ℝ) := by
    have hh := mul_le_mul old_signed_q1_planarC0_le native_boundary_planarC1_le
      (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 11 / 25)
    exact hh.trans (by norm_num)
  unfold oldSignedDerivativeKappa mainKd
  have e1 : (2 / Real.pi) * r * Real.sqrt ((78 / 5) * b ^ 2 / L.1 ^ 2) =
      (2 / Real.pi) * (r * Real.sqrt ((78 / 5) * b ^ 2 / L.1 ^ 2)) := by ring
  rw [e1]
  have hsq1 := Real.sqrt_nonneg ((156 / 5) * mainA2 (b ^ 2))
  have hsq2 := Real.sqrt_nonneg ((46488 / 25) * mainA4 (b ^ 2))
  have hp1 : 0 ≤ r * Real.sqrt ((78 / 5) * b ^ 2 / L.1 ^ 2) :=
    mul_nonneg hr0 (Real.sqrt_nonneg _)
  have hp2 : 0 ≤ r ^ 2 * Real.sqrt ((23244 / 25) * b ^ 2 / L.1 ^ 4) :=
    mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have t1 := mul_le_mul old_signed_q1_two_div_pi_le h1 hp1 (by norm_num : (0:ℝ) ≤ 637/1000)
  have t2 := mul_le_mul hc h2 hp2 (by norm_num : (0:ℝ) ≤ 418/3125)
  calc _ = (2 / Real.pi) * (r * Real.sqrt ((78 / 5) * b ^ 2 / L.1 ^ 2)) +
        planarC0 * planarC1 * (r ^ 2 * Real.sqrt ((23244 / 25) * b ^ 2 / L.1 ^ 4)) := by ring
    _ ≤ (637 / 1000) * Real.sqrt ((156 / 5) * mainA2 (b ^ 2)) +
        (418 / 3125) * Real.sqrt ((46488 / 25) * mainA4 (b ^ 2)) := add_le_add t1 t2
    _ = _ := by ring

end ASDExplicitGamma.Main

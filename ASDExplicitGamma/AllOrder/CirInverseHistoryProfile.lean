/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.ProfileCaps
public import ASDExplicitGamma.Inverse.OrderResetInterface

/-! # Geometric summation of descendant inverse profiles -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3
  ASDExplicitGamma.Inverse

namespace ASDExplicitGamma.AllOrder

noncomputable section

private theorem aoCir_rpow_nat_mul (x : ℝ) (d : ℕ) :
    Real.rpow 3 (x * (d : ℝ)) = (Real.rpow 3 x) ^ d := by
  exact Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3) x d

private theorem aoCir_rpow_nine (x : ℝ) :
    Real.rpow 9 x = Real.rpow 3 (2 * x) := by
  calc
    Real.rpow 9 x = Real.rpow (Real.rpow 3 (2 : ℝ)) x := by
      rw [show (9 : ℝ) = Real.rpow 3 (2 : ℝ) by norm_num]
    _ = Real.rpow 3 (2 * x) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) 2 x).symm

/-- Summing the reset inverse profile over all descendant depths costs the
source history factor. The starting depth remains symbolic; its spatial
population cost is exposed separately as `9^(j/q)`. -/
theorem aoCir_inverse_profile_depth_series_bound
    (γ q : ℝ) (j : ℕ) (hγsmall : γ ≤ 1 / 327680) (hq48 : 48 ≤ q) :
    Summable (fun d : ℕ =>
          (Real.rpow 3 (-(1 / 4 : ℝ))) ^ d *
            Real.rpow 9 (((j + d : ℕ) : ℝ) / q) *
            orderInverseProfile (153 / 100) γ q (((j + d : ℕ) : ℝ) + 1)) ∧
    (1 - Real.rpow 3 (-(1 / 4 : ℝ))) *
        ∑' d : ℕ,
          (Real.rpow 3 (-(1 / 4 : ℝ))) ^ d *
            Real.rpow 9 (((j + d : ℕ) : ℝ) / q) *
            orderInverseProfile (153 / 100) γ q (((j + d : ℕ) : ℝ) + 1) ≤
      aoCirInverseHistoryFactor γ * Real.rpow 9 ((j : ℝ) / q) *
        orderInverseProfile (153 / 100) γ q ((j : ℝ) + 1) := by
  let r : ℝ := Real.rpow 3 (-(1 / 4 : ℝ))
  let ρ₀ : ℝ := Real.rpow 3 (-(5 / 24 : ℝ) + 2 * γ)
  let ρ : ℝ := Real.rpow 3 (-(1 / 4 : ℝ) + 2 / q + 2 * γ)
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hγ0 : γ ≤ 17 / 50000 := by norm_num at hγsmall ⊢; linarith
  have hfactor := aoCir_inverse_history_factor_cap hγ0
  have hqpos : 0 < q := by linarith
  have hq : 2 / q ≤ 1 / 24 := by
    rw [div_le_iff₀ hqpos]
    nlinarith
  have hρexp : -(1 / 4 : ℝ) + 2 / q + 2 * γ ≤ -(5 / 24 : ℝ) + 2 * γ := by
    linarith
  have hρ0lt : ρ₀ < 1 := by
    dsimp [ρ₀]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have hexp : -(5 / 24 : ℝ) + 2 * γ < 0 := by
      norm_num at hγsmall ⊢
      nlinarith
    linarith
  have hρ0pos : 0 < ρ₀ := Real.rpow_pos_of_pos (by norm_num) _
  have hρbound : ρ ≤ ρ₀ := by
    dsimp [ρ, ρ₀]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hρexp
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρlt : ρ < 1 := lt_of_le_of_lt hρbound hρ0lt
  have hbase0 : 0 ≤ Real.rpow 9 ((j : ℝ) / q) *
      orderInverseProfile (153 / 100) γ q ((j : ℝ) + 1) := by
    unfold orderInverseProfile
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
  let H : ℝ := (heightEntrance (orderBand q) : ℝ) + 20
  let e₀ : ℝ := 2 * ((j : ℝ) / q) + 2 * γ * H + 2 * γ * ((j : ℝ) + 1)
  let δ : ℝ := -(1 / 4 : ℝ) + 2 / q + 2 * γ
  have hterm (d : ℕ) :
      r ^ d * Real.rpow 9 (((j + d : ℕ) : ℝ) / q) *
          orderInverseProfile (153 / 100) γ q (((j + d : ℕ) : ℝ) + 1) =
        (Real.rpow 9 ((j : ℝ) / q) *
          orderInverseProfile (153 / 100) γ q ((j : ℝ) + 1)) * ρ ^ d := by
    let a₁ : ℝ := -(1 / 4 : ℝ) * (d : ℝ)
    let a₂ : ℝ := 2 * (((j + d : ℕ) : ℝ) / q)
    let a₃ : ℝ := 2 * γ * H + 2 * γ * (((j + d : ℕ) : ℝ) + 1)
    have hleft : r ^ d * Real.rpow 9 (((j + d : ℕ) : ℝ) / q) *
        orderInverseProfile (153 / 100) γ q (((j + d : ℕ) : ℝ) + 1) =
          (153 / 100 : ℝ) * Real.rpow 3 (a₁ + a₂ + a₃) := by
      calc
        _ = (153 / 100 : ℝ) *
            (Real.rpow 3 a₁ * Real.rpow 3 a₂ * Real.rpow 3 a₃) := by
          rw [orderInverseProfile, aoCir_rpow_nine]
          have hrpow : r ^ d = Real.rpow 3 a₁ := by
            dsimp [r, a₁]
            exact (aoCir_rpow_nat_mul (-(1 / 4 : ℝ)) d).symm
          rw [hrpow]
          dsimp [a₁, a₂, a₃, H]
          ring
        _ = (153 / 100 : ℝ) *
            (Real.rpow 3 (a₁ + a₂) * Real.rpow 3 a₃) := by
          exact congrArg (fun z => (153 / 100 : ℝ) * (z * Real.rpow 3 a₃))
            (Real.rpow_add (by norm_num : (0 : ℝ) < 3) a₁ a₂).symm
        _ = (153 / 100 : ℝ) * Real.rpow 3 ((a₁ + a₂) + a₃) := by
          exact congrArg (fun z => (153 / 100 : ℝ) * z)
            (Real.rpow_add (by norm_num : (0 : ℝ) < 3) (a₁ + a₂) a₃).symm
        _ = _ := by congr 2
    have hexp : -(1 / 4 : ℝ) * (d : ℝ) +
        2 * (((j + d : ℕ) : ℝ) / q) + 2 * γ * H +
        2 * γ * (((j + d : ℕ) : ℝ) + 1) = e₀ + δ * (d : ℝ) := by
      dsimp [e₀, δ]
      push_cast
      ring
    have hexpLet : a₁ + a₂ + a₃ = e₀ + δ * (d : ℝ) := by
      dsimp [a₁, a₂, a₃, e₀, δ, H]
      push_cast
      ring
    calc
      _ = (153 / 100 : ℝ) * Real.rpow 3 (e₀ + δ * (d : ℝ)) := by
        rw [hleft, hexpLet]
      _ = (153 / 100 : ℝ) *
          (Real.rpow 3 e₀ * Real.rpow 3 (δ * (d : ℝ))) := by
        exact congrArg (fun z => (153 / 100 : ℝ) * z)
          (Real.rpow_add (by norm_num : (0 : ℝ) < 3) e₀ (δ * (d : ℝ)))
      _ = (Real.rpow 9 ((j : ℝ) / q) *
          orderInverseProfile (153 / 100) γ q ((j : ℝ) + 1)) * ρ ^ d := by
        have hbase : Real.rpow 9 ((j : ℝ) / q) *
            orderInverseProfile (153 / 100) γ q ((j : ℝ) + 1) =
              (153 / 100 : ℝ) * Real.rpow 3 e₀ := by
          rw [orderInverseProfile, aoCir_rpow_nine]
          have hprofexp :
              2 * γ * ((heightEntrance (orderBand q) : ℝ) + 20) +
                  2 * γ * ((j : ℝ) + 1) =
                2 * γ * H + 2 * γ * ((j : ℝ) + 1) := by
            dsimp [H]
          rw [hprofexp]
          calc
            _ = (153 / 100 : ℝ) *
                (Real.rpow 3 (2 * ((j : ℝ) / q)) *
                  Real.rpow 3
                    (2 * γ * H + 2 * γ * ((j : ℝ) + 1))) := by
              simp only [Real.rpow_eq_pow]
              ring
            _ = (153 / 100 : ℝ) * Real.rpow 3
                (2 * ((j : ℝ) / q) +
                  (2 * γ * H + 2 * γ * ((j : ℝ) + 1))) := by
              exact congrArg (fun z => (153 / 100 : ℝ) * z)
                (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
                  (2 * ((j : ℝ) / q))
                  (2 * γ * H + 2 * γ * ((j : ℝ) + 1))).symm
            _ = _ := by
              have he : 2 * ((j : ℝ) / q) +
                  (2 * γ * H + 2 * γ * ((j : ℝ) + 1)) = e₀ := by
                dsimp [e₀, H]
                ring
              exact congrArg (fun z => (153 / 100 : ℝ) * Real.rpow 3 z) he
        have hdelta : Real.rpow 3 (δ * (d : ℝ)) = ρ ^ d := by
          dsimp [ρ, δ]
          exact aoCir_rpow_nat_mul _ _
        rw [hbase, hdelta]
        ring
  have hgeom0 : Summable (fun d : ℕ => ρ₀ ^ d) :=
    summable_geometric_of_lt_one hρ0pos.le hρ0lt
  have hgeom0sum : (∑' d : ℕ, ρ₀ ^ d) = (1 - ρ₀)⁻¹ :=
    tsum_geometric_of_lt_one hρ0pos.le hρ0lt
  let B : ℝ := Real.rpow 9 ((j : ℝ) / q) *
    orderInverseProfile (153 / 100) γ q ((j : ℝ) + 1)
  have hgeom : Summable (fun d : ℕ => ρ ^ d) :=
    summable_geometric_of_lt_one hρpos.le hρlt
  have hminor : Summable (fun d : ℕ => B * ρ ^ d) := hgeom.mul_left B
  have hmajor : Summable (fun d : ℕ => B * ρ₀ ^ d) := hgeom0.mul_left B
  have hcompare : (∑' d : ℕ, B * ρ ^ d) ≤ ∑' d : ℕ, B * ρ₀ ^ d :=
    hminor.tsum_le_tsum (fun d =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρpos.le hρbound d) hbase0) hmajor
  have hsumMajor :
      (∑' d : ℕ, r ^ d * Real.rpow 9 (((j + d : ℕ) : ℝ) / q) *
          orderInverseProfile (153 / 100) γ q (((j + d : ℕ) : ℝ) + 1)) ≤
        (Real.rpow 9 ((j : ℝ) / q) *
          orderInverseProfile (153 / 100) γ q ((j : ℝ) + 1)) *
          (1 - ρ₀)⁻¹ := by
    calc
      _ = ∑' d : ℕ,
          (Real.rpow 9 ((j : ℝ) / q) *
            orderInverseProfile (153 / 100) γ q ((j : ℝ) + 1)) * ρ ^ d := by
        apply tsum_congr
        exact hterm
      _ ≤ ∑' d : ℕ,
          (Real.rpow 9 ((j : ℝ) / q) *
            orderInverseProfile (153 / 100) γ q ((j : ℝ) + 1)) * ρ₀ ^ d := by
        simpa only [B] using hcompare
      _ = (Real.rpow 9 ((j : ℝ) / q) *
            orderInverseProfile (153 / 100) γ q ((j : ℝ) + 1)) *
          (1 - ρ₀)⁻¹ := by
        rw [tsum_mul_left, hgeom0sum]
  have hseriesSummable : Summable (fun d : ℕ =>
      r ^ d * Real.rpow 9 (((j + d : ℕ) : ℝ) / q) *
        orderInverseProfile (153 / 100) γ q (((j + d : ℕ) : ℝ) + 1)) := by
    have heq : (fun d : ℕ =>
        r ^ d * Real.rpow 9 (((j + d : ℕ) : ℝ) / q) *
          orderInverseProfile (153 / 100) γ q (((j + d : ℕ) : ℝ) + 1)) =
        fun d => B * ρ ^ d := funext hterm
    rw [heq]
    exact hgeom.mul_left B
  have hden : 0 < 1 - ρ₀ := sub_pos.mpr hρ0lt
  have hfactorEq : aoCirInverseHistoryFactor γ = (1 - r) * (1 - ρ₀)⁻¹ := by
    unfold aoCirInverseHistoryFactor
    dsimp [r, ρ₀]
    field_simp [ne_of_gt hden]
  refine ⟨?_, ?_⟩
  · simpa only [r] using hseriesSummable
  · calc
      (1 - r) * ∑' d : ℕ,
          r ^ d * Real.rpow 9 (((j + d : ℕ) : ℝ) / q) *
            orderInverseProfile (153 / 100) γ q (((j + d : ℕ) : ℝ) + 1)
          ≤ (1 - r) *
            ((Real.rpow 9 ((j : ℝ) / q) *
              orderInverseProfile (153 / 100) γ q ((j : ℝ) + 1)) *
              (1 - ρ₀)⁻¹) := by
        exact mul_le_mul_of_nonneg_left hsumMajor (le_of_lt (sub_pos.mpr hr1))
      _ = aoCirInverseHistoryFactor γ *
            (Real.rpow 9 ((j : ℝ) / q) *
              orderInverseProfile (153 / 100) γ q ((j : ℝ) + 1)) := by
        rw [hfactorEq]
        ring
      _ = _ := by ring

end
end ASDExplicitGamma.AllOrder

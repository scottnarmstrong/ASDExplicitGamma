module

public import ASDExplicitGamma.Numerics.Inverse.Scalars
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Monotone real-parameter form of the certified one-pass endpoint bound. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open ASDExplicitGamma.Numerics.Inverse

/-- The one-pass scalar expression is controlled by its certified value at
the maximal molecular parameter. -/
theorem bank_one_pass_scalar_bound (γ : ℝ) (hγ₀ : γ ≤ 17 / 50000) :
    let θ : ℝ := γ / (17 / 50000)
    let R40 : ℝ := (1 - (11 / 5 : ℝ) * 40 * γ)⁻¹
    R40 * (2 + (3 / 50 : ℝ) * θ +
      (711 / 40 : ℝ) * γ * (159 / 100 : ℝ) ^ 3 * R40) - 2 <
        747 / 5000 := by
  let γ₀ : ℝ := 17 / 50000
  let θ : ℝ := γ / γ₀
  let R40 : ℝ := (1 - (11 / 5 : ℝ) * 40 * γ)⁻¹
  let Rmax : ℝ := (1 - (11 / 5 : ℝ) * 40 * γ₀)⁻¹
  have hγ₀pos : 0 < γ₀ := by norm_num [γ₀]
  have hθle : θ ≤ 1 := by
    have hγbound : γ ≤ γ₀ := by dsimp [γ₀]; exact hγ₀
    dsimp [θ]
    exact (div_le_iff₀ hγ₀pos).2 (by simpa only [one_mul] using hγbound)
  have hdenMax : 0 < 1 - (11 / 5 : ℝ) * 40 * γ₀ := by
    norm_num [γ₀]
  have hden : 0 < 1 - (11 / 5 : ℝ) * 40 * γ := by
    have hmul : (11 / 5 : ℝ) * 40 * γ ≤ (11 / 5 : ℝ) * 40 * γ₀ := by
      exact mul_le_mul_of_nonneg_left hγ₀ (by norm_num)
    linarith
  have hRpos : 0 < R40 := by dsimp [R40]; positivity
  have hRmaxPos : 0 < Rmax := by dsimp [Rmax]; positivity
  have hdenMono :
      1 - (11 / 5 : ℝ) * 40 * γ₀ ≤ 1 - (11 / 5 : ℝ) * 40 * γ := by
    have hmul : (11 / 5 : ℝ) * 40 * γ ≤ (11 / 5 : ℝ) * 40 * γ₀ := by
      exact mul_le_mul_of_nonneg_left hγ₀ (by norm_num)
    linarith
  have hRle : R40 ≤ Rmax := by
    dsimp [R40, Rmax]
    simpa only [one_div] using one_div_le_one_div_of_le hdenMax hdenMono
  have hRθ : R40 * θ ≤ Rmax := by
    calc
      R40 * θ ≤ R40 * 1 := mul_le_mul_of_nonneg_left hθle hRpos.le
      _ = R40 := by ring
      _ ≤ Rmax := hRle
  have hR2 : R40 ^ 2 ≤ Rmax ^ 2 := by
    have hsquare : 0 ≤ (Rmax - R40) * (Rmax + R40) :=
      mul_nonneg (sub_nonneg.mpr hRle) (add_nonneg hRmaxPos.le hRpos.le)
    nlinarith
  have hγR2 : γ * R40 ^ 2 ≤ γ₀ * Rmax ^ 2 := by
    calc
      γ * R40 ^ 2 ≤ γ₀ * R40 ^ 2 :=
        mul_le_mul_of_nonneg_right hγ₀ (sq_nonneg R40)
      _ ≤ γ₀ * Rmax ^ 2 :=
        mul_le_mul_of_nonneg_left hR2 hγ₀pos.le
  have hcoef : 0 ≤ (711 / 40 : ℝ) * (159 / 100 : ℝ) ^ 3 := by positivity
  have hterm :
      R40 * (2 + (3 / 50 : ℝ) * θ +
        (711 / 40 : ℝ) * γ * (159 / 100 : ℝ) ^ 3 * R40) ≤
      Rmax * (2 + (3 / 50 : ℝ) +
        (711 / 40 : ℝ) * γ₀ * (159 / 100 : ℝ) ^ 3 * Rmax) := by
    calc
      _ = 2 * R40 + (3 / 50 : ℝ) * (R40 * θ) +
          ((711 / 40 : ℝ) * (159 / 100 : ℝ) ^ 3) * (γ * R40 ^ 2) := by ring
      _ ≤ 2 * Rmax + (3 / 50 : ℝ) * Rmax +
          ((711 / 40 : ℝ) * (159 / 100 : ℝ) ^ 3) * (γ₀ * Rmax ^ 2) := by
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hRle (by norm_num))
          (mul_le_mul_of_nonneg_left hRθ (by norm_num)))
          (mul_le_mul_of_nonneg_left hγR2 hcoef)
      _ = _ := by ring
  have hRmax_eq : Rmax = (invR40 : ℝ) := by
    dsimp [Rmax, γ₀, invR40, invE, invGamma]
    norm_num
  have hγ₀_eq : γ₀ = (invGamma : ℝ) := by
    norm_num [γ₀, invGamma]
  rcases invOnePass with ⟨_, hendpoint, hcap, _⟩
  have hendpoint' :
      Rmax * (2 + (3 / 50 : ℝ) +
        (711 / 40 : ℝ) * γ₀ * (159 / 100 : ℝ) ^ 3 * Rmax) - 2 <
          747 / 5000 := by
    rw [hRmax_eq, hγ₀_eq]
    have hrat := hendpoint.trans_lt hcap
    norm_num [invGamma, invR40, invE] at hrat ⊢
  calc
    R40 * (2 + (3 / 50 : ℝ) * θ +
      (711 / 40 : ℝ) * γ * (159 / 100 : ℝ) ^ 3 * R40) - 2 ≤
        Rmax * (2 + (3 / 50 : ℝ) +
          (711 / 40 : ℝ) * γ₀ * (159 / 100 : ℝ) ^ 3 * Rmax) - 2 :=
      sub_le_sub_right hterm 2
    _ < 747 / 5000 := hendpoint'

end ASDExplicitGamma.Inverse

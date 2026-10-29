module

public import ASDExplicitGamma.Inverse.BankInverse
public import ASDExplicitGamma.Main.InverseDeficitODE

/-! The global inverse bank supplies the exact L128 history/remainder
inputs in the ENNReal representation consumed by the inverse-deficit cubic. -/
@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Inverse
open scoped ENNReal

/-- Convert one actual global inverse-bank conclusion into the integrated
source cubic estimate. The history cap is `β=14103/10000`; the ordinary
remainder reserve is `ε_n=10^-24`. -/
theorem main_inverse_deficit_cubic_integral_bound_of_global_bank
    (M : ABKModel 2) (s : Finset (TriadicCube 2)) (m J : ℤ)
    (weights : ℤ → ℝ) (d : Cutoff.CutoffSample 2 → ℝ)
    (hBank : InverseBankConclusion M .globalInverse s m J weights)
    (hdMeas : Measurable d)
    (hd : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      0 ≤ d ω ∧ d ω ≤ 2 *
        (bankFiniteRootHistoryMax s M m J weights ω).toReal) :
    ∫ ω,
        (bankFiniteRootHistoryMax s M m J weights ω).toReal ^ 2 * d ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (inverseBankCap .globalInverse:ℝ)^2 *
          (∫ ω, d ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
        2 * (2 * (inverseBankCap .globalInverse:ℝ)^2 *
              (inverseBankReserve .globalInverse:ℝ) +
            3 * (inverseBankCap .globalInverse:ℝ) *
              (inverseBankReserve .globalInverse:ℝ)^2 +
            (inverseBankReserve .globalInverse:ℝ)^3) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let β : ℝ := inverseBankCap .globalInverse
  let ε : ℝ := inverseBankReserve .globalInverse
  let Y : Cutoff.CutoffSample 2 → ENNReal :=
    bankFiniteRootHistoryMax s M m J weights
  let R₀ : Cutoff.CutoffSample 2 → ℝ :=
    inverseBankPopulationRemainder .globalInverse s M m J weights
  let R : Cutoff.CutoffSample 2 → ENNReal := fun ω => ENNReal.ofReal (R₀ ω)
  have hβ : 0 ≤ β := by
    norm_num [β, inverseBankCap]
  have hε : 0 ≤ ε := by
    norm_num [ε, inverseBankReserve]
  have hR₀ : ∀ ω, 0 ≤ R₀ ω := by
    intro ω
    exact hBank.remainder_nonneg ω
  have hsplit : ∀ᵐ ω ∂μ, (Y ω).toReal ≤ β + (R ω).toReal := by
    filter_upwards [hBank.history_le] with ω hω
    have hω' : Y ω ≤ ENNReal.ofReal (β + R₀ ω) := by
      rw [← ENNReal.ofReal_add hβ (hR₀ ω)] at hω
      simpa [Y, β, R₀] using hω
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hω'
    simpa [Y, R, ENNReal.toReal_ofReal (add_nonneg hβ (hR₀ ω)),
      ENNReal.toReal_ofReal (hR₀ ω)] using hreal
  have hRfinite : ∀ᵐ ω ∂μ, R ω < ⊤ :=
    Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top
  have hRcap : eLpNorm R 128 μ ≤ ENNReal.ofReal ε := by
    change eLpNorm (ENNReal.ofReal ∘ R₀) 128 μ ≤ _
    calc
      _ = eLpNorm R₀ 128 μ := by
        exact eLpNorm_ofReal R₀ (Filter.Eventually.of_forall hR₀)
      _ ≤ _ := hBank.remainder_L128
  simpa only [μ, β, ε, Y] using
    main_inverse_deficit_cubic_integral_bound_of_ennreal_l128_banks
      β ε Y R d hβ hε hsplit hd hdMeas hBank.history_finite hBank.total_L128
      hRfinite hRcap

end ASDExplicitGamma.Main

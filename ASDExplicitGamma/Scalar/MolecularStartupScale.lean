module

public import ASDExplicitGamma.Model.ShellScaling
public import ASDExplicitGamma.Statements.Theta
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Filter Algsuperdiff.Section3

/-- The actual accumulated shell variance vanishes down the completed labels. -/
theorem shellVarianceSum_tendsto_atBot (h γ : ℝ) (hγ : 0 < γ) :
    Tendsto (shellVarianceSum h γ) atBot (nhds 0) := by
  have hc : Tendsto (fun n : ℤ => (n : ℝ)) atBot atBot := by
    apply tendsto_atBot.mpr
    intro b
    exact eventually_atBot.mpr ⟨⌊b⌋, fun n hn =>
      (Int.cast_le.mpr hn).trans (Int.floor_le b)⟩
  have hm : Tendsto (fun n : ℤ => 2 * γ * (n : ℝ)) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (by positivity : 0 < 2 * γ)).mpr hc
  have hp := (tendsto_rpow_atBot_of_base_gt_one 3 (by norm_num)).comp hm
  have hv := (hp.const_mul (h ^ 2)).div_const (1 - (3 : ℝ) ^ (-(2 * γ)))
  change Tendsto (fun n : ℤ => h ^ 2 * (3 : ℝ) ^ (2 * γ * (n : ℝ)) /
    (1 - (3 : ℝ) ^ (-(2 * γ)))) atBot (nhds 0)
  simpa only [Function.comp_apply, mul_zero, zero_div] using hv

/-- A single completed-label half-line satisfies any positive molecular
variance threshold; the cutoff depends on the fixed molecular parameter. -/
theorem exists_molecular_variance_halfLine (M : ABKModel 2) (h ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℤ, ∀ n : ℤ, n ≤ K → shellVarianceSum h M.gamma n / M.nu ^ 2 ≤ ε := by
  have ht := (shellVarianceSum_tendsto_atBot h M.gamma M.shellPrefix.gamma_pos).div_const (M.nu ^ 2)
  have he : ∀ᶠ n : ℤ in atBot, shellVarianceSum h M.gamma n / M.nu ^ 2 < ε := by
    apply (tendsto_order.mp (by simpa only [zero_div] using ht)).2 ε hε
  obtain ⟨K, hK⟩ := eventually_atBot.mp he
  exact ⟨K, fun n hn => (hK n hn).le⟩

/-- The entrance threshold is attained uniformly on one left half-line. -/
theorem exists_startup_variance_halfLine (M : ABKModel 2) (h : ℝ) :
    ∃ K : ℤ, ∀ n : ℤ, n ≤ K →
      shellVarianceSum h M.gamma n / M.nu ^ 2 ≤ theta M / 400 := by
  apply exists_molecular_variance_halfLine
  have hzero : 0 < gammaZero := by norm_num [gammaZero]
  exact div_pos (div_pos M.shellPrefix.gamma_pos hzero) (by norm_num)

end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Inverse.StoppedDensityPE
public import ASDExplicitGamma.Inverse.WeightedLocalizationResetSeries
public import ASDExplicitGamma.Statements.GammaZero

/-! Complete reset series for each of the actual retained density powers. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- Combining a clock and a retained power gives the exact geometric reset
factor, including its leading resolution offset. -/
theorem density_reset_power_eq (a ν : ℝ) (x : ℕ) :
    (3:ℝ)^(a*(x:ℝ))*(3:ℝ)^(-ν*((x:ℝ)+1)) =
      (3:ℝ)^(-ν)*((3:ℝ)^(a-ν))^x := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3),
    ← Real.rpow_add (by norm_num : (0:ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  congr 1
  ring

/-- Exact closed value of the complete reset power sum. -/
def densityResetPowerSum (a ν : ℝ) (C : ℕ) : ℝ :=
  let z := (3:ℝ)^(a-ν)
  (3:ℝ)^(-ν)*(z^C*localizationProfileT 1 z/(1-z))

/-- Exact closed value of its complete first abscissa moment. -/
def densityResetFirstPowerSum (a ν : ℝ) (C : ℕ) : ℝ :=
  let z := (3:ℝ)^(a-ν)
  (3:ℝ)^(-ν)*(z^C*((C:ℝ)*localizationProfileT 1 z/(1-z)+
    z*localizationProfileT 1 z/(1-z)^2+localizationProfileTf 1 z/(1-z)))

/-- The full infinite height/layer series, with no cutoff in either index. -/
theorem density_reset_power_hasSum (a ν : ℝ) (hdecay : a < ν) (C : ℕ) :
    HasSum (fun p : ℕ × ℕ =>
      (3:ℝ)^(a*(localizationResetAbscissa C p.1 p.2:ℝ))*
      (3:ℝ)^(-ν*((localizationResetAbscissa C p.1 p.2:ℝ)+1)))
      (densityResetPowerSum a ν C) := by
  have hz : 0 ≤ (3:ℝ)^(a-ν) := Real.rpow_nonneg (by norm_num) _
  have hz1 : (3:ℝ)^(a-ν) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hdecay)
  simpa only [density_reset_power_eq,densityResetPowerSum] using
    (localization_reset_series_hasSum _ hz hz1 C).mul_left ((3:ℝ)^(-ν))

/-- The complete first moment, retaining the literal x_{kh} factor. -/
theorem density_reset_first_power_hasSum (a ν : ℝ) (hdecay : a < ν) (C : ℕ) :
    HasSum (fun p : ℕ × ℕ =>
      (localizationResetAbscissa C p.1 p.2:ℝ)*
      ((3:ℝ)^(a*(localizationResetAbscissa C p.1 p.2:ℝ))*
      (3:ℝ)^(-ν*((localizationResetAbscissa C p.1 p.2:ℝ)+1))))
      (densityResetFirstPowerSum a ν C) := by
  have hz : 0 ≤ (3:ℝ)^(a-ν) := Real.rpow_nonneg (by norm_num) _
  have hz1 : (3:ℝ)^(a-ν) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hdecay)
  have hh := (localization_reset_first_series_hasSum _ hz hz1 C).mul_left ((3:ℝ)^(-ν))
  convert hh using 1
  · funext p
    rw [density_reset_power_eq]
    ring
  · rfl

/-- Every source density exponent exceeds both required clock rates under
exactly the campaign gamma cap, for m=2 or m=4. -/
theorem density_rates_decay (γ : ℝ) (hγ : γ ≤ gammaZero)
    (m : ℕ) (hm : m=2 ∨ m=4) (i : Fin 3) :
    2*γ < densityPERate m i ∧ 4*γ < densityPERate m i/2 := by
  have hg : γ ≤ 17/50000 := hγ
  rcases hm with rfl | rfl <;> fin_cases i <;>
    norm_num [densityPERate] <;> constructor <;> linarith only [hg]

end
end ASDExplicitGamma.Inverse

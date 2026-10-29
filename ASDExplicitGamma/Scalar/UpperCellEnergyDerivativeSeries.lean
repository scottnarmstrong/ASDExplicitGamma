module

public import ASDExplicitGamma.Scalar.UpperCellEnergyShellVariance
public import Mathlib.Algebra.Order.Field.GeomSum

/-! Covariances are summed with their physical derivative decay. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Finset
noncomputable section

/-- A uniform geometric ratio for every positive derivative order. -/
theorem upper_cell_derivative_ratio_le (gamma : ℝ) (hg : gamma ≤ 1/6)
    (k : ℕ) (hk : 1 ≤ k) :
    (3:ℝ)^(2*gamma-2*(k:ℝ)) ≤ 1/6 := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hpow : ((3:ℝ)^(2*gamma-2*(k:ℝ)))^3 = (3:ℝ)^(6*gamma-6*(k:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
    congr 1
    ring
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num : (0:ℝ)≤1/6)
    (by norm_num : (3:ℕ) ≠ 0)).mp
  rw [hpow]
  calc
    (3:ℝ)^(6*gamma-6*(k:ℝ)) ≤ (3:ℝ)^(-5:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hg,hkR])
    _ ≤ (1/6:ℝ)^3 := by norm_num [Real.rpow_neg,Real.rpow_ofNat]

/-- The complete finite future derivative covariance pays less than one
unit of gamma. No summation of shellwise supremum norms is used. -/
theorem upper_cell_derivative_geometric_sum (gamma : ℝ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ 1/6) (k height : ℕ) (hk : 1 ≤ k) :
    (9/2:ℝ)*gamma*∑ j ∈ Ico 1 (height+1),
      ((3:ℝ)^(2*gamma-2*(k:ℝ)))^j ≤ gamma := by
  let q := (3:ℝ)^(2*gamma-2*(k:ℝ))
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq := upper_cell_derivative_ratio_le gamma hg k hk
  change q ≤ 1/6 at hq
  have hq1 : q < 1 := hq.trans_lt (by norm_num)
  have hsum := geom_sum_Ico_le_of_lt_one (m := 1) (n := height+1) hq0 hq1
  simp only [pow_one] at hsum
  have hfrac : q/(1-q) ≤ (1/5:ℝ) := by
    rw [div_le_iff₀ (sub_pos.mpr hq1)]
    linarith only [hq]
  have hh := mul_le_mul_of_nonneg_left (hsum.trans hfrac)
    (mul_nonneg (by norm_num : (0:ℝ)≤9/2) hg0)
  change (9/2:ℝ)*gamma*∑ j ∈ Ico 1 (height+1),q^j ≤ gamma
  linarith only [hh,hg0]

end
end ASDExplicitGamma.Scalar

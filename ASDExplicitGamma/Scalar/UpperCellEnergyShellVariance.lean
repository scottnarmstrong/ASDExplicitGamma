module

public import ASDExplicitGamma.Scalar.UpperCellEnergySignal

/-! Physical fresh-shell covariance normalization in the completed true frame. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Algsuperdiff.Section3
noncomputable section

/-- The geometric denominator costs at most 2.2 gamma, uniformly for every
positive gamma; this estimate needs no long-block upper state. -/
theorem upper_cell_variance_denominator_le (gamma : ℝ) (hg : 0 ≤ gamma) :
    1-(3:ℝ)^(-(2*gamma)) ≤ (11/5:ℝ)*gamma := by
  have he := Real.add_one_le_exp (-(2*gamma)*Real.log 3)
  rw [mul_comm (-(2*gamma)) (Real.log 3)] at he
  have hl := mul_le_mul_of_nonneg_right Numerics.Scalar.twice_log_three_lt.le hg
  rw [Real.rpow_def_of_pos (by norm_num)]
  nlinarith only [he,hl]

/-- The actual completed lower corridor normalizes the left-endpoint shell
variance by (9/2) gamma. It uses the OLD native state only. -/
theorem upper_cell_base_variance_le
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (hstate : nativeInductionState M h n) :
    h^2*(3:ℝ)^(2*M.gamma*(n:ℝ)) ≤
      (9/2:ℝ)*M.gamma*(Annealed.sigmaBar M n:ℝ)^2 := by
  let d := 1-(3:ℝ)^(-(2*M.gamma))
  have hd : 0 < d := sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
    (by norm_num) (by nlinarith only [M.shellPrefix.gamma_pos]))
  have hdl : d ≤ (11/5:ℝ)*M.gamma :=
    upper_cell_variance_denominator_le M.gamma M.shellPrefix.gamma_pos.le
  have hlow : (31/50:ℝ)*shellVarianceSum h M.gamma n ≤ (Annealed.sigmaBar M n:ℝ)^2 := by
    have hh := hstate.2.2.2.2.2.2.1
    nlinarith only [hh,sq_nonneg M.nu]
  have hbase : shellVarianceSum h M.gamma n*d = h^2*(3:ℝ)^(2*M.gamma*(n:ℝ)) := by
    unfold shellVarianceSum
    exact div_mul_cancel₀ _ hd.ne'
  have hprod := mul_le_mul_of_nonneg_right hlow hd.le
  have hprod2 := mul_le_mul_of_nonneg_left hdl (sq_nonneg (Annealed.sigmaBar M n:ℝ))
  rw [mul_assoc,hbase] at hprod
  have hpositive := mul_nonneg M.shellPrefix.gamma_pos.le
    (sq_nonneg (Annealed.sigmaBar M n:ℝ))
  nlinarith only [hprod,hprod2,hpositive]

/-- Exact future-shell normalization, preserving its relative scale j.
This supplies the covariance input before summing derivative orders. -/
theorem upper_cell_fresh_shell_variance_le
    (M : ABKModel 2) (h : ℝ) (n j : ℤ) (hstate : nativeInductionState M h n) :
    h^2*(3:ℝ)^(2*M.gamma*((n+j:ℤ):ℝ))/(Annealed.sigmaBar M n:ℝ)^2 ≤
      (9/2:ℝ)*M.gamma*(3:ℝ)^(2*M.gamma*(j:ℝ)) := by
  have hs := (Annealed.sigmaBar M n).property
  rw [div_le_iff₀ (sq_pos_of_pos hs)]
  have he : 2*M.gamma*((n+j:ℤ):ℝ) = 2*M.gamma*(n:ℝ)+2*M.gamma*(j:ℝ) := by
    push_cast; ring
  rw [he,Real.rpow_add (by norm_num : (0:ℝ)<3),←mul_assoc]
  have hh := mul_le_mul_of_nonneg_right (upper_cell_base_variance_le M h n hstate)
    (Real.rpow_nonneg (by norm_num : (0:ℝ)≤3) (2*M.gamma*(j:ℝ)))
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Native.ParentRowHistoryDeltaValue
public import ASDExplicitGamma.Native.ParentRowMeanClockBridge
public import ASDExplicitGamma.Native.ParentBoundaryCommonHistoryDelta

/-! Exact identification of the physical history drift with the stored program. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Scalar Cold Algsuperdiff.Section3
noncomputable section

/-- The source quarter discount is the nested-root program constant. -/
theorem parent_row_discount_root :
    inverseHistoryDiscount=1/Real.sqrt (Real.sqrt 3) := by
  have he : Real.sqrt (Real.sqrt (3:ℝ))=(3:ℝ)^(1/4:ℝ) := by
    simp only [Real.sqrt_eq_rpow]
    rw [←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
    norm_num
  rw [he,one_div,inverse_history_discount_eq]

/-- The five polynomial coefficients are unchanged by square-root factoring. -/
theorem parent_row_history_polynomial_eq (a2 a4 : ℝ) (i : Fin 5) :
    parentBoundaryCommonKernelCoefficients a2 a4 i=parentRowHistoryPolynomial a2 a4 i := by
  have hs (x : ℝ) (c : ℝ) (hc : 0≤c) : Real.sqrt (x*c)=Real.sqrt x*Real.sqrt c :=
    Real.sqrt_mul' x hc
  dsimp only [parentBoundaryCommonKernelCoefficients,parentRowHistoryPolynomial]
  simp only [hs a2 (39/5) (by norm_num),hs a2 (156/5) (by norm_num),hs a4 (46488/25) (by norm_num),
      hs a2 (78/5) (by norm_num),hs a4 (23244/25) (by norm_num)]
  fin_cases i <;> dsimp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;> ring

/-- Literal source geometric ratios use the same real exponentials as the program. -/
theorem parent_row_history_ratio_eq (growth : ℝ) (i : Fin 5) :
    parentBoundaryCommonHistoryRatio gammaZero growth i=
      (1/Real.exp (Real.log 3*(3/20)))*Real.exp (Real.log 3*(growth*(17/50000)))*
        (1/3:ℝ)^i.val := by
  unfold parentBoundaryCommonHistoryRatio coldHistoryBeta gammaZero
  rw [Real.rpow_neg (by norm_num : (0:ℝ)≤3),
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3),
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  simp only [one_div]

/-- The physical complete-depth drift is exactly the unrounded parent program. -/
theorem parent_row_history_delta_eq (height : ℕ) :
    parentBoundaryCommonSourceDelta gammaZero height 5=parentRowHistoryDeltaValue height := by
  unfold parentBoundaryCommonSourceDelta parentBoundaryCommonKernelGeometric
  rw [parent_row_mean_variance_eq,parent_row_mean_a2_eq,parent_row_mean_a4_eq,
    parent_row_mean_raw_base_eq,parent_row_mean_raw_factor_eq]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,Finset.mul_sum]
  unfold parentRowHistoryDeltaValue
  apply Finset.sum_congr rfl
  intro i _
  rw [parent_row_discount_root,parent_row_history_polynomial_eq,
    parent_row_history_ratio_eq,parent_row_history_ratio_eq]
  norm_num only [gammaZero,show (8:ℝ)*(17/50000)=17/6250 by norm_num,
    show (6:ℝ)*(17/50000)=51/25000 by norm_num]
  ring

end
end ASDExplicitGamma.Native

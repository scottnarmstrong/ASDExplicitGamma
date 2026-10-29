module

public import ASDExplicitGamma.Native.ParentRowSymbolic
public import ASDExplicitGamma.Native.ParentBoundaryBandEnergy

/-! The exact full-band endpoint variance as a finite physical shell sum. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Algsuperdiff.Section3 Numerics.Native Numerics.Mirror
noncomputable section

/-- Source syntax for the variance of shell k+1, retaining producer order. -/
def parentRowShellExpr (k : ℕ) : Expr :=
  let e := Expr.exp (.mul (.var 2) (.const ((17/25000:ℚ)*(k+1))))
  .mul e (.const (153/100000))

/-- The finite shell sum used by each literal parent program. -/
def parentRowVarianceExpr : ℕ → Expr
  | 0 => .const 0
  | k+1 => .add (parentRowVarianceExpr k) (parentRowShellExpr k)

/-- Exact endpoint physical variance; no rational enlargement is inserted. -/
def parentRowVarianceClock (height : ℕ) : ℝ :=
  ∑ k ∈ Finset.range height,nativeSourceShellClock gammaZero (k+1)

/-- Every symbolic shell denotes its exact source clock. -/
theorem parent_row_shell_expr_eval (env : ℕ → ℝ) (hlog : env 2=Real.log 3) (k : ℕ) :
    evalReal env (parentRowShellExpr k)=nativeSourceShellClock gammaZero (k+1) := by
  have hc : (((17/25000:ℚ)*(k+1):ℚ):ℝ)=2*gammaZero*((k+1:ℕ):ℝ) := by
    push_cast
    norm_num [gammaZero]
  have he : evalReal env (.exp (.mul (.var 2) (.const ((17/25000:ℚ)*(k+1)))))=
      (3:ℝ)^(2*gammaZero*((k+1:ℕ):ℝ)) := by
    simp only [evalReal,hlog,hc,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  have hv : ((153/100000:ℚ):ℝ)=(9/2:ℝ)*gammaZero := by norm_num [gammaZero]
  change evalReal env (.exp (.mul (.var 2) (.const ((17/25000:ℚ)*(k+1)))))*((153/100000:ℚ):ℝ)=_
  rw [he,hv]
  exact mul_comm _ _

/-- The reflected finite sum denotes the same physical sum at every height. -/
theorem parent_row_variance_expr_eval (env : ℕ → ℝ) (hlog : env 2=Real.log 3)
    (height : ℕ) :
    evalReal env (parentRowVarianceExpr height)=parentRowVarianceClock height := by
  induction height with
  | zero => simp only [parentRowVarianceExpr,evalReal,Rat.cast_zero,parentRowVarianceClock,Finset.range_zero,Finset.sum_empty]
  | succ k ih =>
    simp only [parentRowVarianceExpr,evalReal,ih,parent_row_shell_expr_eval env hlog,
      parentRowVarianceClock,Finset.sum_range_succ]

/-- Endpoint domination keeps the exact single theta factor of a shell. -/
theorem parent_row_shell_clock_theta (M : ABKModel 2) (hg : M.gamma≤gammaZero)
    (s : ℕ) :
    nativeSourceShellClock M.gamma s≤theta M*nativeSourceShellClock gammaZero s := by
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤2)) (Nat.cast_nonneg s))
  have hh := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (by norm_num : (0:ℝ)≤9/2) M.shellPrefix.gamma_pos.le)
  apply hh.trans_eq
  unfold theta nativeSourceShellClock
  have hgamma : gammaZero≠0 := by norm_num [gammaZero]
  field_simp

/-- Every actual shell is retained in the parent full-variance allowance. -/
theorem parent_row_actual_variance_clock
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (height : ℕ) (hstate : nativeInductionState M h n) :
    parentBoundaryBandVariance M h n height≤theta M*parentRowVarianceClock height := by
  have hv := parent_boundary_band_variance_clock M h n height hstate
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin height))) =>
      parent_row_shell_clock_theta M hg (i.val+1))
  apply (hv.trans hs).trans_eq
  rw [←Finset.mul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => nativeSourceShellClock gammaZero (k+1)) height

end
end ASDExplicitGamma.Native

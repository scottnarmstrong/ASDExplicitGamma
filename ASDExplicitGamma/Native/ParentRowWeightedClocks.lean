module

public import ASDExplicitGamma.Native.ParentRowVarianceExpr

/-! Exact weighted physical shell sums for the parent derivative and energy clocks. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Algsuperdiff.Section3 Numerics.Native Numerics.Mirror
noncomputable section

/-- The source program's weighted finite shell sum. -/
def parentRowWeightedExpr (w : ℕ → ℚ) : ℕ → Expr
  | 0 => .const 0
  | k+1 => .add (parentRowWeightedExpr w k) (.mul (parentRowShellExpr k) (.const (w k)))

/-- The same weighted shell clock in real scalars. -/
def parentRowWeightedClock (w : ℕ → ℚ) (height : ℕ) : ℝ :=
  ∑ k ∈ Finset.range height,nativeSourceShellClock gammaZero (k+1)*(w k:ℝ)

/-- The exact mesh-five derivative weight. -/
def parentRowA2Weight (k : ℕ) : ℚ := (1/9)^(k+6)

/-- The summable physical Dirichlet clock weight. -/
def parentRowYWeight (k : ℕ) : ℚ := (26/15)*(1/9)^(k+1)

/-- Symbolic weighted sums denote the same physical source clocks. -/
theorem parent_row_weighted_expr_eval (env : ℕ → ℝ) (hlog : env 2=Real.log 3)
    (w : ℕ → ℚ) (height : ℕ) :
    evalReal env (parentRowWeightedExpr w height)=parentRowWeightedClock w height := by
  induction height with
  | zero => simp only [parentRowWeightedExpr,evalReal,Rat.cast_zero,parentRowWeightedClock,Finset.range_zero,Finset.sum_empty]
  | succ k ih =>
    simp only [parentRowWeightedExpr,evalReal,ih,parent_row_shell_expr_eval env hlog,
      parentRowWeightedClock,Finset.sum_range_succ]

/-- Every nonnegative physical shell weight preserves the single theta factor. -/
theorem parent_row_weighted_actual_variance
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (height : ℕ) (hstate : nativeInductionState M h n)
    (w : ℕ → ℚ) (hw : ∀ k,0≤w k) :
    (∑ i : Fin height,
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))^2*(w i.val:ℝ))≤
      theta M*parentRowWeightedClock w height := by
  have hi (i : Fin height) :=
    (native_source_shell_variance_le_clock M h n (i.val+1) (i.val+1) hstate le_rfl).trans
      (parent_row_shell_clock_theta M hg (i.val+1))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ (Finset.univ : Finset (Fin height))) =>
    mul_le_mul_of_nonneg_right (hi i) (show (0:ℝ)≤(w i.val:ℝ) by exact_mod_cast hw i.val))
  simp only [←div_pow] at hs
  apply hs.trans_eq
  simp only [mul_assoc,←Finset.mul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => nativeSourceShellClock gammaZero (k+1)*(w k:ℝ)) height

end
end ASDExplicitGamma.Native

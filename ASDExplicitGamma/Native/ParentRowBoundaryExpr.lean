module

public import ASDExplicitGamma.Native.ParentRowBoundaryWeights

/-! Exact finite-shell programs for the two centered boundary coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Algsuperdiff.Section3 Numerics.Native Numerics.Mirror
noncomputable section

/-- Literal source expression for one shell's centered boundary weight. -/
def parentRowBoundaryWeightExpr (k : ℕ) (plus : Bool) : Expr :=
  let rho := parentRowBoundaryRho k
  let f := if plus then Expr.add (.sqrt (.const 2)) (.const 2)
    else .add (.sqrt (.const (rho/2))) (.const 1)
  .sqrt (.add (.mul (.mul (.mul (.const 1) f) f) (.const (parentRowBoundaryGradient k)))
    (.const (rho-rho^2/2)))

/-- Exact real interpretation of the sign-specific shell weight. -/
theorem parent_row_boundary_weight_expr_eval (env : ℕ → ℝ) (k : ℕ) (plus : Bool) :
    evalReal env (parentRowBoundaryWeightExpr k plus)=parentRowBoundaryWeight k plus := by
  cases plus <;> simp only [parentRowBoundaryWeightExpr,parentRowBoundaryWeight,
    Bool.false_eq_true,ite_false,ite_true,evalReal,Rat.cast_sub,Rat.cast_pow,Rat.cast_div,
    Rat.cast_ofNat,Rat.cast_one,one_mul] <;> congr 1 <;> ring

/-- The source program sums the boundary weights linearly over fresh shells. -/
def parentRowBoundaryExpr (plus : Bool) : ℕ → Expr
  | 0 => .const 0
  | k+1 => .add (parentRowBoundaryExpr plus k)
      (.mul (parentRowShellExpr k) (parentRowBoundaryWeightExpr k plus))

/-- The same shell sum in real scalars. -/
def parentRowBoundaryValue (height : ℕ) (plus : Bool) : ℝ :=
  ∑ k ∈ Finset.range height,nativeSourceShellClock gammaZero (k+1)*parentRowBoundaryWeight k plus

/-- The boundary source program denotes its exact weighted physical clock. -/
theorem parent_row_boundary_expr_eval (env : ℕ → ℝ) (hlog : env 2=Real.log 3)
    (height : ℕ) (plus : Bool) :
    evalReal env (parentRowBoundaryExpr plus height)=parentRowBoundaryValue height plus := by
  induction height with
  | zero => simp only [parentRowBoundaryExpr,evalReal,Rat.cast_zero,parentRowBoundaryValue,Finset.range_zero,Finset.sum_empty]
  | succ k ih =>
    simp only [parentRowBoundaryExpr,evalReal,ih,parent_row_shell_expr_eval env hlog,
      parent_row_boundary_weight_expr_eval,parentRowBoundaryValue,Finset.sum_range_succ]

/-- Complete actual boundary RMS coefficients have their theta-scaled shell
sum, with each sign retained and no stochastic product split. -/
theorem parent_row_band_beta_value
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (height : ℕ) (plus : Bool) :
    (∑ i : Fin height,parentRowBeta n 5
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ))) plus)≤theta M*parentRowBoundaryValue height plus := by
  have hpoint (i : Fin height) :=
    (native_source_shell_variance_le_clock M h n (i.val+1) (i.val+1) hstate le_rfl).trans
      (parent_row_shell_clock_theta M hg (i.val+1))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i∈(Finset.univ : Finset (Fin height))) =>
    (parent_row_shell_beta_weight n i.val
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ)) plus).trans
      (mul_le_mul_of_nonneg_right (by simpa only [←div_pow] using hpoint i)
        (show 0≤parentRowBoundaryWeight i.val plus from Real.sqrt_nonneg _)))
  apply hs.trans_eq
  simp only [mul_assoc,←Finset.mul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun k => nativeSourceShellClock gammaZero (k+1)*parentRowBoundaryWeight k plus) height

end
end ASDExplicitGamma.Native

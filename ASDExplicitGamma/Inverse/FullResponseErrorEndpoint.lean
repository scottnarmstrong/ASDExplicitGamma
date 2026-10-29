module

public import ASDExplicitGamma.Inverse.FullResponseMatrixEndpoint
public import ASDExplicitGamma.Inverse.FullResponseD4Endpoint

/-! Source-preserving endpoint substitution for all complete positive trace errors. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- Literal endpoint payments of the matrix, D2 and two correlated D4 errors. -/
def fullResponseErrorEndpoint (γ p D E C0 C1 MC M0 Z0 D4 : ℝ) (b : Fin 4) : ℝ :=
  let z := (3:ℝ)^(2*γ*D)
  ![E*MC*(2*M0+80*(p+2)*γ*z*(D*M0+350*M0)),
    E*9*(planarGradientCharge 40+1)*C0*Z0,
    E*40*(2*p+2)*C1*γ*z*D*D4,
    E*40*(2*p+2)*C1*γ*z*350*D4] b

/-- Retained D40/D41 budgets are nonnegative sums of the actual source powers. -/
theorem full_response_D4_budget_nonneg (γ p : ℝ) (hg : γ ≤ gammaZero) :
    0 ≤ densityD40 (rootQ .full) p 1232 γ (planarGradientCharge 40) 339 ∧
      0 ≤ densityD41 (rootQ .full) p 1232 γ (planarGradientCharge 40) 339 := by
  have hS : 0 ≤ planarGradientCharge 40 := by unfold planarGradientCharge; positivity
  constructor
  · have hs := reset_density_budget4_hasSum (rootQ .full) p 1232 γ (planarGradientCharge 40) hg 339 0
    simp only [ite_true] at hs
    rw [← hs.tsum_eq]
    exact tsum_nonneg (reset_density_budget4_nonneg _ _ _ _ _ hS _ _)
  · have hs := reset_density_budget4_hasSum (rootQ .full) p 1232 γ (planarGradientCharge 40) hg 339 1
    simp only [show ¬(1:Fin 2)=0 by decide,ite_false] at hs
    rw [← hs.tsum_eq]
    exact tsum_nonneg (reset_density_budget4_nonneg _ _ _ _ _ hS _ _)

/-- Complete error substitution keeps every source coefficient, with the
favorable physical factor one half paid inside the larger certified cap. -/
theorem full_response_error_endpoint_le (γ p D E C0 C1 MC M0 Z0 D4 : ℝ)
    (hγ : 0 ≤ γ) (hg : γ ≤ gammaZero) (hp : 0 ≤ p) (hD : 0 ≤ D)
    (hE : rootEdelta .full ≤ E) (hC0 : fullResponseTraceC0 ≤ C0)
    (hC1 : fullResponseTraceC1=C1)
    (hmat : fullResponseTraceMatrixBudget γ p D 377 ≤ E*MC*(2*M0+80*(p+2)*γ*(3:ℝ)^(2*γ*D)*(D*M0+350*M0)))
    (hZ : densityEZ γ (planarGradientCharge 40) 339 ≤ 9*(planarGradientCharge 40+1)*Z0)
    (h40 : densityD40 (rootQ .full) p 1232 γ (planarGradientCharge 40) 339 ≤ D4)
    (h41 : densityD41 (rootQ .full) p 1232 γ (planarGradientCharge 40) 339 ≤ 350*D4)
    (b : Fin 4) :
    fullResponseTraceErrorBudget γ p D b ≤ fullResponseErrorEndpoint γ p D E C0 C1 MC M0 Z0 D4 b := by
  have hEactual : 0 ≤ rootEdelta .full := (Real.exp_pos _).le
  have hE0 := hEactual.trans hE
  have hC0actual : 0 ≤ fullResponseTraceC0 := by unfold fullResponseTraceC0 rootTau; positivity
  have hC00 := hC0actual.trans hC0
  have hC10 : 0 ≤ C1 := by rw [← hC1]; unfold fullResponseTraceC1 rootTau; positivity
  have hZ0 : 0 ≤ densityEZ γ (planarGradientCharge 40) 339 := by
    rw [← (reset_density_EZ_hasSum γ (planarGradientCharge 40) hg 339).tsum_eq]
    apply tsum_nonneg
    intro hk
    unfold resetDensityEZBudget planarGradientCharge
    positivity
  have hD40 := full_response_D4_budget_nonneg γ p hg
  have hhalf : rootEdelta .full/2 ≤ E :=
    (div_le_self hEactual (by norm_num : (1:ℝ) ≤ 2)).trans hE
  fin_cases b
  · simpa [fullResponseTraceErrorBudget,fullResponseErrorEndpoint] using hmat
  · have hc := mul_le_mul hE hC0 hC0actual hE0
    have hh := mul_le_mul hc hZ hZ0 (mul_nonneg hE0 hC00)
    dsimp only [fullResponseTraceErrorBudget,fullResponseErrorEndpoint]
    simp only [Matrix.cons_val_succ',Matrix.cons_val_zero']
    convert! hh using 1
    ring
  · let k := C1*γ*(3:ℝ)^(2*γ*D)*D*40*(2*p+2)
    have hk : 0 ≤ k := by dsimp only [k]; positivity
    have hc := mul_le_mul_of_nonneg_right hhalf hk
    have hh := mul_le_mul hc h40 hD40.1 (mul_nonneg hE0 hk)
    dsimp only [fullResponseTraceErrorBudget,fullResponseErrorEndpoint]
    simp only [Matrix.cons_val_succ',Matrix.cons_val_zero']
    rw [hC1]
    dsimp only [k] at hh
    convert! hh using 1 <;> ring
  · let k := C1*γ*(3:ℝ)^(2*γ*D)*40*(2*p+2)
    have hk : 0 ≤ k := by dsimp only [k]; positivity
    have hc := mul_le_mul_of_nonneg_right hhalf hk
    have hh := mul_le_mul hc h41 hD40.2 (mul_nonneg hE0 hk)
    dsimp only [fullResponseTraceErrorBudget,fullResponseErrorEndpoint]
    simp only [Matrix.cons_val_succ',Matrix.cons_val_zero']
    rw [hC1]
    dsimp only [k] at hh
    convert! hh using 1 <;> ring

end
end ASDExplicitGamma.Inverse

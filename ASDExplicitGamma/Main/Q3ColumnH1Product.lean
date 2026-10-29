module

public import ASDExplicitGamma.Main.Q3ColumnProduct
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! Actual derivative columns times general H1 residuals. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian
open scoped BigOperators

/-- The actual q3 derivative-column product before imposing a residual estimate. -/
theorem main_q3_column_h1_product {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q)) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (k+1) (fun x => u.toFun x • mainQ3FiniteColumn e s b L x))) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (fun x => u.toFun x • mainQ3FiniteColumn e s b L x) ≤
      Real.sqrt ((156/5)*b^2/L.1^2)*positiveHaarNorm Q u.toFun+
        cubeScaleFactor Q*planarC1*Real.sqrt ((46488/25)*b^2/L.1^4)*Real.sqrt (energy Q u.toFun) := by
  apply main_hilbert_column_product Q _ (mainQ3FiniteColumn_contDiff e s b L) u
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · apply Filter.Eventually.of_forall
    intro x
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).2
      (mainQ3FiniteColumn_norm_sq_le e s b L x)
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.sq_sqrt (by positivity : 0 ≤ (46488/25:ℝ)*b^2/L.1^4)]
    exact mainQ3FiniteColumn_derivative_sq_le e s b L x

/-- Multiplication by a minus sign does not change the source H1 residual norms. -/
theorem main_q3_negative_column_h1_product {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q)) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (k+1) (fun x => (-u.toFun x) • mainQ3FiniteColumn e s b L x))) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (fun x => (-u.toFun x) • mainQ3FiniteColumn e s b L x) ≤
      Real.sqrt ((156/5)*b^2/L.1^2)*positiveHaarNorm Q u.toFun+
        cubeScaleFactor Q*planarC1*Real.sqrt ((46488/25)*b^2/L.1^4)*Real.sqrt (energy Q u.toFun) := by
  have h := main_q3_column_h1_product e s b L Q (-u)
  simpa only [H1Function.neg_toFun, positiveHaarNorm, primalEnergy_neg, energy_neg] using h

end ASDExplicitGamma.Main

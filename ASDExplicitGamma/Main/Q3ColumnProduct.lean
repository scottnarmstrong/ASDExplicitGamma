module

public import ASDExplicitGamma.Main.Q3FiniteColumn
public import ASDExplicitGamma.Main.ColumnProductCaps

/-! Actual q3 source-column products, uniformly in the Gaussian truncation. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian
open scoped BigOperators

/-- The column coefficient before the shell's physical length substitution. -/
noncomputable def mainQ3ColumnConstant (R b L : ℝ) : ℝ :=
  R*(637/1000)*Real.sqrt ((156/5)*b^2/L^2) +
    R^2*(440/1000)*(304/1000)*Real.sqrt ((46488/25)*b^2/L^4)

/-- Actual finite Gaussian columns obey the common source coefficient, with
no assumed covariance or derivative estimate. This is uniform in the finite
set, a necessary input to the Hilbert--Schmidt limit. -/
theorem main_q3_finite_column_product {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (k+1)
        (fun x => u.toH1Function.toFun x • mainQ3FiniteColumn e s b L x))) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3)
        (fun x => u.toH1Function.toFun x • mainQ3FiniteColumn e s b L x) ≤
      mainQ3ColumnConstant (cubeScaleFactor Q) b L.1 *
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) := by
  apply main_hilbert_column_decimal Q _ (mainQ3FiniteColumn_contDiff e s b L) u
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · apply Filter.Eventually.of_forall
    intro x
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).2
      (mainQ3FiniteColumn_norm_sq_le e s b L x)
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.sq_sqrt (by positivity : 0 ≤ (46488/25:ℝ)*b^2/L.1^4)]
    exact mainQ3FiniteColumn_derivative_sq_le e s b L x

end ASDExplicitGamma.Main

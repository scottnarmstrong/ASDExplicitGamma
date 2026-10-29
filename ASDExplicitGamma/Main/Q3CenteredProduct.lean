module

public import ASDExplicitGamma.Main.Q3CenteredValue
public import ASDExplicitGamma.Main.Q3ValueDerivatives
public import ASDExplicitGamma.Main.HilbertTensorProduct

/-! The actual frozen-source oscillation times a positive-Haar vector field. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped BigOperators

/-- Actual q3 centered covariance columns satisfy the operator-valued product
estimate with the exact r*sigma/sqrt3 amplitude and full trace derivative.
Neither centering, covariance isotropy nor the W^{1,∞} membership is assumed. -/
theorem main_q3_centered_tensor_product {ι ρ : Type*} [Fintype ρ]
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l})
    (Q : TriadicCube 2) {f : Vec 2 → EuclideanSpace ℝ ρ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hP : Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) f))) :
    let ψ := mainQ3FiniteValue e s b L
    let F := fun x => mainEuclideanTensor (ψ x-hilbertCubeAverage Q ψ) (f x)
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) F)) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3) F ≤
      (cubeScaleFactor Q/Real.sqrt 3*Real.sqrt ((156/5)*b^2/L.1^2))*
        hilbertPositiveHaarNorm Q (Real.sqrt 3) f+
      cubeScaleFactor Q*planarC1*Real.sqrt ((156/5)*b^2/L.1^2)*hilbertL2Norm Q f := by
  intro ψ F
  have hR := ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q
  have hσ : 0 ≤ (156/5:ℝ)*b^2/L.1^2 := by positivity
  apply main_hilbert_tensor_product Q (fun x => ψ x-hilbertCubeAverage Q ψ)
    ((mainQ3FiniteValue_contDiff e s b L).sub contDiff_const) hf hP (by positivity) (Real.sqrt_nonneg _)
  · filter_upwards [hilbert_ae_cubeSet Q] with x hx
    have h := main_q3_centered_value_sq_le e s b L Q hx
    have he : (cubeScaleFactor Q/Real.sqrt 3*Real.sqrt ((156/5)*b^2/L.1^2))^2 =
        cubeScaleFactor Q^2/3*((156/5)*b^2/L.1^2) := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sq_sqrt hσ]
    have hM : 0 ≤ cubeScaleFactor Q/Real.sqrt 3*Real.sqrt ((156/5)*b^2/L.1^2) := by positivity
    exact (sq_le_sq₀ (norm_nonneg _) hM).1 (h.trans_eq he.symm)
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.sq_sqrt hσ]
    simp only [fderiv_sub_const]
    exact mainQ3FiniteValue_derivative_frobenius e s b L x

end ASDExplicitGamma.Main

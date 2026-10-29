module

public import ASDExplicitGamma.Gaussian.SupMeanDyadicGaussianPayment

/-! Exact Gaussian tensor supremum mean from dyadic centers, including derived integrability. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory
open scoped BigOperators
noncomputable section

/-- The complete square chaining theorem with the exact source coefficients.
Only point laws and their local increment mean/MGF estimates enter; the compact
supremum's integrability and mean bound are proved by the dense mesh passage. -/
theorem supMean_gaussian_square_supmean {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c : Fin 2 → ℝ) (s : ℝ) (hs : 0 < s)
    (f : Ω → (Fin 2 → ℝ) → E) (hf : ∀ ω, Continuous (f ω))
    (hpoint : ∀ x, Integrable (fun ω => f ω x) μ) (hpointm : ∀ x, Measurable (fun ω => f ω x))
    (a T V A : ℝ) (hT : 0 ≤ T) (hV : 0 < V) (hA : 0 < A)
    (hbase : (∫ ω, ‖f ω c‖ ∂μ) ≤ a)
    (hmean : ∀ x y : Fin 2 → ℝ, (∫ ω, ‖f ω y-f ω x‖ ∂μ) ≤
      Real.sqrt ((T/2)*V*((y-x) 0^2+(y-x) 1^2)))
    (hmgf : ∀ x y : Fin 2 → ℝ, ∀ lam > 0,
      let X := fun ω => ‖f ω y-f ω x‖
      Integrable (fun ω => Real.exp (lam*(X ω-∫ z, X z ∂μ))) μ ∧
      (∫ ω, Real.exp (lam*(X ω-∫ z, X z ∂μ)) ∂μ) ≤
        Real.exp (lam^2*((A^2*V)*((y-x) 0^2+(y-x) 1^2))/2)) :
    Integrable (fun ω => ‖(⟨fun x : supMeanClosedSquare c s => f ω x.val,
      (hf ω).comp continuous_subtype_val⟩ : C(supMeanClosedSquare c s,E))‖) μ ∧
    (∫ ω, ‖(⟨fun x : supMeanClosedSquare c s => f ω x.val,
      (hf ω).comp continuous_subtype_val⟩ : C(supMeanClosedSquare c s,E))‖ ∂μ) ≤
        a+(s*Real.sqrt V)*(Real.sqrt T/2+2*Real.sqrt (Real.log 2)*A) := by
  have ha : 0 ≤ a := (integral_nonneg (fun ω => norm_nonneg _)).trans hbase
  have hC : 0 ≤ a+(s*Real.sqrt V)*(Real.sqrt T/2+2*Real.sqrt (Real.log 2)*A) := by positivity
  apply supMean_dyadic_expectation_limit μ c s hs f hf hpoint a _
    (fun n => (s*Real.sqrt V)*supMeanDyadicIncrementPayment (Real.sqrt T) A n) hC hbase
  · intro n
    exact supMean_dyadic_gaussian_increment_payment μ c s hs f hpoint hpointm T V A hT hV hA hmean hmgf n
  · intro n
    rw [← Finset.mul_sum]
    have hb := mul_le_mul_of_nonneg_left
      (supMean_dyadic_payment_sum_le (Real.sqrt T) A (Real.sqrt_nonneg _) hA.le n)
      (show 0 ≤ s*Real.sqrt V by positivity)
    linarith only [hb]

end
end ASDExplicitGamma.Gaussian

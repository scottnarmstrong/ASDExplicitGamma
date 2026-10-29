module

public import ASDExplicitGamma.Native.OldSignedSqrtProductExpectation

/-! Constant-one annealed Minkowski for two correlated positive energies. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory Native

/-- A common nonnegative weight can be moved into both energy roots. -/
theorem old_hessian_weighted_root_square (w f g a c : ℝ) (hw : 0≤w) :
    w*(a*Real.sqrt f+c*Real.sqrt g)^2=
      (a*Real.sqrt (w*f)+c*Real.sqrt (w*g))^2 := by
  rw [Real.sqrt_mul hw,Real.sqrt_mul hw]
  calc
    _ = (Real.sqrt w)^2*(a*Real.sqrt f+c*Real.sqrt g)^2 := by rw [Real.sq_sqrt hw]
    _ = _ := by ring

/-- A square-root source sum has the exact Minkowski first-moment bound,
including integrability, without an independence assumption. -/
theorem old_hessian_square_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (a c : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ ω,0≤f ω) (hg0 : ∀ ω,0≤g ω) (ha : 0≤a) (hc : 0≤c) :
    Integrable (fun ω => (a*Real.sqrt (f ω)+c*Real.sqrt (g ω))^2) μ ∧
      (∫ ω,(a*Real.sqrt (f ω)+c*Real.sqrt (g ω))^2 ∂μ) ≤
        (a*Real.sqrt (∫ ω,f ω ∂μ)+c*Real.sqrt (∫ ω,g ω ∂μ))^2 := by
  have hp := old_signed_sqrt_product_expectation μ f g hf hg hf0 hg0
  have he : (fun ω => (a*Real.sqrt (f ω)+c*Real.sqrt (g ω))^2)=
      (fun ω => a^2*f ω+(2*a*c)*(Real.sqrt (f ω)*Real.sqrt (g ω))+c^2*g ω) := by
    funext ω
    nlinarith [Real.sq_sqrt (hf0 ω),Real.sq_sqrt (hg0 ω)]
  have hi := ((hf.const_mul (a^2)).add (hp.1.const_mul (2*a*c))).add (hg.const_mul (c^2))
  refine ⟨he.symm ▸ hi,?_⟩
  have hi2 : Integrable (fun ω => a^2*f ω+(2*a*c)*(Real.sqrt (f ω)*Real.sqrt (g ω))) μ :=
    (hf.const_mul (a^2)).add (hp.1.const_mul (2*a*c))
  rw [he,integral_add hi2
    (hg.const_mul (c^2)),integral_add (hf.const_mul (a^2)) (hp.1.const_mul (2*a*c)),
    integral_const_mul,integral_const_mul,integral_const_mul]
  calc
    _ ≤ a^2*(∫ ω,f ω ∂μ)+(2*a*c)*(Real.sqrt (∫ ω,f ω ∂μ)*Real.sqrt (∫ ω,g ω ∂μ))+
        c^2*(∫ ω,g ω ∂μ) := add_le_add
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hp.2 (by positivity))) le_rfl
    _ = _ := by
      nlinarith [Real.sq_sqrt (integral_nonneg (μ := μ) hf0),Real.sq_sqrt (integral_nonneg (μ := μ) hg0)]

end ASDExplicitGamma.Scalar

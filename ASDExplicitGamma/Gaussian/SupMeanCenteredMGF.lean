module

public import ASDExplicitGamma.Gaussian.SupMeanFinite

/-! Recover raw exponential integrability and bounds from a sharp centered MGF and a mean cap. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory

/-- Restoring the actual mean preserves the sharp Gaussian exponential constant. -/
theorem supMean_raw_mgf_of_centered {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (lam m v : ℝ) (hlam : 0 ≤ lam)
    (hmean : (∫ ω, X ω ∂μ) ≤ m)
    (hi : Integrable (fun ω => Real.exp (lam*(X ω-∫ y, X y ∂μ))) μ)
    (hb : (∫ ω, Real.exp (lam*(X ω-∫ y, X y ∂μ)) ∂μ) ≤ Real.exp (lam^2*v/2)) :
    Integrable (fun ω => Real.exp (lam*X ω)) μ ∧
    (∫ ω, Real.exp (lam*X ω) ∂μ) ≤ Real.exp (lam*m+lam^2*v/2) := by
  have he : (fun ω => Real.exp (lam*X ω)) =
      (fun ω => Real.exp (lam*(∫ y, X y ∂μ))*Real.exp (lam*(X ω-∫ y, X y ∂μ))) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ Real.exp (lam*(∫ y, X y ∂μ))*Real.exp (lam^2*v/2) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = Real.exp (lam*(∫ y, X y ∂μ)+lam^2*v/2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hm := mul_le_mul_of_nonneg_left hmean hlam
      linarith only [hm])

end ASDExplicitGamma.Gaussian

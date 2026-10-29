module

public import ASDExplicitGamma.Scalar.ChaosSpectral
public import Mathlib.MeasureTheory.Function.L2Space

/-! Square-product Cauchy bounds for the Hilbert second-chaos moment calculation. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory

/-- Integrable fourth powers give the correct L2 space for squared observables. -/
theorem memLp_square_of_integrable_fourth {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hf4 : Integrable (fun x => (f x)^4) μ) : MemLp (fun x => (f x)^2) 2 μ := by
  apply (memLp_two_iff_integrable_sq (hf.pow 2)).mpr
  convert hf4 using 1
  funext x
  simp only [Pi.pow_apply]
  ring

/-- No distribution assumption is needed for Cauchy--Schwarz between squared observables. -/
theorem square_product_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hf4 : Integrable (fun x => (f x)^4) μ)
    (hg4 : Integrable (fun x => (g x)^4) μ) :
    Integrable (fun x => (f x)^2*(g x)^2) μ ∧
      (∫ x, (f x)^2*(g x)^2 ∂μ) ≤ Real.sqrt (∫ x, (f x)^4 ∂μ)*Real.sqrt (∫ x, (g x)^4 ∂μ) := by
  have hf2 := memLp_square_of_integrable_fourth μ f hf hf4
  have hg2 := memLp_square_of_integrable_fourth μ g hg hg4
  have instHolderTwoTwoOne : ENNReal.HolderTriple 2 2 1 := ⟨by simpa only [inv_one] using ENNReal.inv_two_add_inv_two⟩
  have hInt : Integrable (fun x => (f x)^2*(g x)^2) μ :=
    memLp_one_iff_integrable.mp (hf2.fun_mul hg2)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))
    (Filter.Eventually.of_forall (fun x => sq_nonneg (g x)))
    (show MemLp (fun x => (f x)^2) (ENNReal.ofReal 2) μ by norm_num; exact hf2)
    (show MemLp (fun x => (g x)^2) (ENNReal.ofReal 2) μ by norm_num; exact hg2)
  have hp (u : Ω → ℝ) : (fun x => ((u x)^2)^(2:ℝ)) = fun x => (u x)^4 := by
    funext x
    rw [Real.rpow_two]
    ring
  rw [hp f,hp g,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at h
  exact ⟨hInt,h⟩

end ASDExplicitGamma.Scalar

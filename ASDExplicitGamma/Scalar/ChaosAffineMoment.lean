module

public import ASDExplicitGamma.Scalar.ChaosEnvelopeAlgebra
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Integrating the deterministic quadratic majorant for a Gaussian envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory

theorem integrable_square_const_add_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a b : ℝ) (F : Ω → ℝ)
    (hF : Integrable F μ) (hF2 : Integrable (fun x => (F x)^2) μ) :
    Integrable (fun x => (a+b*F x)^2) μ := by
  have he : (fun x => (a+b*F x)^2) = fun x => a^2+(2*a*b)*F x+b^2*(F x)^2 := by
    funext x
    ring
  rw [he]
  convert ((integrable_const (a^2)).add (hF.const_mul (2*a*b))).add (hF2.const_mul (b^2)) using 1

theorem integral_square_const_add_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a b : ℝ) (F : Ω → ℝ)
    (hF : Integrable F μ) (hF2 : Integrable (fun x => (F x)^2) μ) :
    (∫ x, (a+b*F x)^2 ∂μ) = a^2+2*a*b*(∫ x, F x ∂μ)+b^2*(∫ x, (F x)^2 ∂μ) := by
  have he : (fun x => (a+b*F x)^2) = fun x => a^2+(2*a*b)*F x+b^2*(F x)^2 := by
    funext x
    ring
  have hAdd : Integrable (fun x => a^2+(2*a*b)*F x) μ := by
    convert (integrable_const (a^2)).add (hF.const_mul (2*a*b)) using 1
  rw [he,integral_add hAdd (hF2.const_mul (b^2)),
    integral_add (integrable_const (a^2)) (hF.const_mul (2*a*b))]
  simp only [integral_const_mul]
  simp

end ASDExplicitGamma.Scalar

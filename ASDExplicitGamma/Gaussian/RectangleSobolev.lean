module

public import ASDExplicitGamma.Gaussian.IntervalSobolev
public import Mathlib.MeasureTheory.Integral.Prod

/-! # The rectangular mixed-derivative pointwise bound -/

@[expose] public section

open MeasureTheory Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

private theorem integral_slice_value_sq_le {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] {c d y : ℝ} (hcd : c < d) (hy : y ∈ Icc c d)
    (f g : S → ℝ → ℝ) (hf : ∀ s, ContDiff ℝ 1 (f s)) (hdf : ∀ s, deriv (f s) = g s)
    (hFi : Integrable (fun p : S × ℝ => f p.1 p.2 ^ 2) (μ.prod (volume.restrict (Icc c d))))
    (hGi : Integrable (fun p : S × ℝ => g p.1 p.2 ^ 2) (μ.prod (volume.restrict (Icc c d))))
    (hyi : Integrable (fun s => f s y ^ 2) μ) :
    (∫ s, f s y ^ 2 ∂μ) ≤
      (2 / (d - c)) * (∫ s, ∫ t in Icc c d, f s t ^ 2 ∂volume ∂μ) +
        (2 * (d - c)) * (∫ s, ∫ t in Icc c d, g s t ^ 2 ∂volume ∂μ) := by
  have hF : Integrable (fun s => ∫ t in Icc c d, f s t ^ 2) μ := hFi.integral_prod_left
  have hG : Integrable (fun s => ∫ t in Icc c d, g s t ^ 2) μ := hGi.integral_prod_left
  have hh := integral_mono hyi ((hF.const_mul (2 / (d - c))).add (hG.const_mul (2 * (d - c))))
    (fun s => by
      have hb := interval_value_sq_le_setIntegral hcd (hf s) hy
      rwa [hdf s] at hb)
  simp only [Pi.add_apply] at hh
  rwa [integral_add (hF.const_mul _) (hG.const_mul _), integral_const_mul, integral_const_mul] at hh

private theorem integrable_rectangle_sq {a b c d : ℝ} (f : ℝ → ℝ → ℝ)
    (hf : Continuous (Function.uncurry f)) :
    Integrable (fun p : ℝ × ℝ => f p.1 p.2 ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  rw [Measure.prod_restrict]
  exact (hf.pow 2).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- The elementary rectangular estimate for a function and its two first and one mixed
partial derivative. Applied also to each first derivative, it uses only the ten H³ coordinates.
The integrals are ordinary, unnormalized Lebesgue integrals. -/
theorem rectangle_value_sq_le {a b c d x y : ℝ} (hab : a < b) (hcd : c < d)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (f f₁ f₂ f₁₂ : ℝ → ℝ → ℝ)
    (hC : Continuous (Function.uncurry f)) (hC₁ : Continuous (Function.uncurry f₁))
    (hC₂ : Continuous (Function.uncurry f₂)) (hC₁₂ : Continuous (Function.uncurry f₁₂))
    (hf₁ : ∀ t, ContDiff ℝ 1 (fun s => f s t))
    (hf₂ : ∀ s, ContDiff ℝ 1 (f s)) (hf₁₂ : ∀ s, ContDiff ℝ 1 (f₁ s))
    (hd₁ : ∀ t, deriv (fun s => f s t) = fun s => f₁ s t)
    (hd₂ : ∀ s, deriv (f s) = f₂ s) (hd₁₂ : ∀ s, deriv (f₁ s) = f₁₂ s) :
    f x y ^ 2 ≤
      (2 / (b - a)) * (2 / (d - c)) * (∫ s in Icc a b, ∫ t in Icc c d, f s t ^ 2) +
      (2 * (b - a)) * (2 / (d - c)) * (∫ s in Icc a b, ∫ t in Icc c d, f₁ s t ^ 2) +
      (2 / (b - a)) * (2 * (d - c)) * (∫ s in Icc a b, ∫ t in Icc c d, f₂ s t ^ 2) +
      (2 * (b - a)) * (2 * (d - c)) * (∫ s in Icc a b, ∫ t in Icc c d, f₁₂ s t ^ 2) := by
  have hFi := integrable_rectangle_sq (a := a) (b := b) (c := c) (d := d) f hC
  have hF₁i := integrable_rectangle_sq (a := a) (b := b) (c := c) (d := d) f₁ hC₁
  have hF₂i := integrable_rectangle_sq (a := a) (b := b) (c := c) (d := d) f₂ hC₂
  have hF₁₂i := integrable_rectangle_sq (a := a) (b := b) (c := c) (d := d) f₁₂ hC₁₂
  have hslice : Integrable (fun s => f s y ^ 2) (volume.restrict (Icc a b)) :=
    ((hC.comp (continuous_id.prodMk continuous_const)).pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hslice₁ : Integrable (fun s => f₁ s y ^ 2) (volume.restrict (Icc a b)) :=
    ((hC₁.comp (continuous_id.prodMk continuous_const)).pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hA := integral_slice_value_sq_le (volume.restrict (Icc a b)) hcd hy f f₂ hf₂ hd₂ hFi hF₂i hslice
  have hB := integral_slice_value_sq_le (volume.restrict (Icc a b)) hcd hy f₁ f₁₂ hf₁₂ hd₁₂ hF₁i hF₁₂i hslice₁
  have hpoint := interval_value_sq_le_setIntegral hab (hf₁ y) hx
  rw [hd₁ y] at hpoint
  have hleft := mul_le_mul_of_nonneg_left hA (show 0 ≤ 2 / (b - a) by positivity)
  have hright := mul_le_mul_of_nonneg_left hB (show 0 ≤ 2 * (b - a) by positivity)
  nlinarith only [hpoint, hleft, hright]

end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Model.SpectralMeasure
public import ASDExplicitGamma.Model.Q3Cov
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.Inversion

@[expose] public section

open MeasureTheory FourierTransform Complex
open scoped Convolution

namespace ASDExplicitGamma.Model

private theorem q3FourierKernel_even (x : ℝ) : q3Kernel (-x) = q3Kernel x := by
  rw [q3Kernel, q3Kernel]
  simp [abs_neg]

private theorem q3FourierCov_eq_complexConvolution (u : ℝ) :
    (ASDExplicitGamma.q3Cov u : ℂ) =
      MeasureTheory.convolution (fun x : ℝ => (q3Kernel x : ℂ))
        (fun x : ℝ => (q3Kernel x : ℂ)) (ContinuousLinearMap.mul ℂ ℂ) volume u := by
  rw [ASDExplicitGamma.q3Cov, MeasureTheory.convolution_def]
  rw [← integral_complex_ofReal]
  have hchange := Measure.integral_comp_mul_left
    (fun x : ℝ => (q3Kernel x : ℂ) * (q3Kernel (u - x) : ℂ)) (-1)
  simpa [q3FourierKernel_even, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hchange

private theorem q3FourierCov_eq_realConvolution (u : ℝ) :
    ASDExplicitGamma.q3Cov u =
      MeasureTheory.convolution q3Kernel q3Kernel (ContinuousLinearMap.mul ℝ ℝ) volume u := by
  rw [ASDExplicitGamma.q3Cov, MeasureTheory.convolution_def]
  have hchange := Measure.integral_comp_mul_left
    (fun x : ℝ => q3Kernel x * q3Kernel (u - x)) (-1)
  simpa [q3FourierKernel_even, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hchange

private theorem q3FourierCov_continuous : Continuous ASDExplicitGamma.q3Cov := by
  have hconv : Continuous (MeasureTheory.convolution q3Kernel q3Kernel
      (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    q3Kernel_hasCompactSupport.continuous_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) q3Kernel_integrable.locallyIntegrable q3Kernel_continuous
  have hEq : ASDExplicitGamma.q3Cov =
      MeasureTheory.convolution q3Kernel q3Kernel (ContinuousLinearMap.mul ℝ ℝ) volume :=
    funext q3FourierCov_eq_realConvolution
  rw [hEq]
  exact hconv

private theorem q3FourierCov_transform (ξ : ℝ) :
    FourierTransform.fourier (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)) ξ =
      FourierTransform.fourier (fun x : ℝ => (q3Kernel x : ℂ)) ξ ^ 2 := by
  have hq : Integrable (fun x : ℝ => (q3Kernel x : ℂ)) := q3Kernel_integrable.ofReal
  have hconv : (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)) =
      MeasureTheory.convolution (fun x : ℝ => (q3Kernel x : ℂ))
        (fun x : ℝ => (q3Kernel x : ℂ)) (ContinuousLinearMap.mul ℂ ℂ) volume :=
    funext q3FourierCov_eq_complexConvolution
  rw [hconv]
  simpa [pow_two] using Real.fourier_mul_convolution_eq hq hq ξ

private theorem q3FourierKernel_transform_real (ξ : ℝ) :
    star (FourierTransform.fourier (fun x : ℝ => (q3Kernel x : ℂ)) ξ) =
      FourierTransform.fourier (fun x : ℝ => (q3Kernel x : ℂ)) ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  let g : ℝ → ℂ := fun x =>
    Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) * (q3Kernel x : ℂ)
  change star (∫ x, g x) = ∫ x, g x
  calc
    star (∫ x, g x) = ∫ x, star (g x) := (integral_conj).symm
    _ = ∫ x, g (-x) := by
      congr 1
      funext x
      simp only [g, star_mul]
      have hExp :
          star (Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)) =
            Complex.exp (((-2 * Real.pi * (-x) * ξ : ℝ) : ℂ) * Complex.I) := by
        calc
          _ = Complex.exp
              (star (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)) :=
                (Complex.exp_conj _).symm
          _ = _ := by
            congr 1
            calc
              star (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) =
                  star Complex.I * star ((-2 * Real.pi * x * ξ : ℝ) : ℂ) := star_mul _ _
              _ = (-Complex.I) * ((-2 * Real.pi * x * ξ : ℝ) : ℂ) :=
                congrArg₂ (fun a b : ℂ => a * b) Complex.conj_I (Complex.conj_ofReal _)
              _ = ((-2 * Real.pi * (-x) * ξ : ℝ) : ℂ) * Complex.I := by
                push_cast
                ring
      rw [hExp, q3FourierKernel_even]
      have hreal : star (q3Kernel x : ℂ) = (q3Kernel x : ℂ) :=
        Complex.conj_ofReal _
      calc
        _ = (q3Kernel x : ℂ) *
            Complex.exp (↑(-2 * Real.pi * -x * ξ) * Complex.I) := by rw [hreal]
        _ = _ := by ring
    _ = ∫ x, g x := by
      simpa [g] using Measure.integral_comp_mul_left g (-1)

private theorem q3FourierKernel_sq (ξ : ℝ) :
    q3FourierKernel ξ ^ 2 = (q3SpectralDensity1 ξ : ℂ) := by
  rw [q3SpectralDensity1, pow_two]
  have hs : star (q3FourierKernel ξ) = q3FourierKernel ξ :=
    q3FourierKernel_transform_real ξ
  nth_rw 2 [← hs]
  simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using
    Complex.mul_conj (q3FourierKernel ξ)

private theorem q3Cov_fourier_transform : 𝓕 (fun u : ℝ => (q3Cov u : ℂ)) =
    fun ξ => (q3SpectralDensity1 ξ : ℂ) := by
  funext ξ
  exact (q3FourierCov_transform ξ).trans (q3FourierKernel_sq ξ)

private theorem q3Cov_integrable_complex : Integrable (fun u : ℝ => (q3Cov u : ℂ)) := by
  rw [show (fun u : ℝ => (q3Cov u : ℂ)) =
      MeasureTheory.convolution (fun x : ℝ => (q3Kernel x : ℂ))
        (fun x : ℝ => (q3Kernel x : ℂ)) (ContinuousLinearMap.mul ℂ ℂ) volume from
    funext q3FourierCov_eq_complexConvolution]
  exact Integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    q3Kernel_integrable.ofReal q3Kernel_integrable.ofReal

/-- Fourier inversion identifies the q3 covariance with the spectral density. -/
theorem q3Cov_eq_spectral_integral (u : ℝ) :
    (q3Cov u : ℂ) = ∫ ξ : ℝ, (q3SpectralDensity1 ξ : ℂ) *
      exp ((2 * Real.pi * ξ * u : ℝ) * I) := by
  have hif : Integrable (𝓕 (fun u : ℝ => (q3Cov u : ℂ))) := by
    rw [q3Cov_fourier_transform]
    exact q3SpectralDensity1_integrable.ofReal
  have hinv := q3Cov_integrable_complex.fourierInv_fourier_eq hif
    (Complex.continuous_ofReal.comp q3FourierCov_continuous).continuousAt (v := u)
  rw [q3Cov_fourier_transform, Real.fourierInv_eq'] at hinv
  rw [← hinv]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  have he : ((2 * Real.pi * (u * ξ) : ℝ) : ℂ) * I =
      ((2 * Real.pi * ξ * u : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [he, mul_comm]

/-- The full two-dimensional covariance is the transform of the product measure. -/
theorem q3SpectralMeasure_exponential_integral (h x y : ℝ) :
    (∫ ξ : Q3FrequencyPlane,
      exp (((2 * Real.pi * (ξ.fst * x + ξ.snd * y) : ℝ) : ℂ) * I)
        ∂q3SpectralMeasure h) = (h ^ 2 * q3Cov x * q3Cov y : ℝ) := by
  rw [q3SpectralMeasure, ← MeasurableEquiv.coe_toLp, integral_map_equiv]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (q3SpectralDensity2_continuous h).measurable.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have heq (ξ : ℝ × ℝ) :
      (ENNReal.ofReal (q3SpectralDensity2 h ξ)).toReal •
        exp (((2 * Real.pi *
          (((MeasurableEquiv.toLp 2 (ℝ × ℝ)) ξ).fst * x +
            ((MeasurableEquiv.toLp 2 (ℝ × ℝ)) ξ).snd * y) : ℝ) : ℂ) * I) =
      (h ^ 2 : ℝ) •
        (((q3SpectralDensity1 ξ.1 : ℂ) * exp (((2 * Real.pi * ξ.1 * x : ℝ) : ℂ) * I)) *
          ((q3SpectralDensity1 ξ.2 : ℂ) * exp (((2 * Real.pi * ξ.2 * y : ℝ) : ℂ) * I))) := by
    rw [ENNReal.toReal_ofReal (q3SpectralDensity2_nonneg h ξ)]
    simp only [MeasurableEquiv.toLp_apply, WithLp.toLp_fst, WithLp.toLp_snd,
      Complex.real_smul, q3SpectralDensity2, ofReal_mul]
    have hexp : (((2 * Real.pi * (ξ.1 * x + ξ.2 * y) : ℝ) : ℂ) * I) =
        (((2 * Real.pi * ξ.1 * x : ℝ) : ℂ) * I) +
          (((2 * Real.pi * ξ.2 * y : ℝ) : ℂ) * I) := by
      push_cast
      ring
    simp only [ofReal_mul] at hexp
    rw [hexp, exp_add]
    ring
  simp_rw [heq]
  rw [integral_smul]
  have hprod := integral_prod_mul
    (fun ξ : ℝ => (q3SpectralDensity1 ξ : ℂ) * exp (((2 * Real.pi * ξ * x : ℝ) : ℂ) * I))
    (fun ξ : ℝ => (q3SpectralDensity1 ξ : ℂ) * exp (((2 * Real.pi * ξ * y : ℝ) : ℂ) * I))
    (μ := volume) (ν := volume)
  rw [hprod, ← q3Cov_eq_spectral_integral x, ← q3Cov_eq_spectral_integral y]
  simp only [Complex.real_smul, ofReal_mul]
  ring

end ASDExplicitGamma.Model

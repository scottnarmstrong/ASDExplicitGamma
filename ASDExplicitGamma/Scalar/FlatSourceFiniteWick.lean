module

public import ASDExplicitGamma.Scalar.FlatSourceGaussianWick
public import ASDExplicitGamma.Scalar.ChaosHilbertEnvelope
public import ASDExplicitGamma.Gaussian.GaussMomentHolder

/-! A trace-capped finite-mode Wick estimate for the fixed flat-source
product. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory
open ASDExplicitGamma.Gaussian
open scoped ENNReal

/-- Hölder's step for a positive NEW-bank excess against a flat quadratic
Gaussian envelope. The exponents are the pair
`128` and `128/127`; no independence assumption is used. -/
theorem flat_source_rare_product_holder
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z Y : Ω → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hZ : MemLp Z (ENNReal.ofReal 128) μ)
    (hY : MemLp Y (ENNReal.ofReal (128 / 127 : ℝ)) μ)
    (hZcap : eLpNorm Z (ENNReal.ofReal 128) μ ≤ ENNReal.ofReal (5 / 10^24 : ℝ))
    (hYcap : eLpNorm Y (ENNReal.ofReal (128 / 127 : ℝ)) μ ≤ ENNReal.ofReal C) :
    (∫ ω, Z ω * Y ω ∂μ) ≤ (5 / 10^24 : ℝ) * C := by
  have hconj : (128 : ℝ).HolderConjugate (128 / 127 : ℝ) := by
    rw [Real.holderConjugate_iff_eq_conjExponent (by norm_num : (1 : ℝ) < 128)]
    norm_num
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (ae_of_all μ hZ0) (ae_of_all μ hY0) hZ hY
  have hZnorm : Gaussian.positiveLpNorm μ 128 Z ≤ 5 / 10^24 := by
    rw [Gaussian.positiveLpNorm_eq_eLpNorm_toReal μ (by norm_num) Z hZ0 hZ]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hZcap
    norm_num at h ⊢
    exact h
  have hYnorm : Gaussian.positiveLpNorm μ (128 / 127 : ℝ) Y ≤ C := by
    rw [Gaussian.positiveLpNorm_eq_eLpNorm_toReal μ (by norm_num) Y hY0 hY]
    simpa [ENNReal.toReal_ofReal hC] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hYcap
  have hh' : (∫ ω, Z ω * Y ω ∂μ) ≤
      Gaussian.positiveLpNorm μ 128 Z *
        Gaussian.positiveLpNorm μ (128 / 127 : ℝ) Y := by
    simpa [Gaussian.positiveLpNorm, one_div] using hh
  have hYnonneg : 0 ≤ Gaussian.positiveLpNorm μ (128 / 127 : ℝ) Y := by
    unfold Gaussian.positiveLpNorm
    apply Real.rpow_nonneg
    exact integral_nonneg (fun ω => Real.rpow_nonneg (hY0 ω) _)
  calc
    _ ≤ Gaussian.positiveLpNorm μ 128 Z *
        Gaussian.positiveLpNorm μ (128 / 127 : ℝ) Y := hh'
    _ ≤ (5 / 10^24 : ℝ) * C := by
      exact mul_le_mul hZnorm hYnorm hYnonneg (by norm_num)

end ASDExplicitGamma.Scalar

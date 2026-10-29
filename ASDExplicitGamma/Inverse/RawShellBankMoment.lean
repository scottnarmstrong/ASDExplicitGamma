module

public import ASDExplicitGamma.Inverse.RawMomentChain
public import ASDExplicitGamma.Inverse.RawShellL20Caps

/-! Assemble the bank-derived L20 factors with the actual p=20 source-row
identity used. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory
open ASDExplicitGamma.Gaussian
open scoped ENNReal

/-- The order-128 bank caps discharge the three Holder factors in the p=20
moment chain. The AE source rows are stated with the measurable local-bank
majorant in the two response products. -/
theorem raw_trace_p20_generator_integral_bank_row
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P F T D L Gamma : Ω → ℝ) (gamma : ℝ) (h : ℕ)
    (v kappa kappaB muR : ℝ)
    (hv : 0 ≤ v) (hkappa : 0 ≤ kappa)
    (hmuR : 0 ≤ muR) (hgamma : 0 ≤ gamma)
    (hP0 : ∀ ω, 0 ≤ P ω)
    (hF0 : ∀ ω, 0 ≤ F ω) (hT0 : ∀ ω, 0 ≤ T ω) (hD0 : ∀ ω, 0 ≤ D ω)
    (hTF : ∀ᵐ ω ∂μ, T ω ≤ F ω)
    (hD : ∀ᵐ ω ∂μ, D ω ≤ 2 * P ω)
    (hPmeas : AEStronglyMeasurable P μ) (hFmeas : AEStronglyMeasurable F μ)
    (hTmeas : AEStronglyMeasurable T μ) (hDmeas : AEStronglyMeasurable D μ)
    (hP128 : eLpNorm P (128 : ℝ≥0∞) μ ≤ ENNReal.ofReal (3683 / 2500 : ℝ))
    (hF128 : eLpNorm F (128 : ℝ≥0∞) μ ≤
      ENNReal.ofReal (rawTraceFullResponseCap gamma h))
    (hL : ∀ᵐ ω ∂μ,
      L ω ≤ v * D ω + 2 * v * kappa * (P ω * F ω) +
        v * muR * (P ω ^ 2 * F ω))
    (hGamma : ∀ᵐ ω ∂μ,
      Gamma ω ≤ 4 * v * T ω *
        ((1 + kappa) * D ω + (kappaB ^ 2 + kappa) * (P ω ^ 2 * F ω)))
    (hGenInt : Integrable (fun ω =>
      20 * T ω ^ (19 : ℝ) * L ω + 190 * T ω ^ (18 : ℝ) * Gamma ω) μ) :
    (∫ ω, 20 * T ω ^ (19 : ℝ) * L ω +
      190 * T ω ^ (18 : ℝ) * Gamma ω ∂μ) ≤
      20 * (∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) *
        (v * ((78 + 76 * kappa) * (3683 / 2500 : ℝ) +
          2 * kappa * (3683 / 2500 : ℝ) * rawTraceFullResponseCap gamma h +
          (muR + 38 * (kappaB ^ 2 + kappa)) *
            (3683 / 2500 : ℝ) ^ 2 * rawTraceFullResponseCap gamma h)) := by
  have hcaps := raw_trace_p20_bank_holder_caps μ P F T D gamma h hgamma
    hP0 hF0 hT0 hD0 hTF hD hPmeas hFmeas hTmeas hDmeas hP128 hF128
  rcases hcaps with ⟨hTmem, hDmem, hPFmem, hP2Fmem,
    hTnorm, hDnorm, hPFnorm, hP2Fnorm⟩
  have hchain := raw_trace_p20_generator_integral_bound μ T D
    (fun ω => P ω * F ω) (fun ω => P ω ^ 2 * F ω) L Gamma v kappa muR
    (kappaB ^ 2) hv hkappa hmuR (sq_nonneg kappaB)
    hT0 hD0 (fun ω => mul_nonneg (hP0 ω) (hF0 ω))
    (fun ω => mul_nonneg (sq_nonneg (P ω)) (hF0 ω))
    hTmem hDmem hPFmem hP2Fmem hL hGamma hGenInt
  have hcoef :
      v * (39 + 38 * kappa) * positiveLpNorm μ 20 D +
        2 * v * kappa * positiveLpNorm μ 20 (fun ω => P ω * F ω) +
        v * (muR + 38 * (kappaB ^ 2 + kappa)) *
          positiveLpNorm μ 20 (fun ω => P ω ^ 2 * F ω) ≤
      v * ((78 + 76 * kappa) * (3683 / 2500 : ℝ) +
        2 * kappa * (3683 / 2500 : ℝ) * rawTraceFullResponseCap gamma h +
        (muR + 38 * (kappaB ^ 2 + kappa)) *
          (3683 / 2500 : ℝ) ^ 2 * rawTraceFullResponseCap gamma h) := by
    have hDcoef : 0 ≤ v * (39 + 38 * kappa) := by positivity
    have hPFcoef : 0 ≤ 2 * v * kappa := by positivity
    have hP2Fcoef : 0 ≤ v * (muR + 38 * (kappaB ^ 2 + kappa)) := by positivity
    calc
      _ ≤ v * (39 + 38 * kappa) * (2 * (3683 / 2500 : ℝ)) +
          2 * v * kappa * ((3683 / 2500 : ℝ) * rawTraceFullResponseCap gamma h) +
          v * (muR + 38 * (kappaB ^ 2 + kappa)) *
            ((3683 / 2500 : ℝ) ^ 2 * rawTraceFullResponseCap gamma h) := by
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hDnorm hDcoef)
          (mul_le_mul_of_nonneg_left hPFnorm hPFcoef))
          (mul_le_mul_of_nonneg_left hP2Fnorm hP2Fcoef)
      _ = _ := by ring
  have hmoment0 : 0 ≤ ∫ ω, T ω ^ (20 : ℝ) ∂μ := by
    apply integral_nonneg
    intro ω
    exact Real.rpow_nonneg (hT0 ω) _
  have hscale : 0 ≤ 20 * (∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) := by
    positivity
  calc
    (∫ ω, 20 * T ω ^ (19 : ℝ) * L ω +
      190 * T ω ^ (18 : ℝ) * Gamma ω ∂μ) ≤
        20 * (∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) *
          (v * (39 + 38 * kappa) * positiveLpNorm μ 20 D +
            2 * v * kappa * positiveLpNorm μ 20 (fun ω => P ω * F ω) +
            v * (muR + 38 * (kappaB ^ 2 + kappa)) *
              positiveLpNorm μ 20 (fun ω => P ω ^ 2 * F ω)) := hchain
    _ ≤ _ := mul_le_mul_of_nonneg_left hcoef hscale

end ASDExplicitGamma.Inverse

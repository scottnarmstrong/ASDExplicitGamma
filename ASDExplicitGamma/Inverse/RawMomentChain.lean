module

public import ASDExplicitGamma.Gaussian.GaussMomentHolder
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The finite-`p` moment-chain estimate from its source drift and
bracket inequalities, with all three Hölder terms kept separate. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Filter
open ASDExplicitGamma.Gaussian
open scoped ENNReal

/-- The `p = 20` generator estimate. `A`, `BF`, and
`B2F` represent `tr D`, `B_loc F`, and `B_loc^2 F`; `muR` is `mu_R/v`, while
`q` is `B(rho,delta)^2 + kappa_f`. -/
theorem raw_trace_p20_generator_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T A BF B2F L Gamma : Ω → ℝ) (v kappa muR q : ℝ)
    (hv : 0 ≤ v) (hkappa : 0 ≤ kappa) (hmuR : 0 ≤ muR) (hq : 0 ≤ q)
    (hT0 : ∀ ω, 0 ≤ T ω) (hA0 : ∀ ω, 0 ≤ A ω)
    (hBF0 : ∀ ω, 0 ≤ BF ω) (hB2F0 : ∀ ω, 0 ≤ B2F ω)
    (hT : MemLp T (ENNReal.ofReal 20) μ)
    (hA : MemLp A (ENNReal.ofReal 20) μ)
    (hBF : MemLp BF (ENNReal.ofReal 20) μ)
    (hB2F : MemLp B2F (ENNReal.ofReal 20) μ)
    (hL : ∀ᵐ ω ∂μ, L ω ≤ v * A ω + 2 * v * kappa * BF ω + v * muR * B2F ω)
    (hGamma : ∀ᵐ ω ∂μ,
      Gamma ω ≤ 4 * v * T ω * ((1 + kappa) * A ω + (q + kappa) * B2F ω))
    (hGenInt : Integrable (fun ω =>
      20 * T ω ^ (19 : ℝ) * L ω + 190 * T ω ^ (18 : ℝ) * Gamma ω) μ) :
    (∫ ω, 20 * T ω ^ (19 : ℝ) * L ω +
      190 * T ω ^ (18 : ℝ) * Gamma ω ∂μ) ≤
      20 * (∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) *
        (v * (39 + 38 * kappa) * positiveLpNorm μ 20 A +
          2 * v * kappa * positiveLpNorm μ 20 BF +
          v * (muR + 38 * (q + kappa)) * positiveLpNorm μ 20 B2F) := by
  have hpow : ∀ ω, T ω ^ (18 : ℝ) * T ω = T ω ^ (19 : ℝ) := by
    intro ω
    calc
      _ = T ω ^ (18 : ℝ) * T ω ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ω ^ (18 + 1 : ℝ) :=
        (Real.rpow_add' (hT0 ω) (by norm_num : (18 : ℝ) + 1 ≠ 0)).symm
      _ = _ := by congr 1 <;> norm_num
  have hpoint : ∀ᵐ ω ∂μ,
      20 * T ω ^ (19 : ℝ) * L ω + 190 * T ω ^ (18 : ℝ) * Gamma ω ≤
        (20 * v * (39 + 38 * kappa)) * (T ω ^ (19 : ℝ) * A ω) +
          (40 * v * kappa) * (T ω ^ (19 : ℝ) * BF ω) +
          (20 * v * (muR + 38 * (q + kappa))) *
            (T ω ^ (19 : ℝ) * B2F ω) := by
    filter_upwards [hL, hGamma] with ω hLω hGammaω
    have hT18 : 0 ≤ T ω ^ (18 : ℝ) := Real.rpow_nonneg (hT0 ω) _
    have hT19 : 0 ≤ T ω ^ (19 : ℝ) := Real.rpow_nonneg (hT0 ω) _
    have h20 : (0 : ℝ) ≤ 20 := by norm_num
    have h190 : (0 : ℝ) ≤ 190 := by norm_num
    have hLmul := mul_le_mul_of_nonneg_left hLω
      (mul_nonneg h20 hT19)
    have hGmul := mul_le_mul_of_nonneg_left hGammaω
      (mul_nonneg h190 hT18)
    calc
      _ ≤ 20 * T ω ^ (19 : ℝ) *
            (v * A ω + 2 * v * kappa * BF ω + v * muR * B2F ω) +
          190 * T ω ^ (18 : ℝ) *
            (4 * v * T ω * ((1 + kappa) * A ω + (q + kappa) * B2F ω)) :=
        add_le_add hLmul hGmul
      _ = 20 * T ω ^ (19 : ℝ) *
            (v * A ω + 2 * v * kappa * BF ω + v * muR * B2F ω) +
          760 * v * ((T ω ^ (18 : ℝ) * T ω) *
            ((1 + kappa) * A ω + (q + kappa) * B2F ω)) := by ring
      _ = _ := by rw [hpow ω]; ring
  have hprodA : Integrable (fun ω => T ω ^ (19 : ℝ) * A ω) μ := by
    convert integrable_power_mul (μ := μ) (p := 20) (by norm_num)
      hT0 hT hA using 1 <;> norm_num
  have hprodBF : Integrable (fun ω => T ω ^ (19 : ℝ) * BF ω) μ := by
    convert integrable_power_mul (μ := μ) (p := 20) (by norm_num)
      hT0 hT hBF using 1 <;> norm_num
  have hprodB2F : Integrable (fun ω => T ω ^ (19 : ℝ) * B2F ω) μ := by
    convert integrable_power_mul (μ := μ) (p := 20) (by norm_num)
      hT0 hT hB2F using 1 <;> norm_num
  let cA : ℝ := 20 * v * (39 + 38 * kappa)
  let cBF : ℝ := 40 * v * kappa
  let cB2F : ℝ := 20 * v * (muR + 38 * (q + kappa))
  have htermA : Integrable (fun ω => cA * (T ω ^ (19 : ℝ) * A ω)) μ :=
    hprodA.const_mul cA
  have htermBF : Integrable (fun ω => cBF * (T ω ^ (19 : ℝ) * BF ω)) μ :=
    hprodBF.const_mul cBF
  have htermB2F : Integrable (fun ω => cB2F * (T ω ^ (19 : ℝ) * B2F ω)) μ :=
    hprodB2F.const_mul cB2F
  have hRight : Integrable (fun ω =>
      cA * (T ω ^ (19 : ℝ) * A ω) +
        cBF * (T ω ^ (19 : ℝ) * BF ω) +
        cB2F * (T ω ^ (19 : ℝ) * B2F ω)) μ :=
    (htermA.add htermBF).add htermB2F
  have hAHolder0 := integral_power_mul_le μ (p := 20) (by norm_num)
    hT0 hA0 hT hA
  have hBFHolder0 := integral_power_mul_le μ (p := 20) (by norm_num)
    hT0 hBF0 hT hBF
  have hB2FHolder0 := integral_power_mul_le μ (p := 20) (by norm_num)
    hT0 hB2F0 hT hB2F
  have hAHolder :
      (∫ ω, T ω ^ (19 : ℝ) * A ω ∂μ) ≤
        (∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) *
          positiveLpNorm μ 20 A := by
    simpa only [show (20 : ℝ) - 1 = 19 by norm_num,
      show (1 : ℝ) - (20 : ℝ)⁻¹ = (19 : ℝ) / 20 by norm_num] using hAHolder0
  have hBFHolder :
      (∫ ω, T ω ^ (19 : ℝ) * BF ω ∂μ) ≤
        (∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) *
          positiveLpNorm μ 20 BF := by
    simpa only [show (20 : ℝ) - 1 = 19 by norm_num,
      show (1 : ℝ) - (20 : ℝ)⁻¹ = (19 : ℝ) / 20 by norm_num] using hBFHolder0
  have hB2FHolder :
      (∫ ω, T ω ^ (19 : ℝ) * B2F ω ∂μ) ≤
        (∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) *
          positiveLpNorm μ 20 B2F := by
    simpa only [show (20 : ℝ) - 1 = 19 by norm_num,
      show (1 : ℝ) - (20 : ℝ)⁻¹ = (19 : ℝ) / 20 by norm_num] using hB2FHolder0
  have hcA : 0 ≤ cA := by positivity
  have hcBF : 0 ≤ cBF := by positivity
  have hcB2F : 0 ≤ cB2F := by positivity
  calc
    (∫ ω, 20 * T ω ^ (19 : ℝ) * L ω +
      190 * T ω ^ (18 : ℝ) * Gamma ω ∂μ) ≤
        ∫ ω, cA * (T ω ^ (19 : ℝ) * A ω) +
          cBF * (T ω ^ (19 : ℝ) * BF ω) +
          cB2F * (T ω ^ (19 : ℝ) * B2F ω) ∂μ :=
      integral_mono_ae hGenInt hRight hpoint
    _ = cA * (∫ ω, T ω ^ (19 : ℝ) * A ω ∂μ) +
          cBF * (∫ ω, T ω ^ (19 : ℝ) * BF ω ∂μ) +
          cB2F * (∫ ω, T ω ^ (19 : ℝ) * B2F ω ∂μ) := by
      calc
        _ = ∫ ω, cA * (T ω ^ (19 : ℝ) * A ω) +
              (cBF * (T ω ^ (19 : ℝ) * BF ω) +
                cB2F * (T ω ^ (19 : ℝ) * B2F ω)) ∂μ := by
          congr 1
          funext ω
          ring
        _ = _ := by
          change (∫ ω,
            (fun ω => cA * (T ω ^ (19 : ℝ) * A ω)) ω +
              ((fun ω => cBF * (T ω ^ (19 : ℝ) * BF ω)) +
                (fun ω => cB2F * (T ω ^ (19 : ℝ) * B2F ω))) ω ∂μ) = _
          calc
            _ = (∫ ω, cA * (T ω ^ (19 : ℝ) * A ω) ∂μ) +
                (∫ ω, cBF * (T ω ^ (19 : ℝ) * BF ω) +
                  cB2F * (T ω ^ (19 : ℝ) * B2F ω) ∂μ) :=
              integral_add htermA (htermBF.add htermB2F)
            _ = (∫ ω, cA * (T ω ^ (19 : ℝ) * A ω) ∂μ) +
                ((∫ ω, cBF * (T ω ^ (19 : ℝ) * BF ω) ∂μ) +
                  (∫ ω, cB2F * (T ω ^ (19 : ℝ) * B2F ω) ∂μ)) := by
              congr 1
              exact integral_add htermBF htermB2F
            _ = _ := by
              simp only [integral_const_mul]
              ring
    _ ≤ cA * ((∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) *
          positiveLpNorm μ 20 A) +
        cBF * ((∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) *
          positiveLpNorm μ 20 BF) +
        cB2F * ((∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) *
          positiveLpNorm μ 20 B2F) := by
      nlinarith [mul_le_mul_of_nonneg_left hAHolder hcA,
        mul_le_mul_of_nonneg_left hBFHolder hcBF,
        mul_le_mul_of_nonneg_left hB2FHolder hcB2F]
    _ = _ := by
      dsimp [cA, cBF, cB2F]
      ring

end ASDExplicitGamma.Inverse

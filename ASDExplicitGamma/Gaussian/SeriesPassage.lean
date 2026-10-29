/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.SeriesHeat
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Sqrt

/-!
# Differentiating the infinite-rank Gaussian heat average

This module differentiates the selected Hilbert-series version under the integral, then passes the
finite-rank Gaussian heat identity through the fast subsequence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ASDExplicitGamma.Gaussian

private noncomputable def gaussianRandomHeatPath {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Φ : E → ℝ) (x : E) (Z : (ℕ → ℝ) → E) :
    ℝ → (ℕ → ℝ) → ℝ :=
  fun t ω => Φ (x + Real.sqrt t • Z ω)

private noncomputable def gaussianRandomHeatPathDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Φ : E → ℝ) (x : E) (Z : (ℕ → ℝ) → E) (t : ℝ) :
    (ℕ → ℝ) → ℝ :=
  fun ω => (1 / (2 * Real.sqrt t)) *
    fderiv ℝ Φ (x + Real.sqrt t • Z ω) (Z ω)

private lemma hasDerivAt_gaussianRandomHeatPath {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (x z : E) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Φ (x + Real.sqrt s • z))
      ((1 / (2 * Real.sqrt t)) * fderiv ℝ Φ (x + Real.sqrt t • z) z) t := by
  have hsqrt := Real.hasDerivAt_sqrt (ne_of_gt ht)
  have hpath : HasDerivAt (fun s : ℝ => x + Real.sqrt s • z)
      ((1 / (2 * Real.sqrt t)) • z) t := by
    exact (hsqrt.smul_const z).const_add x
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have houter := (hΦ1.differentiable_one (x + Real.sqrt t • z)).hasFDerivAt
  have hcomp := houter.comp t hpath
  have hderiv := hcomp.hasDerivAt
  simpa [Function.comp_def, ContinuousLinearMap.map_smul, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc]
    using hderiv

/-- Differentiation under the integral for a random direction with enough polynomial moments. -/
private theorem hasDerivAt_gaussianRandomHeatAverage {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] {Φ : E → ℝ}
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (x : E)
    (Z : (ℕ → ℝ) → E)
    (hZmeas : AEStronglyMeasurable Z standardGaussianInfinitePi)
    (hZall : ∀ p : ℝ, 2 ≤ p →
      MemLp Z (ENNReal.ofReal p) standardGaussianInfinitePi)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ ω, gaussianRandomHeatPath Φ x Z s ω
        ∂standardGaussianInfinitePi)
      (∫ ω, gaussianRandomHeatPathDeriv Φ x Z t ω ∂standardGaussianInfinitePi) t := by
  rcases hΦ with ⟨hC2, C, hC, a, hvalue, hfirst, hsecond⟩
  let F := gaussianRandomHeatPath Φ x Z
  let F' := gaussianRandomHeatPathDeriv Φ x Z
  let M : ℝ := 3 * t / 2
  let r : ℝ := Real.sqrt (t / 2)
  let B : ℝ := 1 + ‖x‖ + Real.sqrt M
  let K : ℝ := C * B ^ a / (2 * r)
  let bound : (ℕ → ℝ) → ℝ := fun ω => K * (1 + ‖Z ω‖) ^ (a + 1)
  have ht2 : 0 < t / 2 := by positivity
  have hr : 0 < r := Real.sqrt_pos.2 ht2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hZraw := hZall ((a + 3 : ℕ) : ℝ) (by norm_cast; omega)
  have hZhigh : MemLp Z ((a + 3 : ℕ) : ℝ≥0∞) standardGaussianInfinitePi := by
    simpa only [ENNReal.ofReal_natCast] using hZraw
  have hboundPoly : Integrable (fun ω => (1 + ‖Z ω‖) ^ (a + 1))
      standardGaussianInfinitePi :=
    integrable_one_add_norm_pow_of_memLp (d := a + 1) hZhigh
  have hboundInt : Integrable bound standardGaussianInfinitePi := by
    simpa [bound, mul_comm] using hboundPoly.mul_const K
  have hFmeas (s : ℝ) : AEStronglyMeasurable (F s) standardGaussianInfinitePi := by
    let G : E → ℝ := fun z => Φ (x + Real.sqrt s • z)
    have hG : Continuous G := by
      dsimp [G]
      exact hC2.continuous.comp (continuous_const.add
        ((continuous_const : Continuous fun _ : E => Real.sqrt s).smul continuous_id))
    change AEStronglyMeasurable (G ∘ Z) standardGaussianInfinitePi
    exact hG.comp_aestronglyMeasurable hZmeas
  have hF'meas : AEStronglyMeasurable (F' t) standardGaussianInfinitePi := by
    let A : E × E → ℝ := fun yz => fderiv ℝ Φ yz.1 yz.2
    have hA : Continuous A := hC2.continuous_fderiv_apply (by norm_num)
    have hmap : Continuous (fun z : E => (x + Real.sqrt t • z, z)) := by
      exact (continuous_const.add
        ((continuous_const : Continuous fun _ : E => Real.sqrt t).smul continuous_id)).prodMk
        continuous_id
    have hcomp : AEStronglyMeasurable
        (fun ω => fderiv ℝ Φ (x + Real.sqrt t • Z ω) (Z ω))
        standardGaussianInfinitePi := (hA.comp_aestronglyMeasurable (hmap.comp_aestronglyMeasurable hZmeas))
    change AEStronglyMeasurable
      (fun ω => (1 / (2 * Real.sqrt t)) * fderiv ℝ Φ
        (x + Real.sqrt t • Z ω) (Z ω)) standardGaussianInfinitePi
    exact hcomp.const_mul _
  have hFint : Integrable (F t) standardGaussianInfinitePi := by
    let Y : (ℕ → ℝ) → E := fun ω => x + Real.sqrt t • Z ω
    have hYmem : MemLp Y ((a + 2 : ℕ) : ℝ≥0∞) standardGaussianInfinitePi := by
      have hYhigh : MemLp Y ((a + 3 : ℕ) : ℝ≥0∞) standardGaussianInfinitePi := by
        dsimp [Y]
        exact (memLp_const x).add (hZhigh.const_smul (Real.sqrt t))
      exact hYhigh.mono_exponent (by norm_cast; omega)
    have hpoly := integrable_one_add_norm_pow_of_memLp (d := a) hYmem
    have hdom : ∀ᵐ ω ∂standardGaussianInfinitePi,
        ‖F t ω‖ ≤ C * (1 + ‖Y ω‖) ^ a := by
      filter_upwards [] with ω
      dsimp [F, gaussianRandomHeatPath, Y]
      exact hvalue _
    have hnormInt : Integrable (fun ω => ‖F t ω‖) standardGaussianInfinitePi := by
      have hmajor : Integrable (fun ω => C * (1 + ‖Y ω‖) ^ a)
          standardGaussianInfinitePi := by
        simpa [mul_comm] using hpoly.mul_const C
      have hdom' : ∀ᵐ ω ∂standardGaussianInfinitePi,
          ‖‖F t ω‖‖ ≤ C * (1 + ‖Y ω‖) ^ a := by
        filter_upwards [hdom] with ω hω
        simpa using hω
      exact hmajor.mono' (hFmeas t).norm hdom'
    exact (integrable_norm_iff (hFmeas t)).1 hnormInt
  have hs : Set.Ioo (t / 2) (3 * t / 2) ∈ 𝓝 t := by
    have hleft : t / 2 < t := by linarith
    have hright : t < 3 * t / 2 := by linarith
    exact Ioo_mem_nhds hleft hright
  have hF'meas := hF'meas
  have hboundDeriv : ∀ᵐ ω ∂standardGaussianInfinitePi,
      ∀ s ∈ Set.Ioo (t / 2) (3 * t / 2), ‖F' s ω‖ ≤ bound ω := by
    filter_upwards [] with ω s hs
    have hslo : t / 2 < s := hs.1
    have hshi : s < 3 * t / 2 := hs.2
    have hspos : 0 < s := lt_trans ht2 hslo
    have hsqrtlo : r ≤ Real.sqrt s := by
      dsimp [r]
      exact Real.sqrt_le_sqrt (le_of_lt hslo)
    have hsqrthi : Real.sqrt s ≤ Real.sqrt M := by
      dsimp [M]
      exact Real.sqrt_le_sqrt (le_of_lt hshi)
    have hz : 0 ≤ ‖Z ω‖ := norm_nonneg _
    have hy : 1 + ‖x + Real.sqrt s • Z ω‖ ≤ B * (1 + ‖Z ω‖) := by
      have htri : ‖x + Real.sqrt s • Z ω‖ ≤ ‖x‖ + Real.sqrt M * ‖Z ω‖ := by
        calc
          ‖x + Real.sqrt s • Z ω‖ ≤ ‖x‖ + ‖Real.sqrt s • Z ω‖ := norm_add_le _ _
          _ = ‖x‖ + Real.sqrt s * ‖Z ω‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          _ ≤ ‖x‖ + Real.sqrt M * ‖Z ω‖ := by gcongr
      dsimp [B]
      have hroot : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
      have hprod : 0 ≤ (1 + ‖x‖) * ‖Z ω‖ := mul_nonneg (by positivity) hz
      calc
        1 + ‖x + Real.sqrt s • Z ω‖ ≤ 1 + ‖x‖ + Real.sqrt M * ‖Z ω‖ := by
          linarith [htri]
        _ ≤ (1 + ‖x‖ + Real.sqrt M) * (1 + ‖Z ω‖) := by nlinarith
    have hcoef : 0 ≤ 1 / (2 * Real.sqrt s) := by positivity
    have hcoefle : 1 / (2 * Real.sqrt s) ≤ 1 / (2 * r) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt s)
        (by positivity : 0 < 2 * r)).2
      nlinarith
    have hdf : |fderiv ℝ Φ (x + Real.sqrt s • Z ω) (Z ω)| ≤
        C * (1 + ‖x + Real.sqrt s • Z ω‖) ^ a * ‖Z ω‖ := by
      calc
        |fderiv ℝ Φ (x + Real.sqrt s • Z ω) (Z ω)| =
            ‖fderiv ℝ Φ (x + Real.sqrt s • Z ω) (Z ω)‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖fderiv ℝ Φ (x + Real.sqrt s • Z ω)‖ * ‖Z ω‖ :=
          (fderiv ℝ Φ (x + Real.sqrt s • Z ω)).le_opNorm _
        _ ≤ C * (1 + ‖x + Real.sqrt s • Z ω‖) ^ a * ‖Z ω‖ := by
          gcongr
          exact hfirst _
    have hderiv : ‖F' s ω‖ ≤
        (1 / (2 * r)) * (C * B ^ a) * (1 + ‖Z ω‖) ^ (a + 1) := by
      dsimp [F', gaussianRandomHeatPathDeriv]
      rw [abs_mul, abs_of_nonneg hcoef]
      calc
        (1 / (2 * Real.sqrt s)) *
            |fderiv ℝ Φ (x + Real.sqrt s • Z ω) (Z ω)|
            ≤ (1 / (2 * r)) *
                (C * (B * (1 + ‖Z ω‖)) ^ a * ‖Z ω‖) := by
              calc
                _ ≤ (1 / (2 * Real.sqrt s)) *
                    (C * (1 + ‖x + Real.sqrt s • Z ω‖) ^ a * ‖Z ω‖) :=
                      mul_le_mul_of_nonneg_left hdf hcoef
                _ ≤ _ := by gcongr
        _ ≤ (1 / (2 * r)) * (C * B ^ a) * (1 + ‖Z ω‖) ^ (a + 1) := by
              have hpow : (B * (1 + ‖Z ω‖)) ^ a = B ^ a * (1 + ‖Z ω‖) ^ a := by
                rw [mul_pow]
              rw [hpow]
              have hcoef' : 0 ≤ (1 / (2 * r)) * C * B ^ a := by positivity
              have hzle : ‖Z ω‖ ≤ 1 + ‖Z ω‖ := by linarith
              calc
                (1 / (2 * r)) * (C * (B ^ a * (1 + ‖Z ω‖) ^ a) * ‖Z ω‖) ≤
                    ((1 / (2 * r)) * C * B ^ a) *
                      ((1 + ‖Z ω‖) ^ a * (1 + ‖Z ω‖)) := by
                        have hpowNonneg : 0 ≤ (1 + ‖Z ω‖) ^ a := pow_nonneg (by positivity) _
                        calc
                          _ = ((1 / (2 * r)) * C * B ^ a) *
                              ((1 + ‖Z ω‖) ^ a * ‖Z ω‖) := by ring
                          _ ≤ _ := mul_le_mul_of_nonneg_left
                            (mul_le_mul_of_nonneg_left hzle hpowNonneg) hcoef'
                _ = (1 / (2 * r)) * (C * B ^ a) * (1 + ‖Z ω‖) ^ (a + 1) := by
                        rw [← pow_succ]
                        ring
    simpa [bound, K, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hderiv
  have hdiff : ∀ᵐ ω ∂standardGaussianInfinitePi,
      ∀ s ∈ Set.Ioo (t / 2) (3 * t / 2), HasDerivAt (F · ω) (F' s ω) s := by
    filter_upwards [] with ω s hs
    have hspos : 0 < s := lt_trans ht2 hs.1
    simpa [F, F', gaussianRandomHeatPath, gaussianRandomHeatPathDeriv] using
      hasDerivAt_gaussianRandomHeatPath hC2 x (Z ω) hspos
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Filter.Eventually.of_forall hFmeas) hFint hF'meas hboundDeriv hboundInt hdiff
  simpa [F, F', gaussianRandomHeatPath, gaussianRandomHeatPathDeriv] using hresult.2


/-- The heat identity for the selected infinite-rank Hilbert Gaussian series at positive time. -/
theorem hasDerivAt_gaussianSeriesHeatAverage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] {v : ℕ → V}
    (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) (Φ : E → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (x : E) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussianSeriesHeatAverage hA T Φ x)
      ((1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA T Φ x t) t := by
  rcases hΦ with ⟨hC2, C, hC, a, hvalue, hfirst, hsecond⟩
  let Z : (ℕ → ℝ) → E := gaussianSeriesLimitE hA T
  have hZmeas : AEStronglyMeasurable Z standardGaussianInfinitePi :=
    (stronglyMeasurable_gaussianSeriesLimitE hA T).aestronglyMeasurable
  have hZall : ∀ p : ℝ, 2 ≤ p →
      MemLp Z (ENNReal.ofReal p) standardGaussianInfinitePi := by
    intro p hp
    exact memLp_gaussianSeriesLimitE hA T hp
  have hlimit := hasDerivAt_gaussianRandomHeatAverage
    (Φ := Φ) ⟨hC2, C, hC, a, hvalue, hfirst, hsecond⟩ x Z hZmeas hZall ht
  have hlimit' : HasDerivAt (gaussianSeriesHeatAverage hA T Φ x)
      (∫ ω, gaussianRandomHeatPathDeriv Φ x Z t ω ∂standardGaussianInfinitePi) t := by
    change HasDerivAt (fun s => ∫ ω, Φ (x + Real.sqrt s • Z ω)
      ∂standardGaussianInfinitePi) _ _
    simpa [gaussianSeriesHeatAverage, gaussianSeriesHeatArgument,
      gaussianRandomHeatPath, Z] using hlimit
  let q : ℝ := ∫ ω, gaussianRandomHeatPathDeriv Φ x Z t ω ∂standardGaussianInfinitePi
  let Q : V → ℝ := fun z =>
    (1 / (2 * Real.sqrt t)) * fderiv ℝ Φ (x + Real.sqrt t • T z) (T z)
  have hQcont : Continuous Q := by
    let A : E × E → ℝ := fun yz => fderiv ℝ Φ yz.1 yz.2
    have hAcont : Continuous A := hC2.continuous_fderiv_apply (by norm_num)
    have hmap : Continuous (fun z : V => (x + Real.sqrt t • T z, T z)) := by
      exact (continuous_const.add
        ((continuous_const : Continuous fun _ : V => Real.sqrt t).smul T.continuous)).prodMk
        T.continuous
    dsimp [Q, A]
    exact (continuous_const.mul (hAcont.comp hmap))
  let qk : ℕ → ℝ := fun k => ∫ ω,
      Q (gaussianFastPartialSumSequence hA k ω) ∂standardGaussianInfinitePi
  let ZV : (ℕ → ℝ) → V := gaussianSeriesLimit v hA
  let qV : V → ℝ := fun z =>
    (1 / (2 * Real.sqrt t)) * fderiv ℝ Φ (x + Real.sqrt t • T z) (T z)
  have hqVcont : Continuous qV := hQcont
  have hqFastMeas (k : ℕ) : AEStronglyMeasurable
      (fun ω => Q (gaussianFastPartialSumSequence hA k ω)) standardGaussianInfinitePi := by
    let hm := memLp_gaussianPartialSum v (p := 2) (by norm_num) hA
      (gaussianFastIndex hA k)
    exact hQcont.comp_aestronglyMeasurable hm.aestronglyMeasurable
  have hqMeas : AEStronglyMeasurable (fun ω => qV (ZV ω))
      standardGaussianInfinitePi :=
    (hqVcont.comp_stronglyMeasurable (stronglyMeasurable_gaussianSeriesLimit v hA)).aestronglyMeasurable
  have hqLimit : ∀ᵐ ω ∂standardGaussianInfinitePi,
      Tendsto (fun k => Q (gaussianFastPartialSumSequence hA k ω)) atTop
        (𝓝 (qV (ZV ω))) := by
    filter_upwards [ae_tendsto_gaussianSeriesLimit v hA] with ω hω
    exact hqVcont.continuousAt.tendsto.comp hω
  let B : ℝ := 1 + ‖x‖ + Real.sqrt t * ‖T‖
  let K : ℝ := (1 / (2 * Real.sqrt t)) * C * B ^ a * ‖T‖
  let P : (ℕ → ℝ) → ℝ := fun ω => K * (1 + gaussianFastEnvelope hA ω) ^ (a + 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hPint : Integrable P standardGaussianInfinitePi := by
    simpa [P, mul_comm] using
      (integrable_fastEnvelope_polynomial hA (a + 1)).mul_const K
  have harg := ae_gaussianFastArgument_growth_bound hA T x
    (M := t) (t := t) le_rfl
  have hpartial := ae_norm_gaussianFastPartialSum_le_envelope hA
  have hlimitEnv := ae_norm_gaussianSeriesLimit_le_fastEnvelope hA
  have hbound : ∀ᵐ ω ∂standardGaussianInfinitePi,
      (∀ k, ‖Q (gaussianFastPartialSumSequence hA k ω)‖ ≤ P ω) ∧
        ‖qV (ZV ω)‖ ≤ P ω := by
    filter_upwards [harg, hpartial, hlimitEnv] with ω hargω hpartialω hlimitω
    have hD (y w : E) :
        |fderiv ℝ Φ y w| ≤ C * (1 + ‖y‖) ^ a * ‖w‖ := by
      calc
        |fderiv ℝ Φ y w| = ‖fderiv ℝ Φ y w‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖fderiv ℝ Φ y‖ * ‖w‖ := (fderiv ℝ Φ y).le_opNorm _
        _ ≤ C * (1 + ‖y‖) ^ a * ‖w‖ := by
          exact mul_le_mul_of_nonneg_right (hfirst y) (norm_nonneg _)
    have henvω : 0 ≤ gaussianFastEnvelope hA ω := by
      dsimp [gaussianFastEnvelope, gaussianFastVariation]
      exact add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)
    constructor
    · intro k
      have hZk : ‖T (gaussianFastPartialSumSequence hA k ω)‖ ≤
          ‖T‖ * gaussianFastEnvelope hA ω := by
        calc
          _ ≤ ‖T‖ * ‖gaussianFastPartialSumSequence hA k ω‖ := T.le_opNorm _
          _ ≤ _ := mul_le_mul_of_nonneg_left (hpartialω k) (norm_nonneg _)
      rw [Real.norm_eq_abs]
      dsimp [Q, P]
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt t))]
      calc
        (1 / (2 * Real.sqrt t)) *
            |fderiv ℝ Φ (x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω))
              (T (gaussianFastPartialSumSequence hA k ω))|
          ≤ (1 / (2 * Real.sqrt t)) *
            (C * (B * (1 + gaussianFastEnvelope hA ω)) ^ a *
              (‖T‖ * gaussianFastEnvelope hA ω)) := by
                have hy := hargω.1 k
                have hyB : 1 + ‖x + Real.sqrt t • T
                    (gaussianFastPartialSumSequence hA k ω)‖ ≤
                    B * (1 + gaussianFastEnvelope hA ω) := by simpa [B] using hy
                have hp : (1 + ‖x + Real.sqrt t • T
                    (gaussianFastPartialSumSequence hA k ω)‖) ^ a ≤
                    (B * (1 + gaussianFastEnvelope hA ω)) ^ a := by
                  gcongr
                have h1 := mul_le_mul_of_nonneg_left hp hC
                have h2 := mul_le_mul_of_nonneg_right h1
                  (norm_nonneg (T (gaussianFastPartialSumSequence hA k ω)))
                have hfactor : 0 ≤ C * (B * (1 + gaussianFastEnvelope hA ω)) ^ a :=
                  mul_nonneg hC (pow_nonneg (mul_nonneg hB (by linarith)) _)
                have h3 := mul_le_mul_of_nonneg_left hZk hfactor
                have hinner :
                    C * (1 + ‖x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω)‖) ^ a *
                      ‖T (gaussianFastPartialSumSequence hA k ω)‖ ≤
                    C * (B * (1 + gaussianFastEnvelope hA ω)) ^ a *
                      (‖T‖ * gaussianFastEnvelope hA ω) := h2.trans h3
                calc
                  (1 / (2 * Real.sqrt t)) *
                      |fderiv ℝ Φ (x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω))
                        (T (gaussianFastPartialSumSequence hA k ω))|
                    ≤ (1 / (2 * Real.sqrt t)) *
                        (C * (1 + ‖x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω)‖) ^ a *
                          ‖T (gaussianFastPartialSumSequence hA k ω)‖) :=
                            mul_le_mul_of_nonneg_left (hD _ _) (by positivity)
                  _ ≤ _ := mul_le_mul_of_nonneg_left hinner (by positivity)
        _ ≤ P ω := by
          dsimp [P, K]
          have he : 0 ≤ gaussianFastEnvelope hA ω := by
            dsimp [gaussianFastEnvelope, gaussianFastVariation]
            exact add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)
          have hu : gaussianFastEnvelope hA ω ≤ 1 + gaussianFastEnvelope hA ω := by linarith
          rw [mul_pow]
          calc
            (1 / (2 * Real.sqrt t)) *
                (C * (B ^ a * (1 + gaussianFastEnvelope hA ω) ^ a) *
                  (‖T‖ * gaussianFastEnvelope hA ω))
              = K * ((1 + gaussianFastEnvelope hA ω) ^ a *
                  gaussianFastEnvelope hA ω) := by dsimp [K]; ring
            _ ≤ K * ((1 + gaussianFastEnvelope hA ω) ^ a *
                  (1 + gaussianFastEnvelope hA ω)) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hu (pow_nonneg (by positivity) _)) hK
            _ = K * (1 + gaussianFastEnvelope hA ω) ^ (a + 1) := by rw [← pow_succ]
    · have hZ : ‖T (ZV ω)‖ ≤ ‖T‖ * gaussianFastEnvelope hA ω := by
        calc
          _ ≤ ‖T‖ * ‖ZV ω‖ := T.le_opNorm _
          _ ≤ _ := mul_le_mul_of_nonneg_left hlimitω (norm_nonneg _)
      rw [Real.norm_eq_abs]
      dsimp [qV, ZV, P]
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt t))]
      calc
        (1 / (2 * Real.sqrt t)) *
            |fderiv ℝ Φ (x + Real.sqrt t • T (ZV ω)) (T (ZV ω))|
          ≤ (1 / (2 * Real.sqrt t)) *
            (C * (B * (1 + gaussianFastEnvelope hA ω)) ^ a *
              (‖T‖ * gaussianFastEnvelope hA ω)) := by
                have hy := hargω.2
                have hyB : 1 + ‖x + Real.sqrt t • T (ZV ω)‖ ≤
                    B * (1 + gaussianFastEnvelope hA ω) := by
                  simpa [B, gaussianSeriesHeatArgument, gaussianSeriesLimitE, Z, ZV] using hy
                have hp : (1 + ‖x + Real.sqrt t • T (ZV ω)‖) ^ a ≤
                    (B * (1 + gaussianFastEnvelope hA ω)) ^ a := by
                  gcongr
                have h1 := mul_le_mul_of_nonneg_left hp hC
                have h2 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (T (ZV ω)))
                have hfactor : 0 ≤ C * (B * (1 + gaussianFastEnvelope hA ω)) ^ a :=
                  mul_nonneg hC (pow_nonneg (mul_nonneg hB (by linarith)) _)
                have h3 := mul_le_mul_of_nonneg_left hZ hfactor
                have hinner :
                    C * (1 + ‖x + Real.sqrt t • T (ZV ω)‖) ^ a * ‖T (ZV ω)‖
                      ≤ C * (B * (1 + gaussianFastEnvelope hA ω)) ^ a *
                        (‖T‖ * gaussianFastEnvelope hA ω) := h2.trans h3
                calc
                  (1 / (2 * Real.sqrt t)) *
                      |fderiv ℝ Φ (x + Real.sqrt t • T (ZV ω)) (T (ZV ω))|
                    ≤ (1 / (2 * Real.sqrt t)) *
                        (C * (1 + ‖x + Real.sqrt t • T (ZV ω)‖) ^ a * ‖T (ZV ω)‖) :=
                            mul_le_mul_of_nonneg_left (hD _ _) (by positivity)
                  _ ≤ _ := mul_le_mul_of_nonneg_left hinner (by positivity)
        _ ≤ K * (1 + gaussianFastEnvelope hA ω) ^ (a + 1) := by
          have he : 0 ≤ gaussianFastEnvelope hA ω := by
            dsimp [gaussianFastEnvelope, gaussianFastVariation]
            exact add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)
          have hu : gaussianFastEnvelope hA ω ≤ 1 + gaussianFastEnvelope hA ω := by linarith
          rw [mul_pow]
          calc
            (1 / (2 * Real.sqrt t)) *
                (C * (B ^ a * (1 + gaussianFastEnvelope hA ω) ^ a) *
                  (‖T‖ * gaussianFastEnvelope hA ω))
              = K * ((1 + gaussianFastEnvelope hA ω) ^ a *
                  gaussianFastEnvelope hA ω) := by dsimp [K]; ring
            _ ≤ K * ((1 + gaussianFastEnvelope hA ω) ^ a *
                  (1 + gaussianFastEnvelope hA ω)) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hu (pow_nonneg (by positivity) _)) hK
            _ = K * (1 + gaussianFastEnvelope hA ω) ^ (a + 1) := by rw [← pow_succ]
  have hconv := tendsto_integral_filter_of_dominated_convergence P
    (Filter.Eventually.of_forall hqFastMeas) (Filter.Eventually.of_forall fun k =>
      (hbound.mono fun ω hω => hω.1 k)) hPint hqLimit
  have hqconv : Tendsto qk atTop (𝓝 (∫ ω, qV (ZV ω) ∂standardGaussianInfinitePi)) := by
    simpa [qk] using hconv
  have htraceGrowth := hasPolynomiallyBoundedSecondDirectionalDerivative_of_C2Derivatives
    ⟨hC2, C, hC, a, hvalue, hfirst, hsecond⟩
  have htraceConv := tendsto_gaussianFastHeatTraceAverage hA T Φ hC2 htraceGrowth x t
  have hfastEq : ∀ k, qk k =
      (1 / 2 : ℝ) * gaussianFastHeatTraceAverage hA T Φ x k t := by
    intro k
    let Zk : (ℕ → ℝ) → E := fun ω => T (gaussianFastPartialSumSequence hA k ω)
    have hZkmeas : AEStronglyMeasurable Zk standardGaussianInfinitePi := by
      let hm := memLp_gaussianPartialSum v (p := 2) (by norm_num) hA
        (gaussianFastIndex hA k)
      exact T.continuous.comp_aestronglyMeasurable hm.aestronglyMeasurable
    have hZkall : ∀ p : ℝ, 2 ≤ p →
        MemLp Zk (ENNReal.ofReal p) standardGaussianInfinitePi := by
      intro p hp
      have hm := memLp_gaussianPartialSum v (p := p) hp hA
        (gaussianFastIndex hA k)
      change MemLp (fun ω => T (gaussianPartialSum v (gaussianFastIndex hA k) ω))
        (ENNReal.ofReal p) standardGaussianInfinitePi
      exact hm.continuousLinearMap_comp T
    have hdiffk := hasDerivAt_gaussianRandomHeatAverage
      (Φ := Φ) ⟨hC2, C, hC, a, hvalue, hfirst, hsecond⟩ x Zk hZkmeas hZkall ht
    have hdiffk' : HasDerivAt (gaussianFastHeatAverage hA T Φ x k)
        (∫ ω, gaussianRandomHeatPathDeriv Φ x Zk t ω ∂standardGaussianInfinitePi) t := by
      change HasDerivAt (fun s => ∫ ω, Φ (x + Real.sqrt s •
        T (gaussianFastPartialSumSequence hA k ω)) ∂standardGaussianInfinitePi) _ _
      exact hdiffk
    have hfinite := hasDerivAt_gaussianFastHeatAverage hA T Φ
      ⟨hC2, C, hC, a, hvalue, hfirst, hsecond⟩ x ht k
    have hEq := hdiffk'.unique hfinite
    simpa [qk, Q, gaussianRandomHeatPathDeriv, Zk,
      gaussianFastPartialSumSequence] using hEq
  have hhalfTrace : Tendsto
      (fun k => (1 / 2 : ℝ) * gaussianFastHeatTraceAverage hA T Φ x k t) atTop
      (𝓝 ((1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA T Φ x t)) := by
    exact tendsto_const_nhds.mul htraceConv
  have hqEq : (∫ ω, qV (ZV ω) ∂standardGaussianInfinitePi) =
      (1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA T Φ x t := by
    have hqhalf : Tendsto
        (fun k => (1 / 2 : ℝ) * gaussianFastHeatTraceAverage hA T Φ x k t) atTop
        (𝓝 (∫ ω, qV (ZV ω) ∂standardGaussianInfinitePi)) := by
      exact hqconv.congr' (Filter.Eventually.of_forall hfastEq)
    exact tendsto_nhds_unique hqhalf hhalfTrace
  have hident : (∫ ω, gaussianRandomHeatPathDeriv Φ x Z t ω ∂standardGaussianInfinitePi) =
      (1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA T Φ x t := by
    simpa [qV, ZV, Z, gaussianSeriesLimitE, gaussianSeriesHeatArgument,
      gaussianRandomHeatPathDeriv] using hqEq
  rw [← hident]
  exact hlimit'


private lemma gaussianSeriesHeatArgument_bound_unit {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (x : E) (ω : ℕ → ℝ)
    (hω : ‖gaussianSeriesLimit v hA ω‖ ≤ gaussianFastEnvelope hA ω)
    {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
    1 + ‖gaussianSeriesHeatArgument hA T x s ω‖ ≤
      (1 + ‖x‖ + ‖T‖) * (1 + gaussianFastEnvelope hA ω) := by
  have henv : 0 ≤ gaussianFastEnvelope hA ω :=
    le_trans (norm_nonneg _) hω
  have hz : ‖T (gaussianSeriesLimit v hA ω)‖ ≤
      ‖T‖ * gaussianFastEnvelope hA ω := by
    calc
      _ ≤ ‖T‖ * ‖gaussianSeriesLimit v hA ω‖ := T.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left hω (norm_nonneg _)
  have hsqrt : Real.sqrt s ≤ 1 := by
    calc
      Real.sqrt s ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hs.2
      _ = 1 := Real.sqrt_one
  have hsqrtNonneg := Real.sqrt_nonneg s
  have htri : ‖x + Real.sqrt s • T (gaussianSeriesLimit v hA ω)‖ ≤
      ‖x‖ + ‖T‖ * gaussianFastEnvelope hA ω := by
    calc
      _ ≤ ‖x‖ + ‖Real.sqrt s • T (gaussianSeriesLimit v hA ω)‖ := norm_add_le _ _
      _ = ‖x‖ + Real.sqrt s * ‖T (gaussianSeriesLimit v hA ω)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqrtNonneg]
      _ ≤ ‖x‖ + 1 * ‖T (gaussianSeriesLimit v hA ω)‖ := by
        gcongr
      _ = ‖x‖ + ‖T (gaussianSeriesLimit v hA ω)‖ := by ring
      _ ≤ ‖x‖ + ‖T‖ * gaussianFastEnvelope hA ω := by
        gcongr
  change 1 + ‖x + Real.sqrt s • T (gaussianSeriesLimit v hA ω)‖ ≤ _
  have hprod : 0 ≤ (1 + ‖x‖) * gaussianFastEnvelope hA ω :=
    mul_nonneg (by positivity) henv
  nlinarith [norm_nonneg T, norm_nonneg x]

private theorem ae_gaussianSeriesHeatTrace_bound_unit {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [OpensMeasurableSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    (hsecond : ∀ y w, |secondDirectionalDerivative Φ y w| ≤
      C * (1 + ‖y‖) ^ d * ‖w‖ ^ 2) (x : E) :
    ∀ᵐ ω ∂standardGaussianInfinitePi, ∀ s ∈ Set.Icc 0 1,
      ‖gaussianSeriesHeatTrace hA T Φ x s ω‖ ≤
        (1 + gaussianFastEnvelope hA ω) ^ d *
          (C * (1 + ‖x‖ + ‖T‖) ^ d * ∑' j, ‖T (v j)‖ ^ 2) := by
  let B : ℝ := 1 + ‖x‖ + ‖T‖
  let S : ℝ := ∑' j, ‖T (v j)‖ ^ 2
  let P : (ℕ → ℝ) → ℝ := fun ω => (1 + gaussianFastEnvelope hA ω) ^ d
  let K : ℝ := C * B ^ d * S
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hS : 0 ≤ S := by dsimp [S]; exact tsum_nonneg fun _ => sq_nonneg _
  have hdir := summable_sq_norm_gaussianDirections hA T
  filter_upwards [ae_norm_gaussianSeriesLimit_le_fastEnvelope hA] with ω hω
  intro s hs
  let Y := gaussianSeriesHeatArgument hA T x s ω
  let q : ℝ := C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d
  have hq : 0 ≤ q := by
    dsimp [q]
    have he : 0 ≤ gaussianFastEnvelope hA ω := le_trans (norm_nonneg _) hω
    positivity
  have htrace := summable_gaussianSeriesHeatTrace hA T Φ ⟨C, hC, d, hsecond⟩ x s ω
  have hnorm := norm_tsum_le_tsum_norm htrace.norm
  have hmajor : Summable (fun j => q * ‖T (v j)‖ ^ 2) := hdir.mul_left q
  have hpoint (j : ℕ) :
      |secondDirectionalDerivative Φ Y (T (v j))| ≤ q * ‖T (v j)‖ ^ 2 := by
    calc
      |secondDirectionalDerivative Φ Y (T (v j))|
          ≤ C * (1 + ‖Y‖) ^ d * ‖T (v j)‖ ^ 2 := hsecond _ _
      _ ≤ q * ‖T (v j)‖ ^ 2 := by
        dsimp [q, Y]
        gcongr
        exact gaussianSeriesHeatArgument_bound_unit hA T x ω hω hs
  have htsum := htrace.abs.tsum_le_tsum hpoint hmajor
  calc
    ‖gaussianSeriesHeatTrace hA T Φ x s ω‖ ≤
        ∑' j, |secondDirectionalDerivative Φ Y (T (v j))| := by
          simpa [gaussianSeriesHeatTrace, Y, Real.norm_eq_abs] using hnorm
    _ ≤ ∑' j, q * ‖T (v j)‖ ^ 2 := htsum
    _ = P ω * K := by
      rw [hdir.tsum_mul_left]
      dsimp [P, K, S, B, q]
      rw [mul_pow]
      ring

/-- The heat average is continuous from the right at time zero. -/
theorem tendsto_gaussianSeriesHeatAverage_zero {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [OpensMeasurableSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (x : E) :
    Tendsto (gaussianSeriesHeatAverage hA T Φ x) (𝓝[>] 0)
      (𝓝 (∫ _ω : ℕ → ℝ, Φ x ∂standardGaussianInfinitePi)) := by
  rcases hΦ with ⟨hC2, C, hC, d, hvalue, hfirst, hsecond⟩
  let B : ℝ := 1 + ‖x‖ + ‖T‖
  let P : (ℕ → ℝ) → ℝ := fun ω => C * B ^ d * (1 + gaussianFastEnvelope hA ω) ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hPint : Integrable P standardGaussianInfinitePi := by
    simpa [P, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_fastEnvelope_polynomial hA d).mul_const (C * B ^ d)
  have hbound : ∀ᵐ ω ∂standardGaussianInfinitePi, ∀ s ∈ Set.Ioo 0 1,
      ‖Φ (x + Real.sqrt s • gaussianSeriesLimitE hA T ω)‖ ≤ P ω := by
    filter_upwards [ae_norm_gaussianSeriesLimit_le_fastEnvelope hA] with ω hω s hs
    let Y := x + Real.sqrt s • gaussianSeriesLimitE hA T ω
    have harg : 1 + ‖Y‖ ≤ B * (1 + gaussianFastEnvelope hA ω) := by
      have he : 0 ≤ gaussianFastEnvelope hA ω := le_trans (norm_nonneg _) hω
      have hz : ‖T (gaussianSeriesLimit v hA ω)‖ ≤
          ‖T‖ * gaussianFastEnvelope hA ω := by
        calc
          _ ≤ ‖T‖ * ‖gaussianSeriesLimit v hA ω‖ := T.le_opNorm _
          _ ≤ _ := mul_le_mul_of_nonneg_left hω (norm_nonneg _)
      have hsqrt : Real.sqrt s ≤ 1 := by
        calc
          Real.sqrt s ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (le_of_lt hs.2)
          _ = 1 := Real.sqrt_one
      have htri : ‖Y‖ ≤ ‖x‖ + ‖T‖ * gaussianFastEnvelope hA ω := by
        dsimp [Y, gaussianSeriesLimitE]
        calc
          _ ≤ ‖x‖ + ‖Real.sqrt s • T (gaussianSeriesLimit v hA ω)‖ := norm_add_le _ _
          _ = ‖x‖ + Real.sqrt s * ‖T (gaussianSeriesLimit v hA ω)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          _ ≤ ‖x‖ + 1 * ‖T (gaussianSeriesLimit v hA ω)‖ := by gcongr
          _ = ‖x‖ + ‖T (gaussianSeriesLimit v hA ω)‖ := by ring
          _ ≤ ‖x‖ + ‖T‖ * gaussianFastEnvelope hA ω := by
            gcongr
      have hprod : 0 ≤ (1 + ‖x‖) * gaussianFastEnvelope hA ω :=
        mul_nonneg (by positivity) he
      dsimp [B]
      nlinarith [norm_nonneg T, norm_nonneg x]
    have hval := hvalue Y
    change |Φ Y| ≤ P ω
    calc
      |Φ Y| ≤ C * (1 + ‖Y‖) ^ d := hval
      _ ≤ C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d := by gcongr
      _ = P ω := by dsimp [P, B]; rw [mul_pow]; ring
  have hmeas (s : ℝ) : AEStronglyMeasurable
      (fun ω => Φ (x + Real.sqrt s • gaussianSeriesLimitE hA T ω))
      standardGaussianInfinitePi := by
    have hG : Continuous (fun z : E => Φ (x + Real.sqrt s • z)) := by
      exact hC2.continuous.comp (continuous_const.add
        ((continuous_const : Continuous fun _ : E => Real.sqrt s).smul continuous_id))
    exact hG.comp_stronglyMeasurable
      (stronglyMeasurable_gaussianSeriesLimitE hA T) |>.aestronglyMeasurable
  have hlim : ∀ᵐ ω ∂standardGaussianInfinitePi, Tendsto
      (fun s => Φ (x + Real.sqrt s • gaussianSeriesLimitE hA T ω)) (𝓝[>] 0) (𝓝 (Φ x)) := by
    filter_upwards [] with ω
    have hsqrt0 : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [Real.sqrt_zero] using
        (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto
    have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      hsqrt0.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    have hpath : Tendsto (fun s => x + Real.sqrt s • gaussianSeriesLimitE hA T ω)
        (𝓝[>] 0) (𝓝 x) := by
      simpa using (tendsto_const_nhds.add (hsqrt.smul_const (gaussianSeriesLimitE hA T ω)))
    exact hC2.continuous.continuousAt.tendsto.comp hpath
  have hconv := tendsto_integral_filter_of_dominated_convergence P
    (Filter.Eventually.of_forall hmeas)
    (by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr
      filter_upwards [hbound] with ω hω
      exact hω r hr)
    hPint hlim
  have hfun : gaussianSeriesHeatAverage hA T Φ x = fun s =>
      ∫ ω, Φ (x + Real.sqrt s • gaussianSeriesLimitE hA T ω)
        ∂standardGaussianInfinitePi := by
    funext s
    rfl
  rw [hfun]
  exact hconv

/-- The expected Hessian trace is continuous from the right at time zero. -/
theorem tendsto_gaussianSeriesHeatTraceAverage_zero {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [OpensMeasurableSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (hGrowth : HasPolynomiallyBoundedSecondDirectionalDerivative Φ) (x : E) :
    Tendsto (fun t => gaussianSeriesHeatTraceAverage hA T Φ x t) (𝓝[>] 0)
      (𝓝 (gaussianSeriesHeatTraceAverage hA T Φ x 0)) := by
  rcases hGrowth with ⟨C, hC, d, hsecond⟩
  let H : ℕ → E := fun j => T (v j)
  let B : ℝ := 1 + ‖x‖ + ‖T‖
  let S : ℝ := ∑' j, ‖H j‖ ^ 2
  let P : (ℕ → ℝ) → ℝ := fun ω => (1 + gaussianFastEnvelope hA ω) ^ d
  let K : ℝ := C * B ^ d * S
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hdir : Summable (fun j => ‖H j‖ ^ 2) := summable_sq_norm_gaussianDirections hA T
  have hS : 0 ≤ S := by dsimp [S]; exact tsum_nonneg fun _ => sq_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hboundω := ae_gaussianSeriesHeatTrace_bound_unit hA T Φ C hC d hsecond x
  have hdomInt : Integrable (fun ω => P ω * K) standardGaussianInfinitePi := by
    simpa [P] using (integrable_fastEnvelope_polynomial hA d).mul_const K
  have hpoint : ∀ᵐ ω ∂standardGaussianInfinitePi,
      Tendsto (fun t => gaussianSeriesHeatTrace hA T Φ x t ω) (𝓝[>] 0)
        (𝓝 (gaussianSeriesHeatTrace hA T Φ x 0 ω)) := by
    filter_upwards [ae_norm_gaussianSeriesLimit_le_fastEnvelope hA] with ω hω
    let f : ℝ → ℕ → ℝ := fun t j =>
      secondDirectionalDerivative Φ
        (x + Real.sqrt t • T (gaussianSeriesLimit v hA ω)) (H j)
    let u : ℕ → ℝ := fun j =>
      C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d * ‖H j‖ ^ 2
    have hu : Summable u := by
      simpa [u, H] using hdir.mul_left (C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d)
    have hargcont : Continuous (fun t : ℝ =>
        x + Real.sqrt t • T (gaussianSeriesLimit v hA ω)) := by
      exact continuous_const.add (Real.continuous_sqrt.smul continuous_const)
    have hcont (j : ℕ) : Continuous (f · j) :=
      (continuous_secondDirectionalDerivative hΦ (H j)).comp hargcont
    have hlim (j : ℕ) : Tendsto (f · j) (𝓝[>] 0) (𝓝 (f 0 j)) :=
      (hcont j).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have henv : 0 ≤ gaussianFastEnvelope hA ω := le_trans (norm_nonneg _) hω
    have hBarg (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
        1 + ‖x + Real.sqrt t • T (gaussianSeriesLimit v hA ω)‖ ≤
          B * (1 + gaussianFastEnvelope hA ω) := by
      have harg := gaussianSeriesHeatArgument_bound_unit hA T x ω hω ht
      simpa [gaussianSeriesHeatArgument, gaussianSeriesLimitE, B] using harg
    have htermBound : ∀ᶠ t in 𝓝[>] 0, ∀ j, ‖f t j‖ ≤ u j := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht j
      dsimp [f, u, H]
      calc
        |secondDirectionalDerivative Φ
            (x + Real.sqrt t • T (gaussianSeriesLimit v hA ω)) (T (v j))|
          ≤ C * (1 + ‖x + Real.sqrt t • T (gaussianSeriesLimit v hA ω)‖) ^ d *
              ‖T (v j)‖ ^ 2 := hsecond _ _
        _ ≤ C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d * ‖T (v j)‖ ^ 2 := by
              gcongr
              exact hBarg t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have htsum := tendsto_tsum_of_dominated_convergence hu hlim htermBound
    simpa [f, gaussianSeriesHeatTrace, gaussianSeriesHeatArgument,
      gaussianSeriesLimitE, H] using htsum
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂standardGaussianInfinitePi,
      ‖gaussianSeriesHeatTrace hA T Φ x t ω‖ ≤ P ω * K := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    filter_upwards [hboundω] with ω hω
    simpa [P, K] using hω t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (gaussianSeriesHeatTrace hA T Φ x t) standardGaussianInfinitePi :=
    aestronglyMeasurable_gaussianSeriesHeatTrace hA T Φ hΦ ⟨C, hC, d, hsecond⟩ x t
  have hconv := tendsto_integral_filter_of_dominated_convergence (fun ω => P ω * K)
    (Filter.Eventually.of_forall hmeas) hbound hdomInt hpoint
  have hfun : gaussianSeriesHeatTraceAverage hA T Φ x = fun t =>
      ∫ ω, gaussianSeriesHeatTrace hA T Φ x t ω ∂standardGaussianInfinitePi := by
    funext t
    rfl
  rw [hfun]
  exact hconv

/-- The expected Hessian trace varies continuously at every positive heat time. The proof uses a
local polynomial envelope and dominated convergence first in the trace index, then in the Gaussian
variable. -/
theorem continuousAt_gaussianSeriesHeatTraceAverage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [OpensMeasurableSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (hGrowth : HasPolynomiallyBoundedSecondDirectionalDerivative Φ) (x : E)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ContinuousAt (gaussianSeriesHeatTraceAverage hA T Φ x) t₀ := by
  rcases hGrowth with ⟨C, hC, d, hsecond⟩
  let H : ℕ → E := fun j => T (v j)
  let M : ℝ := t₀ + 1
  let B : ℝ := 1 + ‖x‖ + Real.sqrt M * ‖T‖
  let S : ℝ := ∑' j, ‖H j‖ ^ 2
  let P : (ℕ → ℝ) → ℝ := fun ω => (1 + gaussianFastEnvelope hA ω) ^ d
  let K : ℝ := C * B ^ d * S
  have hM : 0 ≤ M := by dsimp [M]; linarith
  have htM : t₀ < M := by dsimp [M]; linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hdir : Summable (fun j => ‖H j‖ ^ 2) := summable_sq_norm_gaussianDirections hA T
  have hS : 0 ≤ S := by dsimp [S]; exact tsum_nonneg fun _ => sq_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hdomInt : Integrable (fun ω => P ω * K) standardGaussianInfinitePi := by
    simpa [P] using (integrable_fastEnvelope_polynomial hA d).mul_const K
  have hpoint : ∀ᵐ ω ∂standardGaussianInfinitePi,
      Tendsto (fun s => gaussianSeriesHeatTrace hA T Φ x s ω) (𝓝 t₀)
        (𝓝 (gaussianSeriesHeatTrace hA T Φ x t₀ ω)) := by
    filter_upwards [ae_norm_gaussianSeriesLimit_le_fastEnvelope hA] with ω hω
    let f : ℝ → ℕ → ℝ := fun s j =>
      secondDirectionalDerivative Φ
        (x + Real.sqrt s • T (gaussianSeriesLimit v hA ω)) (H j)
    let u : ℕ → ℝ := fun j =>
      C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d * ‖H j‖ ^ 2
    have hu : Summable u := by
      simpa [u, H] using
        hdir.mul_left (C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d)
    have hargBound (s : ℝ) (hs : s ≤ M) :
        1 + ‖x + Real.sqrt s • T (gaussianSeriesLimit v hA ω)‖ ≤
          B * (1 + gaussianFastEnvelope hA ω) := by
      have henv : 0 ≤ gaussianFastEnvelope hA ω := le_trans (norm_nonneg _) hω
      have hZ : ‖T (gaussianSeriesLimit v hA ω)‖ ≤
          ‖T‖ * gaussianFastEnvelope hA ω := by
        calc
          _ ≤ ‖T‖ * ‖gaussianSeriesLimit v hA ω‖ := T.le_opNorm _
          _ ≤ _ := mul_le_mul_of_nonneg_left hω (norm_nonneg _)
      have hsqrt : Real.sqrt s ≤ Real.sqrt M := Real.sqrt_le_sqrt hs
      have hsqrtZ : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
      have hsqrtM : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
      have hnorm :
          ‖x + Real.sqrt s • T (gaussianSeriesLimit v hA ω)‖ ≤
            ‖x‖ + Real.sqrt M * (‖T‖ * gaussianFastEnvelope hA ω) := by
        calc
          _ ≤ ‖x‖ + ‖Real.sqrt s • T (gaussianSeriesLimit v hA ω)‖ := norm_add_le _ _
          _ = ‖x‖ + Real.sqrt s * ‖T (gaussianSeriesLimit v hA ω)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqrtZ]
          _ ≤ ‖x‖ + Real.sqrt M * (‖T‖ * gaussianFastEnvelope hA ω) := by
            gcongr
      have hprod : 0 ≤ (1 + ‖x‖ + Real.sqrt M * ‖T‖) *
          gaussianFastEnvelope hA ω := by positivity
      dsimp [B]
      nlinarith [norm_nonneg x, mul_nonneg hsqrtM (norm_nonneg T), henv]
    have hargcont : Continuous (fun s : ℝ =>
        x + Real.sqrt s • T (gaussianSeriesLimit v hA ω)) := by
      exact continuous_const.add (Real.continuous_sqrt.smul continuous_const)
    have hcont (j : ℕ) : Continuous (f · j) :=
      (continuous_secondDirectionalDerivative hΦ (H j)).comp hargcont
    have hlim (j : ℕ) : Tendsto (f · j) (𝓝 t₀) (𝓝 (f t₀ j)) :=
      (hcont j).continuousAt.tendsto
    have htermBound : ∀ᶠ s in 𝓝 t₀, ∀ j, ‖f s j‖ ≤ u j := by
      filter_upwards [Iio_mem_nhds htM] with s hs j
      dsimp [f, u, H]
      calc
        |secondDirectionalDerivative Φ
            (x + Real.sqrt s • T (gaussianSeriesLimit v hA ω)) (T (v j))|
          ≤ C * (1 + ‖x + Real.sqrt s • T (gaussianSeriesLimit v hA ω)‖) ^ d *
              ‖T (v j)‖ ^ 2 := hsecond _ _
        _ ≤ C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d * ‖T (v j)‖ ^ 2 := by
              gcongr
              exact hargBound s (le_of_lt hs)
    have htsum := tendsto_tsum_of_dominated_convergence hu hlim htermBound
    simpa [f, gaussianSeriesHeatTrace, gaussianSeriesHeatArgument,
      gaussianSeriesLimitE, H] using htsum
  have hbound : ∀ᶠ s in 𝓝 t₀, ∀ᵐ ω ∂standardGaussianInfinitePi,
      ‖gaussianSeriesHeatTrace hA T Φ x s ω‖ ≤ P ω * K := by
    filter_upwards [Iio_mem_nhds htM] with s hs
    have harg := ae_gaussianFastArgument_growth_bound hA T x
      (M := M) (t := s) (le_of_lt hs)
    filter_upwards [harg] with ω hω
    let Y := gaussianSeriesHeatArgument hA T x s ω
    let q : ℝ := C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d
    have htrace := summable_gaussianSeriesHeatTrace hA T Φ ⟨C, hC, d, hsecond⟩ x s ω
    have hmajor : Summable (fun j => q * ‖H j‖ ^ 2) := by
      simpa [q, H] using hdir.mul_left q
    have hterm (j : ℕ) :
        |secondDirectionalDerivative Φ Y (H j)| ≤ q * ‖H j‖ ^ 2 := by
      calc
        |secondDirectionalDerivative Φ Y (H j)| ≤
            C * (1 + ‖Y‖) ^ d * ‖H j‖ ^ 2 := hsecond Y (H j)
        _ ≤ q * ‖H j‖ ^ 2 := by
          dsimp [q]
          gcongr
          exact hω.2
    have hnorm := norm_tsum_le_tsum_norm htrace.norm
    calc
      ‖gaussianSeriesHeatTrace hA T Φ x s ω‖ ≤
          ∑' j, |secondDirectionalDerivative Φ Y (H j)| := by
            simpa [gaussianSeriesHeatTrace, Y, Real.norm_eq_abs] using hnorm
      _ ≤ ∑' j, q * ‖H j‖ ^ 2 := htrace.abs.tsum_le_tsum hterm hmajor
      _ = P ω * K := by
        rw [hdir.tsum_mul_left]
        dsimp [P, K, S, q, B]
        rw [mul_pow]
        ring
  have hmeas (s : ℝ) : AEStronglyMeasurable
      (gaussianSeriesHeatTrace hA T Φ x s) standardGaussianInfinitePi :=
    aestronglyMeasurable_gaussianSeriesHeatTrace hA T Φ hΦ
      ⟨C, hC, d, hsecond⟩ x s
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (fun ω => P ω * K) (Filter.Eventually.of_forall hmeas) hbound hdomInt hpoint
  have hfun : gaussianSeriesHeatTraceAverage hA T Φ x = fun s =>
      ∫ ω, gaussianSeriesHeatTrace hA T Φ x s ω ∂standardGaussianInfinitePi := by
    funext s
    rfl
  rw [hfun]
  exact hconv

/-- The expected infinite Hessian trace is continuous on the nonnegative time axis, with the
endpoint understood from the right. -/
theorem continuousOn_gaussianSeriesHeatTraceAverage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [OpensMeasurableSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (hGrowth : HasPolynomiallyBoundedSecondDirectionalDerivative Φ) (x : E) :
    ContinuousOn (gaussianSeriesHeatTraceAverage hA T Φ x) (Ici 0) := by
  intro t ht
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · subst t
    have hzero := tendsto_gaussianSeriesHeatTraceAverage_zero hA T Φ hΦ hGrowth x
    have hright : ContinuousWithinAt (gaussianSeriesHeatTraceAverage hA T Φ x) (Ioi 0) 0 := by
      change Tendsto (gaussianSeriesHeatTraceAverage hA T Φ x) (𝓝[>] 0)
        (𝓝 (gaussianSeriesHeatTraceAverage hA T Φ x 0))
      exact hzero
    exact (continuousWithinAt_Ioi_iff_Ici).mp hright
  · exact (continuousAt_gaussianSeriesHeatTraceAverage hA T Φ hΦ hGrowth x htpos).continuousWithinAt

/-- The heat average has its expected one-sided derivative at time zero. -/
theorem hasDerivWithinAt_gaussianSeriesHeatAverage_zero {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [OpensMeasurableSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (x : E) :
    HasDerivWithinAt (gaussianSeriesHeatAverage hA T Φ x)
      ((1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA T Φ x 0) (Ici 0) 0 := by
  let hGrowth := hasPolynomiallyBoundedSecondDirectionalDerivative_of_C2Derivatives hΦ
  have hdiff : DifferentiableOn ℝ (gaussianSeriesHeatAverage hA T Φ x) (Ioi 0) := by
    intro t ht
    exact (hasDerivAt_gaussianSeriesHeatAverage hA T Φ hΦ x ht).differentiableAt.differentiableWithinAt
  have hcont := tendsto_gaussianSeriesHeatAverage_zero hA T Φ hΦ x
  have hcont' : ContinuousWithinAt (gaussianSeriesHeatAverage hA T Φ x) (Ici 0) 0 := by
    have hzero : gaussianSeriesHeatAverage hA T Φ x 0 =
        ∫ _ω : (ℕ → ℝ), Φ x ∂standardGaussianInfinitePi := by
      simp [gaussianSeriesHeatAverage, gaussianSeriesHeatArgument]
    have hright : ContinuousWithinAt (gaussianSeriesHeatAverage hA T Φ x) (Ioi 0) 0 := by
      change Tendsto (gaussianSeriesHeatAverage hA T Φ x) (𝓝[>] 0)
        (𝓝 (gaussianSeriesHeatAverage hA T Φ x 0))
      rw [hzero]
      exact hcont
    exact (continuousWithinAt_Ioi_iff_Ici).mp hright
  have hderivlim := tendsto_gaussianSeriesHeatTraceAverage_zero hA T Φ hΦ.1 hGrowth x
  have hderivlim' : Tendsto (fun t => deriv (gaussianSeriesHeatAverage hA T Φ x) t)
      (𝓝[>] 0) (𝓝 ((1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA T Φ x 0)) := by
    have hEq : ∀ᶠ t in 𝓝[>] 0,
        deriv (gaussianSeriesHeatAverage hA T Φ x) t =
          (1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA T Φ x t := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hasDerivAt_gaussianSeriesHeatAverage hA T Φ hΦ x ht).deriv
    exact (tendsto_const_nhds.mul hderivlim).congr' (hEq.mono fun _ ht => ht.symm)
  exact hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
    ((continuousWithinAt_Ioi_iff_Ici).mpr hcont')
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0) hderivlim'

/-- The heat average is continuous on the nonnegative time axis. -/
theorem continuousOn_gaussianSeriesHeatAverage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [OpensMeasurableSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (x : E) :
    ContinuousOn (gaussianSeriesHeatAverage hA T Φ x) (Ici 0) := by
  intro t ht
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · subst t
    have hzero := tendsto_gaussianSeriesHeatAverage_zero hA T Φ hΦ x
    have hzeroVal : gaussianSeriesHeatAverage hA T Φ x 0 =
        ∫ _ω : (ℕ → ℝ), Φ x ∂standardGaussianInfinitePi := by
      simp [gaussianSeriesHeatAverage, gaussianSeriesHeatArgument]
    have hright : ContinuousWithinAt (gaussianSeriesHeatAverage hA T Φ x) (Ioi 0) 0 := by
      change Tendsto (gaussianSeriesHeatAverage hA T Φ x) (𝓝[>] 0)
        (𝓝 (gaussianSeriesHeatAverage hA T Φ x 0))
      rw [hzeroVal]
      exact hzero
    exact (continuousWithinAt_Ioi_iff_Ici).mp hright
  · exact (hasDerivAt_gaussianSeriesHeatAverage hA T Φ hΦ x htpos).continuousAt.continuousWithinAt

/-- The derivative in the infinite-rank heat identity is continuous on the nonnegative time
axis, with its endpoint value interpreted from the right. -/
theorem continuousOn_gaussianSeriesHeatDerivative {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [OpensMeasurableSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (hGrowth : HasPolynomiallyBoundedSecondDirectionalDerivative Φ) (x : E) :
    ContinuousOn (fun t => (1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA T Φ x t)
      (Ici 0) :=
  continuousOn_const.mul (continuousOn_gaussianSeriesHeatTraceAverage hA T Φ hΦ hGrowth x)

/-- The heat average and its displayed derivative are continuous on `[0,∞)`, and the derivative
formula holds at positive times and one-sided at zero. -/
theorem c1On_gaussianSeriesHeatAverage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [OpensMeasurableSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (x : E) :
    ContinuousOn (gaussianSeriesHeatAverage hA T Φ x) (Ici 0) ∧
    ContinuousOn (fun t => (1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA T Φ x t) (Ici 0) ∧
    (∀ t ∈ Ioi 0, HasDerivAt (gaussianSeriesHeatAverage hA T Φ x)
      ((1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA T Φ x t) t) ∧
    HasDerivWithinAt (gaussianSeriesHeatAverage hA T Φ x)
      ((1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA T Φ x 0) (Ici 0) 0 := by
  refine ⟨continuousOn_gaussianSeriesHeatAverage hA T Φ hΦ x,
    continuousOn_gaussianSeriesHeatDerivative hA T Φ hΦ.1
      (hasPolynomiallyBoundedSecondDirectionalDerivative_of_C2Derivatives hΦ) x,
    ?_, hasDerivWithinAt_gaussianSeriesHeatAverage_zero hA T Φ hΦ x⟩
  intro t ht
  exact hasDerivAt_gaussianSeriesHeatAverage hA T Φ hΦ x ht

end ASDExplicitGamma.Gaussian

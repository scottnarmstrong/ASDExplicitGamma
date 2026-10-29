/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaPointwise
public import ASDExplicitGamma.Native.HeatRefinedObserverInverse
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNorms
public import ASDExplicitGamma.Native.HeatVHEATRefinedDriftAssembly
public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaSourceRows
public import ASDExplicitGamma.Native.HeatRemainderControlErrorIntegrals

/-! Expectation of the source-compatible fixed-theta VHEAT bracket. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory Homogenization Gaussian
open ASDExplicitGamma.Numerics.Native Algsuperdiff.Section3
open scoped ENNReal NNReal BigOperators
noncomputable section

private theorem heatVHEATThetaJNonneg
    (ε X F : ℝ) (hε : 0 ≤ ε) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (j l : ℕ) : 0 ≤ nativeHeatVHEATJ ε X F 20 j l := by
  unfold nativeHeatVHEATJ
  split_ifs with hlt
  · exact mul_nonneg (pow_nonneg hε _) (pow_nonneg hX _)
  · exact mul_nonneg
      (mul_nonneg (pow_nonneg hε _) (pow_nonneg hX _))
      (Real.rpow_nonneg (div_nonneg hF hX) _)

private theorem heatVHEATThetaRareMixedIntegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R A T : Ω → ℝ)
    (hR : AEStronglyMeasurable R μ) (hA : AEStronglyMeasurable A μ)
    (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω, 0 ≤ R ω) (hA0 : ∀ ω, 0 ≤ A ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (ε X F : ℝ) (hε : 0 ≤ ε) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hA20 : eLpNorm A 20 μ ≤ ENNReal.ofReal X)
    (hT20 : eLpNorm T 20 μ ≤ ENNReal.ofReal X)
    (hA128 : eLpNorm A 128 μ ≤ ENNReal.ofReal F)
    (hT128 : eLpNorm T 128 μ ≤ ENNReal.ofReal F)
    (j a b : ℕ) (hj : j ≤ 2) (hab : a + b ≤ 20) (hb : 1 ≤ b) :
    Integrable (fun ω => R ω ^ j * (A ω ^ a * T ω ^ b)) μ ∧
      (∫ ω, R ω ^ j * (A ω ^ a * T ω ^ b) ∂μ) ≤
        nativeHeatVHEATJ ε X F 20 j (a + b) := by
  by_cases hXpos : 0 < X
  · exact nativeHeat_correlated_rare_mixed_product_le_J μ R A T hR hA hT
      hR0 hA0 hT0 ε X F hε hXpos hF hR128 hA20 hT20 hA128 hT128
      j a b hj hab
  · have hXzero : X = 0 := le_antisymm (le_of_not_gt hXpos) hX
    subst X
    have hTzero : T =ᵐ[μ] 0 :=
      (eLpNorm_eq_zero_iff (by norm_num : (20 : ℝ≥0∞) ≠ 0)).mp
        (le_antisymm (by simpa only [ENNReal.ofReal_zero] using hT20) bot_le)
    have hzero : (fun ω => R ω ^ j * (A ω ^ a * T ω ^ b)) =ᵐ[μ] 0 := by
      filter_upwards [hTzero] with ω hω
      simp [hω, Nat.ne_of_gt (by omega : 0 < b)]
    refine ⟨(integrable_const (0 : ℝ)).congr hzero.symm, ?_⟩
    rw [integral_congr_ae hzero]
    simp only [Pi.zero_apply, integral_zero]
    exact heatVHEATThetaJNonneg ε 0 F hε le_rfl hF j (a + b)

private theorem heatVHEATThetaRareQuadraticIntegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R A T : Ω → ℝ)
    (hR : AEStronglyMeasurable R μ) (hA : AEStronglyMeasurable A μ)
    (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω, 0 ≤ R ω) (hA0 : ∀ ω, 0 ≤ A ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (ε X F : ℝ) (hε : 0 ≤ ε) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hA20 : eLpNorm A 20 μ ≤ ENNReal.ofReal X)
    (hT20 : eLpNorm T 20 μ ≤ ENNReal.ofReal X)
    (hA128 : eLpNorm A 128 μ ≤ ENNReal.ofReal F)
    (hT128 : eLpNorm T 128 μ ≤ ENNReal.ofReal F)
    (j a : ℕ) (hj : j ≤ 2) (ha : a + 2 ≤ 20) :
    Integrable (fun ω => R ω ^ j * (A ω ^ a * (T ω * (T ω + 4)))) μ ∧
      (∫ ω, R ω ^ j * (A ω ^ a * (T ω * (T ω + 4))) ∂μ) ≤
        4 * nativeHeatVHEATJ ε X F 20 j (a + 1) +
          nativeHeatVHEATJ ε X F 20 j (a + 2) := by
  have h1 := heatVHEATThetaRareMixedIntegral μ R A T hR hA hT hR0 hA0 hT0
    ε X F hε hX hF hR128 hA20 hT20 hA128 hT128 j a 1 hj (by omega) (by norm_num)
  have h2 := heatVHEATThetaRareMixedIntegral μ R A T hR hA hT hR0 hA0 hT0
    ε X F hε hX hF hR128 hA20 hT20 hA128 hT128 j a 2 hj ha (by norm_num)
  have he : (fun ω => R ω ^ j * (A ω ^ a * (T ω * (T ω + 4)))) =
      (fun ω => 4 * (R ω ^ j * (A ω ^ a * T ω)) +
        R ω ^ j * (A ω ^ a * T ω ^ 2)) := by
    funext ω
    ring
  let fPow := fun ω => 4 * (R ω ^ j * (A ω ^ a * T ω ^ 1)) +
    R ω ^ j * (A ω ^ a * T ω ^ 2)
  let fNorm := fun ω => 4 * (R ω ^ j * (A ω ^ a * T ω)) +
    R ω ^ j * (A ω ^ a * T ω ^ 2)
  have hIntPow : Integrable fPow μ := by
    exact (h1.1.const_mul 4).add h2.1
  have hEq : fPow =ᵐ[μ] fNorm := by
    filter_upwards [] with ω
    simp [fPow, fNorm]
  have hIntNorm : Integrable fNorm μ := hIntPow.congr hEq
  refine ⟨he.symm ▸ hIntNorm, ?_⟩
  rw [he]
  calc
    (∫ ω, fNorm ω ∂μ) = ∫ ω, fPow ω ∂μ := integral_congr_ae hEq.symm
    _ = 4 * (∫ ω, R ω ^ j * (A ω ^ a * T ω ^ 1) ∂μ) +
        ∫ ω, R ω ^ j * (A ω ^ a * T ω ^ 2) ∂μ := by
      rw [integral_add (h1.1.const_mul 4) h2.1, integral_const_mul]
    _ ≤ 4 * nativeHeatVHEATJ ε X F 20 j (a + 1) +
        nativeHeatVHEATJ ε X F 20 j (a + 2) :=
      add_le_add (mul_le_mul_of_nonneg_left h1.2 (by norm_num)) h2.2

theorem heatVHEATThetaBracketAverages
    {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset I) (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1)
    (R T : I → Ω → ℝ) (A : Ω → ℝ)
    (hR : ∀ i ∈ s, AEStronglyMeasurable (R i) μ)
    (hT : ∀ i ∈ s, AEStronglyMeasurable (T i) μ)
    (hA : AEStronglyMeasurable A μ)
    (hR0 : ∀ i ∈ s, ∀ ω, 0 ≤ R i ω)
    (hT0 : ∀ i ∈ s, ∀ ω, 0 ≤ T i ω)
    (hA0 : ∀ ω, 0 ≤ A ω)
    (havg : ∀ ω, A ω = ∑ i ∈ s, w i * T i ω)
    (ε X Y F b : ℝ) (hε : 0 ≤ ε) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hF : 0 ≤ F) (hb : 0 ≤ b)
    (hR128 : ∀ i ∈ s, eLpNorm (R i) 128 μ ≤ ENNReal.ofReal ε)
    (hA20 : eLpNorm A 20 μ ≤ ENNReal.ofReal Y)
    (hAX20 : eLpNorm A 20 μ ≤ ENNReal.ofReal X)
    (hT20 : ∀ i ∈ s, eLpNorm (T i) 20 μ ≤ ENNReal.ofReal X)
    (hA128 : eLpNorm A 128 μ ≤ ENNReal.ofReal F)
    (hT128 : ∀ i ∈ s, eLpNorm (T i) 128 μ ≤ ENNReal.ofReal F)
    (a : ℕ) (ha : a + 2 ≤ 20) :
    Integrable (fun ω => A ω ^ a *
      (∑ i ∈ s, w i * ((b + R i ω) ^ 2 * T i ω * (T i ω + 4)))) μ ∧
      (∫ ω, A ω ^ a *
        (∑ i ∈ s, w i * ((b + R i ω) ^ 2 * T i ω * (T i ω + 4))) ∂μ) ≤
        b ^ 2 * Y ^ a * (4 * X + X ^ 2) +
          2 * b * (4 * nativeHeatVHEATJ ε X F 20 1 (a + 1) +
            nativeHeatVHEATJ ε X F 20 1 (a + 2)) +
          4 * nativeHeatVHEATJ ε X F 20 2 (a + 1) +
            nativeHeatVHEATJ ε X F 20 2 (a + 2) ∧
    Integrable (fun ω => A ω ^ a *
      (∑ i ∈ s, w i * ((b + R i ω) * T i ω))) μ ∧
      (∫ ω, A ω ^ a *
        (∑ i ∈ s, w i * ((b + R i ω) * T i ω)) ∂μ) ≤
        b * (∫ ω, A ω ^ (a + 1) ∂μ) +
          nativeHeatVHEATJ ε X F 20 1 (a + 1) := by
  classical
  have hbounded (i : I) (hi : i ∈ s) :=
    nativeHeat_bounded_quadratic_error_integral μ A (T i) hA (hT i hi)
      hA0 (hT0 i hi) Y X hY hX hA20 (hT20 i hi) a ha
  have hrare1 (i : I) (hi : i ∈ s) :=
    heatVHEATThetaRareQuadraticIntegral μ (R i) A (T i)
      (hR i hi) hA (hT i hi) (hR0 i hi) hA0 (hT0 i hi)
      ε X F hε hX hF (hR128 i hi) hAX20 (hT20 i hi)
      hA128 (hT128 i hi) 1 a (by norm_num) ha
  have hrare2 (i : I) (hi : i ∈ s) :=
    heatVHEATThetaRareQuadraticIntegral μ (R i) A (T i)
      (hR i hi) hA (hT i hi) (hR0 i hi) hA0 (hT0 i hi)
      ε X F hε hX hF (hR128 i hi) hAX20 (hT20 i hi)
      hA128 (hT128 i hi) 2 a (by norm_num) ha
  let G (i : I) (ω : Ω) := A ω ^ a *
    ((b + R i ω) ^ 2 * T i ω * (T i ω + 4))
  have hGdecomp (i : I) (ω : Ω) :
      G i ω = b ^ 2 * (A ω ^ a * (T i ω * (T i ω + 4))) +
        2 * b * (R i ω * (A ω ^ a * (T i ω * (T i ω + 4)))) +
        R i ω ^ 2 * (A ω ^ a * (T i ω * (T i ω + 4))) := by
    dsimp [G]
    ring
  have hGint (i : I) (hi : i ∈ s) : Integrable (G i) μ := by
    have h1 := (hbounded i hi).1.const_mul (b ^ 2)
    have h2raw := (hrare1 i hi).1.const_mul (2 * b)
    have h2 : Integrable (fun ω => 2 * b *
        (R i ω * (A ω ^ a * (T i ω * (T i ω + 4))))) μ := by
      simpa only [pow_one] using h2raw
    have h3 := hrare2 i hi |>.1
    have hsum := h1.add (h2.add h3)
    have heq : (fun ω => b ^ 2 * (A ω ^ a * (T i ω * (T i ω + 4))) +
        (2 * b * (R i ω * (A ω ^ a * (T i ω * (T i ω + 4)))) +
        R i ω ^ 2 * (A ω ^ a * (T i ω * (T i ω + 4))))) = G i := by
      funext ω
      rw [hGdecomp]
      ring
    exact hsum.congr (Filter.Eventually.of_forall (fun ω => congrFun heq ω))
  have hGsumInt : Integrable
      (fun ω => ∑ i ∈ s, w i * G i ω) μ :=
    integrable_finsetSum s (fun i hi => (hGint i hi).const_mul (w i))
  have hSourceFun : (fun ω => A ω ^ a *
      (∑ i ∈ s, w i * ((b + R i ω) ^ 2 * T i ω * (T i ω + 4)))) =
      (fun ω => ∑ i ∈ s, w i * G i ω) := by
    funext ω
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [G]
    ring
  have hSourceInt : Integrable
      (fun ω => A ω ^ a *
        (∑ i ∈ s, w i * ((b + R i ω) ^ 2 * T i ω * (T i ω + 4)))) μ := by
    exact hGsumInt.congr
      (Filter.Eventually.of_forall (fun ω => congrFun hSourceFun.symm ω))
  have hGbound (i : I) (hi : i ∈ s) :
      (∫ ω, G i ω ∂μ) ≤
        b ^ 2 * Y ^ a * (4 * X + X ^ 2) +
          2 * b * (4 * nativeHeatVHEATJ ε X F 20 1 (a + 1) +
            nativeHeatVHEATJ ε X F 20 1 (a + 2)) +
          4 * nativeHeatVHEATJ ε X F 20 2 (a + 1) +
            nativeHeatVHEATJ ε X F 20 2 (a + 2) := by
    have hGdecompFun : G i = fun ω =>
        b ^ 2 * (A ω ^ a * (T i ω * (T i ω + 4))) +
          (2 * b * (R i ω * (A ω ^ a * (T i ω * (T i ω + 4)))) +
          R i ω ^ 2 * (A ω ^ a * (T i ω * (T i ω + 4)))) := by
      funext ω
      rw [hGdecomp]
      ring
    rw [hGdecompFun]
    have h1 := (hbounded i hi).1.const_mul (b ^ 2)
    have h2raw := (hrare1 i hi).1.const_mul (2 * b)
    have h2 : Integrable (fun ω => 2 * b *
        (R i ω * (A ω ^ a * (T i ω * (T i ω + 4))))) μ := by
      simpa only [pow_one] using h2raw
    have h3 := (hrare2 i hi).1
    let f1 : Ω → ℝ := fun ω => b ^ 2 * (A ω ^ a * (T i ω * (T i ω + 4)))
    let f2 : Ω → ℝ := fun ω => 2 * b * (R i ω * (A ω ^ a * (T i ω * (T i ω + 4))))
    let f3 : Ω → ℝ := fun ω => R i ω ^ 2 * (A ω ^ a * (T i ω * (T i ω + 4)))
    change (∫ ω, f1 ω + (f2 ω + f3 ω) ∂μ) ≤ _
    have hSplit : (∫ ω, f1 ω + (f2 ω + f3 ω) ∂μ) =
        b ^ 2 * (∫ ω, A ω ^ a * (T i ω * (T i ω + 4)) ∂μ) +
          (2 * b * (∫ ω, R i ω * (A ω ^ a * (T i ω * (T i ω + 4))) ∂μ) +
            ∫ ω, R i ω ^ 2 * (A ω ^ a * (T i ω * (T i ω + 4))) ∂μ) := by
      calc
        _ = ∫ ω, (f1 + (f2 + f3)) ω ∂μ := rfl
        _ = (∫ ω, f1 ω ∂μ) + ∫ ω, (f2 + f3) ω ∂μ :=
          integral_add h1 (h2.add h3)
        _ = (∫ ω, f1 ω ∂μ) +
            ((∫ ω, f2 ω ∂μ) + ∫ ω, f3 ω ∂μ) := by
              congr 1
              exact integral_add h2 h3
        _ = _ := by
          dsimp [f1, f2, f3]
          rw [integral_const_mul, integral_const_mul]
    rw [hSplit]
    have hb2 : 0 ≤ b ^ 2 := sq_nonneg _
    have h2b : 0 ≤ 2 * b := by positivity
    calc
      _ ≤ b ^ 2 * (Y ^ a * (4 * X + X ^ 2)) +
          2 * b * (4 * nativeHeatVHEATJ ε X F 20 1 (a + 1) +
            nativeHeatVHEATJ ε X F 20 1 (a + 2)) +
          4 * nativeHeatVHEATJ ε X F 20 2 (a + 1) +
            nativeHeatVHEATJ ε X F 20 2 (a + 2) := by
        have hh1 := mul_le_mul_of_nonneg_left (hbounded i hi).2 hb2
        have hh2raw := mul_le_mul_of_nonneg_left (hrare1 i hi).2 h2b
        have hh2 : 2 * b *
            (∫ ω, R i ω * (A ω ^ a * (T i ω * (T i ω + 4))) ∂μ) ≤
            2 * b * (4 * nativeHeatVHEATJ ε X F 20 1 (a + 1) +
              nativeHeatVHEATJ ε X F 20 1 (a + 2)) := by
          simpa only [pow_one] using hh2raw
        have hh3 := (hrare2 i hi).2
        nlinarith
      _ = _ := by ring
  have hSourceBound :
      (∫ ω, A ω ^ a *
        (∑ i ∈ s, w i * ((b + R i ω) ^ 2 * T i ω * (T i ω + 4))) ∂μ) ≤
        b ^ 2 * Y ^ a * (4 * X + X ^ 2) +
          2 * b * (4 * nativeHeatVHEATJ ε X F 20 1 (a + 1) +
            nativeHeatVHEATJ ε X F 20 1 (a + 2)) +
          4 * nativeHeatVHEATJ ε X F 20 2 (a + 1) +
            nativeHeatVHEATJ ε X F 20 2 (a + 2) := by
    rw [hSourceFun, integral_finsetSum s (fun i hi => (hGint i hi).const_mul (w i))]
    simp_rw [integral_const_mul]
    calc
      _ ≤ ∑ i ∈ s, w i *
          (b ^ 2 * Y ^ a * (4 * X + X ^ 2) +
            2 * b * (4 * nativeHeatVHEATJ ε X F 20 1 (a + 1) +
              nativeHeatVHEATJ ε X F 20 1 (a + 2)) +
            4 * nativeHeatVHEATJ ε X F 20 2 (a + 1) +
              nativeHeatVHEATJ ε X F 20 2 (a + 2)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hGbound i hi) (hw i hi)
      _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]
  have hTsum : ∀ ω, A ω = ∑ i ∈ s, w i * T i ω := havg
  let H (ω : Ω) := ∑ i ∈ s, w i * ((b + R i ω) * T i ω)
  have hHidentity (ω : Ω) : H ω = b * A ω + ∑ i ∈ s, w i * (R i ω * T i ω) := by
    dsimp [H]
    calc
      (∑ i ∈ s, w i * ((b + R i ω) * T i ω)) =
          ∑ i ∈ s, (b * (w i * T i ω) + w i * (R i ω * T i ω)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i ∈ s, b * (w i * T i ω)) +
          ∑ i ∈ s, w i * (R i ω * T i ω) := by rw [Finset.sum_add_distrib]
      _ = b * (∑ i ∈ s, w i * T i ω) +
          ∑ i ∈ s, w i * (R i ω * T i ω) := by rw [← Finset.mul_sum]
      _ = b * A ω + ∑ i ∈ s, w i * (R i ω * T i ω) := by rw [hTsum ω]
  have hAPowInt : Integrable (fun ω => A ω ^ (a + 1)) μ := by
    simpa only [pow_zero, mul_one] using
      (nativeHeat_trace_mixed_product μ A A hA hA hA0 hA0 Y Y hY hY
        hA20 hA20 (a + 1) 0 (by omega)).1
  have hRareClock (i : I) (hi : i ∈ s) :=
    show Integrable (fun ω => R i ω * (A ω ^ a * T i ω)) μ ∧
        (∫ ω, R i ω * (A ω ^ a * T i ω) ∂μ) ≤
          nativeHeatVHEATJ ε X F 20 1 (a + 1) from by
      simpa only [pow_one] using
        (heatVHEATThetaRareMixedIntegral μ (R i) A (T i)
          (hR i hi) hA (hT i hi) (hR0 i hi) hA0 (hT0 i hi)
          ε X F hε hX hF (hR128 i hi) hAX20 (hT20 i hi)
          hA128 (hT128 i hi) 1 a 1 (by norm_num) (by omega) (by norm_num))
  have hClockSumInt : Integrable
      (fun ω => ∑ i ∈ s, w i * (R i ω * (A ω ^ a * T i ω))) μ :=
    integrable_finsetSum s (fun i hi => (hRareClock i hi).1.const_mul (w i))
  have hClockFun : (fun ω => A ω ^ a * H ω) =
      (fun ω => b * A ω ^ (a + 1) +
        ∑ i ∈ s, w i * (R i ω * (A ω ^ a * T i ω))) := by
    funext ω
    rw [hHidentity ω]
    rw [mul_add]
    congr 1
    · calc
        A ω ^ a * (b * A ω) = b * (A ω ^ a * A ω) := by ring
        _ = b * A ω ^ (a + 1) := by rw [← pow_succ]
    · calc
        A ω ^ a * (∑ i ∈ s, w i * (R i ω * T i ω)) =
            ∑ i ∈ s, A ω ^ a * (w i * (R i ω * T i ω)) := by rw [Finset.mul_sum]
        _ = ∑ i ∈ s, w i * (R i ω * (A ω ^ a * T i ω)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
  have hClockInt : Integrable (fun ω => A ω ^ a * H ω) μ := by
    rw [hClockFun]
    exact (hAPowInt.const_mul b).add hClockSumInt
  have hClockBound :
      (∫ ω, A ω ^ a * H ω ∂μ) ≤
        b * (∫ ω, A ω ^ (a + 1) ∂μ) +
          nativeHeatVHEATJ ε X F 20 1 (a + 1) := by
    rw [hClockFun, integral_add (hAPowInt.const_mul b) hClockSumInt,
      integral_const_mul, integral_finsetSum s
        (fun i hi => (hRareClock i hi).1.const_mul (w i))]
    simp_rw [integral_const_mul]
    calc
      _ ≤ b * (∫ ω, A ω ^ (a + 1) ∂μ) +
          ∑ i ∈ s, w i * nativeHeatVHEATJ ε X F 20 1 (a + 1) := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hRareClock i hi).2 (hw i hi)
      _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]
  exact ⟨hSourceInt, hSourceBound, hClockInt, hClockBound⟩

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Main.EnvelopeHControlComparison

/-! Refined source-mesh caps with the geometric decay `r = 3^(-s)` retained. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Model ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  Algsuperdiff.Section3 MeasureTheory

/-- The raw trace remainder coefficients at `ρ = δ = r ≤ 1/729` are linear/quadratic in `r`. -/
theorem raw_trace_caps_decay (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 729) :
    rawTraceRemainderA r r ≤ 37 / 2 * r ∧ 0 ≤ rawTraceRemainderA r r ∧
    rawTraceRemainderB r r ≤ 147 / 10 * r ∧ 0 ≤ rawTraceRemainderB r r ∧
    rawTraceRemainderKappaF r r ≤ 46 * r ^ 2 ∧ 0 ≤ rawTraceRemainderKappaF r r ∧
    rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
      (rawTraceRemainderA r r) (rawTraceRemainderB r r) ≤ 1600 * r ^ 2 ∧
    0 ≤ rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
      (rawTraceRemainderA r r) (rawTraceRemainderB r r) := by
  have hsqrtA0 : Real.sqrt (78 / 10 : ℝ) ≤ 14 / 5 :=
    (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrtA1 : Real.sqrt (156 / 5 : ℝ) ≤ 28 / 5 :=
    (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrtA2 : Real.sqrt (46488 / 25 : ℝ) ≤ 44 :=
    (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrtB1 : Real.sqrt (78 / 5 : ℝ) ≤ 4 :=
    (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrtB2 : Real.sqrt (23244 / 25 : ℝ) ≤ 31 :=
    (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hr2 : r ^ 2 ≤ r / 729 := by nlinarith
  have hA : rawTraceRemainderA r r ≤ 37 / 2 * r := by
    unfold rawTraceRemainderA
    have h1 : 1.860 * Real.sqrt (78 / 10 : ℝ) * r ≤ 1.860 * (14 / 5) * r := by gcongr
    have h2 : 2.36412 * Real.sqrt (156 / 5 : ℝ) * r ≤ 2.36412 * (28 / 5) * r := by gcongr
    have h3 : 0.52288 * Real.sqrt (46488 / 25 : ℝ) * r ^ 2 ≤ 0.52288 * 44 * (r / 729) := by
      calc _ ≤ 0.52288 * 44 * r ^ 2 := by gcongr
        _ ≤ _ := by gcongr
    linarith
  have hB : rawTraceRemainderB r r ≤ 147 / 10 * r := by
    unfold rawTraceRemainderB
    have h1 : 1.860 * Real.sqrt (78 / 10 : ℝ) * r ≤ 1.860 * (14 / 5) * r := by gcongr
    have h2 : 2.36412 * Real.sqrt (78 / 5 : ℝ) * r ≤ 2.36412 * 4 * r := by gcongr
    have h3 : 0.52288 * Real.sqrt (23244 / 25 : ℝ) * r ^ 2 ≤ 0.52288 * 31 * (r / 729) := by
      calc _ ≤ 0.52288 * 31 * r ^ 2 := by gcongr
        _ ≤ _ := by gcongr
    linarith
  have hA0 : 0 ≤ rawTraceRemainderA r r := by unfold rawTraceRemainderA; positivity
  have hB0 : 0 ≤ rawTraceRemainderB r r := by unfold rawTraceRemainderB; positivity
  have hsqrt2 : 7 / 5 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt2u : Real.sqrt 2 ≤ 3 / 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hκ : rawTraceRemainderKappaF r r ≤ 46 * r ^ 2 := by
    unfold rawTraceRemainderKappaF
    have hc : (78 / 5 : ℝ) / Real.sqrt 2 ≤ 78 / 7 := by
      apply (div_le_iff₀ (by positivity : 0 < Real.sqrt 2)).2
      nlinarith
    have h2 : 2.36412 * ((78 / 5 : ℝ) / Real.sqrt 2) * (r * r) ≤ 2.36412 * (78 / 7) * (r * r) := by
      gcongr
    have h3 : 0.52288 * Real.sqrt 2 * (78 / 5 : ℝ) * r ^ 2 ≤ 0.52288 * (3 / 2) * (78 / 5) * r ^ 2 := by
      gcongr
    nlinarith [sq_nonneg r]
  have hκ0 : 0 ≤ rawTraceRemainderKappaF r r := by unfold rawTraceRemainderKappaF; positivity
  have hH0 : rawTraceRemainderH0 ≤ 12 / 5 := by norm_num [rawTraceRemainderH0]
  have hH00 : 0 ≤ rawTraceRemainderH0 := by norm_num [rawTraceRemainderH0]
  have hsqrtH0 : Real.sqrt rawTraceRemainderH0 ≤ 8 / 5 :=
    (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num [rawTraceRemainderH0]⟩
  have hD0 : rawTraceRemainderD0 ≤ 4 := by
    unfold rawTraceRemainderD0; nlinarith [hsqrtH0]
  have hD00 : 0 ≤ rawTraceRemainderD0 := by
    unfold rawTraceRemainderD0
    exact add_nonneg hH00 (Real.sqrt_nonneg _)
  have hAs : rawTraceRemainderA r r ^ 2 ≤ (37 / 2 * r) ^ 2 := pow_le_pow_left₀ hA0 hA 2
  have hBs : rawTraceRemainderB r r ^ 2 ≤ (147 / 10 * r) ^ 2 := pow_le_pow_left₀ hB0 hB 2
  have hμ : rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
      (rawTraceRemainderA r r) (rawTraceRemainderB r r) ≤ 1600 * r ^ 2 := by
    unfold rawTraceRemainderMu
    set A := rawTraceRemainderA r r
    set B := rawTraceRemainderB r r
    have hA4 : A ^ 4 ≤ (37 / 2 * r) ^ 4 := pow_le_pow_left₀ hA0 hA 4
    have hH2 : rawTraceRemainderH0 ^ 2 ≤ (12 / 5) ^ 2 := pow_le_pow_left₀ hH00 hH0 2
    have hD2 : rawTraceRemainderD0 ^ 2 ≤ 4 ^ 2 := pow_le_pow_left₀ hD00 hD0 2
    have hfirst : rawTraceRemainderH0 ^ 2 * A ^ 4 ≤ (12 / 5) ^ 2 * (37 / 2 * r) ^ 4 :=
      mul_le_mul hH2 hA4 (by positivity) (by positivity)
    have hAB : A ^ 2 * B ^ 2 ≤ (37 / 2 * r) ^ 2 * (147 / 10 * r) ^ 2 :=
      mul_le_mul hAs hBs (by positivity) (by positivity)
    have hsecond : 4 * rawTraceRemainderD0 ^ 2 * A ^ 2 * B ^ 2 ≤
        4 * 4 ^ 2 * ((37 / 2 * r) ^ 2 * (147 / 10 * r) ^ 2) := by
      have := mul_le_mul hD2 hAB (by positivity) (by positivity)
      nlinarith [this]
    have hrad : rawTraceRemainderH0 ^ 2 * A ^ 4 +
        4 * rawTraceRemainderD0 ^ 2 * A ^ 2 * B ^ 2 ≤ (2326 * r ^ 2) ^ 2 := by
      have hr4 : 0 ≤ r ^ 4 := by positivity
      nlinarith [hfirst, hsecond, hr4]
    have hroot : Real.sqrt (rawTraceRemainderH0 ^ 2 * A ^ 4 +
        4 * rawTraceRemainderD0 ^ 2 * A ^ 2 * B ^ 2) ≤ 2326 * r ^ 2 :=
      (Real.sqrt_le_iff).2 ⟨by positivity, hrad⟩
    have hbase : rawTraceRemainderH0 * A ^ 2 ≤ 12 / 5 * (37 / 2 * r) ^ 2 :=
      mul_le_mul hH0 hAs (by positivity) (by norm_num)
    nlinarith [hbase, hroot, sq_nonneg r]
  have hμ0 : 0 ≤ rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
      (rawTraceRemainderA r r) (rawTraceRemainderB r r) := by
    unfold rawTraceRemainderMu
    positivity
  exact ⟨hA, hA0, hB, hB0, hκ, hκ0, hμ, hμ0⟩

end ASDExplicitGamma.Main

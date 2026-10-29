module

public import ASDExplicitGamma.Cold.BadHistory

/-! # Correlated good/bad history products with the exact source factor two -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace ASDExplicitGamma.Cold

/-- Correlated products are split pathwise; no independence hypothesis is used. -/
theorem history_product_split_pointwise {g0 g1 s b D Z ξ : ℝ}
    (hg1 : 0 ≤ g1) (hs : 0 ≤ s) (_hb : 0 ≤ b) (hD : 0 ≤ D) (hZ : 0 ≤ Z)
    (hξ : 0 < ξ) (hbound : Z ≤ 2*b*D) :
    (g0+g1*s*D)*Z ≤ (g0+g1*s*ξ)*Z + 2*g1*s*b*(if ξ < D then D^2 else 0) := by
  split_ifs with hbad
  · have hm := mul_le_mul_of_nonneg_left hbound (mul_nonneg (mul_nonneg hg1 hs) hD)
    have hx := mul_nonneg (mul_nonneg (mul_nonneg hg1 hs) hξ.le) hZ
    nlinarith only [hm,hx]
  · have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_of_not_gt hbad) (mul_nonneg hg1 hs)) hZ
    nlinarith only [hm]

/-- The large even moment controls the second moment without changing the random variable. -/
theorem history_square_le_one_add_twentieth {x : ℝ} (hx : 0 ≤ x) : x^2 ≤ 1+x^20 := by
  by_cases h : x ≤ 1
  · have h2 := pow_le_pow_left₀ hx h 2
    have h20 := pow_nonneg hx 20
    linarith only [h2,h20]
  · have hpow := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ x) (by norm_num : (2 : ℕ) ≤ 20)
    have h20 := pow_nonneg hx 20
    linarith only [hpow,h20]

/-- The actual second history moment is integrable from its twentieth moment. -/
theorem integrable_history_square {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    {D : Ω → ℝ} (hD : Measurable D) (hDn : ∀ᵐ ω ∂ℙ, 0 ≤ D ω)
    (h20 : Integrable (fun ω => D ω^20) ℙ) : Integrable (fun ω => D ω^2) ℙ := by
  apply ((integrable_const (1 : ℝ)).add h20).mono' (hD.pow_const 2).aestronglyMeasurable
  filter_upwards [hDn] with ω hω
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact history_square_le_one_add_twentieth hω

/-- The actual correlated Gram/history product is integrable by its pathwise source bound. -/
theorem integrable_history_product {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    {D Z : Ω → ℝ} (hD : Measurable D) (hZ : Integrable Z ℙ)
    (hDn : ∀ᵐ ω ∂ℙ, 0 ≤ D ω) (hZn : ∀ᵐ ω ∂ℙ, 0 ≤ Z ω)
    {g0 g1 s b : ℝ} (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hs : 0 ≤ s) (_hb : 0 ≤ b)
    (hbound : ∀ᵐ ω ∂ℙ, Z ω ≤ 2*b*D ω) (h20 : Integrable (fun ω => D ω^20) ℙ) :
    Integrable (fun ω => (g0+g1*s*D ω)*Z ω) ℙ := by
  have h2 := integrable_history_square hD hDn h20
  have hM := (hZ.const_mul g0).add (h2.const_mul (2*g1*s*b))
  have hmeas : AEStronglyMeasurable (fun ω => (g0+g1*s*D ω)*Z ω) ℙ :=
    (measurable_const.add (measurable_const.mul hD)).aestronglyMeasurable.mul hZ.aestronglyMeasurable
  apply hM.mono' hmeas
  filter_upwards [hDn,hZn,hbound] with ω hω hZω hBω
  have hn : 0 ≤ (g0+g1*s*D ω)*Z ω := mul_nonneg (by positivity) hZω
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  change _ ≤ g0*Z ω+(2*g1*s*b)*D ω^2
  have hm := mul_le_mul_of_nonneg_left hBω (mul_nonneg (mul_nonneg hg1 hs) hω)
  nlinarith only [hm]

/-- The source good/bad history charge, retaining its exact factor two. -/
theorem expected_history_product_le {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    {D Z : Ω → ℝ} (hD : Measurable D) (hZ : Integrable Z ℙ)
    (hDn : ∀ᵐ ω ∂ℙ, 0 ≤ D ω) (hZn : ∀ᵐ ω ∂ℙ, 0 ≤ Z ω)
    {g0 g1 s b ξ H : ℝ} (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hs : 0 ≤ s) (hb : 0 ≤ b) (hξ : 0 < ξ)
    (hbound : ∀ᵐ ω ∂ℙ, Z ω ≤ 2*b*D ω) (h20 : Integrable (fun ω => D ω^20) ℙ)
    (hMoment : (∫ ω, D ω^20 ∂ℙ) ≤ H^20) :
    (∫ ω, (g0+g1*s*D ω)*Z ω ∂ℙ) ≤
      (g0+g1*s*ξ)*(∫ ω, Z ω ∂ℙ)+2*g1*s*b*H^20/ξ^18 := by
  obtain ⟨hbadInt,hbad⟩ := integral_bad_history_square_le hD hDn hξ h20 hMoment
  have hprod := integrable_history_product hD hZ hDn hZn hg0 hg1 hs hb hbound h20
  have hpoint : ∀ᵐ ω ∂ℙ, (g0+g1*s*D ω)*Z ω ≤
      (g0+g1*s*ξ)*Z ω+(2*g1*s*b)*(if ξ < D ω then D ω^2 else 0) := by
    filter_upwards [hDn,hZn,hbound] with ω hω hZω hBω
    exact history_product_split_pointwise hg1 hs hb hω hZω hξ hBω
  have h := integral_mono_ae hprod ((hZ.const_mul _).add (hbadInt.const_mul _)) hpoint
  change (∫ ω, (g0+g1*s*D ω)*Z ω ∂ℙ) ≤
    ∫ ω, (g0+g1*s*ξ)*Z ω+(2*g1*s*b)*(if ξ < D ω then D ω^2 else 0) ∂ℙ at h
  rw [integral_add (hZ.const_mul _) (hbadInt.const_mul _),integral_const_mul,integral_const_mul] at h
  have hm := mul_le_mul_of_nonneg_left hbad (by positivity : 0 ≤ 2*g1*s*b)
  have heq : 2*g1*s*b*(H^20/ξ^18) = 2*g1*s*b*H^20/ξ^18 := by ring
  rw [heq] at hm
  linarith only [h,hm]

end ASDExplicitGamma.Cold

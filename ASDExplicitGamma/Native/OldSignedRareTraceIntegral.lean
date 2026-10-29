module

public import ASDExplicitGamma.Inverse.ParentGapHolder

/-! Real integrability and mean bounds for the complete correlated rare
products. No conversion from an infinite extended integral is used. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory Inverse
open scoped ENNReal
noncomputable section

/-- The actual Hölder payment also proves genuine integrability of every
rare monomial, rather than merely bounding a `toReal` expression. -/
theorem old_signed_rare_trace_integrable_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R T : Ω → ℝ) (ε C : ℝ) (n : ℕ) (hn : n ≤ 4)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hR0 : ∀ ω,0 ≤ R ω) (hT0 : ∀ ω,0 ≤ T ω)
    (hRmeas : AEStronglyMeasurable R μ) (hTmeas : AEStronglyMeasurable T μ)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hT2 : eLpNorm T 2 μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => R ω^n*T ω) μ ∧
      (∫ ω,R ω^n*T ω ∂μ) ≤ ε^n*C := by
  have h := parent_gap_rare_trace_holder R T ε C n hn hε hR0 hT0 hRmeas hTmeas hR128 hT2
  have hnonneg (ω : Ω) : 0 ≤ R ω^n*T ω := mul_nonneg (pow_nonneg (hR0 ω) n) (hT0 ω)
  have heq (ω : Ω) : ENNReal.ofReal (R ω^n*T ω)=
      ENNReal.ofReal (R ω)^n*ENNReal.ofReal (T ω) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (hR0 ω) n),ENNReal.ofReal_pow (hR0 ω)]
  have hb : (∫⁻ ω,ENNReal.ofReal (R ω^n*T ω) ∂μ) ≤ ENNReal.ofReal (ε^n*C) := by
    simpa only [heq] using h
  have hi : Integrable (fun ω => R ω^n*T ω) μ := (lintegral_ofReal_ne_top_iff_integrable
    ((hRmeas.pow n).mul hTmeas) (Filter.Eventually.of_forall hnonneg)).mp
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
  refine ⟨hi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnonneg)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_nonneg hε n) hC)).mp hb

/-- A directional quadratic dominated by the trace inherits every rare
payment without any independence assertion or weighted isotropy premise. -/
theorem old_signed_rare_directional_integrable_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R T q : Ω → ℝ) (ε C w : ℝ) (n : ℕ) (hn : n ≤ 4)
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hR0 : ∀ ω,0 ≤ R ω) (hT0 : ∀ ω,0 ≤ T ω)
    (hq0 : ∀ ω,0 ≤ q ω) (hqT : ∀ ω,q ω ≤ T ω*w)
    (hRmeas : AEStronglyMeasurable R μ) (hTmeas : AEStronglyMeasurable T μ)
    (hqmeas : AEStronglyMeasurable q μ)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hT2 : eLpNorm T 2 μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => R ω^n*q ω) μ ∧
      (∫ ω,R ω^n*q ω ∂μ) ≤ ε^n*C*w := by
  have h := old_signed_rare_trace_integrable_bound R T ε C n hn hε hC hR0 hT0 hRmeas hTmeas hR128 hT2
  have hmajor (ω : Ω) : R ω^n*q ω ≤ (R ω^n*T ω)*w := by
    calc
      _ ≤ R ω^n*(T ω*w) := mul_le_mul_of_nonneg_left (hqT ω) (pow_nonneg (hR0 ω) n)
      _ = _ := (mul_assoc _ _ _).symm
  have hi := (h.1.mul_const w).mono_nonneg ((hRmeas.pow n).mul hqmeas)
    (Filter.Eventually.of_forall (fun ω => mul_nonneg (pow_nonneg (hR0 ω) n) (hq0 ω)))
    (Filter.Eventually.of_forall hmajor)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω,(R ω^n*T ω)*w ∂μ := integral_mono hi (h.1.mul_const w) hmajor
    _ = (∫ ω,R ω^n*T ω ∂μ)*w := integral_mul_const w _
    _ ≤ ε^n*C*w := mul_le_mul_of_nonneg_right h.2 hw

end
end ASDExplicitGamma.Native

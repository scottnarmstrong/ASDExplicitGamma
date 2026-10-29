module

public import ASDExplicitGamma.Scalar.SmoothFeedbackConsumerArith

/-! The NEW-bank Hölder step of SC-NEW-RESOLVENT-DEFECT. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `E[B H] ≤ b E[H] + ε ‖H‖_{128/127}` when `B ≤ b + R`, `‖R‖₁₂₈ ≤ ε`, `H ≥ 0`. -/
theorem defect_bank_holder [IsFiniteMeasure μ] {Bs R H : Ω → ℝ} {b ε g Eh : ℝ}
    (hRm : Measurable R) (hHm : Measurable H)
    (hB : ∀ ω, Bs ω ≤ b + R ω) (hR0 : ∀ ω, 0 ≤ R ω) (hH0 : ∀ ω, 0 ≤ H ω)
    (hε : 0 ≤ ε) (hg : 0 ≤ g)
    (hR : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hHq : eLpNorm H (ENNReal.ofReal (128 / 127)) μ ≤ ENNReal.ofReal g)
    (hHint : Integrable H μ) (hBH : Integrable (fun ω => Bs ω * H ω) μ)
    (hEH : ∫ ω, H ω ∂μ ≤ Eh) (hb : 0 ≤ b) :
    ∫ ω, Bs ω * H ω ∂μ ≤ b * Eh + ε * g := by
  have hRH := integrable_mul_128 hRm hHm hR hHq
  have h1 : ∫ ω, Bs ω * H ω ∂μ ≤ ∫ ω, (b * H ω + R ω * H ω) ∂μ :=
    integral_mono hBH ((hHint.const_mul b).add hRH) fun ω => by
      have := mul_le_mul_of_nonneg_right (hB ω) (hH0 ω)
      linarith
  rw [integral_add (hHint.const_mul b) hRH, integral_const_mul] at h1
  have h2 := integral_mul_le_128 hRm hHm hR0 hH0 hε hg hR hHq
  have h3 : b * ∫ ω, H ω ∂μ ≤ b * Eh := mul_le_mul_of_nonneg_left hEH hb
  linarith

end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Cold.ExactCentering

/-! # The exact twentieth-moment history charge in P5 and P6 -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace ASDExplicitGamma.Cold

/-- The source pointwise bad-set inequality, with power eighteen in the threshold. -/
theorem bad_history_square_le {D ξ : ℝ} (hD : 0 ≤ D) (hξ : 0 < ξ) :
    (if ξ < D then D^2 else 0) ≤ D^20/ξ^18 := by
  split_ifs with hbad
  · apply (le_div_iff₀ (pow_pos hξ 18)).mpr
    have hpow := pow_le_pow_left₀ hξ.le hbad.le 18
    have h := mul_le_mul_of_nonneg_left hpow (sq_nonneg D)
    convert h using 1
    rw [← pow_add]
  · exact div_nonneg (pow_nonneg hD _) (pow_nonneg hξ.le _)

/-- The genuine bad history is integrable and paid by the exact twentieth moment. -/
theorem integral_bad_history_square_le {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {D : Ω → ℝ} (hD : Measurable D) (hDn : ∀ᵐ ω ∂ℙ, 0 ≤ D ω)
    {ξ H : ℝ} (hξ : 0 < ξ) (hMomentInt : Integrable (fun ω => D ω^20) ℙ)
    (hMoment : (∫ ω, D ω^20 ∂ℙ) ≤ H^20) :
    Integrable (fun ω => if ξ < D ω then D ω^2 else 0) ℙ ∧
      (∫ ω, (if ξ < D ω then D ω^2 else 0) ∂ℙ) ≤ H^20/ξ^18 := by
  have hm : Measurable (fun ω => if ξ < D ω then D ω^2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_const hD) (hD.pow_const 2) measurable_const
  have hpoint : ∀ᵐ ω ∂ℙ, ‖(if ξ < D ω then D ω^2 else 0)‖ ≤ D ω^20/ξ^18 := by
    filter_upwards [hDn] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (by split_ifs <;> positivity)]
    exact bad_history_square_le hω hξ
  have hi := (hMomentInt.div_const (ξ^18)).mono' hm.aestronglyMeasurable hpoint
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, D ω^20/ξ^18 ∂ℙ := integral_mono_ae hi (hMomentInt.div_const _) (hDn.mono fun ω hω =>
      bad_history_square_le hω hξ)
    _ = (∫ ω, D ω^20 ∂ℙ)/ξ^18 := integral_div _ _
    _ ≤ H^20/ξ^18 := div_le_div_of_nonneg_right hMoment (pow_nonneg hξ.le _)

end ASDExplicitGamma.Cold

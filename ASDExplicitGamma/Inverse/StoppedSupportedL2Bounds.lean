module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Actual L2 norm bounds from a measurable finite-volume support and a
uniform amplitude. No independent integrability premise is needed for the
extended-norm estimate. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem supported_eLpNorm_two_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (E : Set Ω) (hE : MeasurableSet E)
    (M V : ℝ) (hM : 0 ≤ M) (hV : 0 ≤ V) (hvol : μ E ≤ ENNReal.ofReal V)
    (hsupp : ∀ᵐ x ∂μ, f x ≠ 0 → x ∈ E) (hbound : ∀ᵐ x ∂μ, |f x| ≤ M) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (M*Real.sqrt V) := by
  have hm : eLpNorm f 2 μ ≤ eLpNorm (E.indicator (fun _ : Ω => M)) 2 μ := by
    apply eLpNorm_mono_ae hf
    filter_upwards [hsupp,hbound] with x hs hb
    by_cases hx : x ∈ E
    · simpa only [Set.indicator_of_mem hx,Real.norm_eq_abs,abs_of_nonneg hM] using hb
    · have hz : f x=0 := by by_contra hn; exact hx (hs hn)
      simp only [Set.indicator_of_notMem hx,hz,norm_zero,le_refl]
  rw [eLpNorm_indicator_const hE.nullMeasurableSet (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞),Real.enorm_eq_ofReal hM] at hm
  norm_num only [ENNReal.toReal_ofNat] at hm
  have hp := ENNReal.rpow_le_rpow hvol (by norm_num : (0:ℝ) ≤ 1/2)
  apply (hm.trans (mul_le_mul_right hp (ENNReal.ofReal M))).trans_eq
  rw [ENNReal.ofReal_rpow_of_nonneg hV (by norm_num : (0:ℝ) ≤ 1/2),
    ← ENNReal.ofReal_mul hM,Real.sqrt_eq_rpow]

theorem supported_L2_norm_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) (E : Set Ω) (hE : MeasurableSet E)
    (M V : ℝ) (hM : 0 ≤ M) (hV : 0 ≤ V) (hvol : μ E ≤ ENNReal.ofReal V)
    (hsupp : ∀ᵐ x ∂μ, f x ≠ 0 → x ∈ E) (hbound : ∀ᵐ x ∂μ, |f x| ≤ M) :
    ‖hf.toLp f‖ ≤ M*Real.sqrt V := by
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (supported_eLpNorm_two_bound μ f hf.aestronglyMeasurable E hE M V hM hV hvol hsupp hbound)
  rw [Lp.norm_toLp]
  simpa only [ENNReal.toReal_ofReal (mul_nonneg hM (Real.sqrt_nonneg V))] using ht

end
end ASDExplicitGamma.Inverse

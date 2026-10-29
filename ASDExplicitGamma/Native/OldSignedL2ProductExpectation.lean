module

public import ASDExplicitGamma.Native.OldSignedHistoryMoments

/-! Correlated matrix products controlled by actual second moments. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
noncomputable section

/-- Two nonnegative square-integrable multipliers have their ordinary
Cauchy--Schwarz payment, including integrability of the correlated product. -/
theorem old_signed_L2_product_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (a b : ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : ∀ ω,0≤f ω) (hg0 : ∀ ω,0≤g ω)
    (ha : 0≤a) (hfa : lpNorm f 2 μ≤a) (hgb : lpNorm g 2 μ≤b) :
    Integrable (fun ω => f ω*g ω) μ ∧ (∫ ω,f ω*g ω ∂μ)≤a*b := by
  have hc : Real.HolderConjugate 2 2 := Real.holderConjugate_iff.mpr (by norm_num)
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hc
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (show MemLp f (ENNReal.ofReal 2) μ by simpa only [ENNReal.ofReal_ofNat] using hf)
    (show MemLp g (ENNReal.ofReal 2) μ by simpa only [ENNReal.ofReal_ofNat] using hg)
  have hh' : (∫ ω,f ω*g ω ∂μ)≤lpNorm f 2 μ*lpNorm g 2 μ := by
    rw [old_signed_lpNorm_two μ f hf,old_signed_lpNorm_two μ g hg]
    simpa only [Real.rpow_ofNat,←Real.sqrt_eq_rpow] using hh
  exact ⟨hf.integrable_mul hg,hh'.trans (mul_le_mul hfa hgb lpNorm_nonneg ha)⟩

end
end ASDExplicitGamma.Native

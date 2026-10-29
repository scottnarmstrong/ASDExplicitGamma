module

public import ASDExplicitGamma.Native.OldSignedSqrtExpectation

/-! Correlated energy products paid by their two genuine first moments. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory

/-- Cauchy--Schwarz for square roots of two integrable energies. No
independence is required, and integrability of the product is included. -/
theorem old_signed_sqrt_product_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ ω,0 ≤ f ω) (hg0 : ∀ ω,0 ≤ g ω) :
    Integrable (fun ω => Real.sqrt (f ω)*Real.sqrt (g ω)) μ ∧
      (∫ ω,Real.sqrt (f ω)*Real.sqrt (g ω) ∂μ) ≤
        Real.sqrt (∫ ω,f ω ∂μ)*Real.sqrt (∫ ω,g ω ∂μ) := by
  have hfm : MemLp (fun ω => Real.sqrt (f ω)) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hf.1)).mpr
      (by simpa only [Real.sq_sqrt (hf0 _)] using hf)
  have hgm : MemLp (fun ω => Real.sqrt (g ω)) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg.1)).mpr
      (by simpa only [Real.sq_sqrt (hg0 _)] using hg)
  refine ⟨hfm.integrable_mul hgm,?_⟩
  have hc : Real.HolderConjugate 2 2 := Real.holderConjugate_iff.mpr (by norm_num)
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hc
    (Filter.Eventually.of_forall (fun ω => Real.sqrt_nonneg (f ω)))
    (Filter.Eventually.of_forall (fun ω => Real.sqrt_nonneg (g ω)))
    (show MemLp (fun ω => Real.sqrt (f ω)) (ENNReal.ofReal 2) μ by simpa using hfm)
    (show MemLp (fun ω => Real.sqrt (g ω)) (ENNReal.ofReal 2) μ by simpa using hgm)
  simpa only [Real.rpow_ofNat,Real.sq_sqrt (hf0 _),Real.sq_sqrt (hg0 _),
    ←Real.sqrt_eq_rpow] using hh

end ASDExplicitGamma.Native

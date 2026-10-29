module

public import ASDExplicitGamma.Native.OldSignedSqrtProductExpectation

/-! Correlated root products with the reciprocal constant retained. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory Native

/-- Both offsets are retained while the two random energies are contracted
by Cauchy--Schwarz, without independence. -/
theorem old_hessian_offset_root_product_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ) (a b : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ ω,0≤f ω) (hg0 : ∀ ω,0≤g ω) (ha : 0≤a) (hb : 0≤b) :
    Integrable (fun ω => (a+Real.sqrt (f ω))*(Real.sqrt (g ω)+b)) μ ∧
    (∫ ω,(a+Real.sqrt (f ω))*(Real.sqrt (g ω)+b) ∂μ)≤
      (a+Real.sqrt (∫ ω,f ω ∂μ))*(Real.sqrt (∫ ω,g ω ∂μ)+b) := by
  have hfr := old_signed_sqrt_expectation μ f hf hf0
  have hgr := old_signed_sqrt_expectation μ g hg hg0
  have hfg := old_signed_sqrt_product_expectation μ f g hf hg hf0 hg0
  have he : (fun ω => (a+Real.sqrt (f ω))*(Real.sqrt (g ω)+b))=
      (fun ω => a*Real.sqrt (g ω)+Real.sqrt (f ω)*Real.sqrt (g ω)+
        b*Real.sqrt (f ω)+a*b) := by funext ω; ring
  rw [he]
  have hi := ((hgr.1.const_mul a).add hfg.1).add (hfr.1.const_mul b)
  refine ⟨hi.add (integrable_const _),?_⟩
  simp only [Pi.add_def] at hi
  rw [integral_add hi (integrable_const (a*b))]
  rw [integral_add (show Integrable (fun ω => a*Real.sqrt (g ω)+Real.sqrt (f ω)*Real.sqrt (g ω)) μ from
    (hgr.1.const_mul a).add hfg.1) (hfr.1.const_mul b)]
  rw [integral_add (hgr.1.const_mul a) hfg.1]
  simp only [integral_const_mul,integral_const,probReal_univ,one_smul]
  have hh := add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hgr.2 ha) hfg.2)
    (mul_le_mul_of_nonneg_left hfr.2 hb)) (le_refl (a*b))
  calc
    _ ≤ (a*Real.sqrt (∫ ω,g ω ∂μ)+Real.sqrt (∫ ω,f ω ∂μ)*Real.sqrt (∫ ω,g ω ∂μ)+
        b*Real.sqrt (∫ ω,f ω ∂μ))+a*b := hh
    _ = _ := by ring

end ASDExplicitGamma.Scalar

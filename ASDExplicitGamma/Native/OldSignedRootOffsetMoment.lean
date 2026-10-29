module

public import ASDExplicitGamma.Native.OldSignedSqrtExpectation

/-! The reciprocal derivative offset keeps the sharp square-root coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory

/-- An integrable nonnegative energy controls the square of its root plus
one, including integrability and the exact offset coefficient. -/
theorem old_signed_root_offset_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (C : ℝ)
    (hf : Integrable f μ) (hf0 : ∀ ω,0≤f ω) (hC : 0≤C)
    (hcap : (∫ ω,f ω ∂μ)≤C) :
    Integrable (fun ω => (Real.sqrt (f ω)+1)^2) μ ∧
    (∫ ω,(Real.sqrt (f ω)+1)^2 ∂μ)≤(Real.sqrt C+1)^2 := by
  have hr := old_signed_sqrt_expectation μ f hf hf0
  have he (ω) : (Real.sqrt (f ω)+1)^2=f ω+2*Real.sqrt (f ω)+1 := by
    nlinarith only [Real.sq_sqrt (hf0 ω)]
  simp_rw [he]
  have hi := hr.1.const_mul 2
  have hiadd : Integrable (fun ω => f ω+2*Real.sqrt (f ω)) μ := hf.add hi
  refine ⟨hiadd.add (integrable_const 1),?_⟩
  rw [integral_add hiadd (integrable_const 1),integral_add hf hi,integral_const_mul]
  have hh := add_le_add hcap (mul_le_mul_of_nonneg_left
    (hr.2.trans (Real.sqrt_le_sqrt hcap)) (by norm_num : (0:ℝ)≤2))
  have hprob : (∫ _ : Ω,(1:ℝ) ∂μ)=1 := by simp
  rw [hprob]
  have hs := Real.sq_sqrt hC
  nlinarith only [hh,hs]

end ASDExplicitGamma.Native

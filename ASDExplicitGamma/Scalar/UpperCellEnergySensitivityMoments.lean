module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPowerMoments

/-! The fresh sensitivity envelope and compatible load remain correlated. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Each term of the physical cubic envelope uses L6 for F and L4 for
its load magnitude P; no independence between them is needed. -/
theorem upper_cell_sensitivity_mixed_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F P : Ω → ℝ)
    (hF : AEStronglyMeasurable F μ) (hP : AEStronglyMeasurable P μ)
    (hF0 : ∀ ω, 0 ≤ F ω) (hP0 : ∀ ω, 0 ≤ P ω)
    (f : ℝ) (hf : 0 ≤ f) (hfcap : eLpNorm F 6 μ ≤ ENNReal.ofReal f)
    (hpcap : eLpNorm P 4 μ ≤ 2)
    (j : ℕ) (hj : 0 < j) (hj3 : j ≤ 3) :
    Integrable (fun ω => F ω^j*P ω^2) μ ∧
      (∫ ω, F ω^j*P ω^2 ∂μ) ≤ 4*f^j := by
  have hfj := upper_cell_sensitivity_power_L2 μ F hF hF0 f hf hfcap j hj hj3
  have hp2 := upper_cell_power_L2 μ P 2 (by norm_num) 2 hP hP0
    (by norm_num) (by norm_num at ⊢; exact hpcap)
  have hh := Native.old_signed_L2_product_expectation μ (fun ω => F ω^j)
    (fun ω => P ω^2) (f^j) 4 hfj.1 hp2.1
    (fun ω => pow_nonneg (hF0 ω) j) (fun ω => sq_nonneg (P ω))
    (pow_nonneg hf j) hfj.2 (by norm_num at hp2; exact hp2.2)
  exact ⟨hh.1,by simpa only [mul_comm] using hh.2⟩

/-- The exact polynomial payment, before the old independent matrix factor.
There is no replacement by the coarser 28 f estimate. -/
theorem upper_cell_sensitivity_polynomial_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F P : Ω → ℝ)
    (hF : AEStronglyMeasurable F μ) (hP : AEStronglyMeasurable P μ)
    (hF0 : ∀ ω, 0 ≤ F ω) (hP0 : ∀ ω, 0 ≤ P ω)
    (f : ℝ) (hf : 0 ≤ f) (hfcap : eLpNorm F 6 μ ≤ ENNReal.ofReal f)
    (hpcap : eLpNorm P 4 μ ≤ 2) :
    Integrable (fun ω => F ω*(1+2*F ω+4*F ω^2)*P ω^2) μ ∧
      (∫ ω, F ω*(1+2*F ω+4*F ω^2)*P ω^2 ∂μ) ≤ 4*(f+2*f^2+4*f^3) := by
  have h1 := upper_cell_sensitivity_mixed_moment μ F P hF hP hF0 hP0
    f hf hfcap hpcap 1 (by norm_num) (by norm_num)
  have h2 := upper_cell_sensitivity_mixed_moment μ F P hF hP hF0 hP0
    f hf hfcap hpcap 2 (by norm_num) (by norm_num)
  have h3 := upper_cell_sensitivity_mixed_moment μ F P hF hP hF0 hP0
    f hf hfcap hpcap 3 (by norm_num) (by norm_num)
  have heq : (fun ω => F ω*(1+2*F ω+4*F ω^2)*P ω^2) =
      (fun ω => F ω^1*P ω^2+2*(F ω^2*P ω^2)+4*(F ω^3*P ω^2)) := by
    funext ω; ring
  rw [heq]
  refine ⟨(h1.1.add (h2.1.const_mul 2)).add (h3.1.const_mul 4),?_⟩
  have hadd := integral_add (h1.1.add (h2.1.const_mul 2)) (h3.1.const_mul 4)
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_add h1.1 (h2.1.const_mul 2),
    integral_const_mul, integral_const_mul]
  have hb := add_le_add (add_le_add h1.2
    (mul_le_mul_of_nonneg_left h2.2 (by norm_num : (0:ℝ) ≤ 2)))
    (mul_le_mul_of_nonneg_left h3.2 (by norm_num : (0:ℝ) ≤ 4))
  exact hb.trans_eq (by ring)

end
end ASDExplicitGamma.Scalar

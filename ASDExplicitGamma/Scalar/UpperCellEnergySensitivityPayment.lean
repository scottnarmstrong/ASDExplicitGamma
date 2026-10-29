module

public import ASDExplicitGamma.Scalar.UpperCellEnergySensitivityMoments
public import Mathlib.Probability.Independence.Integration

/-! The all-event sensitivity payment uses old/fresh independence only. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- Pay the literal sensitivity polynomial with the old L2 matrix majorant.
The fresh envelope F and fresh compatible load magnitude P can be correlated.
This analytic helper keeps its moment and independence inputs explicit; the
physical cell theorem must supply them from the actual old/fresh laws. -/
theorem upper_cell_sensitivity_payment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A F P : Ω → ℝ)
    (hA : MemLp A 2 μ) (hF : AEStronglyMeasurable F μ)
    (hP : AEStronglyMeasurable P μ)
    (hA0 : ∀ ω, 0 ≤ A ω) (hF0 : ∀ ω, 0 ≤ F ω) (hP0 : ∀ ω, 0 ≤ P ω)
    (m f : ℝ) (hm : 0 ≤ m) (hf : 0 ≤ f)
    (hAcap : lpNorm A 2 μ ≤ m) (hfcap : eLpNorm F 6 μ ≤ ENNReal.ofReal f)
    (hpcap : eLpNorm P 4 μ ≤ 2)
    (hind : IndepFun A (fun ω => (F ω,P ω)) μ) :
    Integrable (fun ω => 6*A ω^2*F ω*(1+2*F ω+4*F ω^2)*P ω^2) μ ∧
    (∫ ω,6*A ω^2*F ω*(1+2*F ω+4*F ω^2)*P ω^2 ∂μ) ≤
      24*m^2*(f+2*f^2+4*f^3) := by
  let G := fun ω => F ω*(1+2*F ω+4*F ω^2)*P ω^2
  have hG := upper_cell_sensitivity_polynomial_moment μ F P hF hP hF0 hP0
    f hf hfcap hpcap
  have hA2 : Integrable (fun ω => A ω^2) μ :=
    (memLp_two_iff_integrable_sq hA.aestronglyMeasurable).mp hA
  have hAi := (Native.old_signed_history_first_second_moments μ A m hA hA0 hm hAcap).2
  have hi : IndepFun (fun ω => A ω^2) G μ :=
    hind.comp (show Measurable (fun x : ℝ => x^2) by fun_prop)
      (show Measurable (fun x : ℝ × ℝ => x.1*(1+2*x.1+4*x.1^2)*x.2^2) by fun_prop)
  have hprod : Integrable (fun ω => A ω^2*G ω) μ := hi.integrable_mul hA2 hG.1
  have heq : (fun ω => 6*A ω^2*F ω*(1+2*F ω+4*F ω^2)*P ω^2) =
      (fun ω => 6*(A ω^2*G ω)) := by funext ω; dsimp only [G]; ring
  rw [heq]
  refine ⟨hprod.const_mul 6,?_⟩
  rw [integral_const_mul]
  have hex : (∫ ω,A ω^2*G ω ∂μ) = (∫ ω,A ω^2 ∂μ)*(∫ ω,G ω ∂μ) :=
    hi.integral_mul_eq_mul_integral hA2.aestronglyMeasurable hG.1.aestronglyMeasurable
  rw [hex]
  have hGi : 0 ≤ ∫ ω,G ω ∂μ := integral_nonneg (fun ω => by
    dsimp only [G]
    have h := hF0 ω
    positivity)
  have hh := mul_le_mul hAi hG.2 hGi (sq_nonneg m)
  exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 6)).trans_eq (by ring)

end
end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Scalar.GaussianProduct
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! The exact Hilbert fourth-moment payment from centered Gaussian
coordinate marginals. All correlations between coordinates are retained. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- The square of a centered Gaussian lies in L2, with its exact norm.
No independence or estimate of the fourth moment is a premise. -/
theorem upper_cell_reset_gaussian_square_L2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : HasGaussianLaw X μ) (hm : ∫ ω,X ω ∂μ=0) :
    MemLp (fun ω => (X ω)^2) 2 μ ∧
      lpNorm (fun ω => (X ω)^2) 2 μ=Real.sqrt 3*(∫ ω,(X ω)^2 ∂μ) := by
  let holderFourFourTwo : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4:ℝ≥0∞)=2*2 by norm_num,ENNReal.mul_inv,←add_mul,
      ENNReal.inv_two_add_inv_two,one_mul] <;> norm_num⟩
  have h4 : MemLp X 4 μ := hX.memLp (by norm_num)
  have h2 : MemLp (fun ω => (X ω)^2) 2 μ := by
    simpa only [pow_two] using h4.fun_mul h4
  refine ⟨h2,?_⟩
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) h2.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two]
  have heq : (fun ω => ‖(X ω)^2‖^2)=(fun ω => (X ω)^4) := by
    funext ω
    rw [Real.norm_eq_abs,sq_abs]
    ring
  rw [heq,centered_gaussian_fourth_moment μ X hX hm,←Real.sqrt_eq_rpow,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤3),
    Real.sqrt_sq (integral_nonneg (fun ω => sq_nonneg (X ω)))]

end
end ASDExplicitGamma.Scalar

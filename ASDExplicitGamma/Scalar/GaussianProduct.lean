module

public import ASDExplicitGamma.Scalar.GaussianFourthMoment
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! SC-GAUSSIAN-PRODUCT-BOUND. Cauchy--Schwarz and the exact Gaussian fourth
moment suffice, even without joint Gaussianity or independence. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The Gaussian product estimate holds for any coupling of centered Gaussian marginals. -/
theorem centered_gaussian_product_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : HasGaussianLaw X μ) (hY : HasGaussianLaw Y μ)
    (hmX : ∫ ω, X ω ∂μ = 0) (hmY : ∫ ω, Y ω ∂μ = 0) :
    (∫ ω, (X ω)^2*(Y ω)^2 ∂μ) ≤
      3*(∫ ω, (X ω)^2 ∂μ)*(∫ ω, (Y ω)^2 ∂μ) := by
  have instHolderFourFourTwo : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4:ℝ≥0∞) = 2*2 by norm_num, ENNReal.mul_inv,← add_mul,
      ENNReal.inv_two_add_inv_two,one_mul] <;> norm_num⟩
  have hX4 : MemLp X 4 μ := hX.memLp (by norm_num)
  have hY4 : MemLp Y 4 μ := hY.memLp (by norm_num)
  have hX2 : MemLp (fun ω => (X ω)^2) 2 μ := by
    simpa only [pow_two] using hX4.fun_mul hX4
  have hY2 : MemLp (fun ω => (Y ω)^2) 2 μ := by
    simpa only [pow_two] using hY4.fun_mul hY4
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (Real.HolderConjugate.two_two)
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (X ω)))
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (Y ω)))
    (show MemLp (fun ω => (X ω)^2) (ENNReal.ofReal 2) μ by norm_num; exact hX2)
    (show MemLp (fun ω => (Y ω)^2) (ENNReal.ofReal 2) μ by norm_num; exact hY2)
  have hpow (Z : Ω → ℝ) : (fun ω => ((Z ω)^2)^(2:ℝ)) = fun ω => (Z ω)^4 := by
    funext ω
    rw [Real.rpow_two]
    ring
  rw [hpow X,hpow Y,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow,
    centered_gaussian_fourth_moment μ X hX hmX,centered_gaussian_fourth_moment μ Y hY hmY] at h
  have hx : 0 ≤ ∫ ω, (X ω)^2 ∂μ := integral_nonneg (fun ω => sq_nonneg (X ω))
  have hy : 0 ≤ ∫ ω, (Y ω)^2 ∂μ := integral_nonneg (fun ω => sq_nonneg (Y ω))
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3),
    Real.sqrt_sq hx,Real.sqrt_sq hy] at h
  calc
    _ ≤ _ := h
    _ = (Real.sqrt 3)^2*(∫ ω, (X ω)^2 ∂μ)*(∫ ω, (Y ω)^2 ∂μ) := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Gaussian.DerivativeLaw

/-! Exact finite linear-combination laws with the actual differentiated covariance quadratic form. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section

/-- The variance of a finite Gaussian combination is its actual covariance quadratic form. -/
theorem IsCenteredGaussianFamily.map_linearCombination_covariance {Ω I : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : I → Ω → ℝ} (hg : IsCenteredGaussianFamily μ X)
    {J : Type} [Fintype J] (x : J → I) (t : J → ℝ) :
    μ.map (fun ω => ∑ i, t i*X (x i) ω) = gaussianReal 0 (Real.toNNReal
      (∑ i, ∑ j, t i*t j*(∫ ω, X (x i) ω*X (x j) ω ∂μ))) := by
  classical
  obtain ⟨v,hv⟩ := hg.2 x t
  have hmeas : AEMeasurable (fun ω => ∑ i, t i*X (x i) ω) μ :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ => aemeasurable_const.mul (hg.1 (x i))
  have hmoment := integral_sq_of_map_gaussianReal_zero hmeas hv
  have hi (i j : J) : Integrable (fun ω => (t i*t j)*(X (x i) ω*X (x j) ω)) μ :=
    ((hg.memLp (x i) 2 (by simp)).integrable_mul (hg.memLp (x j) 2 (by simp))).const_mul _
  have hquad : (∫ ω, (∑ i, t i*X (x i) ω)^2 ∂μ) =
      ∑ i, ∑ j, t i*t j*(∫ ω, X (x i) ω*X (x j) ω ∂μ) := by
    have heq : (fun ω => (∑ i, t i*X (x i) ω)^2) =
        fun ω => ∑ i, ∑ j, (t i*t j)*(X (x i) ω*X (x j) ω) := by
      funext ω
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq, integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
    simp only [integral_const_mul]
  rw [← hquad, hmoment, Real.toNNReal_coe]
  exact hv

/-- Every finite mixed family has the exact centered Gaussian law with the scaled
q3 derivative covariance quadratic form, including repeated observation points. -/
theorem q3Shell_derivative_linearCombination_law (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : ℤ) {J : Type} [Fintype J] (o : J → ShellDerivativeObservation) (t : J → ℝ) :
    (ShellField.shellMarginalLaw M.P k).toMeasure.map (fun j => ∑ i, t i*shellDerivativeEval (o i) j) =
      gaussianReal 0 (Real.toNNReal (∑ i, ∑ l, t i*t l*q3ShellDerivativeCovariance M h k (o i) (o l))) := by
  have hc := (q3Shell_stored_derivatives_gaussian M h hM k).map_linearCombination_covariance o t
  simpa only [q3Shell_stored_derivative_covariance M h hM k] using hc

end
end ASDExplicitGamma.Gaussian

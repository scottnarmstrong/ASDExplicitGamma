module

public import ASDExplicitGamma.Gaussian.SupMeanFirstCovariance
public import ASDExplicitGamma.Gaussian.SupMeanGaussianMoments
public import ASDExplicitGamma.Gaussian.WaveGateConstants

/-! Exact first-derivative variance and Frobenius trace for the physical shell. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- The scalar-gradient coordinates scaled by sqrt(2) retain the planar skew
matrix Frobenius payment exactly. -/
def supMeanShellFirstCoordinates (x : Vec 2) (i : Fin 2) (j : ShellField 2) : ℝ :=
  Real.sqrt 2 * shellDerivativeEval (.first x (basisVec i)) j

/-- These are actual jointly Gaussian derivative coordinates, not independent
surrogates for the tensor entries. -/
theorem supMean_shell_first_coordinates_gaussian (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (x : Vec 2) :
    IsCenteredGaussianFamily (ShellField.shellMarginalLaw M.P k).toMeasure
      (supMeanShellFirstCoordinates x) := by
  have hg := (q3Shell_stored_derivatives_gaussian M h hM k).finite_linear_image
    (fun (i : Fin 2) (_ : Fin 1) => .first x (basisVec i))
    (fun (_ : Fin 2) (_ : Fin 1) => Real.sqrt 2)
  simpa only [Fin.sum_univ_one, supMeanShellFirstCoordinates] using! hg

/-- The actual squared first-tensor norm has the source trace tau_1. -/
theorem supMean_shell_first_tensor_trace (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (x : Vec 2) :
    (∑ i : Fin 2, ∫ j, (supMeanShellFirstCoordinates x i j)^2
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) =
        waveTau1*(h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))*((3:ℝ)^k)⁻¹^2 := by
  have hh (i : Fin 2) : (∫ j, (supMeanShellFirstCoordinates x i j)^2
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) =
        2*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))*((3:ℝ)^k)⁻¹^2*(78/5:ℝ)) := by
    simp only [supMeanShellFirstCoordinates, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      integral_const_mul]
    have he := supMean_shell_first_covariance_diagonal M h hM k x (basisVec i) (basisVec i)
    simp only [← pow_two] at he
    rw [he]
    fin_cases i <;> norm_num [basisVec_apply]
  simp only [hh, Fin.sum_univ_two, waveTau1, waveMu1, waveR1]
  ring

/-- The sharp covariance-trace payment at the base point of the first-derivative
chain, with every physical shell variance and length retained. -/
theorem supMean_shell_first_tensor_mean (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (x : Vec 2) :
    (∫ j, ‖(WithLp.toLp 2 (fun i => supMeanShellFirstCoordinates x i j) :
      EuclideanSpace ℝ (Fin 2))‖ ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
        Real.sqrt (waveTau1*(h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))*((3:ℝ)^k)⁻¹^2) := by
  have hh := supMean_gaussian_tensor_mean_le (ShellField.shellMarginalLaw M.P k).toMeasure
    (supMeanShellFirstCoordinates x) (supMean_shell_first_coordinates_gaussian M h hM k x)
  rw [supMean_shell_first_tensor_trace M h hM k x] at hh
  exact hh

end
end ASDExplicitGamma.Gaussian

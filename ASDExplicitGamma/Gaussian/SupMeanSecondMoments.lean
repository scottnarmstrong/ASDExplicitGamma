module

public import ASDExplicitGamma.Gaussian.SupMeanShellJetCovariance
public import ASDExplicitGamma.Gaussian.SupMeanGaussianMoments
public import ASDExplicitGamma.Gaussian.WaveGateConstants

/-! The actual stored Hessian has the exact source Frobenius trace payment. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
open scoped BigOperators
noncomputable section

/-- Scalar Hessian entries with their exact planar skew Frobenius factor. -/
def supMeanShellSecondCoordinates (x : Vec 2) (i : Fin 2 × Fin 2) (j : ShellField 2) : ℝ :=
  Real.sqrt 2 * shellDerivativeEval (.second x (basisVec i.1) (basisVec i.2)) j

/-- Every coordinate is the actual stored Hessian under its joint Gaussian law. -/
theorem supMean_shell_second_coordinates_gaussian (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (x : Vec 2) :
    IsCenteredGaussianFamily (ShellField.shellMarginalLaw M.P k).toMeasure
      (supMeanShellSecondCoordinates x) := by
  have hg := (q3Shell_stored_derivatives_gaussian M h hM k).finite_linear_image
    (fun (i : Fin 2 × Fin 2) (_ : Fin 1) => .second x (basisVec i.1) (basisVec i.2))
    (fun (_ : Fin 2 × Fin 2) (_ : Fin 1) => Real.sqrt 2)
  simpa only [Fin.sum_univ_one, supMeanShellSecondCoordinates] using! hg

/-- The exact physical Hessian trace is tau_2 times variance over length^4. -/
theorem supMean_shell_second_tensor_trace (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (x : Vec 2) :
    (∑ i : Fin 2 × Fin 2, ∫ j, (supMeanShellSecondCoordinates x i j)^2
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) =
        waveTau2*(h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^4 := by
  have hh (i : Fin 2 × Fin 2) : (∫ j, (supMeanShellSecondCoordinates x i j)^2
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) =
        2*q3ScaledJetCovariance (h^2*(3:ℝ)^(2*M.gamma*(k:ℝ))) ((3:ℝ)^k)
          (.second i.1 i.2) (.second i.1 i.2) x x := by
    simp only [supMeanShellSecondCoordinates, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      integral_const_mul]
    have he := supMean_shell_coordinate_covariance M h hM k (.second i.1 i.2) (.second i.1 i.2) x x
    simp only [supMeanJetObservation, ← pow_two] at he
    rw [he]
  simp only [hh, Fintype.sum_prod_type, Fin.sum_univ_two,
    q3ScaledJetCovariance_second_diagonal, waveTau2, waveMu2, waveR1, waveR2]
  norm_num
  ring

/-- The source square-root trace payment at the Hessian chain's base point. -/
theorem supMean_shell_second_tensor_mean (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (x : Vec 2) :
    (∫ j, ‖(WithLp.toLp 2 (fun i => supMeanShellSecondCoordinates x i j) :
      EuclideanSpace ℝ (Fin 2 × Fin 2))‖ ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
        Real.sqrt (waveTau2*(h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^4) := by
  have hh := supMean_gaussian_tensor_mean_le (ShellField.shellMarginalLaw M.P k).toMeasure
    (supMeanShellSecondCoordinates x) (supMean_shell_second_coordinates_gaussian M h hM k x)
  rw [supMean_shell_second_tensor_trace M h hM k x] at hh
  exact hh

end
end ASDExplicitGamma.Gaussian

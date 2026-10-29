module

public import ASDExplicitGamma.Gaussian.SupMeanShellKernel
public import ASDExplicitGamma.Gaussian.SupMeanGaussianKernelVariance
public import ASDExplicitGamma.Gaussian.SupMeanKernelProjectionIncrement

/-! Sharp increment covariance operator bounds for the actual stored shell tensors. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- Every actual tensor-increment projection has the exact variance of its
common white-noise kernel increment. -/
theorem supMean_shell_tensor_increment_variance_eq (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet)
    (a : ι → ℝ) (x y : Vec 2) :
    Var[(fun j => ∑ i, a i*(supMeanShellJetScalar (o i) y j-supMeanShellJetScalar (o i) x j));
      (ShellField.shellMarginalLaw M.P k).toMeasure] =
        ‖∑ i, a i • (supMeanShellJetKernel M h k (o i) y-supMeanShellJetKernel M h k (o i) x)‖^2 := by
  have hg := supMean_gaussian_difference_family (supMean_shell_jets_gaussian M h hM k)
    (fun i => (o i,y)) (fun i => (o i,x))
  apply supMean_gaussian_kernel_combination_variance _ _ hg
  intro i j
  exact supMean_gaussian_kernel_difference_covariance (ShellField.shellMarginalLaw M.P k).toMeasure
    (fun p : Q3SpatialJet × Vec 2 => supMeanShellJetScalar p.1 p.2)
    (supMean_shell_jets_gaussian M h hM k)
    (fun p : Q3SpatialJet × Vec 2 => supMeanShellJetKernel M h k p.1 p.2)
    (fun p q => supMean_shell_jet_kernel_covariance M h hM k p.1 q.1 p.2 q.2)
    (o i,y) (o i,x) (o j,y) (o j,x)

/-- The actual gradient increments use ell_2, without a covariance trace loss. -/
theorem supMean_shell_first_projection_increment (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (a : Fin 2 → ℝ) (x y : Vec 2) :
    Var[(fun j => ∑ i, a i*(supMeanShellJetScalar (.first i) y j-supMeanShellJetScalar (.first i) x j));
      (ShellField.shellMarginalLaw M.P k).toMeasure] ≤
        (waveEll2^2*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^4))*(∑ i, a i^2)*
          ((y-x) 0^2+(y-x) 1^2) := by
  rw [supMean_shell_tensor_increment_variance_eq M h hM k]
  have hh := supMean_kernel_first_projection_increment (supMeanShellKernelAmplitude M h k)
    (supMeanShellKernelLength k) a x y
  simpa only [supMeanShellJetKernel, supMean_shell_kernel_amplitude_sq, supMeanShellKernelLength] using! hh

/-- The actual stored Hessian increments use ell_3, with no random C3-shell premise. -/
theorem supMean_shell_second_projection_increment (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (a : Fin 2 × Fin 2 → ℝ) (x y : Vec 2) :
    Var[(fun j => ∑ i, a i*(supMeanShellJetScalar (.second i.1 i.2) y j-
      supMeanShellJetScalar (.second i.1 i.2) x j)); (ShellField.shellMarginalLaw M.P k).toMeasure] ≤
        (waveEll3^2*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^6))*(∑ i, a i^2)*
          ((y-x) 0^2+(y-x) 1^2) := by
  rw [supMean_shell_tensor_increment_variance_eq M h hM k]
  have hh := supMean_kernel_second_projection_increment (supMeanShellKernelAmplitude M h k)
    (supMeanShellKernelLength k) a x y
  simpa only [supMeanShellJetKernel, supMean_shell_kernel_amplitude_sq, supMeanShellKernelLength] using! hh

end
end ASDExplicitGamma.Gaussian

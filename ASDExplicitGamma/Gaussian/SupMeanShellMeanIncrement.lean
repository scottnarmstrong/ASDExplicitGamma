module

public import ASDExplicitGamma.Gaussian.SupMeanShellKernel
public import ASDExplicitGamma.Gaussian.SupMeanKernelMeanIncrement
public import ASDExplicitGamma.Gaussian.SupMeanKernelDifferenceMoment

/-! Exact tensor increment means under the actual frozen shell law. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
open scoped BigOperators
noncomputable section

/-- Each actual stored tensor increment has its exact Hilbert kernel distance
as its second moment. -/
theorem supMean_shell_jet_difference_sq (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (o : Q3SpatialJet) (x y : Vec 2) :
    (∫ j, (supMeanShellJetScalar o y j-supMeanShellJetScalar o x j)^2
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) =
        ‖supMeanShellJetKernel M h k o y-supMeanShellJetKernel M h k o x‖^2 := by
  exact supMean_gaussian_kernel_difference_sq (ShellField.shellMarginalLaw M.P k).toMeasure
    (fun p : Q3SpatialJet × Vec 2 => supMeanShellJetScalar p.1 p.2)
    (supMean_shell_jets_gaussian M h hM k)
    (fun p : Q3SpatialJet × Vec 2 => supMeanShellJetKernel M h k p.1 p.2)
    (fun p q => supMean_shell_jet_kernel_covariance M h hM k p.1 q.1 p.2 q.2) (o,y) (o,x)

/-- The first-tensor actual Gaussian mean increment has the exact half-trace
payment used by center-to-child chaining. -/
theorem supMean_shell_first_mean_increment (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (x y : Vec 2) :
    (∫ j, ‖(WithLp.toLp 2 (fun i : Fin 2 =>
      supMeanShellJetScalar (.first i) y j-supMeanShellJetScalar (.first i) x j) :
        EuclideanSpace ℝ (Fin 2))‖ ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
          Real.sqrt ((waveTau2/2)*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^4)*
            ((y-x) 0^2+(y-x) 1^2)) := by
  have hg := supMean_gaussian_difference_family (supMean_shell_jets_gaussian M h hM k)
    (fun i : Fin 2 => (Q3SpatialJet.first i,y)) (fun i : Fin 2 => (Q3SpatialJet.first i,x))
  have hm := supMean_gaussian_tensor_mean_le (ShellField.shellMarginalLaw M.P k).toMeasure
    (fun i : Fin 2 => fun j => supMeanShellJetScalar (.first i) y j-supMeanShellJetScalar (.first i) x j) hg
  simp only [supMean_shell_jet_difference_sq M h hM k] at hm
  have hb := supMean_kernel_first_increment_trace (supMeanShellKernelAmplitude M h k)
    (supMeanShellKernelLength k) x y
  have hb' : (∑ i : Fin 2, ‖supMeanShellJetKernel M h k (.first i) y-
      supMeanShellJetKernel M h k (.first i) x‖^2) ≤
        (waveTau2/2)*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^4)*((y-x) 0^2+(y-x) 1^2) := by
    simpa only [supMean_shell_kernel_amplitude_sq, supMeanShellKernelLength, supMeanShellJetKernel] using! hb
  exact hm.trans (Real.sqrt_le_sqrt hb')

/-- The stored Hessian actual mean increment has the tau_3/2 payment, proved
using the third weak Hilbert kernel rather than a random C3-domain convention. -/
theorem supMean_shell_second_mean_increment (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (x y : Vec 2) :
    (∫ j, ‖(WithLp.toLp 2 (fun i : Fin 2 × Fin 2 =>
      supMeanShellJetScalar (.second i.1 i.2) y j-supMeanShellJetScalar (.second i.1 i.2) x j) :
        EuclideanSpace ℝ (Fin 2 × Fin 2))‖ ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
          Real.sqrt ((waveTau3/2)*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^6)*
            ((y-x) 0^2+(y-x) 1^2)) := by
  have hg := supMean_gaussian_difference_family (supMean_shell_jets_gaussian M h hM k)
    (fun i : Fin 2 × Fin 2 => (Q3SpatialJet.second i.1 i.2,y))
    (fun i : Fin 2 × Fin 2 => (Q3SpatialJet.second i.1 i.2,x))
  have hm := supMean_gaussian_tensor_mean_le (ShellField.shellMarginalLaw M.P k).toMeasure
    (fun i : Fin 2 × Fin 2 => fun j => supMeanShellJetScalar (.second i.1 i.2) y j-
      supMeanShellJetScalar (.second i.1 i.2) x j) hg
  simp only [supMean_shell_jet_difference_sq M h hM k] at hm
  have hb := supMean_kernel_second_increment_trace (supMeanShellKernelAmplitude M h k)
    (supMeanShellKernelLength k) x y
  have hb' : (∑ i : Fin 2 × Fin 2, ‖supMeanShellJetKernel M h k (.second i.1 i.2) y-
      supMeanShellJetKernel M h k (.second i.1 i.2) x‖^2) ≤
        (waveTau3/2)*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^6)*((y-x) 0^2+(y-x) 1^2) := by
    simpa only [supMean_shell_kernel_amplitude_sq, supMeanShellKernelLength, supMeanShellJetKernel] using! hb
  exact hm.trans (Real.sqrt_le_sqrt hb')

end
end ASDExplicitGamma.Gaussian

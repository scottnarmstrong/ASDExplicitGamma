module

public import ASDExplicitGamma.Gaussian.SupMeanKernelTensorBounds
public import ASDExplicitGamma.Gaussian.SupMeanShellJetCovariance

/-! A concrete white-noise kernel for every actual stored shell tensor observation. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
open scoped RealInnerProductSpace
noncomputable section

/-- The physical triadic shell length, including negative integer labels. -/
def supMeanShellKernelLength (k : ℤ) : {l : ℝ // 0 < l} := ⟨(3:ℝ)^k, by positivity⟩

/-- Nonnegative physical shell amplitude from its actual variance. -/
def supMeanShellKernelAmplitude (M : ABKModel 2) (h : ℝ) (k : ℤ) : ℝ :=
  Real.sqrt (h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))

/-- The amplitude has exactly the frozen scaled shell variance. -/
theorem supMean_shell_kernel_amplitude_sq (M : ABKModel 2) (h : ℝ) (k : ℤ) :
    (supMeanShellKernelAmplitude M h k)^2 = h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)) :=
  Real.sq_sqrt (by positivity)

/-- The actual scalar observation with its full planar skew Frobenius factor. -/
def supMeanShellJetScalar (o : Q3SpatialJet) (x : Vec 2) (j : ShellField 2) : ℝ :=
  Real.sqrt 2*shellDerivativeEval (supMeanJetObservation o x) j

/-- The corresponding concrete kernel in the ordinary planar white-noise Hilbert space. -/
def supMeanShellJetKernel (M : ABKModel 2) (h : ℝ) (k : ℤ) (o : Q3SpatialJet) (x : Vec 2) : WhiteNoise :=
  Real.sqrt 2 • q3Section (supMeanShellKernelAmplitude M h k) (supMeanShellKernelLength k)
    (supMeanKernelJetIndex o) x

/-- Every mixed cross-point tensor covariance agrees with that concrete kernel,
without a realization or derivative-covariance premise. -/
theorem supMean_shell_jet_kernel_covariance (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (o p : Q3SpatialJet) (x y : Vec 2) :
    (∫ j, supMeanShellJetScalar o x j*supMeanShellJetScalar p y j
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) =
        ⟪supMeanShellJetKernel M h k o x,supMeanShellJetKernel M h k p y⟫ := by
  have heq : (fun j : ShellField 2 => supMeanShellJetScalar o x j*supMeanShellJetScalar p y j) =
      (fun j => 2*(shellDerivativeEval (supMeanJetObservation o x) j*
        shellDerivativeEval (supMeanJetObservation p y) j)) := by
    funext j
    unfold supMeanShellJetScalar
    calc
      _ = (Real.sqrt 2)^2*(shellDerivativeEval (supMeanJetObservation o x) j*
        shellDerivativeEval (supMeanJetObservation p y) j) := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [heq, integral_const_mul, supMean_shell_coordinate_covariance M h hM]
  unfold supMeanShellJetKernel
  rw [supMean_kernel_skew_jet_covariance, supMean_shell_kernel_amplitude_sq]
  rfl

/-- All these scaled observations retain their actual joint centered Gaussian law. -/
theorem supMean_shell_jets_gaussian (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) :
    IsCenteredGaussianFamily (ShellField.shellMarginalLaw M.P k).toMeasure
      (fun p : Q3SpatialJet × Vec 2 => supMeanShellJetScalar p.1 p.2) := by
  have hh := (q3Shell_stored_derivatives_gaussian M h hM k).finite_linear_image
    (fun (p : Q3SpatialJet × Vec 2) (_ : Fin 1) => supMeanJetObservation p.1 p.2)
    (fun (_ : Q3SpatialJet × Vec 2) (_ : Fin 1) => Real.sqrt 2)
  simpa only [Fin.sum_univ_one, supMeanShellJetScalar] using! hh

end
end ASDExplicitGamma.Gaussian

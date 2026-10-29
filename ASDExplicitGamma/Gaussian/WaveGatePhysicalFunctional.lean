module

public import ASDExplicitGamma.Gaussian.SupMeanShellUnitSupremum
public import ASDExplicitGamma.Gaussian.SupMeanKernelTensorBounds
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Operator.Basic
public import ASDExplicitGamma.Gaussian.SupMeanNormalization
public import ASDExplicitGamma.Gaussian.WaveGateMeanPolynomial

/-! Literal physical derivative size in a fixed deterministic scalar frame. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
noncomputable section

/-- The source derivative size is side times the full gradient supremum plus
side squared times the full Hessian supremum, both in the same scalar frame. -/
def waveGateDerivativeSize (c : Vec 2) (s σ : ℝ) (j : ShellField 2) : ℝ :=
  (s/σ)*‖supMeanShellSquareTensor Q3SpatialJet.first c s j‖+
    (s^2/σ)*‖supMeanShellSquareTensor (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j‖

/-- Exact conversion to unit shell tensors; both derivative orders use the
same actual amplitude and the same fixed physical frame. -/
theorem wave_gate_derivative_size_unit (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (c : Vec 2) (s σ : ℝ) (j : ShellField 2) :
    waveGateDerivativeSize c s σ j =
      (supMeanShellKernelAmplitude M h k/σ)*(s/(3:ℝ)^k)*
        (‖supMeanShellUnitSquareTensor M h k 1 Q3SpatialJet.first c s j‖+
        (s/(3:ℝ)^k)*‖supMeanShellUnitSquareTensor M h k 2
          (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j‖) := by
  have hB := (supMean_shell_kernel_amplitude_pos M h hM k).ne'
  have hL : (3:ℝ)^k ≠ 0 := by positivity
  rw [supMean_shell_unit_square_norm, supMean_shell_unit_square_norm]
  unfold waveGateDerivativeSize
  field_simp

end
end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Gaussian.WaveGatePhysicalFunctional

/-! Actual physical combined supremum means, including the full variance/frame factor. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
noncomputable section

/-- Restore the actual shell amplitude and the one fixed physical frame in the
combined source mean. The side ratio is not replaced until the buffer step. -/
theorem wave_gate_physical_mean (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : ℤ) (c : Vec 2) (s σ : ℝ) (hs : 0 < s) (hσ : 0 < σ) :
    (∫ j, waveGateDerivativeSize c s σ j ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
      (supMeanShellKernelAmplitude M h k/σ)*(s/(3:ℝ)^k)*waveMeanAt (s/(3:ℝ)^k) := by
  let μ := (ShellField.shellMarginalLaw M.P k).toMeasure
  let ρ := s/(3:ℝ)^k
  let α := (supMeanShellKernelAmplitude M h k/σ)*ρ
  let Z := fun j => ‖supMeanShellUnitSquareTensor M h k 1 Q3SpatialJet.first c s j‖
  let W := fun j => ‖supMeanShellUnitSquareTensor M h k 2
    (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j‖
  have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
  have hα : 0 ≤ α := by
    dsimp only [α]
    exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hσ.le) hρ
  obtain ⟨hZ,bZ⟩ := supMean_shell_unit_first_supremum_mean M h hM k c s hs
  obtain ⟨hW,bW⟩ := supMean_shell_unit_second_supremum_mean M h hM k c s hs
  have he : waveGateDerivativeSize c s σ = fun j => α*(Z j+ρ*W j) := by
    funext j
    exact wave_gate_derivative_size_unit M h hM k c s σ j
  rw [he, integral_const_mul, integral_add hZ (hW.const_mul ρ), integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ hα
  change (∫ j, Z j ∂μ)+ρ*(∫ j, W j ∂μ) ≤ waveMeanAt ρ
  rw [← wave_mean_at_assembly]
  exact add_le_add bZ (mul_le_mul_of_nonneg_left bW hρ)

/-- The source buffer coefficient is an upper bound whenever rho≤3^(-41). -/
theorem wave_gate_buffer_mean (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : ℤ) (c : Vec 2) (s σ : ℝ) (hs : 0 < s) (hσ : 0 < σ)
    (hρ : s/(3:ℝ)^k ≤ waveBufferRho) :
    (∫ j, waveGateDerivativeSize c s σ j ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
      (supMeanShellKernelAmplitude M h k/σ)*(s/(3:ℝ)^k)*waveBufferMean := by
  have hr : 0 ≤ s/(3:ℝ)^k := by positivity
  exact (wave_gate_physical_mean M h hM k c s σ hs hσ).trans
    (mul_le_mul_of_nonneg_left ((wave_mean_at_mono hr hρ).trans_eq wave_mean_at_buffer)
      (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hσ.le) hr))

end
end ASDExplicitGamma.Gaussian

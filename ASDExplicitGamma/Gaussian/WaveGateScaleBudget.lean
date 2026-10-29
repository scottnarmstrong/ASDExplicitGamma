module

public import ASDExplicitGamma.Gaussian.WaveGateVariance
public import ASDExplicitGamma.Gaussian.WaveGatePowerIdentities
public import ASDExplicitGamma.Gaussian.SupMeanShellKernel

/-! The literal physical amplitude/side budget in the old buffered true frame. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3

/-- Actual shell amplitude times actual side ratio, measured only in the
true sigmaBar at j+40. Smaller observation squares preserve the same budget. -/
theorem wave_gate_scale_sq_bound (M : ABKModel 2) (h : ℝ) (j Λ : ℤ)
    (hj : shellVarianceSum h M.gamma (j+40)/4 ≤ (Annealed.sigmaBar M (j+40):ℝ)^2) (s : ℝ) (hs : 0 ≤ s) (hside : s ≤ (3:ℝ)^j) :
    ((supMeanShellKernelAmplitude M h (j+40+Λ)/(Annealed.sigmaBar M (j+40):ℝ))*
      (s/(3:ℝ)^(j+40+Λ)))^2 ≤
        9*M.gamma*(3:ℝ)^(-80+(-2+2*M.gamma)*(Λ:ℝ)) := by
  have hr : s/(3:ℝ)^(j+40+Λ) ≤ (3:ℝ)^(-(40:ℝ)-(Λ:ℝ)) := by
    rw [← wave_side_shell_ratio j Λ]
    exact div_le_div_of_nonneg_right hside (by positivity)
  have hr0 : 0 ≤ s/(3:ℝ)^(j+40+Λ) := div_nonneg hs (by positivity)
  have hvar := wave_normalized_shell_variance_of_lower M h (j+40) Λ hj
  rw [mul_pow, div_pow, supMean_shell_kernel_amplitude_sq]
  calc
    _ ≤ (9*M.gamma*(3:ℝ)^(2*M.gamma*(Λ:ℝ)))*((3:ℝ)^(-(40:ℝ)-(Λ:ℝ)))^2 :=
      mul_le_mul hvar (pow_le_pow_left₀ hr0 hr 2) (sq_nonneg _)
        (by have hg := M.shellPrefix.gamma_pos; positivity)
    _ = _ := wave_variance_side_power M.gamma (Λ:ℝ)

end ASDExplicitGamma.Gaussian

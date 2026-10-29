module

public import ASDExplicitGamma.Gaussian.WaveGatePhysicalMean
public import ASDExplicitGamma.Gaussian.WaveGatePhysicalConcentration

/-! Turn the exact physical supremum estimates into the raw derivative-failure tail. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
noncomputable section

/-- The raw failure bound retains the small geometric ratio and full physical
amplitude. The twice-the-mean premise here is an ordinary scalar inequality;
the numerical wave gate discharges it at every positive label. -/
theorem wave_gate_raw_tail (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : ℤ) (c : Vec 2) (s σ : ℝ) (hs : 0 < s) (hσ : 0 < σ)
    (hρ : s/(3:ℝ)^k ≤ waveBufferRho) (T : ℝ) (hT : 0 < T)
    (hm : (supMeanShellKernelAmplitude M h k/σ)*(s/(3:ℝ)^k)*waveBufferMean ≤ T/2) :
    (ShellField.shellMarginalLaw M.P k).toMeasure.real {j | T < waveGateDerivativeSize c s σ j} ≤
      Real.exp (-T^2/(8*((supMeanShellKernelAmplitude M h k/σ)*(s/(3:ℝ)^k)*waveBufferEll)^2)) := by
  let α := (supMeanShellKernelAmplitude M h k/σ)*(s/(3:ℝ)^k)
  let C := α*waveEllAt (s/(3:ℝ)^k)
  let D := α*waveBufferEll
  have ha : 0 < α := mul_pos (div_pos (supMean_shell_kernel_amplitude_pos M h hM k) hσ)
    (div_pos hs (by positivity))
  have hr : 0 ≤ s/(3:ℝ)^k := by positivity
  have hC : 0 < C := mul_pos ha (wave_ell_at_pos hr)
  have hCD : C ≤ D := mul_le_mul_of_nonneg_left
    ((wave_ell_at_mono hρ).trans_eq wave_ell_at_buffer) ha.le
  have hD : 0 < D := hC.trans_le hCD
  have hm' := (wave_gate_buffer_mean M h hM k c s σ hs hσ hρ).trans hm
  have hc := wave_gate_physical_concentration M h hM k c s σ hs hσ (T/2) (by positivity)
  have hsub : {j | T < waveGateDerivativeSize c s σ j} ⊆
      {j | T/2 ≤ waveGateDerivativeSize c s σ j-
        ∫ z, waveGateDerivativeSize c s σ z ∂(ShellField.shellMarginalLaw M.P k).toMeasure} := by
    intro j hj
    change T < waveGateDerivativeSize c s σ j at hj
    change T/2 ≤ waveGateDerivativeSize c s σ j-
      ∫ z, waveGateDerivativeSize c s σ z ∂(ShellField.shellMarginalLaw M.P k).toMeasure
    linarith only [hj,hm']
  apply ((measureReal_mono hsub).trans hc).trans
  apply Real.exp_le_exp.mpr
  change -(T/2)^2/(2*C^2) ≤ -T^2/(8*D^2)
  have hd : 2*C^2 ≤ 2*D^2 := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hC.le hCD 2) (by norm_num)
  have hh := div_le_div_of_nonneg_left (sq_nonneg (T/2)) (by positivity : 0 < 2*C^2) hd
  calc
    _ = -((T/2)^2/(2*C^2)) := neg_div _ _
    _ ≤ -((T/2)^2/(2*D^2)) := neg_le_neg hh
    _ = _ := by ring

end
end ASDExplicitGamma.Gaussian

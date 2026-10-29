module

public import ASDExplicitGamma.Gaussian.WaveGateRawTail
public import ASDExplicitGamma.Gaussian.WaveGateScaleBudget
public import ASDExplicitGamma.Gaussian.WaveGateExponentBudget

/-! Source raw wave failures at the actual buffered label and true scalar frame. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
noncomputable section

/-- Every elementary wave failure has the exact source rate, including the
allowance for all 364*3^80 elementary events. The old native premise and fixed
frame are both at j+40, while the fresh shell is j+40+Lambda. -/
theorem wave_gate_elementary_tail (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (j Λ : ℤ) (hj : shellVarianceSum h M.gamma (j+40)/4 ≤ (Annealed.sigmaBar M (j+40):ℝ)^2) (hΛ : 1 ≤ Λ)
    (η : ℝ) (hη : 0 < η)
    (hg : M.gamma ≤ 1/64)
    (hm : M.gamma ≤ η^2*3^80/(12*waveBufferMean^2))
    (ht : M.gamma ≤ η^2*3^80/(60*waveBufferEll^2*(1200+(6+(11/5:ℝ)*40)/5)))
    (c : Vec 2) (s : ℝ) (hs : 0 < s) (hside : s ≤ (3:ℝ)^j) :
    (ShellField.shellMarginalLaw M.P (j+40+Λ)).toMeasure.real
      {F | η*(3:ℝ)^(-(Λ:ℝ)/8) < waveGateDerivativeSize c s (Annealed.sigmaBar M (j+40):ℝ) F} ≤
      Real.exp (-(1200+(6+(11/5:ℝ)*40)/5)*(3:ℝ)^((3/2:ℝ)*(Λ:ℝ))) := by
  let σ : ℝ := Annealed.sigmaBar M (j+40)
  let α := (supMeanShellKernelAmplitude M h (j+40+Λ)/σ)*(s/(3:ℝ)^(j+40+Λ))
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M (j+40)).1
  have hα : 0 < α := mul_pos (div_pos (supMean_shell_kernel_amplitude_pos M h hM _) hσ)
    (div_pos hs (by positivity))
  have hbudget := wave_gate_scale_sq_bound M h j Λ hj s hs.le hside
  have hratio : s/(3:ℝ)^(j+40+Λ) ≤ waveBufferRho := by
    apply le_trans ?_ (wave_label_ratio_le_buffer Λ hΛ)
    rw [← wave_side_shell_ratio j Λ]
    exact div_le_div_of_nonneg_right hside (by positivity)
  have hmean := wave_twice_mean_budget M.gamma η α hη hα.le hg Λ hΛ hbudget hm
  have hraw := wave_gate_raw_tail M h hM (j+40+Λ) c s σ hs hσ hratio
    (η*(3:ℝ)^(-(Λ:ℝ)/8)) (by positivity) hmean
  apply hraw.trans
  apply Real.exp_le_exp.mpr
  have hexp := wave_exponent_budget M.gamma η α waveBufferEll
    (1200+(6+(11/5:ℝ)*40)/5) M.shellPrefix.gamma_pos hα wave_buffer_ell_pos
    (by norm_num) hg Λ hΛ hbudget ht
  have hh := neg_le_neg hexp
  simpa only [neg_div, neg_mul] using! hh

end
end ASDExplicitGamma.Gaussian

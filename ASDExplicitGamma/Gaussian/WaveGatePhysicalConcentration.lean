module

public import ASDExplicitGamma.Gaussian.WaveGatePhysicalFunctional
public import ASDExplicitGamma.Gaussian.SupMeanShellPairConcentration

/-! Actual shell concentration in one fixed physical frame with sharp source metric. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
noncomputable section

/-- Exact restoration of the combined CM constant from the unit tensor law. -/
theorem wave_gate_cm_scale (B L s σ : ℝ) (hB : 0 ≤ B) (hL : 0 < L) :
    (s/σ)*Real.sqrt (waveEll1^2*(B^2/L^2))+
      (s^2/σ)*Real.sqrt (waveEll2^2*(B^2/L^4)) =
      (B/σ)*(s/L)*waveEllAt (s/L) := by
  rw [supMean_sqrt_operator_variance_scale waveEll1 B L (Real.sqrt_nonneg _) hB hL]
  have hsecond : Real.sqrt (waveEll2^2*(B^2/L^4)) = (B/L^2)*waveEll2 := by
    rw [show L^4 = (L^2)^2 by ring]
    exact supMean_sqrt_operator_variance_scale waveEll2 B (L^2) (Real.sqrt_nonneg _) hB (by positivity)
  rw [hsecond]
  unfold waveEllAt
  ring

/-- Sharp concentration of the literal physical derivative size under its
actual frozen shell law. Its frame is the supplied single deterministic sigma;
the gate application specializes it to sigmaBar at the old buffered label. -/
theorem wave_gate_physical_concentration (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : ℤ) (c : Vec 2) (s σ : ℝ) (hs : 0 < s) (hσ : 0 < σ) (t : ℝ) (ht : 0 ≤ t) :
    (ShellField.shellMarginalLaw M.P k).toMeasure.real
      {j | t ≤ waveGateDerivativeSize c s σ j-
        ∫ z, waveGateDerivativeSize c s σ z ∂(ShellField.shellMarginalLaw M.P k).toMeasure} ≤
      Real.exp (-t^2/(2*((supMeanShellKernelAmplitude M h k/σ)*(s/(3:ℝ)^k)*
        waveEllAt (s/(3:ℝ)^k))^2)) := by
  have hh := supMean_shell_pair_tail M h hM k c s hs (s/σ) (s^2/σ)
    (div_pos hs hσ) (div_nonneg (sq_nonneg s) hσ.le) t ht
  dsimp only at hh
  rw [wave_gate_cm_scale (supMeanShellKernelAmplitude M h k) ((3:ℝ)^k) s σ
    (Real.sqrt_nonneg _) (by positivity)] at hh
  exact hh

end
end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Numerics.Wave.Gates
public import ASDExplicitGamma.Model.Q3DerivativeMoments

/-! # DEF-WAVE-GATE-CONSTANTS

Exact transcription of the wave-gate constants.
The absolute constants have no hypotheses; the buffer is fixed at b=40.
The r/mu/tau/ell definitions and the complete rho_b, ell_b, a_b formulas below
are literal. Covariance traces are linked to MO-Q3-DERIVATIVE-MOMENTS below;
concentration and analytic supremum bounds are separate obligations. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian

noncomputable def waveR1 : ℝ := 78 / 5
noncomputable def waveR2 : ℝ := 3432 / 5
noncomputable def waveR3 : ℝ := 61776
noncomputable def waveMu1 : ℝ := 2 * waveR1
noncomputable def waveMu2 : ℝ := 2 * waveR2 + 2 * waveR1 ^ 2
noncomputable def waveMu3 : ℝ := 2 * waveR3 + 6 * waveR1 * waveR2
noncomputable def waveTau1 : ℝ := 2 * waveMu1
noncomputable def waveTau2 : ℝ := 2 * waveMu2
noncomputable def waveTau3 : ℝ := 2 * waveMu3
noncomputable def waveEll1 : ℝ := Real.sqrt (2 * waveR1)
noncomputable def waveEll2 : ℝ := Real.sqrt (2 * (waveR2 + waveR1 ^ 2))
noncomputable def waveEll3 : ℝ := Real.sqrt (2 * waveMu3)
noncomputable def waveBufferRho : ℝ := (3 : ℝ) ^ (-(40 : ℤ) - 1)
noncomputable def waveBufferEll : ℝ := waveEll1 + waveBufferRho * waveEll2
noncomputable def waveBufferMean : ℝ :=
  Real.sqrt waveTau1 + waveBufferRho *
    ((3 / 2) * Real.sqrt waveTau2 + 2 * Real.sqrt (Real.log 2) * waveEll2) +
  waveBufferRho ^ 2 *
    ((1 / 2) * Real.sqrt waveTau3 + 2 * Real.sqrt (Real.log 2) * waveEll3)

/-- Exact tensor traces and increment metric constants of the product-q3 model. -/
theorem wave_constants_values :
    waveTau1 = 312 / 5 ∧ waveTau2 = 92976 / 25 ∧ waveTau3 = 9389952 / 25 ∧
    waveEll1 = Real.sqrt (156 / 5) ∧ waveEll2 = Real.sqrt (46488 / 25) ∧
    waveEll3 = Real.sqrt (9389952 / 25) := by
  norm_num [waveTau1, waveTau2, waveTau3, waveMu1, waveMu2, waveMu3,
    waveR1, waveR2, waveR3, waveEll1, waveEll2, waveEll3]

/-- The numerical gate's exact mean formula is the source derivative package. -/
theorem waveBufferMean_eq_numeric : waveBufferMean = Numerics.Wave.waveA := by
  have hρ : waveBufferRho = (Numerics.Wave.waveRho : ℝ) := by
    norm_num [waveBufferRho, Numerics.Wave.waveRho, zpow_neg]
  obtain ⟨h1, h2, h3, _, he2, he3⟩ := wave_constants_values
  simp only [waveBufferMean, h1, h2, h3, he2, he3, hρ, Numerics.Wave.waveA]

/-- The numerical gate's metric formula is the source Lipschitz package. -/
theorem waveBufferEll_eq_numeric : waveBufferEll = Numerics.Wave.waveEll := by
  have hρ : waveBufferRho = (Numerics.Wave.waveRho : ℝ) := by
    norm_num [waveBufferRho, Numerics.Wave.waveRho, zpow_neg]
  obtain ⟨_, _, _, he1, he2, _⟩ := wave_constants_values
  simp only [waveBufferEll, he1, he2, hρ, Numerics.Wave.waveEll]

end ASDExplicitGamma.Gaussian

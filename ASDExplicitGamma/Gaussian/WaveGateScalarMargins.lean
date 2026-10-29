module

public import ASDExplicitGamma.Gaussian.WaveGatePowerMargins

/-! Pure algebra of the source mean and rate gates, separated from physical powers. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian

/-- The exact mean gate pays four times the squared source mean at every
positive label once its residual power is at least three. -/
theorem wave_mean_gate_algebra (U D p : ℝ) (hU : 0 ≤ U) (hp : 3 ≤ p)
    (hgate : 12*D ≤ U) : 36*D ≤ U*p := by
  have hh := mul_le_mul_of_nonneg_left hp hU
  nlinarith only [hgate,hh]

/-- The exact tail gate pays the rate coefficient after retaining the
six-fifths residual power. -/
theorem wave_tail_gate_algebra (U D R p : ℝ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hp : (6/5:ℝ) ≤ p) (hgate : 60*D*R ≤ U) : 72*D*R ≤ U*p := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hh := mul_le_mul_of_nonneg_right hgate hp0
  have hl := mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 60) hD) hR)
  nlinarith only [hh,hl]

/-- Convert the source mean gate to a square comparison with no square-root loss. -/
theorem wave_mean_gate_square (γ η A p : ℝ) (hA : 0 < A) (hp : 3 ≤ p)
    (hg : γ ≤ η^2*3^80/(12*A^2)) :
    36*γ*A^2 ≤ η^2*3^80*p := by
  have hgate := (le_div_iff₀ (by positivity : (0:ℝ) < 12*A^2)).mp hg
  have hh := wave_mean_gate_algebra (η^2*3^80) (γ*A^2) p (by positivity) hp (by nlinarith only [hgate])
  nlinarith only [hh]

/-- Convert the source tail gate to the raw exponent comparison. -/
theorem wave_tail_gate_exponent (γ η E R p : ℝ) (hγ : 0 < γ) (hE : 0 < E)
    (hR : 0 < R) (hp : (6/5:ℝ) ≤ p)
    (hg : γ ≤ η^2*3^80/(60*E^2*R)) :
    R ≤ η^2*3^80*p/(72*γ*E^2) := by
  have hgate := (le_div_iff₀ (by positivity : (0:ℝ) < 60*E^2*R)).mp hg
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 72*γ*E^2)).mpr
  have hh := wave_tail_gate_algebra (η^2*3^80) (γ*E^2) R p (by positivity) hR.le hp
    (by nlinarith only [hgate])
  nlinarith only [hh]

end ASDExplicitGamma.Gaussian

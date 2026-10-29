module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandEnvelope
public import ASDExplicitGamma.Scalar.UpperCellEnergyEnvelopeConstants

/-! Deterministic insertion of full-band covariance roots into the envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Gaussian Model
open Algsuperdiff.Section3
noncomputable section

/-- The first three scaled covariance roots control the actual chaining mean
profile, without splitting into shellwise supremum norms. -/
theorem upper_cell_band_envelope_mean_scaling {d : ℕ}
    (M : ABKModel 2) (h : ℝ) (k : Fin d → ℤ) (w : Fin d → ℝ)
    (R t delta : ℝ)
    (h1 : R * Real.sqrt (upperCellBandVariance M h k w 1) ≤ t)
    (h2 : R^2 * Real.sqrt (upperCellBandVariance M h k w 2) ≤ t*delta)
    (h3 : R^3 * Real.sqrt (upperCellBandVariance M h k w 3) ≤ t*delta^2) :
    upperCellBandEnvelopeMean M h k w R R (R^2) ≤ t*waveMeanAt delta := by
  have ht1 : 0 ≤ waveTau1 := by norm_num [waveTau1,waveMu1,waveR1]
  have ht2 : 0 ≤ waveTau2 := by norm_num [waveTau2,waveMu2,waveR1,waveR2]
  have hc2 : 0 ≤ (3/2:ℝ)*Real.sqrt waveTau2+2*Real.sqrt (Real.log 2)*waveEll2 := by
    unfold waveEll2
    positivity
  have hc3 : 0 ≤ Real.sqrt waveTau3/2+2*Real.sqrt (Real.log 2)*waveEll3 := by
    unfold waveEll3
    positivity
  have hh := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg waveTau1))
    (mul_le_mul_of_nonneg_left h2 hc2)) (mul_le_mul_of_nonneg_left h3 hc3)
  unfold upperCellBandEnvelopeMean waveMeanAt
  rw [Real.sqrt_mul ht1, Real.sqrt_mul ht2]
  convert hh using 1 <;> ring

/-- The sharp combined operator constant scales by the same full-band roots. -/
theorem upper_cell_band_envelope_cm_scaling {d : ℕ}
    (M : ABKModel 2) (h : ℝ) (k : Fin d → ℤ) (w : Fin d → ℝ)
    (R t delta : ℝ)
    (h1 : R * Real.sqrt (upperCellBandVariance M h k w 1) ≤ t)
    (h2 : R^2 * Real.sqrt (upperCellBandVariance M h k w 2) ≤ t*delta) :
    upperCellBandEnvelopeCM M h k w R (R^2) ≤ t*waveEllAt delta := by
  have he1 : 0 ≤ waveEll1 := Real.sqrt_nonneg _
  have he2 : 0 ≤ waveEll2 := Real.sqrt_nonneg _
  have hh := add_le_add (mul_le_mul_of_nonneg_left h1 he1)
    (mul_le_mul_of_nonneg_left h2 he2)
  unfold upperCellBandEnvelopeCM waveEllAt
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq he1, Real.sqrt_sq he2]
  convert hh using 1 <;> ring

end
end ASDExplicitGamma.Scalar

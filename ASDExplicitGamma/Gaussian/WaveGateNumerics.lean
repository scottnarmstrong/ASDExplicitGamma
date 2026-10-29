module

public import ASDExplicitGamma.Gaussian.WaveGateConstants
public import ASDExplicitGamma.Statements.GammaZero

/-! Consume the three distinct numerical routes with the actual source formulas. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian

/-- Full-response tau=5*10^15 uses its own eta, without an inverse-tuple substitution. -/
theorem wave_full_numeric_gate (γ : ℝ) (hγ : γ ≤ gammaZero) :
    γ < (Numerics.Wave.fullEta : ℝ) ^ 2 * 3 ^ 80 / (12 * waveBufferMean ^ 2) ∧
    γ < (Numerics.Wave.fullEta : ℝ) ^ 2 * 3 ^ 80 /
      (60 * waveBufferEll ^ 2 * (1200 + (6 + 11 * 40 / 5) / 5)) ∧ γ < 1 / 64 := by
  have hc : γ ≤ (17 / 50000 : ℝ) := hγ
  obtain ⟨hm, ht, hg, hs⟩ := Numerics.Wave.full_gates
  rw [waveBufferMean_eq_numeric, waveBufferEll_eq_numeric]
  exact ⟨hc.trans_lt (hg.trans hm), hc.trans_lt (hg.trans ht), hc.trans_lt hs⟩

/-- Inverse tau=10^10 retains its distinct eta and certified source gate. -/
theorem wave_inverse_numeric_gate (γ : ℝ) (hγ : γ ≤ gammaZero) :
    γ < (Numerics.Wave.inverseEta : ℝ) ^ 2 * 3 ^ 80 / (12 * waveBufferMean ^ 2) ∧
    γ < (Numerics.Wave.inverseEta : ℝ) ^ 2 * 3 ^ 80 /
      (60 * waveBufferEll ^ 2 * (1200 + (6 + 11 * 40 / 5) / 5)) ∧ γ < 1 / 64 := by
  have hc : γ ≤ (17 / 50000 : ℝ) := hγ
  obtain ⟨hm, ht, hg, hs⟩ := Numerics.Wave.inverse_gates
  rw [waveBufferMean_eq_numeric, waveBufferEll_eq_numeric]
  exact ⟨hc.trans_lt (hg.trans hm), hc.trans_lt (hg.trans ht), hc.trans_lt hs⟩

/-- The all-order tuple uses its own mean and tail gates. -/
theorem wave_allorder_numeric_gate (γ : ℝ) (hγ : γ ≤ gammaZero) :
    γ < (Numerics.Wave.allOrderEta : ℝ) ^ 2 * 3 ^ 80 / (12 * waveBufferMean ^ 2) ∧
    γ < (Numerics.Wave.allOrderEta : ℝ) ^ 2 * 3 ^ 80 /
      (60 * waveBufferEll ^ 2 * (1200 + (6 + 11 * 40 / 5) / 5)) ∧ γ < 1 / 64 := by
  have hc : γ ≤ (17 / 50000 : ℝ) := hγ
  obtain ⟨hm, ht, hg, hs⟩ := Numerics.Wave.reset_gates
  have hmean : (17 / 50000 : ℝ) < 10896 / 10000 := by norm_num
  rw [waveBufferMean_eq_numeric, waveBufferEll_eq_numeric]
  exact ⟨hc.trans_lt (hmean.trans hm), hc.trans_lt (hg.trans ht), hc.trans_lt hs⟩

end ASDExplicitGamma.Gaussian

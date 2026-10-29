module

public import ASDExplicitGamma.Inverse.StoppedSelectedRootMoment

/-! Exact complete source root selected-tail moment before its geometric majorant. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The literal complete root-tail moment series of the source. -/
def selectedRootExactMoment (γ p : ℝ) (H0 : ℕ) : ℝ :=
  ∑' n : ℕ, (3:ℝ)^(2*p*γ*(selectedFirstClock H0+(n:ℝ)))*selectedTailProbability H0 n

/-- The actual q3 selected root tail is controlled by the full exact series,
with every height present and the first exponent evaluated at Hs. -/
theorem q3_selected_root_tail_exact_moment (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (hg : A.gamma ≤ gammaZero) (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0)
    (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (p : ℝ) (hp : 0 < p) (hp256 : p ≤ 256) :
    (∫⁻ ω, (selectedRootClockTail A.gamma H0 (q3StoppedHeight A Q H0 τ (waveGateEta t)) ω)^p
      ∂(Cutoff.cutoffSampleLaw A).toMeasure) ≤ ENNReal.ofReal (selectedRootExactMoment A.gamma p H0) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let H := q3StoppedHeight A Q H0 τ (waveGateEta t)
  let c := fun n : ℕ => ENNReal.ofReal ((3:ℝ)^(2*A.gamma*(selectedFirstClock H0+(n:ℝ))))
  have hmH : Measurable H := q3_stopped_height_measurable A Q H0 τ (waveGateEta t)
  have hpow (n : ℕ) : (c n)^p = ENNReal.ofReal ((3:ℝ)^(2*p*A.gamma*(selectedFirstClock H0+(n:ℝ)))) := by
    dsimp only [c]
    rw [ENNReal.ofReal_rpow_of_pos (by positivity),← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    ring_nf
  have hatom (n : ℕ) : μ {ω | H ω=H0+12+n} ≤ ENNReal.ofReal (selectedTailProbability H0 n) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    apply ENNReal.ofReal_le_ofReal
    exact q3_selected_height_atom A h hA hg Q H0 hH τ hτ t q hq0 hq hraw hpast n
  have hseries := selected_root_tail_series A.gamma p hg hp hp256 H0 hH
  rw [show (fun ω => (selectedRootClockTail A.gamma H0 H ω)^p) =
    (fun ω => (if H0+11 < H ω then c (H ω-((H0+11)+1)) else 0)^p) by rfl]
  rw [discrete_height_tail_moment μ H hmH (H0+11) c p hp]
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((3:ℝ)^(2*p*A.gamma*(selectedFirstClock H0+(n:ℝ)))*
        selectedTailProbability H0 n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [hpow,ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul_of_nonneg_left (hatom n) (zero_le : (0:ℝ≥0∞) ≤ _)
    _ = ENNReal.ofReal (∑' n : ℕ, (3:ℝ)^(2*p*A.gamma*(selectedFirstClock H0+(n:ℝ)))*
        selectedTailProbability H0 n) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n => by unfold selectedTailProbability; positivity) hseries.1).symm

end
end ASDExplicitGamma.Inverse

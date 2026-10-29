module

public import ASDExplicitGamma.Inverse.StoppedSelectedHolder
public import ASDExplicitGamma.Inverse.StoppedSelectedWaveSeries
public import ASDExplicitGamma.Inverse.StoppedSeriesLp

/-! Correlated selected-wave tail assembly from ordinary Gaussian moment bounds. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The exact complete wave tail in source (9.4), including j=0,1. -/
def selectedWaveExactTail (γ p : ℝ) (H0 : ℕ) (j : Fin 2) : ℝ :=
  ∑' n : ℕ, (selectedFirstClock H0+(n:ℝ))^j.val*
    (3:ℝ)^(4*γ*(selectedFirstClock H0+(n:ℝ)))*(selectedTailProbability H0 n)^(1/(2*p):ℝ)

/-- The complete exact source sum obeys its geometric first-term majorant. -/
theorem selected_wave_exact_tail_le (γ p : ℝ) (hg : γ ≤ gammaZero)
    (hp : 0 < p) (hp256 : p ≤ 256) (H0 : ℕ) (hH : 333 ≤ H0) (j : Fin 2) :
    selectedWaveExactTail γ p H0 j ≤ selectedWaveTailBudget γ p H0 j :=
  (selected_wave_tail_series γ p hg hp hp256 H0 hH j).2

/-- Wave-tail assembly from ordinary 2p moments. The actual q3 height-atom
probabilities are derived internally. This consumes, rather than produces,
the Gaussian moment bound and assumes no independence of the selection. -/
theorem q3_selected_wave_exact_from_moments
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (hg : A.gamma ≤ gammaZero) (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0)
    (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) (j : Fin 2)
    (f : ℕ → Cutoff.CutoffSample 2 → ℝ) (hf : ∀ n, Measurable (f n))
    (hw : ∀ n, eLpNorm (f n) (ENNReal.ofReal (2*p)) (Cutoff.cutoffSampleLaw A).toMeasure ≤
      ENNReal.ofReal (40*(4*p+2)*(selectedFirstClock H0+(n:ℝ))^j.val*
        (3:ℝ)^(4*A.gamma*(selectedFirstClock H0+(n:ℝ))))) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    let H := q3StoppedHeight A Q H0 τ (waveGateEta t)
    let F := fun n => ({ω | H ω=H0+12+n} : Set (Cutoff.CutoffSample 2)).indicator (f n)
    (∀ᵐ ω ∂μ, Summable (fun n => ‖F n ω‖)) ∧
      eLpNorm (fun ω => ∑' n, F n ω) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (40*(4*p+2)*selectedWaveExactTail A.gamma p H0 j) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let H := q3StoppedHeight A Q H0 τ (waveGateEta t)
  let F := fun n => ({ω | H ω=H0+12+n} : Set (Cutoff.CutoffSample 2)).indicator (f n)
  let b := fun n : ℕ => (selectedFirstClock H0+(n:ℝ))^j.val*
    (3:ℝ)^(4*A.gamma*(selectedFirstClock H0+(n:ℝ)))*(selectedTailProbability H0 n)^(1/(2*p):ℝ)
  let C := 40*(4*p+2)
  have hp0 : 0 < p := by linarith only [hp]
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hz (n : ℕ) : 0 ≤ selectedFirstClock H0+(n:ℝ) := by
    have hh : (333:ℝ) ≤ H0 := by exact_mod_cast hH
    unfold selectedFirstClock
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [hh,hn]
  have hb0 (n : ℕ) : 0 ≤ b n := by
    have hzn := hz n
    have hprob : 0 ≤ selectedTailProbability H0 n := by unfold selectedTailProbability; positivity
    dsimp only [b]
    positivity
  have hmH : Measurable H := q3_stopped_height_measurable A Q H0 τ (waveGateEta t)
  have hE (n : ℕ) : MeasurableSet {ω | H ω=H0+12+n} := hmH (measurableSet_singleton _)
  have hF (n : ℕ) : Measurable (F n) := (hf n).indicator (hE n)
  have hbound (n : ℕ) : eLpNorm (F n) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C*b n) := by
    have hzn := hz n
    have hh := q3_selected_indicator_holder A h hA hg Q H0 hH τ hτ t q hq0 hq hraw hpast n
      (f n) (hf n).aestronglyMeasurable p hp0
    apply (hh.trans (mul_le_mul_of_nonneg_right (hw n) (zero_le : (0:ℝ≥0∞) ≤ _))).trans_eq
    rw [← ENNReal.ofReal_mul (show 0 ≤ 40*(4*p+2)*(selectedFirstClock H0+(n:ℝ))^j.val*
      (3:ℝ)^(4*A.gamma*(selectedFirstClock H0+(n:ℝ))) by positivity)]
    congr 1
    dsimp only [C,b]
    ring
  have hseries := selected_wave_tail_series A.gamma p hg hp0 hp256 H0 hH j
  have hs : HasSum (fun n => C*b n) (C*∑' n, b n) := hseries.1.hasSum.mul_left C
  have hh := countable_density_series_Lp μ (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr (by linarith only [hp])) F hF (fun n => C*b n)
    (fun n => mul_nonneg hC (hb0 n)) _ hs hbound
  exact hh

end
end ASDExplicitGamma.Inverse

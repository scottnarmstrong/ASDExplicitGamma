module

public import ASDExplicitGamma.Inverse.StoppedSelectedPhysicalClock
public import ASDExplicitGamma.Inverse.StoppedSelectedDiscreteMoment

/-! Actual q3 selected root-clock tail at every real source order. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The actual nonnegative root clock restricted to the unbounded selected
height tail, indexed from its first atom Hs+1. -/
def selectedRootClockTail {Ω : Type*} (γ : ℝ) (H0 : ℕ) (H : Ω → ℕ) (ω : Ω) : ℝ≥0∞ :=
  if H0+11 < H ω then ENNReal.ofReal ((3:ℝ)^(2*γ*(selectedFirstClock H0+
    ((H ω-(H0+12):ℕ):ℝ)))) else 0

/-- Exact ordinary p-th moment budget from (9.2), including the full tail. -/
def selectedRootMomentBudget (γ p : ℝ) (H0 : ℕ) : ℝ :=
  (1000/999)*(3:ℝ)^(2*p*γ*selectedFirstClock H0)*Real.exp (-heightExponent (H0+11)/32)

/-- The actual selected-height root tail obeys (9.2) from the model and
protected native past, without a selected-height probability premise. -/
theorem q3_selected_root_tail_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (hg : A.gamma ≤ gammaZero) (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0)
    (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (p : ℝ) (hp : 0 < p) (hp256 : p ≤ 256) :
    eLpNorm (selectedRootClockTail A.gamma H0 (q3StoppedHeight A Q H0 τ (waveGateEta t)))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure ≤
        ENNReal.ofReal ((selectedRootMomentBudget A.gamma p H0)^(1/p:ℝ)) := by
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
  have hmoment : (∫⁻ ω, (selectedRootClockTail A.gamma H0 H ω)^p ∂μ) ≤
      ENNReal.ofReal (selectedRootMomentBudget A.gamma p H0) := by
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
      _ ≤ _ := ENNReal.ofReal_le_ofReal hseries.2
  have hmeas : Measurable (selectedRootClockTail A.gamma H0 H) := by
    exact (measurable_of_countable (fun k : ℕ => if H0+11 < k then
      ENNReal.ofReal ((3:ℝ)^(2*A.gamma*(selectedFirstClock H0+((k-(H0+12):ℕ):ℝ)))) else 0)).comp hmH
  rw [nonnegative_Lp_moment_formula μ _ hmeas p hp]
  apply (ENNReal.rpow_le_rpow hmoment (by positivity : (0:ℝ) ≤ 1/p)).trans_eq
  exact ENNReal.ofReal_rpow_of_nonneg (by unfold selectedRootMomentBudget; positivity) (by positivity)

end
end ASDExplicitGamma.Inverse

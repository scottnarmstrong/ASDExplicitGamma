module

public import ASDExplicitGamma.Inverse.StoppedQ3Height
public import Mathlib.Order.Interval.Finset.Nat

/-! Exact twelve-candidate selected-height set and the actual q3 tail atoms. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
noncomputable section

/-- The twelve bounded source candidate heights, including both endpoints. -/
def selectedCandidateHeights (H0 : ℕ) : Finset ℕ := Finset.Icc H0 (H0+11)

theorem selected_candidate_heights_card (H0 : ℕ) :
    (selectedCandidateHeights H0).card = 12 := by
  rw [selectedCandidateHeights,Nat.card_Icc]
  omega

theorem selected_candidate_mem (H0 k : ℕ) :
    k ∈ selectedCandidateHeights H0 ↔ H0 ≤ k ∧ k ≤ H0+11 := Finset.mem_Icc

/-- The first unbounded candidate is Hs+1, so its penalty reads Hs. -/
def selectedTailProbability (H0 n : ℕ) : ℝ :=
  Real.exp (-heightExponent (H0+11+n)/32)

/-- Exact supergeometric expression with the source's first argument. -/
theorem selected_tail_probability_eq (H0 n : ℕ) :
    selectedTailProbability H0 n =
      Real.exp (-(heightExponent (H0+11)/32)*((3:ℝ)^(1/4:ℝ))^n) := by
  unfold selectedTailProbability
  rw [height_exponent_add]
  congr 1
  ring

/-- The actual q3 selected height has each tail atom bounded by p_h with h-1,
including the correct first atoms 345 and 389 in the two source tuples. -/
theorem q3_selected_height_atom (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (hg : A.gamma ≤ gammaZero) (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0)
    (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k) (n : ℕ) :
    (Cutoff.cutoffSampleLaw A).toMeasure.real
      {ω | q3StoppedHeight A Q H0 τ (waveGateEta t) ω=H0+12+n} ≤
      selectedTailProbability H0 n := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  have hsub : {ω | q3StoppedHeight A Q H0 τ (waveGateEta t) ω=H0+12+n} ⊆
      {ω | H0+11+n < q3StoppedHeight A Q H0 τ (waveGateEta t) ω} := by
    intro ω hω
    change q3StoppedHeight A Q H0 τ (waveGateEta t) ω=H0+12+n at hω
    change H0+11+n < q3StoppedHeight A Q H0 τ (waveGateEta t) ω
    omega
  exact (measureReal_mono (μ := μ) hsub (measure_ne_top μ _)).trans
    (q3_stopped_height_tail A h hA hg Q H0 hH τ hτ t q hq0 hq hraw hpast _ (by omega))

end
end ASDExplicitGamma.Inverse

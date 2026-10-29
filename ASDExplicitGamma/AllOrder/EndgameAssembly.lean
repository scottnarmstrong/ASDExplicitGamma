/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.PerDepthAssembly
public import ASDExplicitGamma.AllOrder.HistorySum
public import ASDExplicitGamma.AllOrder.TailMarkov
public import ASDExplicitGamma.AllOrder.AssemblyTail
public import ASDExplicitGamma.Statements.GammaZero

/-! Assembly of the all-order history, coupled tail, and gate. -/

@[expose] public section

open MeasureTheory
open Algsuperdiff.Section3
open Homogenization.IndependentSums
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

/-- AO-HISTORY-SUM. The per-depth profile is supplied internally
by the AO-PER-DEPTH theorem. -/
theorem ao_history_sum {M : ABKModel 2} {h : ℝ} {m : ℤ} (s : ℝ)
    (hM : PlanarQ3Gaussian M h := by assumption)
    (hgamma : M.gamma ≤ (17 / 50000 : ℝ) := by assumption)
    (hstate : ∀ n : ℤ, nativeInductionState M h n := by assumption)
    (hs : 8 * M.gamma ≤ s) (hs1 : s ≤ 1) :
    ∀ ⦃p : ℝ⦄, 1 ≤ p →
      eLpNorm
        (fun ω => Observable.cutoffHomogenizationError M m
          ⟨s, by linarith [M.shellPrefix.gamma_pos]⟩ ω ^ 2)
        (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal
        (2 ^ 29 * M.gamma * p / s ^ 2 +
          Real.exp (-(Real.log 2 / (1350 * M.gamma))) * p ^ 3) := by
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  apply allOrderHistorySum_of_depthProfile M m s hgammaPos hgamma hs hs1
  intro _ p hp t
  exact ao_per_depth M h hM (by simpa only [gammaZero] using hgamma)
    hstate m (p := p) hp t

/-- AO-MARKOV-COUPLED, composed from `ao_history_sum`. -/
theorem ao_markov_coupled {M : ABKModel 2} {h : ℝ} {m : ℤ} (s : ℝ)
    (hM : PlanarQ3Gaussian M h := by assumption)
    (hgamma : M.gamma ≤ (17 / 50000 : ℝ) := by assumption)
    (hstate : ∀ n : ℤ, nativeInductionState M h n := by assumption)
    (hs : s ∈ Set.Icc (8 * M.gamma) 1) :
    Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2 : ℝ))
      (Observable.cutoffHomogenizationError M m
        ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8) M.shellPrefix.gamma_pos).trans_le hs.1⟩)
      (2 ^ 16 * Real.sqrt M.gamma / s)
      (Real.exp (-(Real.log 2 / (8192 * M.gamma)))) := by
  apply allOrderMarkovCoupled_of_history M m s hs hgamma
  intro p hp
  have h := ao_history_sum (M := M) (h := h) (m := m) s hM hgamma hstate
    hs.1 hs.2
  exact h hp

/-- End-to-end all-order gate with the single conditional reset input used by
the pre-source helper. -/
theorem allorder_of_state_of_reset (reset : OrderResetProducer)
    {M : ABKModel 2} {h : ℝ} {m : ℤ}
    (hM : PlanarQ3Gaussian M h := by assumption)
    (hγ : M.gamma ≤ gammaZero := by assumption)
    (hstate : ∀ n : ℤ, nativeInductionState M h n := by assumption) :
    AllOrderBounds M m := by
  have hgamma : M.gamma ≤ (17 / 50000 : ℝ) := by
    simpa only [gammaZero] using hγ
  have hHistory : ∀ (s : ℝ), ∀ (hs : s ∈ Set.Icc (8 * M.gamma) 1),
      ∀ ⦃p : ℝ⦄, 1 ≤ p →
        eLpNorm
          (fun ω => Observable.cutoffHomogenizationError M m
            ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8) M.shellPrefix.gamma_pos).trans_le hs.1⟩ ω ^ 2)
          (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal
          (2 ^ 29 * M.gamma * p / s ^ 2 +
            Real.exp (-(Real.log 2 / (1350 * M.gamma))) * p ^ 3) := by
    intro s hs p hp
    have hsum := allOrderHistorySum_of_depthProfile M m s M.shellPrefix.gamma_pos
      hgamma hs.1 hs.2 (fun _ => by
        intro q hq t
        exact ao_per_depth_of_reset reset M h hM hgamma hstate m (p := q) hq t)
    exact hsum hp
  exact allorder_of_state_of_nodes (M := M) (h := h) (m := m) hM hgamma hstate hHistory

/-- GATE-ALLORDER. The order reset is instantiated here. -/
theorem allorder_of_state {M : ABKModel 2} {h : ℝ} {m : ℤ}
    (hM : PlanarQ3Gaussian M h := by assumption)
    (hγ : M.gamma ≤ gammaZero := by assumption)
    (hstate : ∀ n : ℤ, nativeInductionState M h n := by assumption) :
    AllOrderBounds M m :=
  allorder_of_state_of_reset order_reset_producer hM hγ hstate

end ASDExplicitGamma.AllOrder

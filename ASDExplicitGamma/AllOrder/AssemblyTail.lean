module

public import ASDExplicitGamma.AllOrder.TailMarkov
public import ASDExplicitGamma.Statements.AllOrderBounds
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Statements.PlanarQ3Gaussian

/-! The all-order gate assembled from the conditional history node. -/

@[expose] public section

open MeasureTheory
open Algsuperdiff.Section3
open Homogenization.IndependentSums
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

/-- Assemble the frozen all-order conclusion from the exact internal-rate
history statement. The history premise is the AO-HISTORY-SUM source conclusion;
the first clause is then supplied by the proved coupled Markov conversion, and
the frozen moment rate is weakened from 1350 to 1500. -/
theorem allorder_of_state_of_nodes {M : ABKModel 2} {h : ℝ} {m : ℤ}
    (hM : PlanarQ3Gaussian M h := by assumption)
    (hgamma : M.gamma ≤ 17 / 50000 := by assumption)
    (hstate : ∀ n : ℤ, ASDExplicitGamma.nativeInductionState M h n := by assumption)
    (hHistory : ∀ (s : ℝ), ∀ (hs : s ∈ Set.Icc (8 * M.gamma) 1),
      ∀ ⦃p : ℝ⦄, 1 ≤ p →
        eLpNorm
          (fun ω => Observable.cutoffHomogenizationError M m
            ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8) M.shellPrefix.gamma_pos).trans_le hs.1⟩ ω ^ 2)
          (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal
          (2 ^ 29 * M.gamma * p / s ^ 2 +
            Real.exp (-(Real.log 2 / (1350 * M.gamma))) * p ^ 3) := by assumption) :
    ASDExplicitGamma.AllOrderBounds M m := by
  have _hSourceModel : PlanarQ3Gaussian M h := hM
  have _hSourceState : ∀ n : ℤ, ASDExplicitGamma.nativeInductionState M h n := hstate
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  intro s hs
  refine ⟨allOrderMarkovCoupled_of_history M m s hs hgamma (hHistory s hs), ?_⟩
  intro p hp
  have hMoment := hHistory s hs (p := p) hp
  have hden1350 : 0 < 1350 * M.gamma := by positivity
  have hden1500 : 0 < 1500 * M.gamma := by positivity
  have hrate : Real.log 2 / (1500 * M.gamma) ≤ Real.log 2 / (1350 * M.gamma) := by
    apply (div_le_div_iff₀ hden1500 hden1350).2
    nlinarith
  have hexp :
      Real.exp (-(Real.log 2 / (1350 * M.gamma))) ≤
        Real.exp (-(Real.log 2 / (1500 * M.gamma))) :=
    Real.exp_le_exp.mpr (neg_le_neg hrate)
  have hrare := mul_le_mul_of_nonneg_right hexp (pow_nonneg (le_trans zero_le_one hp) 3)
  have hpoly :
      2 ^ 29 * M.gamma * p / s ^ 2 +
          Real.exp (-(Real.log 2 / (1350 * M.gamma))) * p ^ 3 ≤
        2 ^ 29 * M.gamma * p / s ^ 2 +
          Real.exp (-(Real.log 2 / (1500 * M.gamma))) * p ^ 3 :=
    add_le_add le_rfl hrare
  exact hMoment.trans (ENNReal.ofReal_le_ofReal hpoly)

end ASDExplicitGamma.AllOrder

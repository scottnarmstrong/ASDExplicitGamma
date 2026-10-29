module

public import ASDExplicitGamma.Main.MultiplierMoments

/-! Successors of `MultiplierMoments` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

noncomputable section

open MeasureTheory Homogenization ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
  ASDExplicitGamma.Inverse ASDExplicitGamma.Cold Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Homogenization.Book.Ch04
open Algsuperdiff.Section3.Provider.BadEvents

namespace ASDExplicitGamma.Main

/-- Successor of `main_multiplier_moments_of_main_envelope_h` with the history envelope `Hfun`. -/
theorem main_multiplier_moments_of_main_envelope_h_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    ((((∫ ω, mainPartialInsertedMultiplierHistory M m t ω ∂
      (Cutoff.cutoffSampleLaw M).toMeasure) ≤
        mainM0 (Hfun t) ∧
    (∫ ω, mainD * mainPartialInsertedMultiplierHistory M m t ω *
      (mainPartialInsertedTraceMaxHistory M m t ω).toReal ∂
        (Cutoff.cutoffSampleLaw M).toMeasure) ≤
      mainD * mainM0 (Hfun t) *
        Hfun t) ∧
    lpNorm (fun ω => mainPartialInsertedMultiplierHistory M m t ω) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      mainM0 (Hfun t)) ∧
    MemLp (mainPartialInsertedMultiplierHistory M m t) 2
      (Cutoff.cutoffSampleLaw M).toMeasure) ∧
    0 ≤ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      mainPartialInsertedMultiplierHistory M m t := by
  have hEnvelope := hHist t ⟨ht0, ht1⟩
  have hfinite : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mainPartialInsertedTraceMaxHistory M m t ω < ⊤ := by
    simpa only [mainPartialInsertedTraceMaxHistory,
      mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
      Scalar.inverseHistoryDiscount, mainAlpha] using hEnvelope.1
  have hmem : MemLp
      (fun ω => (mainPartialInsertedTraceMaxHistory M m t ω).toReal)
      2 (Cutoff.cutoffSampleLaw M).toMeasure := by
    simpa only [mainPartialInsertedTraceMaxHistory,
      mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
      Scalar.inverseHistoryDiscount, mainAlpha] using hEnvelope.2.1
  have hcap : lpNorm
      (fun ω => (mainPartialInsertedTraceMaxHistory M m t ω).toReal)
      2 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      Hfun t := by
    simpa only [mainPartialInsertedTraceMaxHistory,
      mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
      Scalar.inverseHistoryDiscount, mainAlpha] using hEnvelope.2.2
  exact main_multiplier_moments_of_max_history_envelope M m t
    ⟨ht0, ht1⟩ (Hfun t) hfinite hmem hcap

end ASDExplicitGamma.Main
end
end

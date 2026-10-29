module

public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Model.Cutoff
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Actual cutoff-law adapter for the MA old/new mixed bridge. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open scoped BigOperators

/-- On the actual cutoff-sample law, the combined `k=1` bridge row splits
into the nonnegative OLD part and the NEW part. Together with the bridge's
other moment rows, this gives the exact MA-MIXED-BRIDGE source conclusion.
All functions are actual carriers on `cutoffSampleLaw M`; the moment rows are
the corresponding IN-MIXED-BRIDGE producer outputs. -/
theorem main_mixed_bridge_actual_law
    (M : ABKModel 2) (xi f H : ℝ)
    (B V G Vl : Cutoff.CutoffSample 2 → ℝ)
    (hBnonneg : 0 ≤ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure] B)
    (hVgap : (∫ ω, V ω ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      xi - mainBetaOld * f)
    (hMom : ∀ k : Fin 4,
      (∫ ω, B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          2 * mainBeta ^ k.val * xi)
    (hBVInt : Integrable (fun ω => B ω * V ω ^ 2)
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hBGInt : Integrable (fun ω => B ω * G ω ^ 2)
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hVL : (∫ ω, B ω * Vl ω ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      mainBeta * xi + mainEpsNew * mainD * mainBeta * H) :
    (∫ ω, V ω ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        xi - mainBetaOld * f ∧
      (∀ k : Fin 4,
        (∫ ω, B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
            2 * mainBeta ^ k.val * xi) ∧
      (∫ ω, B ω * G ω ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        2 * mainBeta * xi ∧
      (∫ ω, B ω * Vl ω ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        mainBeta * xi + mainEpsNew * mainD * mainBeta * H := by
  have hSplit :
      (∫ ω, B ω * (V ω ^ 2 + G ω ^ 2)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        (∫ ω, B ω * V ω ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
          (∫ ω, B ω * G ω ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) := by
    have hpoint (ω : Cutoff.CutoffSample 2) :
        B ω * (V ω ^ 2 + G ω ^ 2) = B ω * V ω ^ 2 + B ω * G ω ^ 2 := by ring
    calc
      _ = ∫ ω, (B ω * V ω ^ 2 + B ω * G ω ^ 2)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
      _ = _ := integral_add hBVInt hBGInt
  have hBVnonneg : 0 ≤ ∫ ω, B ω * V ω ^ 2
      ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    apply integral_nonneg_of_ae
    filter_upwards [hBnonneg] with ω hBω
    exact mul_nonneg hBω (sq_nonneg (V ω))
  have hCombined :
      (∫ ω, B ω * (V ω ^ 2 + G ω ^ 2)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ 2 * mainBeta * xi := by
    simpa using hMom (1 : Fin 4)
  have hBG : (∫ ω, B ω * G ω ^ 2
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ 2 * mainBeta * xi := by
    rw [hSplit] at hCombined
    nlinarith [hBVnonneg]
  exact ⟨hVgap, hMom, hBG, hVL⟩

end ASDExplicitGamma.Main

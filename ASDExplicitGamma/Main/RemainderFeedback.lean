module

public import ASDExplicitGamma.Main.RemainderFeedbackAssembly
public import ASDExplicitGamma.Model.Cutoff

/-! Actual-law assembly of the positive-split remainder feedback row. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

/-- Assemble the two positive-split feedback moment outputs on the actual
cutoff law. `B`, `dPrime`, and `G` are the actual source observables; the
mixed-bridge row stays weighted by the NEW global inverse variable, while
`mainLoadD` retains the separate OLD-frame coefficient. -/
theorem main_e_remainder_feedback_actual_law
    (M : ABKModel 2) (B dPrime G : Cutoff.CutoffSample 2 → ℝ)
    (v a f H xi : ℝ)
    (hBd : (∫ ω, B ω * dPrime ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      mainBeta * mainLoadD v a f H xi (mainKd v))
    (hBGd : (∫ ω, B ω * G ω * dPrime ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      mainLoadZ v a f H xi (mainKd v) * mainRec xi) :
    2 * mainKd v * (63 / 50) *
        (Real.sqrt 2 *
            (∫ ω, B ω * dPrime ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
          (∫ ω, B ω * G ω * dPrime ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)) ≤
      2 * mainKd v * (63 / 50) *
        (Real.sqrt 2 * mainBeta * mainLoadD v a f H xi (mainKd v) +
          mainLoadZ v a f H xi (mainKd v) * mainRec xi) := by
  exact main_remainder_feedback_bound_of_source_rows v a f H xi
    (∫ ω, B ω * dPrime ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)
    (∫ ω, B ω * G ω * dPrime ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)
    hBd hBGd

end ASDExplicitGamma.Main

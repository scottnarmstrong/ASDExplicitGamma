module

public import ASDExplicitGamma.Gaussian.WeightedBandLaw
public import ASDExplicitGamma.Gaussian.Q3WeightedBandSpatial
public import ASDExplicitGamma.Gaussian.Q3BandRealization

/-! # The actual attenuated product-q3 band and its common ordinary-H³ realization -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

namespace ASDExplicitGamma.Gaussian

/-- Actual weighted shell laws use the same ordinary-H³ band series and physical value maps.
The weights may vanish and need not be positive for this law identity. -/
theorem actualWeightedBandLaw_eq_h3Series {n : ℕ} [NeZero n] (a b c d : ℝ)
    (hab : a < b) (hcd : c < d) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin n → ℤ) (hk : Function.Injective k) (w : Fin n → ℝ) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map (modelWeightedBand (closedRectangle a b c d) k w) =
      standardGaussianInfinitePi.map (fun ω =>
        q3WeightedBandH3Value a b c d (fun i => q3ModelAmplitude M h (k i)) w
          (fun i => q3ModelLength (k i))
          (q3BandSeries a b c d (fun i => q3ModelAmplitude M h (k i))
            (fun i => q3ModelLength (k i)) ω)) := by
  apply @modelWeightedBand_law_of_factors n inferInstance
    (fun i => Q3H3Range a b c d (q3ModelAmplitude M h (k i)) (q3ModelLength (k i)))
    (fun _ => inferInstance)
    (fun i => instQ3H3RangeInnerProductSpace a b c d (q3ModelAmplitude M h (k i)) (q3ModelLength (k i)))
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
    (closedRectangle a b c d) inferInstance M k hk w
    (fun i => q3H3RangeValue a b c d (q3ModelAmplitude M h (k i)) (q3ModelLength (k i)))
    (fun i => q3H3Directions a b c d (q3ModelAmplitude M h (k i)) (q3ModelLength (k i)) whiteBasis)
    (fun i => q3H3Directions_summable a b c d (q3ModelAmplitude M h (k i)) (q3ModelLength (k i)) whiteBasis)
  intro i
  exact actualShellLaw_eq_h3Series a b c d hab hcd M h hM (k i)

end ASDExplicitGamma.Gaussian

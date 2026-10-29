module

public import ASDExplicitGamma.Gaussian.Q3BandH3

/-! # The actual finite-band law has the ordinary-H³/C¹ direct-sum realization -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization Filter
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

section
variable {n : ℕ} [NeZero n] (a b c d : ℝ) (β : Fin n → ℝ)
  (L : Fin n → {l : ℝ // 0 < l})

noncomputable instance instQ3BandH3MeasurableSpace :
    MeasurableSpace (Q3BandH3 a b c d β L) := borel _

instance instQ3BandH3BorelSpace : BorelSpace (Q3BandH3 a b c d β L) := ⟨rfl⟩

noncomputable def q3BandSeries : (ℕ → ℝ) → Q3BandH3 a b c d β L :=
  @gaussianSeriesLimit (Q3BandH3 a b c d β L) inferInstance
    (instQ3BandH3InnerProductSpace a b c d β L) inferInstance inferInstance inferInstance inferInstance
    inferInstance (q3BandH3Directions a b c d β L) (q3BandH3Directions_summable a b c d β L)

theorem stronglyMeasurable_q3BandSeries : StronglyMeasurable (q3BandSeries a b c d β L) :=
  @stronglyMeasurable_gaussianSeriesLimit (Q3BandH3 a b c d β L) inferInstance
    (instQ3BandH3InnerProductSpace a b c d β L) inferInstance inferInstance inferInstance inferInstance
    inferInstance _ (q3BandH3Directions_summable a b c d β L)

/-- The finite-band Hilbert series has every finite moment of order at least two. -/
theorem memLp_q3BandSeries {p : ℝ} (hp : 2 ≤ p) :
    MemLp (q3BandSeries a b c d β L) (ENNReal.ofReal p) standardGaussianInfinitePi := by
  exact @memLp_gaussianSeriesLimit (Q3BandH3 a b c d β L) inferInstance
    (instQ3BandH3InnerProductSpace a b c d β L) inferInstance inferInstance inferInstance inferInstance
    inferInstance _ (q3BandH3Directions_summable a b c d β L) p hp

noncomputable def q3BandValueMap : Q3BandH3 a b c d β L →L[ℝ] C(closedRectangle a b c d, ℝ) :=
  @finiteFactor n (fun i => Q3H3Range a b c d (β i) (L i))
    (fun _ => inferInstance) (fun _ => inferInstance) _ inferInstance inferInstance
    (fun i => q3H3RangeValue a b c d (β i) (L i))

end

/-- No realization premise: the actual independent physical shell band has this Sobolev law. -/
theorem actualBandLaw_eq_h3Series {n : ℕ} [NeZero n] (a b c d : ℝ)
    (hab : a < b) (hcd : c < d) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin n → ℤ) (hk : Function.Injective k) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand (closedRectangle a b c d) k) =
      standardGaussianInfinitePi.map (fun ω =>
        q3BandValueMap a b c d (fun i => q3ModelAmplitude M h (k i))
          (fun i => q3ModelLength (k i))
          (q3BandSeries a b c d (fun i => q3ModelAmplitude M h (k i))
            (fun i => q3ModelLength (k i)) ω)) := by
  apply @modelBand_law_of_factors n inferInstance
    (fun i => Q3H3Range a b c d (q3ModelAmplitude M h (k i)) (q3ModelLength (k i)))
    (fun _ => inferInstance)
    (fun i => instQ3H3RangeInnerProductSpace a b c d (q3ModelAmplitude M h (k i)) (q3ModelLength (k i)))
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
    (closedRectangle a b c d) inferInstance M k hk
    (fun i => q3H3RangeValue a b c d (q3ModelAmplitude M h (k i)) (q3ModelLength (k i)))
    (fun i => q3H3Directions a b c d (q3ModelAmplitude M h (k i)) (q3ModelLength (k i)) whiteBasis)
    (fun i => q3H3Directions_summable a b c d (q3ModelAmplitude M h (k i)) (q3ModelLength (k i)) whiteBasis)
  intro i
  exact actualShellLaw_eq_h3Series a b c d hab hcd M h hM (k i)

end ASDExplicitGamma.Gaussian

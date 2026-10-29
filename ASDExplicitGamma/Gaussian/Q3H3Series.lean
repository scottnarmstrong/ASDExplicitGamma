module

public import ASDExplicitGamma.Gaussian.H3Separable
public import ASDExplicitGamma.Gaussian.HilbertBasisEnumeration
public import ASDExplicitGamma.Gaussian.SeriesHeat
public import ASDExplicitGamma.Gaussian.SeriesFullLp

/-! # Ordinary-H³ Gaussian series and their uniform first-jet images -/

@[expose] public section

open MeasureTheory Homogenization Set Filter
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

section
variable {ι : Type*} [Countable ι] (a b c d β : ℝ) (L : {l : ℝ // 0 < l})
  (e : HilbertBasis ι ℝ WhiteNoise)

/-- Zero-padding uses every basis direction and also covers finite-dimensional factors. -/
noncomputable def q3H3Directions : ℕ → Q3H3Range a b c d β L :=
  gaussEnumerated (fun j => q3H3RangeFactor a b c d β L (e j))

theorem q3H3Directions_summable : Summable (fun n => ‖q3H3Directions a b c d β L e n‖ ^ 2) :=
  enumerated_summable_sq _ (q3H3RangeFactor_summable a b c d β L e e.orthonormal)

/-- The series is constructed in the complete ordinary weak H³ Hilbert carrier. -/
noncomputable def q3H3Series : (ℕ → ℝ) → Q3H3Range a b c d β L :=
  gaussianSeriesLimit (V := Q3H3Range a b c d β L) (q3H3Directions a b c d β L e) (q3H3Directions_summable a b c d β L e)

/-- The value and first spatial derivatives are taken by the same bounded first-jet map. -/
noncomputable def q3C1Series : (ℕ → ℝ) → C1Jet (closedRectangle a b c d) :=
  fun ω => q3H3RangeC1 a b c d β L (q3H3Series a b c d β L e ω)

theorem stronglyMeasurable_q3H3Series : StronglyMeasurable (q3H3Series a b c d β L e) :=
  stronglyMeasurable_gaussianSeriesLimit _ _

theorem stronglyMeasurable_q3C1Series : StronglyMeasurable (q3C1Series a b c d β L e) :=
  (q3H3RangeC1 a b c d β L).continuous.comp_stronglyMeasurable
    (stronglyMeasurable_q3H3Series a b c d β L e)

end
end ASDExplicitGamma.Gaussian

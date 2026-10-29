module

public import ASDExplicitGamma.Gaussian.Q3C1Bound
public import ASDExplicitGamma.Gaussian.HilbertRangeFactor

/-! # The ordinary-H³ Hilbert realization with a bounded actual C¹ first-jet map -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- The closed ordinary-Sobolev range of the physical q3 covariance factor. -/
noncomputable abbrev Q3H3Range (a b c d β : ℝ) (L : {l : ℝ // 0 < l}) : Type :=
  ↥(hilbertRange (q3SobolevOperator (openRectangle a b c d) β L))

/-- The range carries the inherited ordinary Sobolev Hilbert structure. -/
noncomputable instance instQ3H3RangeInnerProductSpace (a b c d β : ℝ) (L : {l : ℝ // 0 < l}) :
    @InnerProductSpace ℝ (Q3H3Range a b c d β L) inferInstance
      (inferInstance : NormedAddCommGroup (Q3H3Range a b c d β L)).toSeminormedAddCommGroup := by
  convert (inferInstance : InnerProductSpace ℝ (hilbertRange
    (q3SobolevOperator (openRectangle a b c d) β L))) using 1

noncomputable def q3H3RangeFactor (a b c d β : ℝ) (L : {l : ℝ // 0 < l}) :
    WhiteNoise →L[ℝ] Q3H3Range a b c d β L :=
  hilbertRangeFactor (q3SobolevOperator (openRectangle a b c d) β L)

/-- The first-jet image is extended only after the actual H³-to-C¹ bound has been proved. -/
noncomputable def q3H3RangeC1 (a b c d β : ℝ) (L : {l : ℝ // 0 < l}) :
    Q3H3Range a b c d β L →L[ℝ] C1Jet (closedRectangle a b c d) :=
  hilbertRangeImage (q3SobolevOperator (openRectangle a b c d) β L)
    (q3C1JetOperator (closedRectangle a b c d) β L)

/-- Every white-noise direction has exactly its actual value and first derivatives as image. -/
theorem q3H3RangeC1_factor (a b c d β : ℝ) (hab : a < b) (hcd : c < d)
    (L : {l : ℝ // 0 < l}) (u : WhiteNoise) :
    q3H3RangeC1 a b c d β L (q3H3RangeFactor a b c d β L u) =
      q3C1JetOperator (closedRectangle a b c d) β L u := by
  apply hilbertRangeImage_factor
  exact ⟨rectangleSobolevConstant a b c d, q3C1JetOperator_norm_le a b c d β hab hcd L⟩

/-- The ordinary H³ Hilbert norm controls the entire first jet also on the completed range. -/
theorem q3H3RangeC1_norm_le (a b c d β : ℝ) (hab : a < b) (hcd : c < d)
    (L : {l : ℝ // 0 < l}) (u : Q3H3Range a b c d β L) :
    ‖q3H3RangeC1 a b c d β L u‖ ≤ rectangleSobolevConstant a b c d * ‖u‖ :=
  hilbertRangeImage_norm_le _ _ _ (q3C1JetOperator_norm_le a b c d β hab hcd L) u

/-- The Hilbert realization retains the actual source Hilbert–Schmidt summability. -/
theorem q3H3RangeFactor_summable {ι : Type*} (a b c d β : ℝ) (L : {l : ℝ // 0 < l})
    (e : ι → WhiteNoise) (he : Orthonormal ℝ e) :
    Summable (fun j => ‖q3H3RangeFactor a b c d β L (e j)‖ ^ 2) :=
  q3SobolevOperator_summable (openRectangle a b c d) β L e he

end ASDExplicitGamma.Gaussian

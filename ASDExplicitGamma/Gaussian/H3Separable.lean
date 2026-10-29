module

public import ASDExplicitGamma.Gaussian.Q3H3Range
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # Separability of the ordinary white-noise and weak Sobolev Hilbert carriers -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

private instance instTwoFinite : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

instance instWhiteNoiseSecondCountable : SecondCountableTopology WhiteNoise :=
  inferInstanceAs (SecondCountableTopology (Lp ℝ 2 (volume : Measure (Vec 2))))

instance instH3JetSecondCountable (U : Set (Vec 2)) : SecondCountableTopology (H3Jet U) :=
  inferInstance

instance instQ3H3RangeSecondCountable (a b c d β : ℝ) (L : {l : ℝ // 0 < l}) :
    SecondCountableTopology (Q3H3Range a b c d β L) := inferInstance

noncomputable instance instQ3H3RangeMeasurableSpace (a b c d β : ℝ) (L : {l : ℝ // 0 < l}) :
    MeasurableSpace (Q3H3Range a b c d β L) := borel _

instance instQ3H3RangeBorelSpace (a b c d β : ℝ) (L : {l : ℝ // 0 < l}) :
    BorelSpace (Q3H3Range a b c d β L) := ⟨rfl⟩

end ASDExplicitGamma.Gaussian

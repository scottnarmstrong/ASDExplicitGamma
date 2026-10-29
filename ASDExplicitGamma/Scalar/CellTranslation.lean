module

public import ASDExplicitGamma.Scalar.CutoffPatching
public import ASDExplicitGamma.Model.CutoffAction
public import Homogenization.CoarseGraining.Translation
public import Homogenization.Sobolev.PotentialSolenoidalTranslation

/-! Translation covariance for the stationary trial. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

/-- Translating a source variation translates its cell and preserves all three
parts of the actual source variation predicate. -/
theorem scalarVariation_translateSet {U : Set (Vec 2)}
    {F : Vec 2 → BlockVec 2} (hF : ScalarVariation U F) (z : Vec 2) :
    ScalarVariation (translateSet z U) (fun x => F (x - z)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hF.1.comp_measurePreserving
      (measurePreserving_subRight_restrict_translateSet z U)
  · exact isPotentialZeroTraceOn_translateSet hF.2.1 z
  · exact isSolenoidalZeroNormalTraceOn_translateSet hF.2.2 z

/-- The expected value of any cutoff-sample observable is translation
invariant under the actual sample law. -/
theorem integral_cutoffSample_vadd (M : ABKModel 2) (z : Vec 2)
    (f : Cutoff.CutoffSample 2 → ℝ) :
    (∫ ω, f (z +ᵥ ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, f ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let shift : Cutoff.CutoffSample 2 → Cutoff.CutoffSample 2 := fun ω => z +ᵥ ω
  have hleft (ω : Cutoff.CutoffSample 2) : -z +ᵥ shift ω = ω := by
    change (-z) +ᵥ (z +ᵥ ω) = ω
    rw [← add_vadd, neg_add_cancel, zero_vadd]
  have hsurj : Function.Surjective shift := by
    intro ω
    refine ⟨-z +ᵥ ω, ?_⟩
    change z +ᵥ (-z +ᵥ ω) = ω
    rw [← add_vadd, add_neg_cancel, zero_vadd]
  have hrange : MeasurableSet (Set.range shift) := by
    rw [Set.range_eq_univ.mpr hsurj]
    exact MeasurableSet.univ
  have hemb : MeasurableEmbedding shift :=
    MeasurableEmbedding.of_measurable_inverse
      (Cutoff.measurable_translateCutoffSample z) hrange
      (Cutoff.measurable_translateCutoffSample (-z)) hleft
  have hmp : MeasurePreserving shift μ μ :=
    ⟨Cutoff.measurable_translateCutoffSample z,
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M z⟩
  exact hmp.integral_comp hemb f

end ASDExplicitGamma.Scalar

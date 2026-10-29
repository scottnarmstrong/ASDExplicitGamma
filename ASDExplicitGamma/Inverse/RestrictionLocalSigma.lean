module

public import ASDExplicitGamma.Cold.NativeSharpLocalIndependence

/-! IN-RESTRICTION-INDEPENDENCE adapters consuming the completed local sigma-field theorem. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

/-- All locally measurable tensor, history and event families inherit the same
joint independence from those entire restriction sigma-fields. -/
theorem restriction_local_observables_independent {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (U : ι → Set (Vec 2)) (hU : ∀ i, MeasurableSet (U i))
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, ∃ k : Fin 2, (3:ℝ)^m ≤ |(x-y) k|)
    {X : ∀ i, CutoffSample 2 → E i}
    (hX : ∀ i, @Measurable (CutoffSample 2) (E i) (cutoffSampleLocalSigma M m (U i)) _ (X i)) :
    iIndepFun X (cutoffSampleLaw M).toMeasure :=
  Cold.cold_iIndepFun_cutoffLocal M h hM m U hU hsep hX

end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Cold.NativeSharpCutoffRange
public import Algsuperdiff.Section3.Cutoff.CoefficientLocality
public import Algsuperdiff.Section3.Provider.BadEvents.LambdaLocal

/-! # Mutual sharp local independence for the genuine completed coefficient -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Finite intersections of local events factor exactly for sharply separated arbitrary regions. -/
theorem cold_cutoffLocal_biInter {ι : Type*} (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (U : ι → Set (Vec 2)) (hU : ∀ i, MeasurableSet (U i))
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, ∃ k : Fin 2, (3:ℝ)^m ≤ |(x-y) k|)
    (s : Finset ι) (f : ι → Set (CutoffSample 2))
    (hf : ∀ i ∈ s, MeasurableSet[cutoffSampleLocalSigma M m (U i)] (f i)) :
    (cutoffSampleLaw M).toMeasure (⋂ i ∈ s, f i) = ∏ i ∈ s, (cutoffSampleLaw M).toMeasure (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hA := hf a (Finset.mem_insert_self _ _)
    have hC : MeasurableSet[cutoffSampleLocalSigma M m (⋃ i ∈ (s:Set ι), U i)] (⋂ i ∈ s, f i) := by
      apply Finset.measurableSet_biInter
      intro i hi
      exact Algsuperdiff.Section3.Provider.BadEvents.cutoffSampleLocalSigma_mono M le_rfl (fun x hx => Set.mem_biUnion hi hx) _
        (hf i (Finset.mem_insert_of_mem hi))
    have hUnion : MeasurableSet (⋃ i ∈ (s:Set ι), U i) := s.finite_toSet.measurableSet_biUnion (fun i _ => hU i)
    have hsep' : ∀ x ∈ U a, ∀ y ∈ (⋃ i ∈ (s:Set ι), U i), ∃ k : Fin 2, (3:ℝ)^m ≤ |(x-y) k| := by
      intro x hx y hy
      obtain ⟨i,hi,hyi⟩ := Set.mem_iUnion₂.mp hy
      exact hsep a i (by intro he; subst i; exact ha hi) x hx y hyi
    have hp := (Indep_iff _ _ _).mp (cold_indep_cutoffSampleLocalSigma M h hM m _ _ (hU a) hUnion hsep')
      _ _ hA hC
    rw [Finset.set_biInter_insert,hp,Finset.prod_insert ha,ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- The full independent-family form, at the sharp coordinate range of the actual cutoff. -/
theorem cold_iIndep_cutoffLocal {ι : Type*} (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (U : ι → Set (Vec 2)) (hU : ∀ i, MeasurableSet (U i))
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, ∃ k : Fin 2, (3:ℝ)^m ≤ |(x-y) k|) :
    iIndep (fun i => cutoffSampleLocalSigma M m (U i)) (cutoffSampleLaw M).toMeasure := by
  rw [iIndep_iff]
  intro s f hf
  exact cold_cutoffLocal_biInter M h hM m U hU hsep s f (fun i hi => hf i hi)

/-- Arbitrary locally measurable observables of the separated cutoff cells are mutually independent. -/
theorem cold_iIndepFun_cutoffLocal {ι : Type*} {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (U : ι → Set (Vec 2)) (hU : ∀ i, MeasurableSet (U i))
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, ∃ k : Fin 2, (3:ℝ)^m ≤ |(x-y) k|)
    {X : ∀ i, CutoffSample 2 → E i}
    (hX : ∀ i, @Measurable (CutoffSample 2) (E i) (cutoffSampleLocalSigma M m (U i)) _ (X i)) :
    iIndepFun X (cutoffSampleLaw M).toMeasure := by
  rw [iIndepFun_iff_iIndep]
  exact iIndep_of_iIndep_of_le (cold_iIndep_cutoffLocal M h hM m U hU hsep) (fun i => (hX i).comap_le)

end ASDExplicitGamma.Cold

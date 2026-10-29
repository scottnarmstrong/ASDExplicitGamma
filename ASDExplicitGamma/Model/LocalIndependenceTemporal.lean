module

public import ASDExplicitGamma.Model.Cutoff

/-! Whole lower-cutoff information is independent of every later shell block. -/
@[expose] public section
namespace ASDExplicitGamma.Model
open Homogenization MeasureTheory ProbabilityTheory
open Algsuperdiff.Section3

/-- Later-shell information on the genuine cutoff carrier, retaining the entire block. -/
@[instance_reducible] noncomputable def cutoffLaterSigma (J : Set ℤ) : MeasurableSpace (Cutoff.CutoffSample 2) :=
  (Cutoff.shellIndexSigma (d := 2) J).comap Subtype.val

/-- Later-shell information is a sub-sigma-field of the ambient sample information. -/
theorem cutoff_later_sigma_le (J : Set ℤ) :
    cutoffLaterSigma J ≤ (inferInstance : MeasurableSpace (Cutoff.CutoffSample 2)) :=
  (MeasurableSpace.comap_mono (Cutoff.shellIndexSigma_le_borel J)).trans
    measurable_subtype_coe.comap_le

private theorem sample_preimage_measure (M : ABKModel 2) {s : Set (Cutoff.ShellSeq 2)}
    (hs : MeasurableSet s) :
    (Cutoff.cutoffSampleLaw M).toMeasure (Subtype.val ⁻¹' s) = M.P.toMeasure s := by
  rw [← Measure.map_apply_of_aemeasurable measurable_subtype_coe.aemeasurable hs,
    Cutoff.map_cutoffSampleLaw_val]

private theorem sample_preimage_ae (M : ABKModel 2) {s t : Set (Cutoff.ShellSeq 2)}
    (hst : s =ᵐ[M.P.toMeasure] t) :
    (Subtype.val : Cutoff.CutoffSample 2 → Cutoff.ShellSeq 2) ⁻¹' s =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      (Subtype.val : Cutoff.CutoffSample 2 → Cutoff.ShellSeq 2) ⁻¹' t := by
  rw [← Cutoff.map_cutoffSampleLaw_val M] at hst
  exact (Measure.tendsto_ae_map measurable_subtype_coe.aemeasurable).eventually hst

/-- The entire completed lower-cutoff information is independent of the entire
later shell block. Completion is handled by actual a.e. representatives. -/
theorem cutoff_lower_later_independent (M : ABKModel 2) (n : ℤ) (U : Set (Vec 2))
    (J : Set ℤ) (hJ : J ⊆ Set.Ioi n) :
    Indep (Cutoff.cutoffSampleLocalSigma M n U) (cutoffLaterSigma J)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hd : Disjoint (Set.Iic n) J := Set.disjoint_left.mpr (by
    intro k hk hkJ
    have h1 : k ≤ n := hk
    have h2 : n < k := hJ hkJ
    omega)
  have hi := Cutoff.indep_lowerShellLocalCompletion_shellIndexSigma_of_disjoint M hd U
  rw [Indep_iff]
  intro s t hs ht
  obtain ⟨s', hs', rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  obtain ⟨t', ht', rfl⟩ := MeasurableSpace.measurableSet_comap.mp ht
  obtain ⟨s0, hs0, he⟩ := hs'
  have hs0b : MeasurableSet s0 := Cutoff.lowerShellLocalSigma_le_borel n U s0 hs0
  have htb : MeasurableSet t' := Cutoff.shellIndexSigma_le_borel J t' ht'
  have hae := sample_preimage_ae M he
  have hiae := hae.inter (Filter.EventuallyEq.rfl (f := (Subtype.val : Cutoff.CutoffSample 2 → Cutoff.ShellSeq 2) ⁻¹' t'))
  calc
    _ = (Cutoff.cutoffSampleLaw M).toMeasure (Subtype.val ⁻¹' s0 ∩ Subtype.val ⁻¹' t') :=
      measure_congr hiae
    _ = M.P.toMeasure (s0 ∩ t') := sample_preimage_measure M (hs0b.inter htb)
    _ = M.P.toMeasure s0 * M.P.toMeasure t' :=
      (Indep_iff _ _ M.P.toMeasure).mp hi s0 t' ⟨s0, hs0, Filter.EventuallyEq.rfl⟩ ht'
    _ = (Cutoff.cutoffSampleLaw M).toMeasure (Subtype.val ⁻¹' s0) *
        (Cutoff.cutoffSampleLaw M).toMeasure (Subtype.val ⁻¹' t') := by
      rw [sample_preimage_measure M hs0b, sample_preimage_measure M htb]
    _ = _ := congrArg (fun r => r * (Cutoff.cutoffSampleLaw M).toMeasure (Subtype.val ⁻¹' t'))
      (measure_congr hae).symm

end ASDExplicitGamma.Model

module

public import ASDExplicitGamma.Model.Cutoff

/-! Independence of the completed OLD coefficient information from the entire
fresh shell sigma-algebra on the genuine cutoff sample space. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
noncomputable section

/-- All strictly later shells, retaining their full spatial fields. -/
abbrev upperCellFreshSigma (n : ℤ) : MeasurableSpace (Cutoff.CutoffSample 2) :=
  (Cutoff.shellIndexSigma (Set.Ioi n)).comap Subtype.val

private theorem upper_cell_ae_preimage
    (M : ABKModel 2) {s t : Set (Cutoff.ShellSeq 2)} (hst : s =ᵐ[M.P.toMeasure] t) :
    (Subtype.val : Cutoff.CutoffSample 2 → Cutoff.ShellSeq 2) ⁻¹' s =ᵐ[
      (Cutoff.cutoffSampleLaw M).toMeasure]
      (Subtype.val : Cutoff.CutoffSample 2 → Cutoff.ShellSeq 2) ⁻¹' t := by
  rw [←Cutoff.map_cutoffSampleLaw_val M] at hst
  exact (Measure.tendsto_ae_map measurable_subtype_coe.aemeasurable).eventually hst

private theorem upper_cell_measure_preimage
    (M : ABKModel 2) {s : Set (Cutoff.ShellSeq 2)} (hs : MeasurableSet s) :
    (Cutoff.cutoffSampleLaw M).toMeasure
      ((Subtype.val : Cutoff.CutoffSample 2 → Cutoff.ShellSeq 2) ⁻¹' s) = M.P.toMeasure s := by
  rw [←Measure.map_apply_of_aemeasurable measurable_subtype_coe.aemeasurable hs,
    Cutoff.map_cutoffSampleLaw_val]

/-- Completion of the OLD local information preserves independence from all
fresh shells; this is not an independence assumption about fresh observables. -/
theorem upper_cell_old_fresh_sigma_independent (M : ABKModel 2) (n : ℤ) :
    Indep (Cutoff.cutoffSampleLocalSigma M n Set.univ) (upperCellFreshSigma n)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hi := Cutoff.indep_lowerShellLocalCompletion_shellIndexSigma_of_disjoint
    M (show Disjoint (Set.Iic n) (Set.Ioi n) from Set.disjoint_left.mpr
      (fun k hk hk' => (show n<k from hk').not_ge hk)) Set.univ
  rw [Indep_iff]
  intro s t hs ht
  rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨s',hs',rfl⟩
  rcases MeasurableSpace.measurableSet_comap.mp ht with ⟨t',ht',rfl⟩
  obtain ⟨s0,hs0,hs'0⟩ := hs'
  have hs0b : MeasurableSet s0 := Cutoff.lowerShellLocalSigma_le_borel n Set.univ s0 hs0
  have htb : MeasurableSet t' := Cutoff.shellIndexSigma_le_borel (Set.Ioi n) t' ht'
  have hsCut := upper_cell_ae_preimage M hs'0
  have hst : (Subtype.val : Cutoff.CutoffSample 2 → Cutoff.ShellSeq 2) ⁻¹' (s'∩t') =ᵐ[
      (Cutoff.cutoffSampleLaw M).toMeasure]
      (Subtype.val : Cutoff.CutoffSample 2 → Cutoff.ShellSeq 2) ⁻¹' (s0∩t') := by
    simpa only [Set.preimage_inter] using hsCut.inter Filter.EventuallyEq.rfl
  rw [←Set.preimage_inter,measure_congr hst,measure_congr hsCut,
    upper_cell_measure_preimage M (hs0b.inter htb),
    upper_cell_measure_preimage M hs0b,upper_cell_measure_preimage M htb]
  exact (Indep_iff _ _ M.P.toMeasure).mp hi s0 t' ⟨s0,hs0,Filter.EventuallyEq.rfl⟩ ht'

/-- Measurable OLD and fresh observables are independent. A single fresh
observable may be a pair, so correlation within that pair is retained. -/
theorem upper_cell_old_fresh_observables_independent
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (M : ABKModel 2) (n : ℤ) (X : Cutoff.CutoffSample 2 → E) (Y : Cutoff.CutoffSample 2 → F)
    (hX : @Measurable _ _ (Cutoff.cutoffSampleLocalSigma M n Set.univ) _ X)
    (hY : @Measurable _ _ (upperCellFreshSigma n) _ Y) :
    IndepFun X Y (Cutoff.cutoffSampleLaw M).toMeasure := by
  apply (IndepFun_iff_Indep _ _ _).mpr
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (upper_cell_old_fresh_sigma_independent M n) hX.comap_le) hY.comap_le

/-- Each strictly later whole shell is measurable from the fresh information. -/
theorem upper_cell_shell_fresh_measurable (n k : ℤ) (hk : n<k) :
    @Measurable _ _ (upperCellFreshSigma n) _
      (fun ω : Cutoff.CutoffSample 2 => ω.val k) :=
  (Cutoff.measurable_shellCoordinate_shellIndexSigma (I := Set.Ioi n) hk).comp
    (Measurable.of_comap_le le_rfl)

end
end ASDExplicitGamma.Scalar

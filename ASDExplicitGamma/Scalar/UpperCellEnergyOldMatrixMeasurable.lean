module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalIndependence
public import ASDExplicitGamma.Scalar.UpperCellEnergyOldPrincipal

/-! OLD matrix entry measurability on the completed coefficient information. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory Variational Algsuperdiff.Section3
noncomputable section

/-- Every coarse matrix entry is OLD, including the off-diagonal blocks. -/
theorem upper_cell_old_matrix_entry_measurable
    (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (α β : BlockCoord 2) :
    @Measurable _ _ (Cutoff.cutoffSampleLocalSigma M n Set.univ) _
      (fun ω => blockMatEntry (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu n ω).toFun) α β) := by
  letI oldDomain : MeasurableSpace (Cutoff.CutoffSample 2) := Cutoff.cutoffSampleLocalSigma M n Set.univ
  have hMu (P : BlockVec 2) : Measurable (fun ω =>
      Mu (cubeSet Q) P (Cutoff.coefficientCutoff M.nu n ω).toFun) :=
    Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_Mu_cubeSet
      (Model.measurable_coefficientCutoff_local_field M n)
      (fun ω => Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M n ω) Q P
  have hentry (a b : BlockCoord 2) : Measurable (fun ω =>
      coarseBlockEntry (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun a b) := by
    by_cases hab : a = b
    · simpa only [coarseBlockEntry, dif_pos hab] using (hMu (blockBasis a)).const_mul 2
    · simp only [coarseBlockEntry, dif_neg hab]
      exact ((hMu (blockBasis a + blockBasis b)).sub (hMu (blockBasis a))).sub (hMu (blockBasis b))
  cases α with
  | inl i =>
    cases β with
    | inl j => exact hentry (.inl i) (.inl j)
    | inr j => exact hentry (.inl i) (.inr j)
  | inr i =>
    cases β with
    | inl j => exact hentry (.inr i) (.inl j)
    | inr j => exact hentry (.inr i) (.inr j)

/-- Deterministic true-frame normalization preserves OLD measurability. -/
theorem upper_cell_old_framed_entry_measurable
    (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (sigma : ℝ) (α β : BlockCoord 2) :
    @Measurable _ _ (Cutoff.cutoffSampleLocalSigma M n Set.univ) _
      (fun ω => blockMatEntry (frameMatrix sigma (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu n ω).toFun)) α β) := by
  letI oldDomain : MeasurableSpace (Cutoff.CutoffSample 2) := Cutoff.cutoffSampleLocalSigma M n Set.univ
  cases α with
  | inl i =>
    cases β with
    | inl j => exact (upper_cell_old_matrix_entry_measurable M n Q (.inl i) (.inl j)).const_mul _
    | inr j => exact upper_cell_old_matrix_entry_measurable M n Q (.inl i) (.inr j)
  | inr i =>
    cases β with
    | inl j => exact upper_cell_old_matrix_entry_measurable M n Q (.inr i) (.inl j)
    | inr j => exact (upper_cell_old_matrix_entry_measurable M n Q (.inr i) (.inr j)).const_mul _

/-- The actual framed OLD entry is independent of the whole fresh mean vector. -/
theorem upper_cell_old_entry_physical_mean_independent
    (M : ABKModel 2) (n terminal : ℤ) (Q : TriadicCube 2) (sigma c : ℝ)
    (e : Vec 2) (α β : BlockCoord 2) :
    IndepFun (fun ω => blockMatEntry (frameMatrix sigma (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu n ω).toFun)) α β)
      (upperCellPhysicalPotentialMean M n terminal c e Q)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  apply upper_cell_old_fresh_observables_independent M n
  · exact upper_cell_old_framed_entry_measurable M n Q sigma α β
  · letI freshDomain : MeasurableSpace (Cutoff.CutoffSample 2) := upperCellFreshSigma n
    exact measurable_pi_iff.mpr
      (upper_cell_physical_potential_mean_fresh_measurable M n terminal c e Q)

end
end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Inverse.ClippedMatrixHistoryLocal
public import ASDExplicitGamma.Model.LocalIndependenceTemporal
public import Mathlib.Probability.ConditionalExpectation

/-! Conditional expectations of the actual full clipped matrix, before any geometry selection. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped Matrix.Norms.Elementwise ENNReal

private instance clippedConditionalMatrixBorelSpace : BorelSpace (FullBlockMat 2) := by
  change BorelSpace (BlockCoord 2 → BlockCoord 2 → ℝ)
  infer_instance

private instance clippedConditionalMatrixPseudoMetrizable :
    TopologicalSpace.PseudoMetrizableSpace (FullBlockMat 2) := by
  change TopologicalSpace.PseudoMetrizableSpace (BlockCoord 2 → BlockCoord 2 → ℝ)
  infer_instance

private instance clippedConditionalMatrixSecondCountable : SecondCountableTopology (FullBlockMat 2) := by
  change SecondCountableTopology (BlockCoord 2 → BlockCoord 2 → ℝ)
  infer_instance

/-- The actual whole-history clipping is local to the same lower-shell information. -/
theorem clipped_cell_matrix_local_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (tau : ℝ) {U : Set (Vec 2)} (hQU : cubeSet Q ⊆ U) :
    @Measurable (Cutoff.CutoffSample 2) (FullBlockMat 2) (Cutoff.cutoffSampleLocalSigma M n U) _
      (clippedCellMatrix M n Q tau) := by
  let clippedConditionalInfo : MeasurableSpace (Cutoff.CutoffSample 2) := Cutoff.cutoffSampleLocalSigma M n U
  have hE : MeasurableSet (clippedCellGoodEvent M n Q tau) :=
    measurableSet_le (clipped_raw_history_local_measurable M n Q hQU) measurable_const
  exact (clipped_source_local_measurable M n Q hQU).indicator hE

/-- The literal clipped matrix is ambient-measurable as well as lower-shell local. -/
theorem clipped_cell_matrix_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (tau : ℝ) :
    Measurable (clippedCellMatrix M n Q tau) := by
  have hh := (clipped_full_frame_measurable (Annealed.sigmaBar M n : ℝ)).comp
    (history_full_coarse_measurable M n Q)
  have hs : Measurable (clippedSourceMatrix M n Q) := by
    convert hh using 1
    funext ω
    simp only [Function.comp_apply, ofFullBlockMat_toFullBlockMat]
    rfl
  exact hs.indicator (clipped_cell_good_event_measurable M n Q tau)

/-- Conditioning on the entire later-shell block leaves the full clipped mean
unchanged. No independence of the selected height or cluster mask is assumed. -/
theorem clipped_cell_condExp_eq (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (tau : ℝ)
    (J : Set ℤ) (hJ : J ⊆ Set.Ioi n) :
    (Cutoff.cutoffSampleLaw M).toMeasure[clippedCellMatrix M n Q tau | Model.cutoffLaterSigma J] =ᵐ[
      (Cutoff.cutoffSampleLaw M).toMeasure]
      fun _ => ∫ ω, clippedCellMatrix M n Q tau ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have hm := clipped_cell_matrix_measurable M n Q tau
  have hl := clipped_cell_matrix_local_measurable M n Q tau (U := Set.univ) (Set.subset_univ _)
  have hi := indep_of_indep_of_le_left
    (Model.cutoff_lower_later_independent M n Set.univ J hJ) hl.comap_le
  have hsm : StronglyMeasurable[(inferInstance : MeasurableSpace (FullBlockMat 2)).comap
      (clippedCellMatrix M n Q tau)] (clippedCellMatrix M n Q tau) := by
    exact (show @Measurable _ _
      ((inferInstance : MeasurableSpace (FullBlockMat 2)).comap (clippedCellMatrix M n Q tau)) _
      (clippedCellMatrix M n Q tau) from Measurable.of_comap_le le_rfl).stronglyMeasurable
  exact condExp_indep_eq hm.comap_le (Model.cutoff_later_sigma_le J) hsm hi

end ASDExplicitGamma.Inverse

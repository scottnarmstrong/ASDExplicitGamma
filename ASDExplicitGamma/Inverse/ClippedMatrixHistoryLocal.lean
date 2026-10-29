module

public import ASDExplicitGamma.Inverse.ClippedMatrixLocal

/-! Infinite old-history clipping is measurable in the same lower-shell information. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped Matrix.Norms.Elementwise ENNReal

/-- The reflected operator norm is a measurable function of the full framed matrix. -/
theorem clipped_operator_map_measurable : Measurable (fun A : FullBlockMat 2 =>
    ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (historyDefectMatrix (ofFullBlockMat A))‖) := by
  have hH : Measurable (fun A : FullBlockMat 2 => historyDefectMatrix (ofFullBlockMat A)) := by
    apply Measurable.of_eval_matrix
    intro i j
    have he (A : FullBlockMat 2) : historyDefectMatrix (ofFullBlockMat A) i j =
        (1 / 2 : ℝ) * (A i j + A (Sum.swap i) (Sum.swap j)) - (1 : FullBlockMat 2) i j := by
      cases i <;> cases j <;> rfl
    simp_rw [he]
    have hi : Measurable (fun A : FullBlockMat 2 => A i j) :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    have hj : Measurable (fun A : FullBlockMat 2 => A (Sum.swap i) (Sum.swap j)) :=
      (measurable_pi_apply (Sum.swap j)).comp (measurable_pi_apply (Sum.swap i))
    exact ((hi.add hj).const_mul (1 / 2 : ℝ)).sub measurable_const
  let L : FullBlockMat 2 →ₗ[ℝ]
      (EuclideanSpace ℝ (BlockCoord 2) →L[ℝ] EuclideanSpace ℝ (BlockCoord 2)) :=
    { toFun := fun A => Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A
      map_add' := fun A B => map_add (Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)) A B
      map_smul' := fun r A => map_smul (Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)) r A }
  exact L.continuous_of_finiteDimensional.norm.measurable.comp hH

/-- The genuine operator defect retains lower-shell locality. -/
theorem clipped_operator_local_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    {U : Set (Vec 2)} (hQU : cubeSet Q ⊆ U) :
    @Measurable (Cutoff.CutoffSample 2) ℝ (Cutoff.cutoffSampleLocalSigma M n U) _
      (historyOperatorDefect M n Q) := by
  have hh := clipped_operator_map_measurable.comp (clipped_source_local_measurable M n Q hQU)
  convert hh using 1
  funext ω
  simp only [Function.comp_apply, clippedSourceMatrix, ofFullBlockMat_toFullBlockMat]
  rfl

/-- Local finite maxima need measurability only at indices that occur. -/
theorem clipped_finite_max_measurable {ι Ω : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (f : ι → Ω → ℝ≥0∞) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (historyFiniteMax s f) := by
  classical
  change Measurable (fun ω => s.sup (fun i => f i ω))
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty] using measurable_const (a := (⊥ : ℝ≥0∞))
  | @insert i s hi ih =>
    have hm := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sup_insert] using (hf i (Finset.mem_insert_self i s)).max hm

/-- All descendant observations in the raw history remain in the same local information. -/
theorem clipped_raw_history_local_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    {U : Set (Vec 2)} (hQU : cubeSet Q ⊆ U) :
    @Measurable (Cutoff.CutoffSample 2) ℝ≥0∞ (Cutoff.cutoffSampleLocalSigma M n U) _
      (clippedCellRawHistory M n Q) := by
  let clippedHistoryInfo : MeasurableSpace (Cutoff.CutoffSample 2) := Cutoff.cutoffSampleLocalSigma M n U
  apply Measurable.tsum
  intro r
  apply Measurable.const_mul
  apply clipped_finite_max_measurable
  intro R hR
  exact (clipped_operator_local_measurable M n R
    ((cubeSet_subset_of_mem_descendantsAtDepth hR).trans hQU)).ennreal_ofReal

end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Native.ParentRowHistoryMoments
public import ASDExplicitGamma.Native.ParentRowFlatSpatial
public import ASDExplicitGamma.Native.OldSignedCellAverageExpectation
public import ASDExplicitGamma.Native.ParentBoundaryInverseBulk

/-! Annealed flat energies with the exact deterministic spatial weights. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Main Algsuperdiff.Section3
noncomputable section

/-- The full matrix term is paid after spatial averaging with its exact
deterministic oscillation weight. -/
theorem parent_row_flat_matrix_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (height r : ℕ) (hr : r≤5) (hheight : 1≤height)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let C := parentHistorySourceEnvelope height r t
    let A := 1+2*C+Real.sqrt (2*C)
    Integrable (parentRowFlatMatrixEnergy M n height r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,parentRowFlatMatrixEnergy M n height r t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      A*descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2) := by
  intro Q C A
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let H := fun (U : OldSignedCellIndex Q r) ω =>
    oldSignedMaxTraceHistory U.val (parentBoundaryBandFrameField M n height t ω)
  let mat := fun U ω => 1+2*H U ω+Real.sqrt (2*H U ω)
  have hm (U : OldSignedCellIndex Q r) :=
    parent_row_matrix_corrector_moments M h hM hg n hpast hstate height r hr hheight U.val U.property t ht
  have hA : 0≤A := add_nonneg (add_nonneg (by norm_num)
    (mul_nonneg (by norm_num) (sq_nonneg _))) (Real.sqrt_nonneg _)
  have hmat (U : OldSignedCellIndex Q r) (ω) : 0≤mat U ω :=
    add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num)
      (parent_boundary_band_max_trace_history_nonneg M n height r U.val U.property t ω))) (Real.sqrt_nonneg _)
  have he (U : OldSignedCellIndex Q r) := (old_signed_history_first_second_moments μ
    (mat U) A (hm U).1 (hmat U) hA (hm U).2.1).1
  have hh := old_signed_cell_weighted_expectation μ Q r mat
    (fun U => oldSignedFlatOscillationSize Q U.val b L false^2) A
    (fun U => (hm U).1.integrable (by norm_num)) (fun _ => sq_nonneg _) (fun U => he U)
  refine ⟨hh.1,?_⟩
  rw [old_signed_cell_average_eq_descendantsAverage Q r
    (fun U => oldSignedFlatOscillationSize Q U b L false^2)] at hh
  exact hh.2

/-- The corrector cross retains theta and only one physical variance after
the exact minus flat-energy partition. -/
theorem parent_row_flat_corrector_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (height r : ℕ) (hr : r≤5) (hheight : 1≤height)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let C := parentHistorySourceEnvelope height r t
    let A := 1+2*C+Real.sqrt (2*C)
    Integrable (parentRowFlatCorrectorEnergy M n height r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,parentRowFlatCorrectorEnergy M n height r t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (theta M*((1+inverseHistoryDiscount)*A*C))*
        parentBoundaryDirichletEnergy (originCube 2 n) b L := by
  intro C A
  let Q := originCube 2 n
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let H := fun (U : OldSignedCellIndex Q r) ω =>
    oldSignedMaxTraceHistory U.val (parentBoundaryBandFrameField M n height t ω)
  let F := fun U ω => (1+inverseHistoryDiscount)*(1+2*H U ω+Real.sqrt (2*H U ω))*H U ω
  have hm (U : OldSignedCellIndex Q r) :=
    parent_row_matrix_corrector_moments M h hM hg n hpast hstate height r hr hheight U.val U.property t ht
  have hh := old_signed_cell_weighted_expectation μ Q r F
    (fun U => oldSignedFlatL2Size Q U.val b L false^2) (theta M*((1+inverseHistoryDiscount)*A*C))
    (fun U => (hm U).2.2.1) (fun _ => sq_nonneg _) (fun U => (hm U).2.2.2)
  refine ⟨hh.1, ?_⟩
  rw [old_signed_cell_average_eq_descendantsAverage Q r
    (fun U => oldSignedFlatL2Size Q U b L false^2)] at hh
  have hY : descendantsAverage Q r (fun U => oldSignedFlatL2Size Q U b L false^2) =
      parentBoundaryDirichletEnergy Q b L := by
    rw [old_signed_flat_l2_size_partition, old_signed_flat_l2_size_sq]
    simp only [oldSignedFlatInput,Bool.false_eq_true,ite_false,old_signed_flat_minus_l2_mode]
    rfl
  rw [hY] at hh
  exact hh.2

end
end ASDExplicitGamma.Native

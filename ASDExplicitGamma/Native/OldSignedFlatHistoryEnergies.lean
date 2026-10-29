module

public import ASDExplicitGamma.Native.OldSignedCellAverageExpectation
public import ASDExplicitGamma.Native.OldSignedQ1MatrixMoments
public import ASDExplicitGamma.Native.OldSignedFlatProfileCaps

/-! Spatial matrix and corrector energies in the OLD flat block. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Main Algsuperdiff.Section3
noncomputable section

/-- Full matrix history majorant weighted by the actual minus oscillations. -/
def oldSignedActualFlatMatrixEnergy (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  oldSignedCellAverage Q r (fun U =>
    let H := oldSignedMaxTraceHistory U.val (oldSignedPartialFrameField M n 1 t ω)
    (1+2*H+Real.sqrt (2*H))*oldSignedFlatOscillationSize Q U.val b L false^2)

/-- Corrector history majorant weighted by the actual flat minus energy. -/
def oldSignedActualFlatCorrectorEnergy (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  oldSignedCellAverage Q r (fun U =>
    let H := oldSignedMaxTraceHistory U.val (oldSignedPartialFrameField M n 1 t ω)
    ((1+inverseHistoryDiscount)*(1+2*H+Real.sqrt (2*H))*H)*oldSignedFlatL2Size Q U.val b L false^2)

/-- The full matrix term is paid after spatial averaging with its exact
deterministic oscillation weight. -/
theorem old_signed_q1_flat_matrix_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (r : ℕ) (hr : r=5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let C := oldSignedQ1PanelHistory t
    let A := 1+2*C+Real.sqrt (2*C)
    Integrable (oldSignedActualFlatMatrixEnergy M n r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualFlatMatrixEnergy M n r t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      A*descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2) := by
  intro Q C A
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let H := fun (U : OldSignedCellIndex Q r) ω =>
    oldSignedMaxTraceHistory U.val (oldSignedPartialFrameField M n 1 t ω)
  let mat := fun U ω => 1+2*H U ω+Real.sqrt (2*H U ω)
  have hm (U : OldSignedCellIndex Q r) :=
    old_signed_q1_matrix_corrector_moments M h hM hg n hpast r hr U.val U.property t ht
  have hA : 0≤A := add_nonneg (add_nonneg (by norm_num)
    (mul_nonneg (by norm_num) (sq_nonneg _))) (Real.sqrt_nonneg _)
  have hmat (U : OldSignedCellIndex Q r) (ω) : 0≤mat U ω :=
    add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num)
      (old_signed_actual_max_trace_history_nonneg M n r U.val U.property t ω))) (Real.sqrt_nonneg _)
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
theorem old_signed_q1_flat_corrector_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (r : ℕ) (hr : r=5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let C := oldSignedQ1PanelHistory t
    let A := 1+2*C+Real.sqrt (2*C)
    Integrable (oldSignedActualFlatCorrectorEnergy M n r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualFlatCorrectorEnergy M n r t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (theta M*((1+inverseHistoryDiscount)*A*C))*b^2 := by
  intro C A
  let Q := originCube 2 n
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let H := fun (U : OldSignedCellIndex Q r) ω =>
    oldSignedMaxTraceHistory U.val (oldSignedPartialFrameField M n 1 t ω)
  let F := fun U ω => (1+inverseHistoryDiscount)*(1+2*H U ω+Real.sqrt (2*H U ω))*H U ω
  have hm (U : OldSignedCellIndex Q r) :=
    old_signed_q1_matrix_corrector_moments M h hM hg n hpast r hr U.val U.property t ht
  have hh := old_signed_cell_weighted_expectation μ Q r F
    (fun U => oldSignedFlatL2Size Q U.val b L false^2) (theta M*((1+inverseHistoryDiscount)*A*C))
    (fun U => (hm U).2.2.1) (fun _ => sq_nonneg _) (fun U => (hm U).2.2.2)
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [old_signed_cell_average_eq_descendantsAverage Q r (fun U => oldSignedFlatL2Size Q U b L false^2)]
  have hC : 0≤C := sq_nonneg _
  have hA : 0≤A := add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hC)) (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_left (old_signed_flat_minus_partition_l2_cap Q r b L)
    (mul_nonneg (Cold.cold_theta_pos M).le (mul_nonneg
      (mul_nonneg (add_nonneg (by norm_num) inverse_history_discount_range.1.le) hA) hC))

end
end ASDExplicitGamma.Native

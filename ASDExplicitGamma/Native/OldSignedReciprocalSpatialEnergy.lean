module

public import ASDExplicitGamma.Native.OldSignedCellAverageExpectation
public import ASDExplicitGamma.Native.OldSignedQ1InverseMatrixMoments
public import ASDExplicitGamma.Native.OldSignedLocalHistoryMoments
public import ASDExplicitGamma.Native.OldSignedFlatOscillationCaps

/-! The correlated reciprocal oscillation energy in the OLD mixed cross. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

/-- Actual spatial energy of both reciprocal flat remainders. The matrix
majorant retains the cell history; the inverse bank is common to the tiling. -/
def oldSignedActualReciprocalSpatialEnergy (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  let B := rawShellBandLocalHistory M n 1 t ω
  oldSignedCellAverage Q r (fun U =>
    let H := oldSignedMaxTraceHistory U.val (oldSignedPartialFrameField M n 1 t ω)
    (B+1)^2*oldSignedFlatOscillationSize Q U.val b L true^2+
      (B*(1+2*H+Real.sqrt (2*H)))*oldSignedFlatOscillationSize Q U.val b L false^2)

/-- Both reciprocal mode energies are nonnegative before expectation. -/
theorem old_signed_reciprocal_spatial_energy_nonneg (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    0≤oldSignedActualReciprocalSpatialEnergy M n r t b L ω := by
  unfold oldSignedActualReciprocalSpatialEnergy oldSignedCellAverage
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro U _
  have hH := old_signed_actual_max_trace_history_nonneg M n r U.val U.property t ω
  exact add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hH)) (Real.sqrt_nonneg _)))
      (sq_nonneg _))

/-- The reciprocal spatial energy has the exact common-bank/matrix moment
payment. All random factors refer to the same actual law. -/
theorem old_signed_q1_reciprocal_spatial_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (r : ℕ) (hr : r=5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let C := oldSignedQ1PanelHistory t
    let A := 1+2*C+Real.sqrt (2*C)
    let B := (3683/2500:ℝ)
    Integrable (oldSignedActualReciprocalSpatialEnergy M n r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualReciprocalSpatialEnergy M n r t b L ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (B+1)^2*descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2)+
      (B*A)*descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2) := by
  intro Q C A B
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let bank := rawShellBandLocalHistory M n 1 t
  let H := fun (U : OldSignedCellIndex Q r) ω =>
    oldSignedMaxTraceHistory U.val (oldSignedPartialFrameField M n 1 t ω)
  let mat := fun U ω => 1+2*H U ω+Real.sqrt (2*H U ω)
  have hb := old_signed_actual_local_history_moments M h hM hg n (fun l hl => hpast l hl.le) t ht
  have hm (U : OldSignedCellIndex Q r) :=
    old_signed_q1_inverse_matrix_product M h hM hg n hpast r hr U.val U.property t ht
  have hp := old_signed_cell_weighted_expectation μ Q r (fun _ ω => (bank ω+1)^2)
    (fun U => oldSignedFlatOscillationSize Q U.val b L true^2) ((B+1)^2)
    (fun _ => hb.2.2.1) (fun _ => sq_nonneg _) (fun _ => hb.2.2.2)
  have hn := old_signed_cell_weighted_expectation μ Q r (fun U ω => bank ω*mat U ω)
    (fun U => oldSignedFlatOscillationSize Q U.val b L false^2) (B*A)
    (fun U => (hm U).1) (fun _ => sq_nonneg _) (fun U => (hm U).2)
  have he : oldSignedActualReciprocalSpatialEnergy M n r t b L=
      fun ω => oldSignedCellAverage Q r (fun U => (bank ω+1)^2*oldSignedFlatOscillationSize Q U.val b L true^2)+
        oldSignedCellAverage Q r (fun U => bank ω*mat U ω*oldSignedFlatOscillationSize Q U.val b L false^2) := by
    funext ω
    exact old_signed_cell_average_add Q r _ _
  rw [he]
  refine ⟨hp.1.add hn.1,?_⟩
  rw [integral_add hp.1 hn.1]
  have hh := add_le_add hp.2 hn.2
  rw [old_signed_cell_average_eq_descendantsAverage Q r
    (fun U => oldSignedFlatOscillationSize Q U b L true^2),
    old_signed_cell_average_eq_descendantsAverage Q r
    (fun U => oldSignedFlatOscillationSize Q U b L false^2)] at hh
  exact hh

end
end ASDExplicitGamma.Native

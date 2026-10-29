module

public import ASDExplicitGamma.Native.OldSignedReciprocalSpatialEnergy
public import ASDExplicitGamma.Native.OldSignedRootOffsetMoment

/-! Complete reciprocal derivative energy, including the additive one. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

/-- The reciprocal derivative multiplier is retained inside the actual
spatial average; the bank and matrix are correlated. -/
def oldSignedActualReciprocalOffsetEnergy (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  let B := rawShellBandLocalHistory M n 1 t ω
  oldSignedCellAverage Q r (fun U =>
    let H := oldSignedMaxTraceHistory U.val (oldSignedPartialFrameField M n 1 t ω)
    (Real.sqrt (B*(1+2*H+Real.sqrt (2*H)))+1)^2*oldSignedFlatOscillationSize Q U.val b L false^2)

/-- The offset spatial energy is pointwise nonnegative. -/
theorem old_signed_reciprocal_offset_energy_nonneg (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    0≤oldSignedActualReciprocalOffsetEnergy M n r t b L ω := by
  unfold oldSignedActualReciprocalOffsetEnergy oldSignedCellAverage
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- Sharp offset moment for the reciprocal derivative feedback, with all
model moment inputs discharged and no independence premise. -/
theorem old_signed_q1_reciprocal_offset_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (r : ℕ) (hr : r=5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let C := oldSignedQ1PanelHistory t
    let A := 1+2*C+Real.sqrt (2*C)
    let B := (3683/2500:ℝ)
    Integrable (oldSignedActualReciprocalOffsetEnergy M n r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualReciprocalOffsetEnergy M n r t b L ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (Real.sqrt (B*A)+1)^2*descendantsAverage Q r
        (fun U => oldSignedFlatOscillationSize Q U b L false^2) := by
  intro Q C A B
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let bank := rawShellBandLocalHistory M n 1 t
  let H := fun (U : OldSignedCellIndex Q r) ω =>
    oldSignedMaxTraceHistory U.val (oldSignedPartialFrameField M n 1 t ω)
  let mat := fun U ω => 1+2*H U ω+Real.sqrt (2*H U ω)
  have hC : 0≤C := sq_nonneg _
  have hBA : 0≤B*A := mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hC)) (Real.sqrt_nonneg _))
  have hm (U : OldSignedCellIndex Q r) :=
    old_signed_q1_inverse_matrix_product M h hM hg n hpast r hr U.val U.property t ht
  have hoff (U : OldSignedCellIndex Q r) := old_signed_root_offset_moment μ
    (fun ω => bank ω*mat U ω) (B*A) (hm U).1 (fun ω =>
      mul_nonneg (show 0≤bank ω from ENNReal.toReal_nonneg)
        (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num)
          (old_signed_actual_max_trace_history_nonneg M n r U.val U.property t ω)))
            (Real.sqrt_nonneg _))) hBA (hm U).2
  have hh := old_signed_cell_weighted_expectation μ Q r
    (fun U ω => (Real.sqrt (bank ω*mat U ω)+1)^2)
    (fun U => oldSignedFlatOscillationSize Q U.val b L false^2) ((Real.sqrt (B*A)+1)^2)
    (fun U => (hoff U).1) (fun _ => sq_nonneg _) (fun U => (hoff U).2)
  refine ⟨hh.1,?_⟩
  rw [old_signed_cell_average_eq_descendantsAverage Q r
    (fun U => oldSignedFlatOscillationSize Q U b L false^2)] at hh
  exact hh.2

end
end ASDExplicitGamma.Native

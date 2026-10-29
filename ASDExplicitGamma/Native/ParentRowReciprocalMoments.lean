module

public import ASDExplicitGamma.Native.ParentRowInverseMatrixMoments
public import ASDExplicitGamma.Native.ParentRowSourceMixedSpatial
public import ASDExplicitGamma.Native.ParentRowDerivativeProfiles
public import ASDExplicitGamma.Native.OldSignedCellAverageExpectation
public import ASDExplicitGamma.Native.OldSignedRootOffsetMoment

/-! Correlated reciprocal energies on the simultaneous parent band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Main Triadic Cold Variational Algsuperdiff.Section3
noncomputable section

/-- The actual inverse multiplier and its reciprocal offset retain the bank
constant under the first and second moments used by the flat error bill. -/
theorem parent_row_bank_offset_moments
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ l<n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    let B := fun ω => (nativeSourceBandHistory M n height t ω).toReal
    Integrable B (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,B ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤(3683/2500:ℝ) ∧
    Integrable (fun ω => (B ω+1)^2) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,(B ω+1)^2 ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤((3683/2500:ℝ)+1)^2 := by
  intro B
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hb := parent_row_band_history_L2 M h hM hg n height hpast t ht.2
  have hb0 (ω) : 0≤B ω := ENNReal.toReal_nonneg
  have hfirst := old_signed_history_first_second_moments μ B (3683/2500) hb.1 hb0 (by norm_num) hb.2
  have hoff : MemLp (fun ω => B ω+1) 2 μ := hb.1.add (memLp_const (1:ℝ))
  have hone : lpNorm (fun _ : Cutoff.CutoffSample 2 => (1:ℝ)) 2 μ=1 := by
    rw [lpNorm_const' (by norm_num) (by norm_num)]
    simp only [norm_one,probReal_univ,Real.one_rpow,mul_one]
  have hnorm : lpNorm (fun ω => B ω+1) 2 μ≤(3683/2500:ℝ)+1 := by
    have hh := lpNorm_add_le (g := fun _ => (1:ℝ)) hb.1 (by norm_num)
    rw [hone] at hh
    exact hh.trans (add_le_add hb.2 le_rfl)
  have hsecond := (old_signed_history_first_second_moments μ (fun ω => B ω+1)
    ((3683/2500:ℝ)+1) hoff (fun ω => add_nonneg (hb0 ω) (by norm_num)) (by norm_num) hnorm).2
  exact ⟨hb.1.integrable (by norm_num),hfirst.1,
    (memLp_two_iff_integrable_sq hoff.aestronglyMeasurable).mp hoff,hsecond⟩


/-- The reciprocal spatial energy has the exact common-bank/matrix moment
payment. All random factors refer to the same actual law. -/
theorem parent_row_reciprocal_spatial_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (height r : ℕ) (hr : r≤5) (hheight : 1≤height)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let C := parentHistorySourceEnvelope height r t
    let A := 1+2*C+Real.sqrt (2*C)
    let B := (3683/2500:ℝ)
    Integrable (parentRowReciprocalSpatialEnergy M n height r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,parentRowReciprocalSpatialEnergy M n height r t b L ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (B+1)^2*descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2)+
      (B*A)*descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2) := by
  intro Q C A B
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let bank := fun ω => (nativeSourceBandHistory M n height t ω).toReal
  let H := fun (U : OldSignedCellIndex Q r) ω =>
    oldSignedMaxTraceHistory U.val (parentBoundaryBandFrameField M n height t ω)
  let mat := fun U ω => 1+2*H U ω+Real.sqrt (2*H U ω)
  have hb := parent_row_bank_offset_moments M h hM hg n height hpast t ht
  have hm (U : OldSignedCellIndex Q r) :=
    parent_row_inverse_matrix_product M h hM hg n hpast hstate height r hr hheight U.val U.property t ht
  have hp := old_signed_cell_weighted_expectation μ Q r (fun _ ω => (bank ω+1)^2)
    (fun U => oldSignedFlatOscillationSize Q U.val b L true^2) ((B+1)^2)
    (fun _ => hb.2.2.1) (fun _ => sq_nonneg _) (fun _ => hb.2.2.2)
  have hn := old_signed_cell_weighted_expectation μ Q r (fun U ω => bank ω*mat U ω)
    (fun U => oldSignedFlatOscillationSize Q U.val b L false^2) (B*A)
    (fun U => (hm U).1) (fun _ => sq_nonneg _) (fun U => (hm U).2)
  have he : parentRowReciprocalSpatialEnergy M n height r t b L=
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


/-- Sharp offset moment for the reciprocal derivative feedback, with all
model moment inputs discharged and no independence premise. -/
theorem parent_row_reciprocal_offset_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (height r : ℕ) (hr : r≤5) (hheight : 1≤height)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let C := parentHistorySourceEnvelope height r t
    let A := 1+2*C+Real.sqrt (2*C)
    let B := (3683/2500:ℝ)
    Integrable (parentRowReciprocalOffsetEnergy M n height r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,parentRowReciprocalOffsetEnergy M n height r t b L ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (Real.sqrt (B*A)+1)^2*descendantsAverage Q r
        (fun U => oldSignedFlatOscillationSize Q U b L false^2) := by
  intro Q C A B
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let bank := fun ω => (nativeSourceBandHistory M n height t ω).toReal
  let H := fun (U : OldSignedCellIndex Q r) ω =>
    oldSignedMaxTraceHistory U.val (parentBoundaryBandFrameField M n height t ω)
  let mat := fun U ω => 1+2*H U ω+Real.sqrt (2*H U ω)
  have hC : 0≤C := sq_nonneg _
  have hBA : 0≤B*A := mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hC)) (Real.sqrt_nonneg _))
  have hm (U : OldSignedCellIndex Q r) :=
    parent_row_inverse_matrix_product M h hM hg n hpast hstate height r hr hheight U.val U.property t ht
  have hoff (U : OldSignedCellIndex Q r) := old_signed_root_offset_moment μ
    (fun ω => bank ω*mat U ω) (B*A) (hm U).1 (fun ω =>
      mul_nonneg (show 0≤bank ω from ENNReal.toReal_nonneg)
        (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num)
          (parent_boundary_band_max_trace_history_nonneg M n height r U.val U.property t ω)))
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

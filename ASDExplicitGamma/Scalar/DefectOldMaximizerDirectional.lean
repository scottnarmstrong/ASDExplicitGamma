module

public import ASDExplicitGamma.Scalar.DefectOldMaximizerMoment
public import ASDExplicitGamma.Scalar.SmoothFeedbackDirectionalHistory
public import ASDExplicitGamma.Native.OldSignedTiledWeakProjection

/-! Directional tiled weak energy of the actual affine-top defect and reciprocal gradient
at the scalar observer, its pathwise series bound by directional pair charges, and the
correlated `E[B² ·]` bound with the exact factor one half. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Triadic Variational Native Inverse Gaussian
  Algsuperdiff.Section3 Numerics.Inverse ASDExplicitGamma.Main
open scoped ENNReal BigOperators
attribute [local irreducible] Homogenization.descendantsAtDepth
noncomputable section

/-- The directional pair-charge average at depth `134 + j`. -/
def dirX (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  descendantsAverage Q (134 + j) (fun R => smoothFeedbackPairCharge M m R e ω)

theorem cellT_eq_raw (M : ABKModel 2) (m : ℤ) (R : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    smoothFeedbackCellT M m R ω = rawCubeFourLoadTrace M m R 0 ω := by
  unfold smoothFeedbackCellT Cold.coldNativeCellTrace
  change traceDefect (cubeSet R) (Cutoff.coefficientCutoff M.nu m ω).toFun _ =
    traceDefect (cubeSet R) (Model.partialInsertedCoefficient M m 0 ω).toFun _
  rw [partialInserted_zero]

theorem dirX_nonneg (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) : 0 ≤ dirX M m Q e ω j :=
  descendantsAverage_nonneg Q _ _ (fun R _ =>
    (smooth_feedback_cell_pair_charge_bounds M m R e ω).1)

theorem dirX_le (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    dirX M m Q e ω j ≤ vecNormSq e * rawWeakTraceSequence M m Q 0 ω (134 + j) := by
  unfold dirX
  rw [rawSeq_eq_avg, ← descendantsAverage_mul_left]
  unfold descendantsAverage
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro R _
  have := (smooth_feedback_cell_pair_charge_bounds M m R e ω).2
  rw [cellT_eq_raw] at this
  linarith

theorem dirX_mean (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2) (j : ℕ) :
    ∫ ω, dirX M m Q e ω j ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      (1 / 2 : ℝ) * vecNormSq e *
        ∫ ω, rawWeakTraceSequence M m Q 0 ω (134 + j) ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hX : (fun ω => dirX M m Q e ω j) = fun ω =>
      ((descendantsAtDepth Q (134 + j)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q (134 + j), smoothFeedbackPairCharge M m R e ω := rfl
  have hT : (fun ω => rawWeakTraceSequence M m Q 0 ω (134 + j)) = fun ω =>
      ((descendantsAtDepth Q (134 + j)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q (134 + j), smoothFeedbackCellT M m R ω := by
    funext ω
    rw [rawSeq_eq_avg]
    unfold descendantsAverage
    simp only [cellT_eq_raw]
  have hint (R : TriadicCube 2) :
      Integrable (fun ω => smoothFeedbackPairCharge M m R e ω) μ :=
    smooth_feedback_cell_pair_charge_integrable M m R e
  have hintT (R : TriadicCube 2) :
      Integrable (fun ω => smoothFeedbackCellT M m R ω) μ := by
    have := Cold.coldNativeCellTrace_integrable M m R
    exact this
  rw [hX, hT, integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun R _ => hint R), integral_finsetSum _ (fun R _ => hintT R)]
  rw [Finset.sum_congr rfl (fun R _ => smooth_feedback_cell_mean_pair_quadratic M m R e)]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem traceSeries_summable (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      rawWeakTraceSequence M m Q 0 ω (134 + j)) := by
  have hα := Scalar.inverse_history_discount_range
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).property
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
    (oldCutoffSkewCoefficient m Q ω)
  have hfield (x : Vec 2) (hx : x ∈ openCubeSet Q) :
      responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (oldCutoffSkewCoefficient m Q ω) x =
      (Annealed.sigmaBar M m : ℝ)⁻¹ •
        (Model.partialInsertedCoefficient M m 0 ω).toFun x := by
    rw [← insertion_skew_zero]
    exact main_directional_response_frame_eq_scaled_partial_coefficient M m 0 Q ω x hx
  have hs := old_signed_trace_depth_series_summable Q _ hEll
  have hs2 := (summable_nat_add_iff 134).mpr hs
  have hs3 := hs2.mul_left ((Scalar.inverseHistoryDiscount ^ 134)⁻¹)
  refine hs3.congr (fun j => ?_)
  have hT := obs_source_trace_average_eq M m 0 ⟨le_rfl, zero_le_one⟩ ω Q _ hfield (j + 134)
  rw [hT, show j + 134 = 134 + j by omega, pow_add]
  have : Scalar.inverseHistoryDiscount ^ 134 ≠ 0 := (pow_pos hα.1 _).ne'
  have h0 : Scalar.inverseHistoryDiscount ≠ 0 := hα.1.ne'
  field_simp

end
end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Native.OldSignedSourceCellFrame
public import ASDExplicitGamma.Native.OldSignedSourceCellTraceLaw

/-! Positivity, integrability and trace domination for source-cell directions. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- The subtype-indexed raw trace is the ordinary finite descendant average. -/
theorem old_signed_raw_trace_average (M : ABKModel 2) (n : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    rawWeakTraceSequence M n U t ω j=descendantsAverage U j
      (fun V => traceDefect (cubeSet V) (Model.partialInsertedCoefficient M n t ω).toFun
        (Annealed.sigmaBar M n)) := by
  change oldSignedCellAverage U j (fun V => rawCubeFourLoadTrace M n V.val t ω)=_
  exact old_signed_cell_average_eq_descendantsAverage U j (fun V => rawCubeFourLoadTrace M n V t ω)

/-- Raw trace integrability on every source cell, independently of a moment cap. -/
theorem old_signed_source_trace_integrable (M : ABKModel 2) (n : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (j : ℕ) :
    Integrable (fun ω => rawWeakTraceSequence M n U t ω j) (Cutoff.cutoffSampleLaw M).toMeasure := by
  simp_rw [old_signed_raw_trace_average]
  unfold descendantsAverage
  dsimp only
  exact (integrable_finsetSum _ (fun V _ =>
    old_signed_trace_sample_integrable M n t ht V (Annealed.sigmaBar M n))).const_mul _

/-- Source-cell directional quadratics are genuinely integrable. -/
theorem old_signed_source_directional_integrable (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (j : ℕ) (e : Vec 2) :
    Integrable (fun ω => vecDot e (matVecMul (oldSignedPairedDepthMatrix U j
      (oldSignedPartialFrameField M n 1 t ω)) e)) (Cutoff.cutoffSampleLaw M).toMeasure := by
  simp_rw [old_signed_source_directional_matrix M n r U hU,vecDot_matVecMul_descendantsAverageMat]
  unfold descendantsAverage
  dsimp only
  exact (integrable_finsetSum _ (fun V _ =>
    old_signed_directional_sample_integrable M n t ht V (Annealed.sigmaBar M n) e)).const_mul _

/-- Directional positivity and full-trace domination on the same actual
source cell. No weighted isotropy is used in this pathwise statement. -/
theorem old_signed_source_directional_nonneg_le (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) (e : Vec 2) :
    let q := vecDot e (matVecMul (oldSignedPairedDepthMatrix U j (oldSignedPartialFrameField M n 1 t ω)) e)
    0 ≤ q ∧ q ≤ rawWeakTraceSequence M n U t ω j*vecNormSq e := by
  intro q
  let Q := originCube 2 n
  let k := oldSignedPartialResponseCoefficient n 1 t ω
  let kU := oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k
  have he := old_signed_paired_depth_matrix_congr U j
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n) kU)
    (oldSignedPartialFrameField M n 1 t ω)
    (old_signed_cell_frame_coefficient_ae Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU)
      M.nu (Annealed.sigmaBar M n) k)
  have hn (v : Vec 2) : 0 ≤ vecDot v (matVecMul
      (oldSignedPairedDepthMatrix U j (oldSignedPartialFrameField M n 1 t ω)) v) := by
    rw [←he]
    exact old_signed_paired_depth_quadratic_nonneg U j M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1 kU v
  refine ⟨hn e,?_⟩
  have hh := old_signed_nonnegative_quadratic_le_trace _ hn e
  rw [old_signed_paired_depth_matrix_trace,old_signed_source_trace_depth M n r U hU] at hh
  exact hh

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Inverse.ClippedMatrixEvent
public import Algsuperdiff.Section3.Provider.BadEvents.LambdaLocal

/-! The entire old clipped matrix reads only its actual completed lower-shell information. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped Matrix.Norms.Elementwise ENNReal

/-- Every full coarse entry is measurable in the genuine local lower-shell sigma-field. -/
theorem clipped_coarse_local_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    {U : Set (Vec 2)} (hQU : cubeSet Q ⊆ U) :
    @Measurable (Cutoff.CutoffSample 2) (FullBlockMat 2) (Cutoff.cutoffSampleLocalSigma M n U) _
      (fun ω => toFullBlockMat (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun)) := by
  let clippedLocalInfo : MeasurableSpace (Cutoff.CutoffSample 2) := Cutoff.cutoffSampleLocalSigma M n U
  have hmu (P : BlockVec 2) :=
    Provider.BadEvents.measurable_Mu_coefficientCutoff_cutoffSampleLocal M n Q hQU P
  have he (alpha beta : BlockCoord 2) : Measurable (fun ω =>
      coarseBlockEntry (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun alpha beta) := by
    by_cases h : alpha = beta
    · simpa only [coarseBlockEntry, dite_eq_left h] using (hmu (blockBasis alpha)).const_mul 2
    · simp only [coarseBlockEntry, dite_eq_right h]
      convert ((hmu (blockBasis alpha + blockBasis beta)).sub (hmu (blockBasis alpha))).sub
        (hmu (blockBasis beta)) using 1
  apply Measurable.of_eval_matrix
  intro alpha beta
  cases alpha <;> cases beta <;> simpa only [toFullBlockMat, coarseBlockMatrix] using he _ _

/-- Scalar framing is a measurable map of the full doubled matrix. -/
theorem clipped_full_frame_measurable (sigma : ℝ) :
    Measurable (fun A : FullBlockMat 2 => toFullBlockMat (Variational.frameMatrix sigma (ofFullBlockMat A))) := by
  apply Measurable.of_eval_matrix
  intro alpha beta
  cases alpha with
  | inl i =>
    cases beta with
    | inl j =>
      change Measurable (fun A : FullBlockMat 2 => sigma⁻¹ * A (Sum.inl i) (Sum.inl j))
      have hi : Measurable (fun A : FullBlockMat 2 => A (Sum.inl i) (Sum.inl j)) :=
        (measurable_pi_apply (Sum.inl j)).comp (measurable_pi_apply (Sum.inl i))
      exact hi.const_mul sigma⁻¹
    | inr j =>
      change Measurable (fun A : FullBlockMat 2 => A (Sum.inl i) (Sum.inr j))
      exact (measurable_pi_apply (Sum.inr j)).comp (measurable_pi_apply (Sum.inl i))
  | inr i =>
    cases beta with
    | inl j =>
      change Measurable (fun A : FullBlockMat 2 => A (Sum.inr i) (Sum.inl j))
      exact (measurable_pi_apply (Sum.inl j)).comp (measurable_pi_apply (Sum.inr i))
    | inr j =>
      change Measurable (fun A : FullBlockMat 2 => sigma * A (Sum.inr i) (Sum.inr j))
      have hi : Measurable (fun A : FullBlockMat 2 => A (Sum.inr i) (Sum.inr j)) :=
        (measurable_pi_apply (Sum.inr j)).comp (measurable_pi_apply (Sum.inr i))
      exact hi.const_mul sigma

/-- The full true-frame matrix retains the complete lower-shell locality. -/
theorem clipped_source_local_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    {U : Set (Vec 2)} (hQU : cubeSet Q ⊆ U) :
    @Measurable (Cutoff.CutoffSample 2) (FullBlockMat 2) (Cutoff.cutoffSampleLocalSigma M n U) _
      (clippedSourceMatrix M n Q) := by
  have hh := (clipped_full_frame_measurable (Annealed.sigmaBar M n : ℝ)).comp
    (clipped_coarse_local_measurable M n Q hQU)
  convert hh using 1
  funext ω
  simp only [Function.comp_apply, ofFullBlockMat_toFullBlockMat]
  rfl

end ASDExplicitGamma.Inverse

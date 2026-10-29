module

public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets
public import ASDExplicitGamma.Native.OldSignedCellAverage
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw
public import ASDExplicitGamma.Inverse.RawTraceHistory

/-! Exact identification of the OLD parent proxy with the actual partial
insertion's inverse maxima and common-tiling trace sequence. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Cold Algsuperdiff.Section3
noncomputable section

/-- Actual open response restriction for the parent cube during one insertion. -/
def oldSignedPartialResponseCoefficient (n : ℤ) (s : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ResponseCoefficient (openCubeSet (originCube 2 n)) :=
  pureFluxOpenResponseRestriction n
    (modelInsertedScalar (closure (cubeSet (originCube 2 n))) (n+(s:ℤ)-1) t ω)

/-- The same partial response in its fixed completed scalar frame. -/
def oldSignedPartialFrameField (M : ABKModel 2) (n : ℤ) (s : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : CoeffField 2 :=
  responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
    (oldSignedPartialResponseCoefficient n s t ω)

/-- Every actual descendant response has the correct physical scalar frame. -/
theorem old_signed_partial_cell_frame (M : ABKModel 2) (n : ℤ) (s : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (U : TriadicCube 2) (j : ℕ)
    (hU : U ∈ descendantsAtDepth (originCube 2 n) j) :
    coarseBlockMatrix (cubeSet U) (oldSignedPartialFrameField M n s t ω)=
      frameMatrix (Annealed.sigmaBar M n)
        (coarseBlockMatrix (cubeSet U) (Model.partialInsertedCoefficient M (n+(s:ℤ)-1) t ω).toFun) := by
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact (closure (cubeSet (originCube 2 n)))
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  exact pureFlux_partialInsertion_coarseMatrix_frame n M ell hK s t ω hU

/-- The framed trace sequence is the literal physical trace with frame sigma_n.
For s=1 it is exactly the raw OLD trace sequence at cutoff n. -/
theorem old_signed_partial_trace_depth (M : ABKModel 2) (n : ℤ) (s : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    descendantsAverage (originCube 2 n) j (fun U =>
      traceDefect (openCubeSet U) (oldSignedPartialFrameField M n s t ω) 1)=
    descendantsAverage (originCube 2 n) j (fun U =>
      traceDefect (cubeSet U) (Model.partialInsertedCoefficient M (n+(s:ℤ)-1) t ω).toFun
        (Annealed.sigmaBar M n)) := by
  unfold descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  unfold traceDefect
  rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U,
    old_signed_partial_cell_frame M n s t ω U j hU]
  simp only [frameMatrix,inv_one,one_mul,Matrix.trace_smul,smul_eq_mul]

/-- Exact identification with the source's common-tiling trace sequence,
not an independently chosen origin trace. -/
theorem old_signed_one_shell_trace_depth (M : ABKModel 2) (n : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    descendantsAverage (originCube 2 n) j (fun U =>
      traceDefect (openCubeSet U) (oldSignedPartialFrameField M n 1 t ω) 1)=
      rawWeakTraceSequence M n (originCube 2 n) t ω j := by
  rw [old_signed_partial_trace_depth]
  change _=oldSignedCellAverage (originCube 2 n) j (fun U => rawCubeFourLoadTrace M n U.val t ω)
  rw [old_signed_cell_average_eq_descendantsAverage (originCube 2 n) j (fun U => rawCubeFourLoadTrace M n U t ω)]
  simp only [Nat.cast_one,add_sub_cancel_right,rawCubeFourLoadTrace]

end
end ASDExplicitGamma.Native

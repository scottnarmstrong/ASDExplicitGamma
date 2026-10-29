module

public import ASDExplicitGamma.Native.OldSignedCoarseDirectionalSample
public import ASDExplicitGamma.Main.EnvelopeHTransport
public import ASDExplicitGamma.Scalar.CellTranslation

/-! Stationary transfer of the actual directional expectation identity to
every descendant cell; no cell independence is invoked. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Main Scalar Algsuperdiff.Section3
noncomputable section

/-- The actual cell coarse response is the origin response of the
translated actual cutoff sample. -/
theorem old_signed_partial_coarse_cell_translate (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    coarseBlockMatrix (cubeSet Q) (Model.partialInsertedCoefficient M m t ω).toFun=
      coarseBlockMatrix (cubeSet (originCube 2 Q.scale))
        (Model.partialInsertedCoefficient M m t (triadicCubeShift Q +ᵥ ω)).toFun := by
  rw [cubeSet_eq_translateSet_originCube_of_triadicCube Q,
    coarseBlockMatrix_translateSet_eq_translateCoeffField]
  change _=coarseBlockMatrix (cubeSet (originCube 2 Q.scale))
    (Model.partialInsertedCoefficient M m t (Cutoff.translateCutoffSample (triadicCubeShift Q) ω)).toFun
  rw [main_partialInsertedCoefficient_translate]
  rfl

/-- The directional majorant on the actual cell has the same stationary
expectation as its origin-scale counterpart. -/
theorem old_signed_coarse_directional_cell_mean_eq_origin (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (t sigma : ℝ) (e : Vec 2) :
    (∫ ω,vecDot e (matVecMul (oldSignedCoarseDirectionalMatrix Q
      (Model.partialInsertedCoefficient M m t ω).toFun sigma) e)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
    ∫ ω,vecDot e (matVecMul (oldSignedCoarseDirectionalMatrix (originCube 2 Q.scale)
      (Model.partialInsertedCoefficient M m t ω).toFun sigma) e)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have he (ω : Cutoff.CutoffSample 2) : oldSignedCoarseDirectionalMatrix Q
      (Model.partialInsertedCoefficient M m t ω).toFun sigma=
      oldSignedCoarseDirectionalMatrix (originCube 2 Q.scale)
        (Model.partialInsertedCoefficient M m t (triadicCubeShift Q +ᵥ ω)).toFun sigma := by
    unfold oldSignedCoarseDirectionalMatrix
    rw [old_signed_partial_coarse_cell_translate]
  simp_rw [he]
  exact integral_cutoffSample_vadd M (triadicCubeShift Q) (fun ω => vecDot e
    (matVecMul (oldSignedCoarseDirectionalMatrix (originCube 2 Q.scale)
      (Model.partialInsertedCoefficient M m t ω).toFun sigma) e))

/-- The actual directional half-trace identity holds on every source cell,
with the same cutoff, insertion time, and fixed physical frame. -/
theorem old_signed_coarse_directional_cell_mean (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (sigma : ℝ) (e : Vec 2) :
    (∫ ω,vecDot e (matVecMul (oldSignedCoarseDirectionalMatrix Q
      (Model.partialInsertedCoefficient M m t ω).toFun sigma) e)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
    (1/2 : ℝ)*(∫ ω,traceDefect (cubeSet Q)
      (Model.partialInsertedCoefficient M m t ω).toFun sigma
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)*vecNormSq e := by
  rw [old_signed_coarse_directional_cell_mean_eq_origin,
    old_signed_coarse_directional_sample_mean M m Q.scale t ht sigma e]
  have he (ω : Cutoff.CutoffSample 2) : traceDefect (cubeSet Q)
      (Model.partialInsertedCoefficient M m t ω).toFun sigma=
      traceDefect (cubeSet (originCube 2 Q.scale))
        (Model.partialInsertedCoefficient M m t (triadicCubeShift Q +ᵥ ω)).toFun sigma := by
    unfold traceDefect
    rw [old_signed_partial_coarse_cell_translate]
  simp_rw [he]
  rw [integral_cutoffSample_vadd M (triadicCubeShift Q) (fun ω =>
    traceDefect (cubeSet (originCube 2 Q.scale)) (Model.partialInsertedCoefficient M m t ω).toFun sigma)]

end
end ASDExplicitGamma.Native

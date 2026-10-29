module

public import ASDExplicitGamma.Inverse.ClippedMatrixQuadratic
public import ASDExplicitGamma.Inverse.HistoryDefectMeasurable

/-! The genuine cutoff matrix: true frame, positivity, integrability and exact mean. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped Matrix.Norms.Elementwise

/-- The full old response in its own true completed-label frame. -/
noncomputable def clippedSourceMatrix (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : FullBlockMat 2 :=
  toFullBlockMat (Variational.frameMatrix (Annealed.sigmaBar M n : ℝ)
    (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun))

/-- The fixed-load quadratic functional agrees with the literal block pairing. -/
theorem fullMatrixQuadratic_block (A : BlockMat 2) (P : BlockVec 2) :
    fullMatrixQuadratic (toFullBlockVec P) (toFullBlockMat A) =
      blockVecDot P (blockMatVecMul A P) := by
  change dotProduct (toFullBlockVec P) ((toFullBlockMat A).mulVec (toFullBlockVec P)) = _
  rw [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec]

/-- The full framed response is positive in every direction, at every genuine sample. -/
theorem clipped_source_quadratic_nonneg (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (v : BlockCoord 2 → ℝ) :
    0 ≤ fullMatrixQuadratic v (clippedSourceMatrix M n Q ω) := by
  obtain ⟨Lam, hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M n ω Q
  have hh := history_framed_pair_bounds Q _ M.nu_pos hEll _ (Annealed.sigmaBar_characterization M n).1
  have hp := hh.1 (ofFullBlockVec v).1 (ofFullBlockVec v).2
  have hn := hh.2 (ofFullBlockVec v).1 (ofFullBlockVec v).2
  have he := fullMatrixQuadratic_block
    (Variational.frameMatrix (Annealed.sigmaBar M n : ℝ)
      (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun)) (ofFullBlockVec v)
  rw [toFullBlockVec_ofFullBlockVec] at he
  change 0 ≤ fullMatrixQuadratic v (toFullBlockMat _)
  rw [he]
  linarith only [hp, hn]

/-- Integrability is supplied by the actual cutoff law, without a boundedness premise. -/
theorem clipped_source_integrable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) :
    Integrable (clippedSourceMatrix M n Q) (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hh : Integrable (fun a : RegCoeffField 2 => toFullBlockMat
      (Variational.frameMatrix (Annealed.sigmaBar M n : ℝ) (coarseBlockMatrix (cubeSet Q) a.toFun)))
      (Cutoff.coefficientCutoffLaw M n) :=
    Integrable.of_eval (fun i => Integrable.of_eval (fun j =>
      Variational.integrable_frameMatrix_entry M n Q _ i j))
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hh
  exact (integrable_map_measure hh.aestronglyMeasurable
    (Cutoff.measurable_coefficientCutoff M.nu n).aemeasurable).mp hh

/-- The ordinary matrix expectation equals the genuine annealed response in that same frame. -/
theorem clipped_source_integral (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) :
    (∫ ω, clippedSourceMatrix M n Q ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      toFullBlockMat (Variational.frameMatrix (Annealed.sigmaBar M n : ℝ)
        (Book.Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M n) (cubeSet Q))) := by
  have hh := Variational.integral_frameMatrix M n Q (Annealed.sigmaBar M n : ℝ)
  have hi : Integrable (fun a : RegCoeffField 2 => toFullBlockMat
      (Variational.frameMatrix (Annealed.sigmaBar M n : ℝ) (coarseBlockMatrix (cubeSet Q) a.toFun)))
      (Cutoff.coefficientCutoffLaw M n) :=
    Integrable.of_eval (fun i => Integrable.of_eval (fun j =>
      Variational.integrable_frameMatrix_entry M n Q _ i j))
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hh hi
  rw [integral_map (Cutoff.measurable_coefficientCutoff M.nu n).aemeasurable
    hi.aestronglyMeasurable] at hh
  exact hh

end ASDExplicitGamma.Inverse

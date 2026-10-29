module

public import ASDExplicitGamma.Scalar.UpperCellEnergyOldMatrixMeasurable

/-! Actual-law integrability and expectation of the OLD true-frame entries. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Variational Algsuperdiff.Section3
noncomputable section

/-- Integrability on the original sample space, not merely the coefficient law. -/
theorem upper_cell_old_framed_entry_integrable
    (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (sigma : ℝ) (α β : BlockCoord 2) :
    Integrable (fun ω => blockMatEntry (frameMatrix sigma (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu n ω).toFun)) α β) (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hi := integrable_frameMatrix_entry M n Q sigma α β
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hi
  exact (integrable_map_measure hi.aestronglyMeasurable
    (Cutoff.measurable_coefficientCutoff M.nu n).aemeasurable).mp hi

/-- The actual-law entry mean is the accepted annealed true-frame entry. -/
theorem upper_cell_old_framed_entry_integral
    (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (sigma : ℝ) (α β : BlockCoord 2) :
    (∫ ω, blockMatEntry (frameMatrix sigma (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu n ω).toFun)) α β ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
    blockMatEntry (frameMatrix sigma (Book.Ch04.annealedBlockMatrix
      (Cutoff.coefficientCutoffLaw M n) (cubeSet Q))) α β := by
  have hi := integrable_frameMatrix_entry M n Q sigma α β
  have he := integral_frameMatrix_entry M n (cubeSet Q) sigma α β
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hi he
  rw [integral_map (Cutoff.measurable_coefficientCutoff M.nu n).aemeasurable
    hi.aestronglyMeasurable] at he
  exact he

end
end ASDExplicitGamma.Scalar

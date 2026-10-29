module

public import ASDExplicitGamma.Scalar.UpperCellEnergyOldMatrixMean
public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalMeanEnergy
public import ASDExplicitGamma.Scalar.UpperCellEnergyIndependentQuadratic

/-! Principal OLD quadratic expectation at the genuine fresh potential mean. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory Variational Algsuperdiff.Section3
noncomputable section

/-- Every OLD entry can be averaged before the correlated fresh load. -/
theorem upper_cell_old_quadratic_expectation
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2) (sigma : ℝ) :
    let P := fun ω => (e, upperCellPhysicalPotentialMean M n terminal c e Q ω)
    let A := fun ω => frameMatrix sigma (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu n ω).toFun)
    let meanA := frameMatrix sigma (Book.Ch04.annealedBlockMatrix
      (Cutoff.coefficientCutoffLaw M n) (cubeSet Q))
    Integrable (fun ω => blockVecDot (P ω) (blockMatVecMul (A ω) (P ω)))
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, blockVecDot (P ω) (blockMatVecMul (A ω) (P ω)) ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, blockVecDot (P ω) (blockMatVecMul meanA (P ω)) ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let W := upperCellPhysicalPotentialMean M n terminal c e Q
  let P := fun ω => (e, W ω)
  let A := fun ω => frameMatrix sigma (coarseBlockMatrix (cubeSet Q)
    (Cutoff.coefficientCutoff M.nu n ω).toFun)
  let meanA := frameMatrix sigma (Book.Ch04.annealedBlockMatrix
    (Cutoff.coefficientCutoffLaw M n) (cubeSet Q))
  have hY (i : BlockCoord 2) : MemLp (fun ω => toFullBlockVec (P ω) i) 2 μ := by
    cases i with
    | inl i => exact memLp_const _
    | inr i => exact (upper_cell_physical_mean_coordinate_energy M n terminal c e Q i).1
  have hy (i : BlockCoord 2) : Measurable (fun w : Vec 2 => toFullBlockVec (e,w) i) := by
    cases i <;> simp only [toFullBlockVec] <;> fun_prop
  have hind (i j : BlockCoord 2) : IndepFun (fun ω => toFullBlockMat (A ω) i j)
      (fun ω => toFullBlockVec (P ω) i*toFullBlockVec (P ω) j) μ :=
    (upper_cell_old_entry_physical_mean_independent M n terminal Q sigma c e i j).comp
      measurable_id ((hy i).mul (hy j))
  have hh := upper_cell_independent_quadratic_expectation μ
    (fun ω => toFullBlockMat (A ω)) (fun ω => toFullBlockVec (P ω))
    (fun i j => upper_cell_old_framed_entry_integrable M n Q sigma i j) hY hind
  have he (i j : BlockCoord 2) : (∫ ω, toFullBlockMat (A ω) i j ∂μ) = toFullBlockMat meanA i j :=
    upper_cell_old_framed_entry_integral M n Q sigma i j
  simp_rw [he, ←upper_cell_block_quadratic_sum] at hh
  exact hh

end
end ASDExplicitGamma.Scalar

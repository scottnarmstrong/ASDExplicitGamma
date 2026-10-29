module

public import ASDExplicitGamma.Cold.SquareMatchedOptimizers
public import ASDExplicitGamma.Cold.SquareCellMean

/-! # Four-load version of the actual optimizer projection gap -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The actual total residual energy on one own cell. -/
def squareMatchedCellResidual (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : SquareMatchedOptimizers Q a)
    {r : ℕ} (f : ∀ R : SquareCells Q r, SquareMatchedOptimizers R.val a) (R : SquareCells Q r) : ℝ :=
  ∑ i : Fin 2, (volumeAverage (openCubeSet R.val)
    (scalarVariationEnergyIntegrand a (squareCellDifference Q hEll (v.primal i) (fun R => (f R).primal i) R)) +
    volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand (adjointCoeffField a)
      (squareCellDifference Q (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i)
        (fun R => (f R).adjoint i) R)))

/-- The actual four-load residual is exactly the own-cell-minus-parent energy drop. -/
theorem squareMatchedCellResidual_mean (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : SquareMatchedOptimizers Q a)
    {r : ℕ} (f : ∀ R : SquareCells Q r, SquareMatchedOptimizers R.val a) :
    squareCellMean Q r (squareMatchedCellResidual Q hEll v f) =
      2*(squareCellMean Q r (fun R => traceDefect (openCubeSet R.val) a 1) - traceDefect (openCubeSet Q) a 1) := by
  unfold squareMatchedCellResidual
  rw [squareCellMean_sum]
  simp_rw [squareCellMean_add]
  have hp (i : Fin 2) := square_optimizer_partition_gap Q hEll (Pi.single i 1) (Pi.single i 1) r
    (v.primal i) (v.primal_max i) (fun R => (f R).primal i) (fun R => (f R).primal_max i)
  have ha (i : Fin 2) := square_optimizer_partition_gap Q (isEllipticFieldOn_adjointCoeffField hEll)
    (Pi.single i 1) (Pi.single i 1) r (v.adjoint i) (v.adjoint_max i)
    (fun R => (f R).adjoint i) (fun R => (f R).adjoint_max i)
  simp_rw [hp,ha]
  have hsplit : (∑ i : Fin 2,
      ((squareCellMean Q r (fun R => volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand a ((f R).primal i))) -
       volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a (v.primal i))) +
      (squareCellMean Q r (fun R => volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand (adjointCoeffField a) ((f R).adjoint i))) -
       volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand (adjointCoeffField a) (v.adjoint i))))) =
      (∑ i : Fin 2, (squareCellMean Q r (fun R => volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand a ((f R).primal i))) +
       squareCellMean Q r (fun R => volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand (adjointCoeffField a) ((f R).adjoint i))))) -
      (∑ i : Fin 2, (volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a (v.primal i)) +
       volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand (adjointCoeffField a) (v.adjoint i)))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsplit, square_matched_optimizer_energy Q hEll _ _ v.primal_max v.adjoint_max]
  simp_rw [← squareCellMean_add]
  rw [← squareCellMean_sum]
  have hcell (R : SquareCells Q r) :
      (∑ i : Fin 2, (volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand a ((f R).primal i)) +
       volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand (adjointCoeffField a) ((f R).adjoint i)))) =
      2*traceDefect (openCubeSet R.val) a 1 :=
    square_matched_optimizer_energy R.val (hEll.mono (measurableSet_openCubeSet R.val)
      (openCubeSet_subset_of_mem_descendantsAtDepth R.property)) _ _ (f R).primal_max (f R).adjoint_max
  simp_rw [hcell]
  rw [squareCellMean_mul]
  ring

end ASDExplicitGamma.Cold

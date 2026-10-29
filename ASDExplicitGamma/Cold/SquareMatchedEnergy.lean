module

public import ASDExplicitGamma.Cold.SquareOptimizerProjection
public import ASDExplicitGamma.Statements.TraceDefect
public import Homogenization.CoarseGraining.AdjointSymmetry.BasicAdjoint

/-! # Actual four-load response and energy identities in the normalized coefficient -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Actual transpose compatibility on every native square. -/
theorem coarse_square_adjoint_block (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    coarseBlockMatrix (openCubeSet Q) (adjointCoeffField a) =
      blockMatFlipFlux (coarseBlockMatrix (openCubeSet Q) a) := by
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  obtain ⟨sigma,hA,_,_,_,_,_,_⟩ := Variational.exists_energyMap_coarseData
    (isOpenBoundedConvexDomain_openCubeSet Q) hEll hvol
  exact coarseBlockMatrix_adjointCoeffField_of_exists ⟨_,hA⟩

/-- The matched primal/adjoint coordinate responses add to the actual normalized trace defect. -/
theorem square_matched_response_trace (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    (∑ i : Fin 2, (ResponseJ (openCubeSet Q) (Pi.single i 1) (Pi.single i 1) a +
      ResponseJ (openCubeSet Q) (Pi.single i 1) (Pi.single i 1) (adjointCoeffField a))) =
      traceDefect (openCubeSet Q) a 1 := by
  have hAdj := isEllipticFieldOn_adjointCoeffField hEll
  have hcoord (i : Fin 2) :
      ResponseJ (openCubeSet Q) (Pi.single i 1) (Pi.single i 1) a +
      ResponseJ (openCubeSet Q) (Pi.single i 1) (Pi.single i 1) (adjointCoeffField a) =
      (coarseBlockMatrix (openCubeSet Q) a).upperLeft i i +
      (coarseBlockMatrix (openCubeSet Q) a).lowerRight i i - 2 := by
    rw [coarse_square_response_quadratic Q hEll, coarse_square_response_quadratic Q hAdj,
      coarse_square_adjoint_block Q hEll]
    fin_cases i <;>
      simp [blockVecDot,blockMatVecMul,vecDot,matVecMul,Pi.single_apply,
        blockMatFlipFlux] <;> ring
  simp_rw [hcoord]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, traceDefect, inv_one, one_mul, Matrix.trace, Matrix.diag_apply]
  ring

/-- The actual integrated energies of the four matched optimizers sum to twice the defect. -/
theorem square_matched_optimizer_energy (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (v : Fin 2 → AHarmonicFunction a (openCubeSet Q))
    (w : Fin 2 → AHarmonicFunction (adjointCoeffField a) (openCubeSet Q))
    (hv : ∀ i, IsResponseMaximizer (openCubeSet Q) (Pi.single i 1) (Pi.single i 1) a (v i))
    (hw : ∀ i, IsResponseMaximizer (openCubeSet Q) (Pi.single i 1) (Pi.single i 1)
      (adjointCoeffField a) (w i)) :
    (∑ i : Fin 2, (volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a (v i)) +
      volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand (adjointCoeffField a) (w i)))) =
      2 * traceDefect (openCubeSet Q) a 1 := by
  simp_rw [square_optimizer_energy Q hEll _ _ _ (hv _),
    square_optimizer_energy Q (isEllipticFieldOn_adjointCoeffField hEll) _ _ _ (hw _)]
  rw [← square_matched_response_trace Q hEll, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end ASDExplicitGamma.Cold

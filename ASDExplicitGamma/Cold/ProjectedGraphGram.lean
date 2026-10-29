module

public import ASDExplicitGamma.Cold.ProjectedGraphEnergy

/-! # Actual Gram bounds for the terminal and residual graph families -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The actual full trace defect is unchanged by transposition of the coefficient. -/
theorem coarse_square_traceDefect_adjoint (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    traceDefect (openCubeSet Q) (adjointCoeffField a) 1 = traceDefect (openCubeSet Q) a 1 := by
  rw [traceDefect,coarse_square_adjoint_block Q hEll]
  rfl

/-- The source Gram estimate summed over four actual harmonic fields. -/
theorem square_four_graph_gram (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam η : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (hη : 0 < η)
    (v : Fin 2 → AHarmonicFunction a (openCubeSet Q))
    (w : Fin 2 → AHarmonicFunction (adjointCoeffField a) (openCubeSet Q)) :
    squareFourGraphEnergy Q v w ≤ (2*(1+η)+(2+1/(4*η))*traceDefect (openCubeSet Q) a 1)*
      (∑ i : Fin 2, (volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a (v i)) +
        volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand (adjointCoeffField a) (w i)))) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => add_le_add
    (plateau_gram_trace Q hEll hη (v i))
    (plateau_gram_trace Q (isEllipticFieldOn_adjointCoeffField hEll) hη (w i)))
  simp_rw [coarse_square_traceDefect_adjoint Q hEll] at h
  rw [Finset.mul_sum]
  unfold squareFourGraphEnergy
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every actual own-cell residual energy is nonnegative. -/
theorem squareMatchedCellResidual_nonneg (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : SquareMatchedOptimizers Q a) {r : ℕ}
    (f : ∀ R : SquareCells Q r, SquareMatchedOptimizers R.val a) (R : SquareCells Q r) :
    0 ≤ squareMatchedCellResidual Q hEll v f R := by
  apply Finset.sum_nonneg
  intro i _
  let hER := hEll.mono (measurableSet_openCubeSet R.val) (openCubeSet_subset_of_mem_descendantsAtDepth R.property)
  exact add_nonneg
    (volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (openCubeSet R.val) a hER _)
    (volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (openCubeSet R.val) (adjointCoeffField a)
      (isEllipticFieldOn_adjointCoeffField hER) _)

/-- P3 bounds the actual residual graph using the source depth maximum. -/
theorem square_residual_graph_gram (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam η M : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (hη : 0 < η)
    (v : SquareMatchedOptimizers Q a) {r : ℕ}
    (f : ∀ R : SquareCells Q r, SquareMatchedOptimizers R.val a)
    (hmax : ∀ R : SquareCells Q r, traceDefect (openCubeSet R.val) a 1 ≤ M) :
    squareResidualGraphEnergy Q hEll v f ≤ (2*(1+η)+(2+1/(4*η))*M)*
      (2*(squareCellMean Q r (fun R => traceDefect (openCubeSet R.val) a 1)-traceDefect (openCubeSet Q) a 1)) := by
  have hg1 : 0 ≤ 2+1/(4*η) := by positivity
  have hcell (R : SquareCells Q r) :
      squareFourGraphEnergy R.val
        (fun i => squareCellDifference Q hEll (v.primal i) (fun R => (f R).primal i) R)
        (fun i => squareCellDifference Q (isEllipticFieldOn_adjointCoeffField hEll)
          (v.adjoint i) (fun R => (f R).adjoint i) R) ≤
      (2*(1+η)+(2+1/(4*η))*M)*squareMatchedCellResidual Q hEll v f R := by
    have h := square_four_graph_gram R.val
      (hEll.mono (measurableSet_openCubeSet R.val) (openCubeSet_subset_of_mem_descendantsAtDepth R.property)) hη
      (fun i => squareCellDifference Q hEll (v.primal i) (fun R => (f R).primal i) R)
      (fun i => squareCellDifference Q (isEllipticFieldOn_adjointCoeffField hEll)
        (v.adjoint i) (fun R => (f R).adjoint i) R)
    exact h.trans (mul_le_mul_of_nonneg_right
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hmax R) hg1))
      (squareMatchedCellResidual_nonneg Q hEll v f R))
  have h := squareCellMean_mono Q r hcell
  rw [squareCellMean_mul,squareMatchedCellResidual_mean] at h
  exact h

/-- The actual source energy drop is nonnegative and bounded by twice its depth maximum. -/
theorem square_energy_drop_bounds (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam M : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : SquareMatchedOptimizers Q a) {r : ℕ}
    (f : ∀ R : SquareCells Q r, SquareMatchedOptimizers R.val a)
    (hmax : ∀ R : SquareCells Q r, traceDefect (openCubeSet R.val) a 1 ≤ M) :
    0 ≤ 2*(squareCellMean Q r (fun R => traceDefect (openCubeSet R.val) a 1)-traceDefect (openCubeSet Q) a 1) ∧
    2*(squareCellMean Q r (fun R => traceDefect (openCubeSet R.val) a 1)-traceDefect (openCubeSet Q) a 1) ≤ 2*M := by
  have hn := squareCellMean_mono Q r (fun R => squareMatchedCellResidual_nonneg Q hEll v f R)
  rw [squareCellMean_const,squareMatchedCellResidual_mean] at hn
  have hm := squareCellMean_mono Q r hmax
  rw [squareCellMean_const] at hm
  have hp := coarse_square_traceDefect_nonneg Q hEll
  exact ⟨hn, by linarith only [hm,hp]⟩

end ASDExplicitGamma.Cold

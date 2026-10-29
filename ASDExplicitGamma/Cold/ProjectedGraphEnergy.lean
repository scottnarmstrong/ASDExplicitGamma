module

public import ASDExplicitGamma.Cold.GraphMeanSplit

/-! # The source projected graph energies are actual cell-average graph norms -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- The actual four-load graph mean norm on one square. -/
def squareFourGraphEnergy (Q : TriadicCube 2) {a : CoeffField 2}
    (v : Fin 2 → AHarmonicFunction a (openCubeSet Q))
    (w : Fin 2 → AHarmonicFunction (adjointCoeffField a) (openCubeSet Q)) : ℝ :=
  ∑ i : Fin 2, (blockVecDot (coarseGraphMean Q (v i)) (coarseGraphMean Q (v i)) +
    blockVecDot (coarseGraphMean Q (w i)) (coarseGraphMean Q (w i)))

/-- The source own-cell graph energy. -/
def squareOwnGraphEnergy (Q : TriadicCube 2) {a : CoeffField 2} {r : ℕ}
    (f : ∀ R : SquareCells Q r, SquareMatchedOptimizers R.val a) : ℝ :=
  squareCellMean Q r (fun R => squareFourGraphEnergy R.val (f R).primal (f R).adjoint)

/-- The source projected terminal graph energy at depth r. -/
def squareProjectedGraphEnergy (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : SquareMatchedOptimizers Q a) (r : ℕ) : ℝ :=
  squareCellMean Q r (fun R => squareFourGraphEnergy R.val
    (fun i => squareCellRestriction Q hEll (v.primal i) R)
    (fun i => squareCellRestriction Q (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i) R))

/-- The actual residual graph energy on all source cells. -/
def squareResidualGraphEnergy (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : SquareMatchedOptimizers Q a) {r : ℕ}
    (f : ∀ R : SquareCells Q r, SquareMatchedOptimizers R.val a) : ℝ :=
  squareCellMean Q r (fun R => squareFourGraphEnergy R.val
    (fun i => squareCellDifference Q hEll (v.primal i) (fun R => (f R).primal i) R)
    (fun i => squareCellDifference Q (isEllipticFieldOn_adjointCoeffField hEll)
      (v.adjoint i) (fun R => (f R).adjoint i) R))

/-- Actual Euclidean graph norms are nonnegative. -/
theorem squareFourGraphEnergy_nonneg (Q : TriadicCube 2) {a : CoeffField 2}
    (v : Fin 2 → AHarmonicFunction a (openCubeSet Q))
    (w : Fin 2 → AHarmonicFunction (adjointCoeffField a) (openCubeSet Q)) :
    0 ≤ squareFourGraphEnergy Q v w := by
  apply Finset.sum_nonneg
  intro i _
  unfold blockVecDot vecDot
  exact add_nonneg
    (add_nonneg (Finset.sum_nonneg fun _ _ => mul_self_nonneg _) (Finset.sum_nonneg fun _ _ => mul_self_nonneg _))
    (add_nonneg (Finset.sum_nonneg fun _ _ => mul_self_nonneg _) (Finset.sum_nonneg fun _ _ => mul_self_nonneg _))

/-- The actual own/residual graph split at the displayed source depth. -/
theorem square_projected_graph_split (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam t : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (ht : 0 < t)
    (v : SquareMatchedOptimizers Q a) {r : ℕ}
    (f : ∀ R : SquareCells Q r, SquareMatchedOptimizers R.val a) :
    squareProjectedGraphEnergy Q hEll v r ≤
      (1+t)*squareOwnGraphEnergy Q f+(1+1/t)*squareResidualGraphEnergy Q hEll v f := by
  have hcell (R : SquareCells Q r) :
      squareFourGraphEnergy R.val
        (fun i => squareCellRestriction Q hEll (v.primal i) R)
        (fun i => squareCellRestriction Q (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i) R) ≤
      (1+t)*squareFourGraphEnergy R.val (f R).primal (f R).adjoint +
      (1+1/t)*squareFourGraphEnergy R.val
        (fun i => squareCellDifference Q hEll (v.primal i) (fun R => (f R).primal i) R)
        (fun i => squareCellDifference Q (isEllipticFieldOn_adjointCoeffField hEll)
          (v.adjoint i) (fun R => (f R).adjoint i) R) := by
    let hER := hEll.mono (measurableSet_openCubeSet R.val) (openCubeSet_subset_of_mem_descendantsAtDepth R.property)
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => add_le_add
      (own_graph_split R.val hER ht ((f R).primal i) (squareCellRestriction Q hEll (v.primal i) R))
      (own_graph_split R.val (isEllipticFieldOn_adjointCoeffField hER) ht ((f R).adjoint i)
        (squareCellRestriction Q (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i) R)))
    unfold squareFourGraphEnergy
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    convert h using 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [squareCellDifference]
    ring
  have h := squareCellMean_mono Q r hcell
  rw [squareCellMean_add,squareCellMean_mul,squareCellMean_mul] at h
  exact h

/-- Scalar projected energies agree exactly with the actual squared cell means. -/
theorem energy_projection_eq_squareCellMean (Q : TriadicCube 2) (r : ℕ) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    energy Q (cubeProjection Q r f) = squareCellMean Q r (fun R => cubeAverage R.val f ^ 2) := by
  rw [← pairing_projection_energy Q r hf,pairing_projection_right Q r f hf]
  unfold descendantsAverage squareCellMean
  simp only [pow_two]
  congr 1
  exact (Finset.sum_attach (descendantsAtDepth Q r) (fun R => cubeAverage R f*cubeAverage R f)).symm

end ASDExplicitGamma.Cold

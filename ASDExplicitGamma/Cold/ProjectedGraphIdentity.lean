module

public import ASDExplicitGamma.Cold.ProjectedGraphEnergy
public import ASDExplicitGamma.Cold.RatioNineProjection

/-! # Exact identification of the projected graph with the P2 projection energy -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- A projected actual harmonic graph has exactly the P2 flux-plus-gradient energy. -/
theorem projected_graph_energy_identity (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (w : AHarmonicFunction a (openCubeSet Q)) (r : ℕ) :
    squareCellMean Q r (fun R =>
      blockVecDot (coarseGraphMean R.val (squareCellRestriction Q hEll w R))
        (coarseGraphMean R.val (squareCellRestriction Q hEll w R))) =
      squareVectorEnergy Q (squareProjection Q r (fun x => matVecMul (a x) (w.toH1.grad x))) +
      squareVectorEnergy Q (squareProjection Q r w.toH1.grad) := by
  have hflux (i : Fin 2) := memLp_normalized_of_memL2On
    ((memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1.grad_memVectorL2).eval i)
  have hgrad (i : Fin 2) := memLp_normalized_of_memL2On (w.toH1.gradMemL2 i)
  unfold blockVecDot vecDot coarseGraphMean
  rw [squareCellMean_add,squareCellMean_sum,squareCellMean_sum]
  unfold squareVectorEnergy squareProjection
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [energy_projection_eq_squareCellMean Q r (hflux i)]
    apply congrArg (squareCellMean Q r)
    funext R
    rw [← square_volumeAverage_eq_cubeAverage]
    simp only [pow_two]
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    rw [energy_projection_eq_squareCellMean Q r (hgrad i)]
    apply congrArg (squareCellMean Q r)
    funext R
    rw [← square_volumeAverage_eq_cubeAverage]
    simp only [pow_two]
    rfl

end ASDExplicitGamma.Cold

module

public import ASDExplicitGamma.Cold.SquareMatchedProjection
public import ASDExplicitGamma.Cold.PlateauCellRecovery

/-! # Actual four-load cutoff recovery before expectation -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Distribute the cutoff over the four actual energy densities. -/
theorem square_four_weighted_average (Q R : TriadicCube 2) (f g : Fin 2 → Vec 2 → ℝ)
    (hf : ∀ i, IntegrableOn (fun x => plateauOnSquare Q x*f i x) (openCubeSet R))
    (hg : ∀ i, IntegrableOn (fun x => plateauOnSquare Q x*g i x) (openCubeSet R)) :
    volumeAverage (openCubeSet R) (fun x => plateauOnSquare Q x * (∑ i : Fin 2, (f i x+g i x))) =
      ∑ i : Fin 2, (volumeAverage (openCubeSet R) (fun x => plateauOnSquare Q x*f i x) +
        volumeAverage (openCubeSet R) (fun x => plateauOnSquare Q x*g i x)) := by
  have heq : (fun x => plateauOnSquare Q x*(∑ i : Fin 2, (f i x+g i x))) =
      (fun x => ∑ i : Fin 2, (plateauOnSquare Q x*f i x+plateauOnSquare Q x*g i x)) := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq,volumeAverage_sum (s := Finset.univ)
    (f := fun i x => plateauOnSquare Q x*f i x+plateauOnSquare Q x*g i x)
    (fun i _ => (hf i).add (hg i))]
  apply Finset.sum_congr rfl
  intro i _
  exact volumeAverage_add (hf i) (hg i)

/-- The weighted actual matched density is spatially integrable. -/
theorem integrable_plateau_squareMatchedDensity (Q R : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (v : SquareMatchedOptimizers R a) :
    IntegrableOn (fun x => plateauOnSquare Q x*squareMatchedDensity R v x) (openCubeSet R) := by
  have h := integrable_finsetSum Finset.univ (fun i _ =>
    (integrable_plateau_local_energy Q R hEll (v.primal i)).add
      (integrable_plateau_local_energy Q R (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i)))
  have heq : (fun x => plateauOnSquare Q x*squareMatchedDensity R v x) =
      (fun x => ∑ i : Fin 2, ((fun y => plateauOnSquare Q y*scalarVariationEnergyIntegrand a (v.primal i) y) +
        (fun y => plateauOnSquare Q y*scalarVariationEnergyIntegrand (adjointCoeffField a) (v.adjoint i) y)) x) := by
    funext x
    simp only [squareMatchedDensity,Pi.add_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  exact h

/-- The four actual cellwise Young inequalities sum to the source total-energy comparison. -/
theorem square_matched_cell_cutoff_recovery (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam c : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (hc : 0 < c) (hc1 : c < 1)
    (v : SquareMatchedOptimizers Q a) {r : ℕ}
    (f : ∀ R : SquareCells Q r, SquareMatchedOptimizers R.val a) (R : SquareCells Q r) :
    (1-c)*volumeAverage (openCubeSet R.val) (fun x => plateauOnSquare Q x*squareMatchedDensity R.val (f R) x) -
      (1/c-1)*(12/7)*squareMatchedCellResidual Q hEll v f R ≤
      volumeAverage (openCubeSet R.val) (fun x => plateauOnSquare Q x*squareMatchedDensity Q v x) := by
  let hER := hEll.mono (measurableSet_openCubeSet R.val) (openCubeSet_subset_of_mem_descendantsAtDepth R.property)
  have hp (i : Fin 2) := harmonic_plateau_cell_recovery Q R.val hER hc hc1 ((f R).primal i)
    (squareCellRestriction Q hEll (v.primal i) R)
  have ha (i : Fin 2) := harmonic_plateau_cell_recovery Q R.val
    (isEllipticFieldOn_adjointCoeffField hER) hc hc1 ((f R).adjoint i)
    (squareCellRestriction Q (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i) R)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => add_le_add (hp i) (ha i))
  have hF := square_four_weighted_average Q R.val
    (fun i => scalarVariationEnergyIntegrand a ((f R).primal i))
    (fun i => scalarVariationEnergyIntegrand (adjointCoeffField a) ((f R).adjoint i))
    (fun i => integrable_plateau_local_energy Q R.val hER ((f R).primal i))
    (fun i => integrable_plateau_local_energy Q R.val (isEllipticFieldOn_adjointCoeffField hER) ((f R).adjoint i))
  have hV := square_four_weighted_average Q R.val
    (fun i => scalarVariationEnergyIntegrand a (v.primal i))
    (fun i => scalarVariationEnergyIntegrand (adjointCoeffField a) (v.adjoint i))
    (fun i => integrable_plateau_local_energy Q R.val hER (squareCellRestriction Q hEll (v.primal i) R))
    (fun i => integrable_plateau_local_energy Q R.val (isEllipticFieldOn_adjointCoeffField hER)
      (squareCellRestriction Q (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i) R))
  dsimp only [squareMatchedDensity]
  rw [hF,hV]
  unfold squareMatchedCellResidual
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  convert hs using 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [squareCellDifference]
  ring
  rfl

/-- The exact pathwise four-load cutoff recovery inequality, with the actual projection gap. -/
theorem square_matched_partition_cutoff_recovery (Q : TriadicCube 2)
    {a : CoeffField 2} {lam Lam c : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hc : 0 < c) (hc1 : c < 1) (v : SquareMatchedOptimizers Q a) {r : ℕ}
    (f : ∀ R : SquareCells Q r, SquareMatchedOptimizers R.val a) :
    (1-c)*squareCellMean Q r (fun R => volumeAverage (openCubeSet R.val)
      (fun x => plateauOnSquare Q x*squareMatchedDensity R.val (f R) x)) -
      (1/c-1)*(12/7)*(2*(squareCellMean Q r (fun R => traceDefect (openCubeSet R.val) a 1) -
        traceDefect (openCubeSet Q) a 1)) ≤
      volumeAverage (openCubeSet Q) (fun x => plateauOnSquare Q x*squareMatchedDensity Q v x) := by
  have h := squareCellMean_mono Q r (fun R => square_matched_cell_cutoff_recovery Q hEll hc hc1 v f R)
  rw [squareCellMean_sub,squareCellMean_mul,squareCellMean_mul,squareMatchedCellResidual_mean,
    squareCellMean_volumeAverage Q r (integrable_plateau_squareMatchedDensity Q Q hEll v)] at h
  exact h

end ASDExplicitGamma.Cold

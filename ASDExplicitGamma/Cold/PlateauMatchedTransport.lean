module

public import ASDExplicitGamma.Cold.ProjectedGraphIdentity
public import ASDExplicitGamma.Cold.PlateauTransportWeights
public import ASDExplicitGamma.Cold.HarmonicCutoffRecovery

/-! # Applying the proved transport estimate to the actual four cold optimizers -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The actual projected graph energy of one harmonic function. -/
def harmonicProjectedGraphEnergy (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (w : AHarmonicFunction a (openCubeSet Q)) (r : ℕ) : ℝ :=
  squareCellMean Q r (fun R => blockVecDot (coarseGraphMean R.val (squareCellRestriction Q hEll w R))
    (coarseGraphMean R.val (squareCellRestriction Q hEll w R)))

/-- Summability follows from contraction of the actual spatial L2 projections. -/
theorem summable_harmonicProjectedGraphEnergy (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (w : AHarmonicFunction a (openCubeSet Q)) :
    Summable (fun k => plateauEvenWeight k*harmonicProjectedGraphEnergy Q hEll w (2*(k+1))) := by
  let j := fun x => matVecMul (a x) (w.toH1.grad x)
  have hg (i : Fin 2) := memLp_normalized_of_memL2On (w.toH1.gradMemL2 i)
  have hj (i : Fin 2) := memLp_normalized_of_memL2On
    ((memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1.grad_memVectorL2).eval i)
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (plateauEvenWeight_nonneg k) ?_)
    (fun k => mul_le_mul_of_nonneg_left ?_ (plateauEvenWeight_nonneg k))
    (summable_plateauEvenWeight.mul_right (squareVectorEnergy Q j+squareVectorEnergy Q w.toH1.grad))
  · rw [harmonicProjectedGraphEnergy,projected_graph_energy_identity]
    exact add_nonneg (squareVectorEnergy_nonneg Q _) (squareVectorEnergy_nonneg Q _)
  · rw [harmonicProjectedGraphEnergy,projected_graph_energy_identity]
    exact add_le_add (squareProjection_energy_le Q hj _) (squareProjection_energy_le Q hg _)

/-- The actual weighted harmonic energy is controlled by the proved transport sum. -/
theorem plateau_harmonic_energy_le (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (w : AHarmonicFunction a (openCubeSet Q)) :
    volumeAverage (openCubeSet Q) (fun x => plateauOnSquare Q x*scalarVariationEnergyIntegrand a w x) ≤
      ∑' k : ℕ, plateauEvenWeight k*harmonicProjectedGraphEnergy Q hEll w (2*(k+1)) := by
  have h := plateau_transport_weights Q w.toH1
    (memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1.grad_memVectorL2) w.isHarmonic.2
  have heq : (fun x => plateauOnSquare Q x*scalarVariationEnergyIntegrand a w x) =
      (fun x => plateauOnSquare Q x*(∑ i : Fin 2, w.toH1.grad x i*matVecMul (a x) (w.toH1.grad x) i)) := by
    funext x
    rw [scalarVariationEnergyIntegrand,vecDot_matVecMul_symmPart]
    rfl
  rw [heq,square_volumeAverage_eq_cubeAverage,cubeAverage_eq_integral_normalizedCubeMeasure]
  apply (le_abs_self _).trans
  simp_rw [harmonicProjectedGraphEnergy,projected_graph_energy_identity]
  convert h using 1
  congr 1
  funext k
  ring

/-- The four-load projection graph is exactly the sum of its individual graph energies. -/
theorem squareProjectedGraphEnergy_eq_sum (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : SquareMatchedOptimizers Q a) (r : ℕ) :
    squareProjectedGraphEnergy Q hEll v r = ∑ i : Fin 2,
      (harmonicProjectedGraphEnergy Q hEll (v.primal i) r+
       harmonicProjectedGraphEnergy Q (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i) r) := by
  unfold squareProjectedGraphEnergy squareFourGraphEnergy harmonicProjectedGraphEnergy
  rw [squareCellMean_sum]
  simp_rw [squareCellMean_add]

/-- The actual four-load P2 bound, ready for the cutoff recovery inequality. -/
theorem plateau_matched_energy_le (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : SquareMatchedOptimizers Q a) :
    volumeAverage (openCubeSet Q) (fun x => plateauOnSquare Q x*squareMatchedDensity Q v x) ≤
      ∑' k : ℕ, plateauEvenWeight k*squareProjectedGraphEnergy Q hEll v (2*(k+1)) := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => add_le_add
    (plateau_harmonic_energy_le Q hEll (v.primal i))
    (plateau_harmonic_energy_le Q (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i)))
  have hp (i : Fin 2) := summable_harmonicProjectedGraphEnergy Q hEll (v.primal i)
  have ha (i : Fin 2) := summable_harmonicProjectedGraphEnergy Q (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i)
  have he : volumeAverage (openCubeSet Q) (fun x => plateauOnSquare Q x*squareMatchedDensity Q v x) =
      ∑ i : Fin 2, (volumeAverage (openCubeSet Q) (fun x => plateauOnSquare Q x*scalarVariationEnergyIntegrand a (v.primal i) x)+
        volumeAverage (openCubeSet Q) (fun x => plateauOnSquare Q x*scalarVariationEnergyIntegrand (adjointCoeffField a) (v.adjoint i) x)) := by
    have heq : (fun x => plateauOnSquare Q x*squareMatchedDensity Q v x) =
        (fun x => ∑ i : Fin 2, (plateauOnSquare Q x*scalarVariationEnergyIntegrand a (v.primal i) x+
          plateauOnSquare Q x*scalarVariationEnergyIntegrand (adjointCoeffField a) (v.adjoint i) x)) := by
      funext x
      simp only [squareMatchedDensity,Finset.mul_sum,mul_add]
    rw [heq,volumeAverage_sum (s := Finset.univ) (f := fun i x =>
      plateauOnSquare Q x*scalarVariationEnergyIntegrand a (v.primal i) x+
      plateauOnSquare Q x*scalarVariationEnergyIntegrand (adjointCoeffField a) (v.adjoint i) x)
      (fun i _ => (integrable_plateau_local_energy Q Q hEll (v.primal i)).add
        (integrable_plateau_local_energy Q Q (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i)))]
    apply Finset.sum_congr rfl
    intro i _
    exact volumeAverage_add (integrable_plateau_local_energy Q Q hEll (v.primal i))
      (integrable_plateau_local_energy Q Q (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i))
  rw [he]
  refine hsum.trans_eq ?_
  simp_rw [squareProjectedGraphEnergy_eq_sum,Finset.mul_sum,mul_add]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact ((hp i).tsum_add (ha i)).symm
  · intro i _
    exact (hp i).add (ha i)

end ASDExplicitGamma.Cold

module

public import ASDExplicitGamma.Cold.SquareFinitePotentials
public import ASDExplicitGamma.Cold.PlateauFiniteTransport

/-! # Strong convergence of actual projected potentials in the plateau form -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- The normalized L² realization of a genuine weak gradient coordinate. -/
def squareNormalizedGradient (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
    (i : Fin 2) : Lp ℝ 2 (normalizedCubeMeasure Q) :=
  (memLp_normalized_of_memL2On (u.gradMemL2 i)).toLp (fun x => u.grad x i)

/-- Every actual coordinate is strongly approximated by the finite projected potentials. -/
theorem tendsto_squarePartialPotential_gradient (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q)) (i : Fin 2) :
    Tendsto (fun N => squareNormalizedGradient Q (squarePartialPotential Q u.grad N) i)
      atTop (𝓝 (squareNormalizedGradient Q u i)) := by
  apply tendsto_toLp_of_integral_sq_sub_tendsto_zero
    (fun N => memLp_normalized_of_memL2On ((squarePartialPotential Q u.grad N).gradMemL2 i))
    (memLp_normalized_of_memL2On (u.gradMemL2 i))
  have heq (N : ℕ) : (∫ x, ((squarePartialPotential Q u.grad N).grad x i - u.grad x i) ^ 2
      ∂normalizedCubeMeasure Q) = energy Q (fun x => (u - squarePartialPotential Q u.grad N).grad x i) := by
    rw [energy_eq_integral_sq]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [H1Function.sub_grad, Pi.sub_apply]
      ring
  simp_rw [heq]
  exact squeeze_zero (fun _ => energy_nonneg Q _)
    (fun N => Finset.single_le_sum (fun j _ => energy_nonneg Q
      (fun x => (u - squarePartialPotential Q u.grad N).grad x j)) (Finset.mem_univ i))
    (tendsto_squarePartialPotential_residual_energy Q u)

/-- The actual normalized transport as two bounded-coefficient L² pairings. -/
theorem plateauTransport_eq_normalized_pairings (Q : TriadicCube 2)
    (u w : H1Function (openCubeSet Q)) :
    plateauTransport Q u w =
      -weightedL2Pairing (memLp_plateauOnSquare Q ⊤)
        (squareNormalizedGradient Q u 0) (squareNormalizedGradient Q w 1) +
      weightedL2Pairing (memLp_plateauOnSquare Q ⊤)
        (squareNormalizedGradient Q u 1) (squareNormalizedGradient Q w 0) := by
  unfold squareNormalizedGradient
  rw [weightedL2Pairing_eq_integral_of_ae _ _ _
      (memLp_normalized_of_memL2On (u.gradMemL2 0)).coeFn_toLp
      (memLp_normalized_of_memL2On (w.gradMemL2 1)).coeFn_toLp,
    weightedL2Pairing_eq_integral_of_ae _ _ _
      (memLp_normalized_of_memL2On (u.gradMemL2 1)).coeFn_toLp
      (memLp_normalized_of_memL2On (w.gradMemL2 0)).coeFn_toLp]
  exact normalizedSquareTransport_eq_integrals Q _ u w

/-- The finite actual transport converges to the source H¹ transport. -/
theorem tendsto_plateauTransport_partialPotential (Q : TriadicCube 2)
    (u w : H1Function (openCubeSet Q)) :
    Tendsto (fun N => plateauTransport Q (squarePartialPotential Q u.grad N)
      (squarePartialPotential Q w.grad N)) atTop (𝓝 (plateauTransport Q u w)) := by
  simp_rw [plateauTransport_eq_normalized_pairings]
  have hM : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖plateauOnSquare Q x‖ ≤ (12 / 7 : ℝ) :=
    Filter.Eventually.of_forall (norm_plateauOnSquare_le Q)
  exact (tendsto_weightedL2Pairing (memLp_plateauOnSquare Q ⊤) _ hM
    (tendsto_squarePartialPotential_gradient Q u 0) (tendsto_squarePartialPotential_gradient Q w 1)).neg.add
    (tendsto_weightedL2Pairing (memLp_plateauOnSquare Q ⊤) _ hM
    (tendsto_squarePartialPotential_gradient Q u 1) (tendsto_squarePartialPotential_gradient Q w 0))

end ASDExplicitGamma.Cold

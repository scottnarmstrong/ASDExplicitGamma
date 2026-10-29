module

public import ASDExplicitGamma.Cold.SquareVectorEnergy

/-! # Actual mean-zero gradient projections on the square -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- The actual mean-zero H¹ potential of the orthogonal gradient projection. -/
def squareGradientPotential (Q : TriadicCube 2) {G : Vec 2 → Vec 2}
    (hG : MemVectorL2 (openCubeSet Q) G) : H1MeanZeroFunction (openCubeSet Q) :=
  H1MeanZeroFunction.gradientProblemSolution hG
    (h1CoerciveEstimate_of_isOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q))

/-- Its source Neumann-primitive characterization follows from the variational solver. -/
theorem squareGradientPotential_isNeumannPrimitive (Q : TriadicCube 2) {G : Vec 2 → Vec 2}
    (hG : MemVectorL2 (openCubeSet Q) G) :
    Support.Localization.IsNeumannPrimitive Q G (squareGradientPotential Q hG).toH1Function := by
  constructor
  · have hm := (squareGradientPotential Q hG).meanZero
    rw [MeanZeroOn] at hm
    rw [cubeAverage_eq_integral_normalizedCubeMeasure, integral_normalized_eq_open, hm, mul_zero]
  · intro φ
    have hv := H1Function.gradientProblemSolution_firstVariation_eq_integral hG
      (h1CoerciveEstimate_of_isOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)) φ
    rw [cubeAverage_eq_integral_normalizedCubeMeasure, cubeAverage_eq_integral_normalizedCubeMeasure,
      integral_normalized_eq_open, integral_normalized_eq_open]
    exact congrArg (fun t : ℝ => (cubeVolume Q)⁻¹ * t) hv

/-- The weak projection identity in the actual Euclidean L² pairing. -/
theorem squareGradientPotential_pairing (Q : TriadicCube 2) {G : Vec 2 → Vec 2}
    (hG : MemVectorL2 (openCubeSet Q) G) (φ : H1Function (openCubeSet Q)) :
    vectorPairing Q (squareGradientPotential Q hG).toH1Function.grad φ.grad =
      vectorPairing Q G φ.grad := by
  have hGn (i : Fin 2) := memLp_normalized_of_memL2On (hG.eval i)
  have hWn (i : Fin 2) := memLp_normalized_of_memL2On
    ((squareGradientPotential Q hG).toH1Function.gradMemL2 i)
  have hφn (i : Fin 2) := memLp_normalized_of_memL2On (φ.gradMemL2 i)
  rw [vectorPairing_eq_integral_sum Q hWn hφn, vectorPairing_eq_integral_sum Q hGn hφn]
  have h := (squareGradientPotential_isNeumannPrimitive Q hG).2 φ
  rw [cubeAverage_eq_integral_normalizedCubeMeasure, cubeAverage_eq_integral_normalizedCubeMeasure] at h
  exact h

/-- The variational projection contracts Euclidean L² energy. This is proved from the
weak equation, and can also be applied to differences and finite sums of projected potentials. -/
theorem weak_gradient_projection_energy_le (Q : TriadicCube 2) {G : Vec 2 → Vec 2}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (w : H1Function (openCubeSet Q))
    (hw : ∀ φ : H1Function (openCubeSet Q),
      vectorPairing Q w.grad φ.grad = vectorPairing Q G φ.grad) :
    squareVectorEnergy Q w.grad ≤ squareVectorEnergy Q G := by
  have hW (i : Fin 2) := memLp_normalized_of_memL2On (w.gradMemL2 i)
  have hE : squareVectorEnergy Q w.grad = vectorPairing Q G w.grad := by
    rw [← vectorPairing_self]
    exact hw w
  have hA := squareVectorEnergy_nonneg Q w.grad
  have hB := squareVectorEnergy_nonneg Q G
  have hupper : squareVectorEnergy Q w.grad ≤
      Real.sqrt (squareVectorEnergy Q G) * Real.sqrt (squareVectorEnergy Q w.grad) := by
    calc
      _ = vectorPairing Q G w.grad := hE
      _ ≤ |vectorPairing Q G w.grad| := le_abs_self _
      _ ≤ _ := abs_squareVectorPairing_le Q hG hW
  have hsq := pow_le_pow_left₀ hA hupper 2
  rw [mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hA] at hsq
  by_cases hz : squareVectorEnergy Q w.grad = 0
  · rw [hz]
    exact hB
  · have hp : 0 < squareVectorEnergy Q w.grad := lt_of_le_of_ne hA (Ne.symm hz)
    apply le_of_mul_le_mul_right (b := squareVectorEnergy Q w.grad) _ hp
    simpa only [pow_two] using hsq

/-- The canonical actual gradient projection obeys the source contraction estimate. -/
theorem squareGradientPotential_energy_le (Q : TriadicCube 2) {G : Vec 2 → Vec 2}
    (hG : MemVectorL2 (openCubeSet Q) G) :
    squareVectorEnergy Q (squareGradientPotential Q hG).toH1Function.grad ≤ squareVectorEnergy Q G :=
  weak_gradient_projection_energy_le Q (fun i => memLp_normalized_of_memL2On (hG.eval i))
    (squareGradientPotential Q hG).toH1Function (squareGradientPotential_pairing Q hG)

end ASDExplicitGamma.Cold

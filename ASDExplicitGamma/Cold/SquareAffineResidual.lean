module

public import ASDExplicitGamma.Cold.SquareGradientProjection
public import ASDExplicitGamma.Cold.ResidualPoincare

/-! # The actual affine/residual split of an H¹ function on a square -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- The affine H¹ function with the displayed constant gradient. -/
def squareAffine (Q : TriadicCube 2) (p : Vec 2) : H1Function (openCubeSet Q) :=
  H1Function.affineOnIsSobolevRegularDomain
    (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain p

/-- The affine part has the literal constant weak gradient. -/
theorem squareAffine_grad (Q : TriadicCube 2) (p : Vec 2) (x : Vec 2) :
    (squareAffine Q p).grad x = p :=
  H1Function.affineOnIsSobolevRegularDomain_grad _ p x

/-- The ordinary spatial average of the actual weak gradient. -/
theorem averageGradient_eq_cubeAverage (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
    (i : Fin 2) : u.averageGradient i = cubeAverage Q (fun x => u.grad x i) := by
  rw [cubeAverage_eq_integralAverage_openCubeSet]
  rfl

/-- Subtract the affine gradient part and then its scalar mean. -/
def squareResidual (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) :
    H1Function (openCubeSet Q) := (u - squareAffine Q u.averageGradient).subAverage

/-- The residual has the actual fluctuation of the weak gradient. -/
theorem squareResidual_grad (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) (x : Vec 2) :
    (squareResidual Q u).grad x = u.grad x - u.averageGradient := by
  unfold squareResidual
  rw [H1Function.grad_subAverage, H1Function.sub_grad]
  simp only [squareAffine_grad]

/-- Its scalar mean is exactly zero. -/
theorem squareResidual_mean (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) :
    ∫ x, (squareResidual Q u).toFun x ∂normalizedCubeMeasure Q = 0 := by
  have h := H1Function.meanZeroOn_subAverage (u - squareAffine Q u.averageGradient)
  rw [MeanZeroOn] at h
  rw [integral_normalized_eq_open]
  change (cubeVolume Q)⁻¹ * (∫ x in openCubeSet Q,
    (u - squareAffine Q u.averageGradient).subAverage.toFun x) = 0
  rw [h, mul_zero]

/-- The residual's spatial mean gradient is exactly zero, coordinate by coordinate. -/
theorem squareResidual_gradient_mean (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
    (i : Fin 2) :
    ∫ x, (squareResidual Q u).grad x i ∂normalizedCubeMeasure Q = 0 := by
  simp only [squareResidual_grad, Pi.sub_apply]
  rw [← cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_sub_const_of_memLp_two Q (memLp_normalized_of_memL2On (u.gradMemL2 i)),
    ← averageGradient_eq_cubeAverage]
  ring

/-- The source orthogonal decomposition of the gradient energies. -/
theorem squareResidual_energy_decomposition (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) :
    squareVectorEnergy Q u.grad = (∑ i : Fin 2, u.averageGradient i ^ 2) +
      squareVectorEnergy Q (squareResidual Q u).grad := by
  have hcoord (i : Fin 2) : energy Q (fun x => (squareResidual Q u).grad x i) =
      energy Q (fun x => u.grad x i) - u.averageGradient i ^ 2 := by
    simp only [squareResidual_grad, Pi.sub_apply]
    rw [energy_sub Q (memLp_normalized_of_memL2On (u.gradMemL2 i)) (memLp_const _),
      pairing_const_right, energy_const, ← averageGradient_eq_cubeAverage]
    ring
  unfold squareVectorEnergy
  simp_rw [hcoord]
  rw [Finset.sum_sub_distrib]
  ring

/-- The residual satisfies the proved source Poincaré estimate. -/
theorem squareResidual_poincare (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) :
    Real.sqrt (energy Q (squareResidual Q u).toFun) ≤
      (cubeScaleFactor Q / (Real.sqrt 2 * Real.pi)) *
        Real.sqrt (squareVectorEnergy Q (squareResidual Q u).grad) := by
  simpa only [energy_eq_integral_sq, squareVectorEnergy] using
    square_residual_poincare Q (squareResidual Q u) (squareResidual_mean Q u)
      (squareResidual_gradient_mean Q u)

/-- The affine and residual pieces reconstruct the actual gradient. -/
theorem squareAffine_add_residual_grad (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) :
    (squareAffine Q u.averageGradient + squareResidual Q u).grad = u.grad := by
  funext x
  simp only [H1Function.add_grad, squareAffine_grad, squareResidual_grad]
  rw [← add_sub_assoc, add_sub_cancel_left]

end ASDExplicitGamma.Cold

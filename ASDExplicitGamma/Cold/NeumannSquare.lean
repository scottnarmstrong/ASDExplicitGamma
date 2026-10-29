module

public import ASDExplicitGamma.Cold.NeumannMixedCoefficient
public import ASDExplicitGamma.Triadic.PlanarNeumannBridge
public import ASDExplicitGamma.Triadic.PlanarDirichletSpectral

/-! # The square Neumann Hessian identity for weak H² functions

The first derivatives are themselves H¹ functions. The coordinate Green identities express
zero normal derivative on each pair of opposite faces; they are boundary conditions, not
spectral or Hessian-energy assumptions. The proof identifies all second-derivative Fourier
coefficients from these boundary conditions and the weak derivatives, then applies Parseval.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- First derivative cosine/sine coefficient identity for any H¹ function. -/
theorem h1_sine_derivative_coefficient (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q)) (i : Fin 2) (p : Fin 2 → ℤ) :
    ∫ x, cubeSin Q i p x * u.grad x i ∂normalizedCubeMeasure Q =
      -cubeFreq Q p i * ∫ x, cubeCos Q p x * u.toFun x ∂normalizedCubeMeasure Q := by
  have hu := memLp_normalized_of_memL2On u.memL2
  have hgi := memLp_normalized_of_memL2On (u.gradMemL2 i)
  have hid := Torus.integral_weakDeriv_mul_boxMode (cubeCorner Q) (cubeScaleFactor_pos' Q) i p
    (g := u.toFun) (gi := fun x => u.grad x i)
    (by rw [← openCubeSet_eq_box Q]; exact u.hasWeakGradient i)
    (by rw [← openCubeSet_eq_box Q]; exact integrableOn_open_of_memLp hu)
    (by rw [← openCubeSet_eq_box Q]; exact integrableOn_open_of_memLp hgi)
  rw [integral_normalized_eq_open, integral_normalized_eq_open]
  simp only [cubeSin, cubeCos, cubeFreq, openCubeSet_eq_box]
  simp_rw [mul_comm (boxMode _ _ _ _ _) (u.grad _ _),
    mul_comm (boxMode _ _ _ _ _) (u.toFun _)]
  rw [hid]
  ring

end ASDExplicitGamma.Cold

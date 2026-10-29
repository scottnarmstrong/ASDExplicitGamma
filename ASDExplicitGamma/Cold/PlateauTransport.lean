module

public import ASDExplicitGamma.Cold.SquareTransportBound
public import ASDExplicitGamma.Cold.SquareAffineResidual
public import ASDExplicitGamma.Cold.PlateauTransportAlgebra

/-! # The genuine plateau transport form on a native square -/

@[expose] public section
noncomputable section
open MeasureTheory Set Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal NNReal
namespace ASDExplicitGamma.Cold

/-- The normalized transport form with the source plateau cutoff. -/
def plateauTransport (Q : TriadicCube 2) (u w : H1Function (openCubeSet Q)) : ℝ :=
  normalizedSquareTransport Q (plateauOnSquare Q) u w

/-- Its scale-correct bound follows from weak integration by parts. -/
theorem abs_plateauTransport_le (Q : TriadicCube 2) (u w : H1Function (openCubeSet Q)) :
    |plateauTransport Q u w| ≤ (48 / (7 * cubeScaleFactor Q)) *
      Real.sqrt (energy Q u.toFun) * Real.sqrt (squareVectorEnergy Q w.grad) := by
  have h := abs_normalizedSquareTransport_le Q (lipschitzWith_plateauOnSquare Q)
    (tsupport_plateauOnSquare_subset Q) (12 / 7) (norm_plateauOnSquare_le Q) u w
  have hc : (↑((48 / 7 : ℝ≥0) * (NNReal.mk (cubeScaleFactor Q)
      (cubeScaleFactor_pos' Q).le)⁻¹) : ℝ) = 48 / (7 * cubeScaleFactor Q) := by
    simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_inv, NNReal.coe_mk]
    ring
  rw [hc] at h
  exact h

/-- Transport is alternating. -/
theorem plateauTransport_swap (Q : TriadicCube 2) (u w : H1Function (openCubeSet Q)) :
    plateauTransport Q w u = -plateauTransport Q u w := by
  unfold plateauTransport normalizedSquareTransport squareTransportForm
  have h (i j : Fin 2) :
      (fun x => plateauOnSquare Q x * w.grad x i * u.grad x j) =
      (fun x => plateauOnSquare Q x * u.grad x j * w.grad x i) := by funext x; ring
  rw [h 0 1, h 1 0]
  ring

/-- Bilinearity in the first H¹ function. -/
theorem plateauTransport_add_left (Q : TriadicCube 2) (u v w : H1Function (openCubeSet Q)) :
    plateauTransport Q (u + v) w = plateauTransport Q u w + plateauTransport Q v w := by
  have hφ : MemLp (plateauOnSquare Q) ⊤ (volume.restrict (openCubeSet Q)) :=
    MemLp.of_bound (lipschitzWith_plateauOnSquare Q).continuous.aestronglyMeasurable
      (12 / 7) (Filter.Eventually.of_forall (norm_plateauOnSquare_le Q))
  unfold plateauTransport normalizedSquareTransport
  simp_rw [squareTransportForm_eq_pairings Q hφ, H1Function.gradCoordToScalarL2_add,
    weightedL2Pairing_add_left]
  ring

/-- Bilinearity in the second H¹ function. -/
theorem plateauTransport_add_right (Q : TriadicCube 2) (u v w : H1Function (openCubeSet Q)) :
    plateauTransport Q u (v + w) = plateauTransport Q u v + plateauTransport Q u w := by
  rw [plateauTransport_swap, plateauTransport_add_left,
    plateauTransport_swap Q v u, plateauTransport_swap Q w u]
  ring

/-- Only the actual weak gradients enter this form. -/
theorem plateauTransport_congr_grad (Q : TriadicCube 2)
    {u v w z : H1Function (openCubeSet Q)} (hu : u.grad = v.grad) (hw : w.grad = z.grad) :
    plateauTransport Q u w = plateauTransport Q v z := by
  unfold plateauTransport normalizedSquareTransport squareTransportForm
  rw [hu, hw]

/-- The affine/affine entry uses the exact mean-one plateau identity. -/
theorem plateauTransport_affine (Q : TriadicCube 2) (p q : Vec 2) :
    plateauTransport Q (squareAffine Q p) (squareAffine Q q) = -p 0 * q 1 + p 1 * q 0 := by
  unfold plateauTransport
  rw [normalizedSquareTransport_eq_integrals]
  simp_rw [squareAffine_grad]
  rw [integral_mul_const, integral_mul_const, integral_mul_const, integral_mul_const,
    integral_plateauOnSquare]
  ring

end ASDExplicitGamma.Cold

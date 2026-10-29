module

public import ASDExplicitGamma.Cold.PlateauAffineBound

/-! # The sharp top/top plateau block for arbitrary H¹ functions -/

@[expose] public section
noncomputable section
open MeasureTheory Set Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- The residual/residual entry, with the source scale canceled exactly. -/
theorem abs_plateauTransport_residual_le (Q : TriadicCube 2)
    (u w : H1Function (openCubeSet Q)) :
    |plateauTransport Q (squareResidual Q u) (squareResidual Q w)| ≤
      (48 / (7 * Real.sqrt 2 * Real.pi)) *
        Real.sqrt (squareVectorEnergy Q (squareResidual Q u).grad) *
        Real.sqrt (squareVectorEnergy Q (squareResidual Q w).grad) := by
  have hℓ := cubeScaleFactor_pos' Q
  have h := abs_plateauTransport_le Q (squareResidual Q u) (squareResidual Q w)
  have hp := mul_le_mul_of_nonneg_left (squareResidual_poincare Q u)
    (by positivity : 0 ≤ 48 / (7 * cubeScaleFactor Q))
  have hmul := mul_le_mul_of_nonneg_right hp
    (Real.sqrt_nonneg (squareVectorEnergy Q (squareResidual Q w).grad))
  refine h.trans (hmul.trans_eq ?_)
  field_simp [(cubeScaleFactor_pos' Q).ne']

/-- The four actual affine/residual entries reconstruct the source transport. -/
theorem plateauTransport_split (Q : TriadicCube 2) (u w : H1Function (openCubeSet Q)) :
    plateauTransport Q u w =
      plateauTransport Q (squareAffine Q u.averageGradient) (squareAffine Q w.averageGradient) +
      plateauTransport Q (squareAffine Q u.averageGradient) (squareResidual Q w) +
      plateauTransport Q (squareResidual Q u) (squareAffine Q w.averageGradient) +
      plateauTransport Q (squareResidual Q u) (squareResidual Q w) := by
  rw [← plateauTransport_congr_grad Q (squareAffine_add_residual_grad Q u)
    (squareAffine_add_residual_grad Q w)]
  rw [plateauTransport_add_left, plateauTransport_add_right, plateauTransport_add_right]
  ring

/-- The source top/top estimate, without additional spectral or boundary assumptions. -/
theorem abs_plateauTransport_top_le (Q : TriadicCube 2) (u w : H1Function (openCubeSet Q)) :
    |plateauTransport Q u w| ≤ squareVectorEnergy Q u.grad + squareVectorEnergy Q w.grad := by
  let x0 := Real.sqrt (∑ i : Fin 2, u.averageGradient i ^ 2)
  let y0 := Real.sqrt (∑ i : Fin 2, w.averageGradient i ^ 2)
  let x1 := Real.sqrt (squareVectorEnergy Q (squareResidual Q u).grad)
  let y1 := Real.sqrt (squareVectorEnergy Q (squareResidual Q w).grad)
  let b := Real.sqrt (17 / 49 : ℝ)
  let m := (48 : ℝ) / (7 * Real.sqrt 2 * Real.pi)
  have h00 := abs_plateauTransport_affine_le Q u.averageGradient w.averageGradient
  have h01 := abs_plateauTransport_affine_residual_le Q u.averageGradient
    (squareResidual Q w) (squareResidual_gradient_mean Q w)
  have h10 := abs_plateauTransport_affine_residual_le Q w.averageGradient
    (squareResidual Q u) (squareResidual_gradient_mean Q u)
  rw [plateauTransport_swap, abs_neg] at h10
  have h11 := abs_plateauTransport_residual_le Q u w
  have hsum : |plateauTransport Q u w| ≤
      x0 * y0 + b * (x0 * y1 + x1 * y0) + m * x1 * y1 := by
    rw [plateauTransport_split]
    have htri := (abs_add_le
      (plateauTransport Q (squareAffine Q u.averageGradient) (squareAffine Q w.averageGradient) +
       plateauTransport Q (squareAffine Q u.averageGradient) (squareResidual Q w) +
       plateauTransport Q (squareResidual Q u) (squareAffine Q w.averageGradient))
      (plateauTransport Q (squareResidual Q u) (squareResidual Q w)))
    have htri2 := abs_add_le
      (plateauTransport Q (squareAffine Q u.averageGradient) (squareAffine Q w.averageGradient) +
       plateauTransport Q (squareAffine Q u.averageGradient) (squareResidual Q w))
      (plateauTransport Q (squareResidual Q u) (squareAffine Q w.averageGradient))
    have htri3 := abs_add_le
      (plateauTransport Q (squareAffine Q u.averageGradient) (squareAffine Q w.averageGradient))
      (plateauTransport Q (squareAffine Q u.averageGradient) (squareResidual Q w))
    change _ ≤ x0 * y0 at h00
    change _ ≤ b * x0 * y1 at h01
    change _ ≤ b * y0 * x1 at h10
    change _ ≤ m * x1 * y1 at h11
    nlinarith only [htri, htri2, htri3, h00, h01, h10, h11]
  have hblock := plateau_top_block_le (x0 := x0) (x1 := x1) (y0 := y0) (y1 := y1)
    (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17 / 49)) plateau_residual_entry_le
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hx0 : x0 ^ 2 = ∑ i : Fin 2, u.averageGradient i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hy0 : y0 ^ 2 = ∑ i : Fin 2, w.averageGradient i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hx1 : x1 ^ 2 = squareVectorEnergy Q (squareResidual Q u).grad :=
    Real.sq_sqrt (squareVectorEnergy_nonneg Q _)
  have hy1 : y1 ^ 2 = squareVectorEnergy Q (squareResidual Q w).grad :=
    Real.sq_sqrt (squareVectorEnergy_nonneg Q _)
  have hu := squareResidual_energy_decomposition Q u
  have hw := squareResidual_energy_decomposition Q w
  exact hsum.trans (hblock.trans_eq (by rw [hx0, hy0, hx1, hy1, ← hu, ← hw]))

end ASDExplicitGamma.Cold

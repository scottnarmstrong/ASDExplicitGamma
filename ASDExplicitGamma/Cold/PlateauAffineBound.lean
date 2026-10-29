module

public import ASDExplicitGamma.Cold.PlateauTransport

/-! # The affine/residual entries of the source plateau block -/

@[expose] public section
noncomputable section
open MeasureTheory Set Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- The affine/affine entry is the planar determinant and obeys Euclidean Cauchy–Schwarz. -/
theorem abs_plateauTransport_affine_le (Q : TriadicCube 2) (p q : Vec 2) :
    |plateauTransport Q (squareAffine Q p) (squareAffine Q q)| ≤
      Real.sqrt (∑ i : Fin 2, p i ^ 2) * Real.sqrt (∑ i : Fin 2, q i ^ 2) := by
  rw [plateauTransport_affine]
  have hs := Real.sq_sqrt (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (p i)))
  have ht := Real.sq_sqrt (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (q i)))
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, hs, ht]
  simp only [Fin.sum_univ_two]
  nlinarith only [sq_nonneg (p 0 * q 0 + p 1 * q 1)]

/-- The exact variance `17/49` controls the affine/residual entry when the actual mean gradient
of the second function vanishes. -/
theorem abs_plateauTransport_affine_residual_le (Q : TriadicCube 2) (p : Vec 2)
    (w : H1Function (openCubeSet Q))
    (hw : ∀ i, ∫ x, w.grad x i ∂normalizedCubeMeasure Q = 0) :
    |plateauTransport Q (squareAffine Q p) w| ≤ Real.sqrt (17 / 49 : ℝ) *
      Real.sqrt (∑ i : Fin 2, p i ^ 2) * Real.sqrt (squareVectorEnergy Q w.grad) := by
  let H : Vec 2 → Vec 2 := fun x i => (plateauOnSquare Q x - 1) * p i
  let R : Vec 2 → Vec 2 := fun x => ![-w.grad x 1, w.grad x 0]
  have hφ := (memLp_plateauOnSquare Q 2).sub (memLp_const (1 : ℝ))
  have hH (i : Fin 2) : MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q) := hφ.mul_const _
  have hR (i : Fin 2) : MemLp (fun x => R x i) 2 (normalizedCubeMeasure Q) := by
    fin_cases i
    · exact (memLp_normalized_of_memL2On (w.gradMemL2 1)).neg
    · exact memLp_normalized_of_memL2On (w.gradMemL2 0)
  have hcoord (i : Fin 2) : ∫ x, (plateauOnSquare Q x - 1) * p i * w.grad x (1-i)
      ∂normalizedCubeMeasure Q =
      ∫ x, plateauOnSquare Q x * p i * w.grad x (1-i) ∂normalizedCubeMeasure Q := by
    have hf : Integrable (fun x => plateauOnSquare Q x * p i * w.grad x (1-i))
        (normalizedCubeMeasure Q) := ((memLp_plateauOnSquare Q 2).mul_const _).integrable_mul
          (memLp_normalized_of_memL2On (w.gradMemL2 (1-i)))
    have hg : Integrable (fun x => p i * w.grad x (1-i)) (normalizedCubeMeasure Q) :=
      ((memLp_normalized_of_memL2On (w.gradMemL2 (1-i))).integrable (by norm_num)).const_mul _
    have heq : (fun x => (plateauOnSquare Q x - 1) * p i * w.grad x (1-i)) =
        (fun x => plateauOnSquare Q x * p i * w.grad x (1-i) - p i * w.grad x (1-i)) := by
      funext x; ring
    rw [heq, integral_sub hf hg, integral_const_mul, hw, mul_zero, sub_zero]
  have hidentity : plateauTransport Q (squareAffine Q p) w = vectorPairing Q H R := by
    rw [vectorPairing_eq_integral_sum Q hH hR]
    simp only [Fin.sum_univ_two, H, R, Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg]
    have hi0 := (hH 0).integrable_mul (memLp_normalized_of_memL2On (w.gradMemL2 1))
    have hi1 := (hH 1).integrable_mul (memLp_normalized_of_memL2On (w.gradMemL2 0))
    rw [integral_add (f := fun x => -((plateauOnSquare Q x - 1) * p 0 * w.grad x 1))
      (g := fun x => (plateauOnSquare Q x - 1) * p 1 * w.grad x 0) hi0.neg hi1, integral_neg]
    have hc0 := hcoord 0
    have hc1 := hcoord 1
    simp only [sub_zero, sub_self] at hc0 hc1
    rw [hc0, hc1]
    unfold plateauTransport
    rw [normalizedSquareTransport_eq_integrals]
    simp only [squareAffine_grad]
  have hHE : squareVectorEnergy Q H = (17 / 49 : ℝ) * (∑ i : Fin 2, p i ^ 2) := by
    unfold squareVectorEnergy
    have he (i : Fin 2) : energy Q (fun x => H x i) = (17 / 49 : ℝ) * p i ^ 2 := by
      rw [energy_eq_integral_sq]
      simp only [H, mul_pow]
      rw [integral_mul_const, integral_plateauOnSquare_sub_one_sq]
    simp_rw [he]
    exact (Finset.mul_sum _ _ _).symm
  have hRE : squareVectorEnergy Q R = squareVectorEnergy Q w.grad := by
    unfold squareVectorEnergy
    simp only [Fin.sum_univ_two, R, Matrix.cons_val_zero, Matrix.cons_val_one,
      energy_eq_integral_sq, neg_sq]
    ring
  rw [hidentity]
  have h := abs_squareVectorPairing_le Q hH hR
  rw [hHE, hRE, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 17 / 49)] at h
  exact h

end ASDExplicitGamma.Cold

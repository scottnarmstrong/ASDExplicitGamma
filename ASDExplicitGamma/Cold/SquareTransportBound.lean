module

public import ASDExplicitGamma.Cold.SquareSmoothApprox
public import ASDExplicitGamma.Cold.PlateauOnSquareMoments

/-! # The actual normalized transport form and its cutoff gradient bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal NNReal

namespace ASDExplicitGamma.Cold

/-- The actual normalized spatial cutoff transport form. -/
def normalizedSquareTransport (Q : TriadicCube 2) (φ : Vec 2 → ℝ)
    (u w : H1Function (openCubeSet Q)) : ℝ :=
  (cubeVolume Q)⁻¹ * squareTransportForm Q φ u w

/-- The normalization agrees with the normalized spatial integrals of the source fields. -/
theorem normalizedSquareTransport_eq_integrals (Q : TriadicCube 2) (φ : Vec 2 → ℝ)
    (u w : H1Function (openCubeSet Q)) :
    normalizedSquareTransport Q φ u w =
      -(∫ x, φ x * u.grad x 0 * w.grad x 1 ∂normalizedCubeMeasure Q) +
        ∫ x, φ x * u.grad x 1 * w.grad x 0 ∂normalizedCubeMeasure Q := by
  rw [integral_normalized_eq_open, integral_normalized_eq_open]
  unfold normalizedSquareTransport squareTransportForm
  ring

/-- The weak gradient bound controls the normalized L² energy of the multiplier. -/
theorem square_cutoff_multiplier_energy (Q : TriadicCube 2) {φ : Vec 2 → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) (u : H1Function (openCubeSet Q)) :
    squareVectorEnergy Q (fun x i => lipschitzWeakGradient φ x i * u.toFun x) ≤
      (C : ℝ) ^ 2 * energy Q u.toFun := by
  let H : Vec 2 → Vec 2 := fun x i => lipschitzWeakGradient φ x i * u.toFun x
  have hu := memLp_normalized_of_memL2On u.memL2
  have hH (i : Fin 2) : MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q) :=
    (hφ.memLp_lineDeriv (μ := normalizedCubeMeasure Q) (basisVec i)).mul hu
  have hgrad : ∀ᵐ x ∂normalizedCubeMeasure Q,
      (∑ i : Fin 2, lipschitzWeakGradient φ x i ^ 2) ≤ (C : ℝ) ^ 2 :=
    (square_ae_normalized_iff Q).mpr (ae_restrict_of_ae (lipschitzWeakGradient_ae_sq_bound hφ))
  have hint : Integrable (fun x => ∑ i : Fin 2, H x i ^ 2) (normalizedCubeMeasure Q) :=
    integrable_finsetSum _ (fun i _ => (hH i).integrable_sq)
  calc
    _ = ∫ x, (∑ i : Fin 2, H x i ^ 2) ∂normalizedCubeMeasure Q := by
      unfold squareVectorEnergy
      simp_rw [energy_eq_integral_sq]
      exact (integral_finsetSum _ (fun i _ => (hH i).integrable_sq)).symm
    _ ≤ ∫ x, (C : ℝ) ^ 2 * u.toFun x ^ 2 ∂normalizedCubeMeasure Q := by
      apply integral_mono_ae hint (hu.integrable_sq.const_mul _)
      filter_upwards [hgrad] with x hx
      have heq : (∑ i : Fin 2, H x i ^ 2) =
          (∑ i : Fin 2, lipschitzWeakGradient φ x i ^ 2) * u.toFun x ^ 2 := by
        simp only [H, mul_pow, Finset.sum_mul]
      rw [heq]
      exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)
    _ = _ := by rw [integral_const_mul, energy_eq_integral_sq]

/-- The integration-by-parts multiplier bound for actual H¹ functions on the square. -/
theorem abs_normalizedSquareTransport_le (Q : TriadicCube 2) {φ : Vec 2 → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) (hφs : tsupport φ ⊆ closedSquare Q)
    (M : ℝ) (hM : ∀ x, ‖φ x‖ ≤ M) (u w : H1Function (openCubeSet Q)) :
    |normalizedSquareTransport Q φ u w| ≤ (C : ℝ) * Real.sqrt (energy Q u.toFun) *
      Real.sqrt (squareVectorEnergy Q w.grad) := by
  let H : Vec 2 → Vec 2 := fun x i => lipschitzWeakGradient φ x i * u.toFun x
  let R : Vec 2 → Vec 2 := fun x => ![w.grad x 1, -w.grad x 0]
  have hu := memLp_normalized_of_memL2On u.memL2
  have hH (i : Fin 2) : MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q) :=
    (hφ.memLp_lineDeriv (μ := normalizedCubeMeasure Q) (basisVec i)).mul hu
  have hR (i : Fin 2) : MemLp (fun x => R x i) 2 (normalizedCubeMeasure Q) := by
    fin_cases i
    · exact memLp_normalized_of_memL2On (w.gradMemL2 1)
    · exact (memLp_normalized_of_memL2On (w.gradMemL2 0)).neg
  have hidentity : normalizedSquareTransport Q φ u w = vectorPairing Q H R := by
    unfold normalizedSquareTransport
    rw [squareTransportForm_eq_boundary Q hφ hφs M hM]
    unfold squareTransportBoundaryForm vectorPairing pairing
    simp only [Fin.sum_univ_two, H, R, Matrix.cons_val_zero, Matrix.cons_val_one,
      cubeAverage_eq_integral_normalizedCubeMeasure, mul_neg, integral_neg]
    rw [integral_normalized_eq_open, integral_normalized_eq_open]
    ring
  have hRE : squareVectorEnergy Q R = squareVectorEnergy Q w.grad := by
    unfold squareVectorEnergy
    simp only [Fin.sum_univ_two, R, Matrix.cons_val_zero, Matrix.cons_val_one, energy_eq_integral_sq,
      neg_sq]
    ring
  have hHbound : Real.sqrt (squareVectorEnergy Q H) ≤ (C : ℝ) * Real.sqrt (energy Q u.toFun) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt (energy_nonneg Q _)]
      exact square_cutoff_multiplier_energy Q hφ u
  rw [hidentity]
  calc
    _ ≤ Real.sqrt (squareVectorEnergy Q H) * Real.sqrt (squareVectorEnergy Q R) :=
      abs_squareVectorPairing_le Q hH hR
    _ ≤ _ := by
      rw [hRE]
      exact mul_le_mul_of_nonneg_right hHbound (Real.sqrt_nonneg _)

end ASDExplicitGamma.Cold

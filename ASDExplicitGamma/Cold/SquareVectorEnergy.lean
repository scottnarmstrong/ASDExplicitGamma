module

public import ASDExplicitGamma.Cold.SquareStreamFunction

/-! # Normalized vector L² energy and Cauchy–Schwarz on the square -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- The squared normalized Euclidean L² norm of a vector field. -/
def squareVectorEnergy (Q : TriadicCube 2) {m : ℕ} (F : Vec 2 → Fin m → ℝ) : ℝ :=
  ∑ i, energy Q (fun x => F x i)

/-- Vector energy is nonnegative. -/
theorem squareVectorEnergy_nonneg (Q : TriadicCube 2) {m : ℕ} (F : Vec 2 → Fin m → ℝ) :
    0 ≤ squareVectorEnergy Q F := Finset.sum_nonneg (fun _ _ => energy_nonneg Q _)

/-- Coordinatewise scalar Cauchy–Schwarz gives its Euclidean vector form. -/
theorem abs_squareVectorPairing_le (Q : TriadicCube 2) {m : ℕ}
    {F G : Vec 2 → Fin m → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    |vectorPairing Q F G| ≤
      Real.sqrt (squareVectorEnergy Q F) * Real.sqrt (squareVectorEnergy Q G) := by
  have hEF : 0 ≤ squareVectorEnergy Q F := by
    unfold squareVectorEnergy
    exact Finset.sum_nonneg fun i _ => energy_nonneg Q _
  have hEG : 0 ≤ squareVectorEnergy Q G := by
    unfold squareVectorEnergy
    exact Finset.sum_nonneg fun i _ => energy_nonneg Q _
  have hcoord : ∀ i : Fin m,
      |pairing Q (fun x => F x i) (fun x => G x i)| ≤
        Real.sqrt (energy Q (fun x => F x i)) *
          Real.sqrt (energy Q (fun x => G x i)) := by
    intro i
    simpa [l2Norm] using abs_pairing_le Q (hF i) (hG i)
  have hsum :
      |vectorPairing Q F G| ≤
        ∑ i : Fin m, Real.sqrt (energy Q (fun x => F x i)) *
          Real.sqrt (energy Q (fun x => G x i)) := by
    unfold vectorPairing
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => hcoord i)
  have hcs :
      (∑ i : Fin m, Real.sqrt (energy Q (fun x => F x i)) *
        Real.sqrt (energy Q (fun x => G x i))) ^ 2 ≤
      squareVectorEnergy Q F * squareVectorEnergy Q G := by
    unfold squareVectorEnergy
    calc
      _ ≤ (∑ i : Fin m, Real.sqrt (energy Q (fun x => F x i)) ^ 2) *
            ∑ i : Fin m, Real.sqrt (energy Q (fun x => G x i)) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      _ = (∑ i : Fin m, energy Q (fun x => F x i)) *
            ∑ i : Fin m, energy Q (fun x => G x i) := by
              congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
                rw [Real.sq_sqrt (energy_nonneg Q _)]
  have hprod : 0 ≤ Real.sqrt (squareVectorEnergy Q F) *
      Real.sqrt (squareVectorEnergy Q G) := by positivity
  have hprodSq : (Real.sqrt (squareVectorEnergy Q F) *
      Real.sqrt (squareVectorEnergy Q G)) ^ 2 =
        squareVectorEnergy Q F * squareVectorEnergy Q G := by
    rw [mul_pow, Real.sq_sqrt hEF, Real.sq_sqrt hEG]
  apply (sq_le_sq₀ (abs_nonneg _) hprod).mp
  calc
    |vectorPairing Q F G| ^ 2 ≤
        (∑ i : Fin m, Real.sqrt (energy Q (fun x => F x i)) *
          Real.sqrt (energy Q (fun x => G x i))) ^ 2 := by
            exact (sq_le_sq₀ (abs_nonneg _) (Finset.sum_nonneg fun i _ =>
              mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hsum
    _ ≤ squareVectorEnergy Q F * squareVectorEnergy Q G := hcs
    _ = (Real.sqrt (squareVectorEnergy Q F) *
          Real.sqrt (squareVectorEnergy Q G)) ^ 2 := hprodSq.symm


/-- The coordinate pairing is the actual normalized integral of the Euclidean dot product. -/
theorem vectorPairing_eq_integral_sum (Q : TriadicCube 2) {m : ℕ} {F G : Vec 2 → Fin m → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    vectorPairing Q F G = ∫ x, (∑ i : Fin m, F x i * G x i) ∂normalizedCubeMeasure Q := by
  unfold vectorPairing pairing
  simp_rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact (integral_finsetSum _ (fun i _ => (hF i).integrable_mul (hG i))).symm

/-- Bilinearity of the normalized vector pairing in its first entry. -/
theorem vectorPairing_sub_left (Q : TriadicCube 2) {m : ℕ} {F G H : Vec 2 → Fin m → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) :
    vectorPairing Q (fun x => F x - G x) H = vectorPairing Q F H - vectorPairing Q G H := by
  unfold vectorPairing
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact pairing_sub_left Q (hF i) (hG i) (hH i)

/-- The normalized vector self-pairing is its squared Euclidean L² norm. -/
theorem vectorPairing_self (Q : TriadicCube 2) {m : ℕ} (F : Vec 2 → Fin m → ℝ) :
    vectorPairing Q F F = squareVectorEnergy Q F := rfl

end ASDExplicitGamma.Cold

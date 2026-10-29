module

public import ASDExplicitGamma.Cold.PlateauWeights

/-! # The absolutely convergent source plateau-weight telescope -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Bounded nonnegative projected energies can be multiplied by the geometric weights. -/
theorem summable_geometric_energy {V : ℕ → ℝ} {M : ℝ}
    (hV : ∀ k, 0 ≤ V k) (hM : ∀ k, V k ≤ M) :
    Summable (fun k => (1 / 9 : ℝ) ^ k * V k) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity) (hV k))
    (fun k => mul_le_mul_of_nonneg_left (hM k) (by positivity))
    ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 9 : ℝ)‖ < 1)).mul_right M)

/-- The fine energy series is absolutely summable from bounded projected energies. -/
theorem summable_plateau_fine_energy {V : ℕ → ℝ} {M : ℝ}
    (hV : ∀ k, 0 ≤ V k) (hM : ∀ k, V k ≤ M) :
    Summable (fun k => (1 / 9 : ℝ) ^ (k+1) * (V (k+2) - V (k+1))) := by
  have h1 := summable_geometric_energy (fun k => hV (k+2)) (fun k => hM (k+2))
  have h2 := summable_geometric_energy (fun k => hV (k+1)) (fun k => hM (k+1))
  have h := (h1.sub h2).mul_left (1 / 9 : ℝ)
  convert h using 1
  funext k
  rw [pow_succ]
  ring

/-- The actual weighted projected energies are summable. -/
theorem summable_plateau_projected_energy {V : ℕ → ℝ} {M : ℝ}
    (hV : ∀ k, 0 ≤ V k) (hM : ∀ k, V k ≤ M) :
    Summable (fun k => plateauEvenWeight k * V (k+1)) :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (plateauEvenWeight_nonneg k) (hV _))
    (fun k => mul_le_mul_of_nonneg_left (hM _) (plateauEvenWeight_nonneg k))
    (summable_plateauEvenWeight.mul_right M)

/-- The exact source telescope, including the exceptional first plateau weight. -/
theorem plateau_energy_telescope {V : ℕ → ℝ} {M : ℝ}
    (hV : ∀ k, 0 ≤ V k) (hM : ∀ k, V k ≤ M) :
    (9 / 4 : ℝ) * V 1 + 7 *
        (∑' k : ℕ, (1 / 9 : ℝ) ^ (k+1) * (V (k+2) - V (k+1))) =
      2 * (∑' k : ℕ, plateauEvenWeight k * V (k+1)) := by
  let A := ∑' k : ℕ, (1 / 9 : ℝ) ^ k * V (k+2)
  have hA := summable_geometric_energy (fun k => hV (k+2)) (fun k => hM (k+2))
  have hB := summable_geometric_energy (fun k => hV (k+1)) (fun k => hM (k+1))
  have hsplit : (∑' k : ℕ, (1 / 9 : ℝ) ^ k * V (k+1)) = V 1 + (1 / 9 : ℝ) * A := by
    rw [hB.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, zero_add]
    congr 1
    simp_rw [pow_succ]
    dsimp [A]
    rw [← tsum_mul_left]
    congr 1
    funext k
    ring
  have hf : (∑' k : ℕ, (1 / 9 : ℝ) ^ (k+1) * (V (k+2) - V (k+1))) =
      (1 / 9 : ℝ) * A - (1 / 9 : ℝ) *
        (∑' k : ℕ, (1 / 9 : ℝ) ^ k * V (k+1)) := by
    have heq : (fun k => (1 / 9 : ℝ) ^ (k+1) * (V (k+2) - V (k+1))) =
        (fun k => (1 / 9 : ℝ) * ((1 / 9 : ℝ) ^ k * V (k+2) -
          (1 / 9 : ℝ) ^ k * V (k+1))) := by funext k; rw [pow_succ]; ring
    rw [heq, tsum_mul_left, hA.tsum_sub hB]
    dsimp [A]
    ring
  have hw : (∑' k : ℕ, plateauEvenWeight k * V (k+1)) =
      (53 / 72 : ℝ) * V 1 + (28 / 81 : ℝ) * A := by
    rw [(summable_plateau_projected_energy hV hM).tsum_eq_zero_add]
    simp only [plateauEvenWeight, ↓reduceIte, zero_add]
    congr 1
    have heq : (fun k : ℕ => (if k+1 = 0 then (53 / 72 : ℝ) else 28 * (1 / 9 : ℝ) ^ (k+1+1)) * V (k+1+1)) =
        (fun k : ℕ => (28 / 81 : ℝ) * ((1 / 9 : ℝ) ^ k * V (k+2))) := by
      funext k
      rw [ite_eq_right (by omega)]
      have he : k+1+1 = k+2 := by omega
      rw [he, pow_add]
      norm_num
      ring
    rw [heq, tsum_mul_left]
  rw [hf, hsplit, hw]
  ring

end ASDExplicitGamma.Cold

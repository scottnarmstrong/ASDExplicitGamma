module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Rev
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # The scalar summation in the cold spectral-pair estimate -/

@[expose] public section

namespace ASDExplicitGamma.Cold

/-- One positive reciprocal pair has nonnegative trace excess. -/
theorem reciprocal_pair_excess_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : 1 ≤ x * y) : 0 ≤ x + y - 2 := by
  nlinarith only [hx, hy, hxy, sq_nonneg (x - y)]

/-- The exact scalar pair estimate. -/
theorem reciprocal_pair_sq_le {x y : ℝ} (hxy : 1 ≤ x * y) :
    (x - 1) ^ 2 + (y - 1) ^ 2 ≤
      2 * (x + y - 2) + (x + y - 2) ^ 2 := by
  nlinarith only [hxy]

/-- Summing reciprocal pairs gives the sharp trace excess bound. A pair is
counted twice, so its excess is bounded by the total excess, not twice it. -/
theorem reciprocal_pairs_sum_sq_le {d : ℕ} (lambda : Fin (2 * d) → ℝ)
    (hpos : ∀ i, 0 < lambda i)
    (hpair : ∀ i, 1 ≤ lambda i * lambda (Fin.rev i)) :
    0 ≤ (∑ i, lambda i) - (2 * d : ℕ) ∧
      (∑ i, (lambda i - 1) ^ 2) ≤
        2 * ((∑ i, lambda i) - (2 * d : ℕ)) +
          ((∑ i, lambda i) - (2 * d : ℕ)) ^ 2 := by
  let t : Fin (2 * d) → ℝ := fun i => lambda i + lambda (Fin.rev i) - 2
  let T : ℝ := (∑ i, lambda i) - (2 * d : ℕ)
  have ht : ∀ i, 0 ≤ t i := fun i =>
    reciprocal_pair_excess_nonneg (hpos i) (hpos (Fin.rev i)) (hpair i)
  have hrev : ∑ i, lambda (Fin.rev i) = ∑ i, lambda i :=
    Equiv.sum_comp (Fin.revPerm : Fin (2 * d) ≃ Fin (2 * d)) lambda
  have hsum : (∑ i, t i) = 2 * T := by
    dsimp only [t, T]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hrev]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hT : 0 ≤ T := by
    have h : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun i _ => ht i
    rw [hsum] at h
    linarith only [h]
  have hmax : ∀ i, t i ≤ T := by
    intro i
    have hne : i ≠ Fin.rev i := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_rev] at hv
      have hi := i.isLt
      omega
    have htwo : t i + t (Fin.rev i) ≤ ∑ k, t k := by
      calc
        _ = ∑ k ∈ ({i, Fin.rev i} : Finset (Fin (2 * d))), t k := by
          simp only [Finset.sum_pair hne]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun k _ _ => ht k)
    have hti : t (Fin.rev i) = t i := by
      dsimp only [t]
      rw [Fin.rev_rev, add_comm]
    rw [hti, hsum] at htwo
    linarith only [htwo]
  have hsq : (∑ i, t i ^ 2) ≤ 2 * T ^ 2 := by
    calc
      _ ≤ ∑ i, T * t i := Finset.sum_le_sum fun i _ => by
        have h := mul_le_mul_of_nonneg_right (hmax i) (ht i)
        simpa only [pow_two] using h
      _ = _ := by rw [← Finset.mul_sum, hsum]; ring
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => reciprocal_pair_sq_le (hpair i)
  have hrevSq : ∑ i, (lambda (Fin.rev i) - 1) ^ 2 = ∑ i, (lambda i - 1) ^ 2 :=
    Equiv.sum_comp (Fin.revPerm : Fin (2 * d) ≃ Fin (2 * d)) (fun i => (lambda i - 1) ^ 2)
  change (∑ i, ((lambda i - 1) ^ 2 + (lambda (Fin.rev i) - 1) ^ 2)) ≤
    ∑ i, (2 * t i + t i ^ 2) at h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hrevSq,
    ← Finset.mul_sum, hsum] at h
  exact ⟨hT, by change (∑ i, (lambda i - 1) ^ 2) ≤ 2 * T + T ^ 2; linarith only [h, hsq]⟩

end ASDExplicitGamma.Cold

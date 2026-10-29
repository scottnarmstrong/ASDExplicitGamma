module

public import ASDExplicitGamma.Triadic.DiagReflection
import Mathlib.Tactic.LinearCombination

/-! The finite reflected lattice row from internal and zero-boundary cell identities. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open scoped BigOperators

noncomputable section

/-- Reflecting the two cell functionals with their different parities gives
the exact cyclic row, including both boundary edges. -/
theorem diagReflectedMeans_row {N : ℕ} (hN : 0 < N) (r σ : ℝ) (m a e : Fin N → ℝ)
    (hinner : ∀ k l : Fin N, l.val = k.val + 1 →
      (m l - m k) / r = (a k + a l) / 2 + σ * (e k - e l))
    (hlower : m ⟨0, hN⟩ / r = a ⟨0, hN⟩ / 2 - σ * e ⟨0, hN⟩)
    (hupper : m ⟨N - 1, by omega⟩ / r = -a ⟨N - 1, by omega⟩ / 2 - σ * e ⟨N - 1, by omega⟩)
    (k : Fin (2 * N)) :
    (diagReflectOdd N m (diagPeriodShift N k) - diagReflectOdd N m k) / r =
      diagLatticeRow (diagPeriodShift N) σ (diagReflectEven N a) (diagReflectOdd N e) k := by
  let K := diagReflectIndex N k
  let L := diagReflectIndex N (diagPeriodShift N k)
  have hk := k.isLt
  have hs := diagPeriodShift_val N k
  by_cases hp : k.val < N
  · by_cases hn : k.val + 1 < N
    · have hrot : k.val + 1 < 2 * N := by omega
      have hK : K.val = k.val := by simp [K, diagReflectIndex, hp]
      have hL : L.val = k.val + 1 := by simp [L, diagReflectIndex, hs, hrot, hn]
      have h := hinner K L (by omega)
      simp only [diagLatticeRow, diagReflectEven, diagReflectOdd, diagReflectSign,
        hs, hp, hrot, hn, ite_true, one_mul]
      exact h
    · have hrot : k.val + 1 < 2 * N := by omega
      have hkLast : k.val = N - 1 := by omega
      have hafter : (diagPeriodShift N k).val = N := by rw [hs, ite_eq_left hrot]; omega
      have hnot : ¬(diagPeriodShift N k).val < N := by omega
      have hK : K = ⟨N - 1, by omega⟩ := by
        apply Fin.ext
        simp only [K, diagReflectIndex, ite_eq_left hp]
        exact hkLast
      have hL : L = ⟨N - 1, by omega⟩ := by
        apply Fin.ext
        change (if (diagPeriodShift N k).val < N then (diagPeriodShift N k).val else
          2 * N - 1 - (diagPeriodShift N k).val) = N - 1
        rw [ite_eq_right hnot, hafter]
        omega
      simp only [diagLatticeRow, diagReflectEven, diagReflectOdd, diagReflectSign,
        hp, hnot, ite_true, ite_false, one_mul, neg_one_mul]
      change (-m L - m K) / r = (a K + a L) / 2 + σ * (e K - -e L)
      rw [hK, hL]
      linear_combination -2 * hupper
  · by_cases hn : k.val + 1 < 2 * N
    · have hnot : ¬(diagPeriodShift N k).val < N := by rw [hs, ite_eq_left hn]; omega
      have hK : K.val = 2 * N - 1 - k.val := by simp [K, diagReflectIndex, hp]
      have hL : L.val = 2 * N - 1 - (k.val + 1) := by
        change (if (diagPeriodShift N k).val < N then (diagPeriodShift N k).val else
          2 * N - 1 - (diagPeriodShift N k).val) = 2 * N - 1 - (k.val + 1)
        rw [ite_eq_right hnot, hs, ite_eq_left hn]
      have h := hinner L K (by omega)
      simp only [diagLatticeRow, diagReflectEven, diagReflectOdd, diagReflectSign,
        hp, hnot, ite_false, neg_one_mul]
      change (-m L - -m K) / r = (a K + a L) / 2 + σ * (-e K - -e L)
      linear_combination h
    · have hlast : k.val = 2 * N - 1 := by omega
      have hafter : (diagPeriodShift N k).val = 0 := by rw [hs, ite_eq_right hn]
      have hpos : (diagPeriodShift N k).val < N := by omega
      have hK : K = ⟨0, hN⟩ := by
        apply Fin.ext
        simp only [K, diagReflectIndex, ite_eq_right hp]
        omega
      have hL : L = ⟨0, hN⟩ := by
        apply Fin.ext
        change (if (diagPeriodShift N k).val < N then (diagPeriodShift N k).val else
          2 * N - 1 - (diagPeriodShift N k).val) = 0
        rw [ite_eq_left hpos, hafter]
      simp only [diagLatticeRow, diagReflectEven, diagReflectOdd, diagReflectSign,
        hp, hpos, ite_false, ite_true, one_mul, neg_one_mul]
      change (m L - -m K) / r = (a K + a L) / 2 + σ * (-e K - e L)
      rw [hK, hL]
      linear_combination 2 * hlower

/-- The sharp source lattice estimate once the actual cell identities and
joint cell budgets have been established. Reflections contribute exactly two
copies to each unnormalized sum. -/
theorem diagReflectedMeans_difference_energy_le {N : ℕ} (hN : 0 < N)
    (r σ : ℝ) (hσ : σ ^ 2 ≤ 1 / 4) (m a e K : Fin N → ℝ)
    (hinner : ∀ k l : Fin N, l.val = k.val + 1 →
      (m l - m k) / r = (a k + a l) / 2 + σ * (e k - e l))
    (hlower : m ⟨0, hN⟩ / r = a ⟨0, hN⟩ / 2 - σ * e ⟨0, hN⟩)
    (hupper : m ⟨N - 1, by omega⟩ / r = -a ⟨N - 1, by omega⟩ / 2 - σ * e ⟨N - 1, by omega⟩)
    (hcell : ∀ k, a k ^ 2 + e k ^ 2 ≤ K k) :
    (∑ k : Fin (2 * N),
      ((diagReflectOdd N m (diagPeriodShift N k) - diagReflectOdd N m k) / r) ^ 2) ≤
        2 * ∑ k : Fin N, K k := by
  have h := diagLatticeRow_contracts (diagPeriodShift N) hσ (diagReflectEven N a) (diagReflectOdd N e)
  simp only [← diagReflectedMeans_row hN r σ m a e hinner hlower hupper] at h
  rw [Finset.sum_add_distrib, diagReflectEven_sum_sq, diagReflectOdd_sum_sq] at h
  have hc := Finset.sum_le_sum (s := Finset.univ) fun k _ => hcell k
  simp only [Finset.sum_add_distrib] at hc
  linarith only [h, hc]

end

end ASDExplicitGamma.Triadic

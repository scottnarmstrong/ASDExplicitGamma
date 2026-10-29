module

public import ASDExplicitGamma.Triadic.TriadicDualNorms

/-! The exact positive-weight tail identity for nonnegative orthogonal energies. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open scoped BigOperators

noncomputable section

/-- The complete strict tail of a nonnegative Haar energy sequence. -/
def haarEnergyTail (a : ℕ → ℝ) (j : ℕ) : ℝ := ∑' n, a (n+j+1)

theorem haarEnergyTail_eq_succ {a : ℕ → ℝ} (ha : Summable a) (j : ℕ) :
    haarEnergyTail a j = a (j+1)+haarEnergyTail a (j+1) := by
  have hs : Summable (fun n => a (n+j+1)) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (j+1)).2 ha
  simpa only [haarEnergyTail, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using hs.tsum_eq_zero_add

/-- Positive weighted summability controls the unweighted energies. -/
theorem summable_of_summable_weighted_energy {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {q : ℝ} (hq : 1 < q) (hs : Summable (fun n => q^n*a n)) : Summable a := by
  apply hs.of_nonneg_of_le ha
  intro n
  exact le_mul_of_one_le_left (ha n) (one_le_pow₀ hq.le)

/-- Finite summation by parts, with the exact remaining tail. -/
theorem haarEnergyTail_finite_identity {a : ℕ → ℝ} (ha : Summable a) (q : ℝ) (N : ℕ) :
    (q-1)*(∑ j ∈ Finset.range N, q^j*haarEnergyTail a j) =
      (∑ n ∈ Finset.range (N+1), q^n*a n)-a 0-haarEnergyTail a 0+q^N*haarEnergyTail a N := by
  induction N with
  | zero => simp
  | succ N hN =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, pow_succ]
      have ht := haarEnergyTail_eq_succ ha N
      linear_combination hN + q^N*q*ht

/-- A weighted strict tail is bounded by the corresponding tail of weighted energies. -/
theorem haarEnergyTail_weighted_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {q : ℝ} (hq : 1 < q)
    (hs : Summable (fun n => q^n*a n)) (N : ℕ) :
    q^N*haarEnergyTail a N ≤ ∑' n, q^(n+N+1)*a (n+N+1) := by
  have haa := summable_of_summable_weighted_energy ha hq hs
  have ht : Summable (fun n => a (n+N+1)) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (N+1)).2 haa
  have hwt : Summable (fun n => q^(n+N+1)*a (n+N+1)) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (N+1)).2 hs
  unfold haarEnergyTail
  rw [← tsum_mul_left]
  exact (ht.mul_left (q^N)).tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hq.le (by omega)) (ha _)) hwt

/-- Membership in the positive Haar space proves weighted residual-tail
summability; no residual-tail finiteness is assumed. -/
theorem haarEnergyTail_weighted_summable {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {q : ℝ} (hq : 1 < q)
    (hs : Summable (fun n => q^n*a n)) : Summable (fun j => q^j*haarEnergyTail a j) := by
  have haa := summable_of_summable_weighted_energy ha hq hs
  have htail (j : ℕ) : 0 ≤ haarEnergyTail a j := tsum_nonneg fun _ => ha _
  apply summable_of_sum_range_le (fun j => mul_nonneg (pow_nonneg (zero_le_one.trans hq.le) _) (htail j))
  intro N
  have hfinite := haarEnergyTail_finite_identity haa q N
  have htaille := haarEnergyTail_weighted_le ha hq hs N
  have htotal := hs.sum_add_tsum_nat_add (N+1)
  simp only [← Nat.add_assoc] at htotal
  have hbound : (q-1)*(∑ j ∈ Finset.range N, q^j*haarEnergyTail a j) ≤ ∑' n, q^n*a n := by
    linarith only [hfinite, htaille, htotal, ha 0, htail 0]
  exact (le_div_iff₀ (sub_pos.mpr hq)).2 (by simpa only [mul_comm] using hbound)

/-- Exact geometric tail identity for every summable positive Haar energy. -/
theorem haarEnergyTail_identity {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {q : ℝ} (hq : 1 < q)
    (hs : Summable (fun n => q^n*a n)) :
    (∑' n, q^n*a n) = (∑' n, a n)+(q-1)*∑' j, q^j*haarEnergyTail a j := by
  have haa := summable_of_summable_weighted_energy ha hq hs
  have htails := haarEnergyTail_weighted_summable ha hq hs
  have habel := weighted_differences (haarEnergyTail a) q htails
  have hdiff (j : ℕ) : haarEnergyTail a (j+1)-haarEnergyTail a j = -a (j+1) := by
    rw [haarEnergyTail_eq_succ haa j]
    ring
  simp_rw [hdiff, mul_neg] at habel
  rw [tsum_neg] at habel
  have hw := hs.tsum_eq_zero_add
  have hu := haa.tsum_eq_zero_add
  simp only [pow_zero, one_mul] at hw
  change (∑' n, a n) = a 0+haarEnergyTail a 0 at hu
  linarith only [habel, hw, hu]

end

end ASDExplicitGamma.Triadic

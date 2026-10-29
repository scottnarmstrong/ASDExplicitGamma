module

public import ASDExplicitGamma.Native.OldSignedAffineCorrector
public import ASDExplicitGamma.Variational.ProjectedSource
public import ASDExplicitGamma.Scalar.InverseHistory
public import ASDExplicitGamma.Variational.LemmaVH1

/-! Stochastic dominance of the geometric weights (Abel summation): for a nondecreasing
nonnegative depth profile `b`, the order-1/4 weak-norm weights `(1-α²)α^{2j}` give no
more than the bank weights `(1-α)α^j`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Scalar ASDExplicitGamma.Native ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic

/-- Abel/dominance inequality for nondecreasing nonnegative sequences. -/
theorem hot_abel_weights_le (α : ℝ) (h0 : 0 < α) (h1 : α < 1) (b : ℕ → ℝ)
    (hb0 : ∀ j, 0 ≤ b j) (hmono : Monotone b)
    (hs : Summable (fun j : ℕ => α ^ j * b j)) :
    (1 - α ^ 2) * (∑' j : ℕ, α ^ (2 * j) * b j) ≤ (1 - α) * (∑' j : ℕ, α ^ j * b j) := by
  have hα2 : α ^ 2 < 1 := by nlinarith
  have hpow (j : ℕ) : α ^ (2 * j) ≤ α ^ j :=
    pow_le_pow_of_le_one h0.le h1.le (by omega)
  have hsq : Summable (fun j : ℕ => α ^ (2 * j) * b j) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (by positivity) (hb0 j))
      (fun j => mul_le_mul_of_nonneg_right (hpow j) (hb0 j)) hs
  -- c j := ν_j b_j - ω_j b_j, with partial sums bounded below by S_N b_N
  let c : ℕ → ℝ := fun j => (1 - α) * (α ^ j * b j) - (1 - α ^ 2) * (α ^ (2 * j) * b j)
  have hcs : Summable c := (hs.mul_left (1 - α)).sub (hsq.mul_left (1 - α ^ 2))
  let S : ℕ → ℝ := fun N => α ^ (2 * N) - α ^ N
  have hSnp (N : ℕ) : S N ≤ 0 := by
    simp only [S]; linarith [hpow N]
  have hSstep (N : ℕ) : S N + ((1 - α) * α ^ N - (1 - α ^ 2) * α ^ (2 * N)) = S (N + 1) := by
    simp only [S]
    rw [show 2 * (N + 1) = 2 * N + 2 by ring, pow_succ, pow_add]
    ring
  have hP (N : ℕ) : S N * b N ≤ ∑ j ∈ Finset.range N, c j := by
    induction N with
    | zero => simp [S]
    | succ N ih =>
        rw [Finset.sum_range_succ]
        have e : c N = ((1 - α) * α ^ N - (1 - α ^ 2) * α ^ (2 * N)) * b N := by
          simp only [c]; ring
        have h2 : S (N + 1) * b (N + 1) ≤ S (N + 1) * b N :=
          mul_le_mul_of_nonpos_left (hmono (Nat.le_succ N)) (hSnp (N + 1))
        have h3 : S (N + 1) * b N = S N * b N + c N := by
          rw [e, ← hSstep N]; ring
        linarith
  have hlow (N : ℕ) : -(α ^ N * b N) ≤ ∑ j ∈ Finset.range N, c j := by
    have : -(α ^ N * b N) ≤ S N * b N := by
      have hSge : -(α ^ N) ≤ S N := by
        simp only [S]; have : 0 ≤ α ^ (2 * N) := by positivity
        linarith
      nlinarith [hb0 N, mul_le_mul_of_nonneg_right hSge (hb0 N)]
    exact this.trans (hP N)
  have hlim : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, c j) Filter.atTop
      (nhds (∑' j, c j)) := hcs.hasSum.tendsto_sum_nat
  have hzero : Filter.Tendsto (fun N => -(α ^ N * b N)) Filter.atTop (nhds 0) := by
    have := hs.tendsto_atTop_zero
    simpa using this.neg
  have hge : 0 ≤ ∑' j, c j := le_of_tendsto_of_tendsto hzero hlim
    (Filter.Eventually.of_forall hlow)
  have hsplit : ∑' j, c j = (1 - α) * (∑' j : ℕ, α ^ j * b j) -
      (1 - α ^ 2) * (∑' j : ℕ, α ^ (2 * j) * b j) := by
    simp only [c]
    rw [hs.mul_left (1 - α) |>.tsum_sub (hsq.mul_left (1 - α ^ 2)), tsum_mul_left, tsum_mul_left]
  linarith

end ASDExplicitGamma.Main

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Scalar ASDExplicitGamma.Native ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic

/-- The weak-norm-weighted inverse depth profile is dominated by the complete bank-weighted
inverse history. -/
theorem hot_weak_weights_le_inverse_history (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    (1 - Scalar.inverseHistoryDiscount ^ 2) * (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
      lemmaVInverseDepthMax Q a j) ≤ oldSignedInverseHistory Q a := by
  have hα := Scalar.inverse_history_discount_range
  have hq : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hqinv : ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ = Scalar.inverseHistoryDiscount :=
    (Scalar.inverse_history_discount_eq).symm
  have hs : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      lemmaVInverseDepthMax Q a j) := by
    have := lemmaVInverseHistory_summable Q hEll hq
    rwa [hqinv] at this
  have h := hot_abel_weights_le _ hα.1 hα.2 (lemmaVInverseDepthMax Q a)
    (lemmaVInverseDepthMax_nonneg Q a)
    (monotone_nat_of_le_succ (fun j => lemmaVInverseDepthMax_le_succ Q hEll j)) hs
  unfold oldSignedInverseHistory lemmaVInverseHistory
  rw [hqinv]
  exact h

end ASDExplicitGamma.Main

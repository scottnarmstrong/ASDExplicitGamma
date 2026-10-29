module

public import ASDExplicitGamma.Cold.PlateauWeights
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # The ratio-nine Schur kernel in the plateau transport estimate -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace ASDExplicitGamma.Cold

/-- The two-sided geometric kernel has total mass exactly two. -/
theorem plateauSchur_geometric_tsum :
    Summable (fun n : ℤ => (1 / 3 : ℝ) ^ n.natAbs) ∧
      (∑' n : ℤ, (1 / 3 : ℝ) ^ n.natAbs) = 2 := by
  let f : ℤ → ℝ := fun n => (1 / 3 : ℝ) ^ n.natAbs
  have hg := summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 3 : ℝ)‖ < 1)
  have hp : Summable (fun n : ℕ => f n) := by simpa [f] using hg
  have hn : Summable (fun n : ℕ => f (-(n + 1))) := by
    convert hg.mul_left (1 / 3 : ℝ) using 1
    funext n
    change (1 / 3 : ℝ) ^ (-(n + 1 : ℤ)).natAbs = (1 / 3 : ℝ) * (1 / 3 : ℝ) ^ n
    rw [show -(n + 1 : ℤ) = -((n + 1 : ℕ) : ℤ) by push_cast; rfl,
      Int.natAbs_neg, Int.natAbs_natCast, pow_succ]
    ring
  refine ⟨Summable.of_nat_of_neg_add_one hp hn, ?_⟩
  change (∑' n : ℤ, f n) = 2
  rw [tsum_of_nat_of_neg_add_one hp hn]
  change (∑' n : ℕ, (1 / 3 : ℝ) ^ n) + (∑' n : ℕ, (1 / 3 : ℝ) ^ (n + 1)) = 2
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by norm_num)]
  norm_num

/-- The ratio-nine off-diagonal decay kernel. -/
def plateauSchurKernel (k l : ℕ) : ℝ := (1 / 3 : ℝ) ^ ((k : ℤ) - l).natAbs

/-- The kernel is symmetric. -/
theorem plateauSchurKernel_comm (k l : ℕ) : plateauSchurKernel k l = plateauSchurKernel l k := by
  unfold plateauSchurKernel
  rw [show (k : ℤ) - l = -((l : ℤ) - k) by ring, Int.natAbs_neg]

/-- Every finite row sum is bounded by the full two-sided mass. -/
theorem plateauSchurKernel_row_le (S : Finset ℕ) (k : ℕ) :
    (∑ l ∈ S, plateauSchurKernel k l) ≤ 2 := by
  classical
  have hinj : Function.Injective (fun l : ℕ => (k : ℤ) - l) := by
    intro l m h
    change (k : ℤ) - (l : ℤ) = (k : ℤ) - (m : ℤ) at h
    exact_mod_cast (sub_right_inj.mp h)
  calc
    _ = ∑ z ∈ S.image (fun l : ℕ => (k : ℤ) - l), (1 / 3 : ℝ) ^ z.natAbs := by
      rw [Finset.sum_image]
      · rfl
      · exact fun _ _ _ _ h => hinj h
    _ ≤ ∑' z : ℤ, (1 / 3 : ℝ) ^ z.natAbs :=
      plateauSchur_geometric_tsum.1.sum_le_tsum _ (fun _ _ => pow_nonneg (by norm_num) _)
    _ = 2 := plateauSchur_geometric_tsum.2

/-- The finite Schur estimate with exactly the source row constant. -/
theorem plateauSchur_finite (S T : Finset ℕ) (a b : ℕ → ℝ) :
    (∑ k ∈ S, ∑ l ∈ T, plateauSchurKernel k l * a k * b l) ≤
      (∑ k ∈ S, a k ^ 2) + (∑ l ∈ T, b l ^ 2) := by
  have hrowA : (∑ k ∈ S, ∑ l ∈ T, plateauSchurKernel k l * a k ^ 2) ≤
      2 * ∑ k ∈ S, a k ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (plateauSchurKernel_row_le T k) (sq_nonneg _)
  have hrowB : (∑ k ∈ S, ∑ l ∈ T, plateauSchurKernel k l * b l ^ 2) ≤
      2 * ∑ l ∈ T, b l ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    simp_rw [plateauSchurKernel_comm _ l]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (plateauSchurKernel_row_le S l) (sq_nonneg _)
  have hpoint (k l : ℕ) : 2 * (plateauSchurKernel k l * a k * b l) ≤
      plateauSchurKernel k l * a k ^ 2 + plateauSchurKernel k l * b l ^ 2 := by
    have hn : 0 ≤ plateauSchurKernel k l := pow_nonneg (by norm_num) _
    nlinarith only [mul_nonneg hn (sq_nonneg (a k - b l))]
  have hs := Finset.sum_le_sum (s := S) (fun k _ =>
    Finset.sum_le_sum (s := T) (fun l _ => hpoint k l))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  linarith only [hs, hrowA, hrowB]

end ASDExplicitGamma.Cold

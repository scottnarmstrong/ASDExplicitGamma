module

public import ASDExplicitGamma.Cold.MatrixFrobeniusTriangle

/-! # Finite-sum and scaling rules for the actual annealed Frobenius norm -/

@[expose] public section
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Finite Minkowski for actual random matrices, retaining their Frobenius norm. -/
theorem matrixFrobeniusL2_sum_le {Ω ι n : Type*} [MeasurableSpace Ω] [Fintype n]
    {ℙ : Measure Ω} (s : Finset ι) {Y : ι → Ω → Matrix n n ℝ}
    (hY : ∀ a ∈ s, ∀ i j, MemLp (fun ω => Y a ω i j) 2 ℙ) :
    matrixFrobeniusL2 ℙ (fun ω => ∑ a ∈ s, Y a ω) ≤ ∑ a ∈ s, matrixFrobeniusL2 ℙ (Y a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [matrixFrobeniusL2,matrixFrobeniusSq]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hsum (i j : n) : MemLp (fun ω => (∑ a ∈ s, Y a ω) i j) 2 ℙ := by
      simpa only [Matrix.sum_apply] using memLp_finsetSum s
        (fun b hb => hY b (Finset.mem_insert_of_mem hb) i j)
    exact (matrixFrobeniusL2_add_le (hY a (Finset.mem_insert_self _ _)) hsum).trans
      (add_le_add_right (ih (fun b hb => hY b (Finset.mem_insert_of_mem hb))) _)

/-- Scalar multiplication has the exact ordinary L2 Frobenius scaling. -/
theorem matrixFrobeniusL2_const_mul {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    (ℙ : Measure Ω) (A : Ω → Matrix n n ℝ) (c : ℝ) :
    matrixFrobeniusL2 ℙ (fun ω => c • A ω) = |c| *matrixFrobeniusL2 ℙ A := by
  have hs (B : Matrix n n ℝ) : matrixFrobeniusSq (c • B) = c^2*matrixFrobeniusSq B := by
    simp only [matrixFrobeniusSq,Matrix.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]
  unfold matrixFrobeniusL2
  simp_rw [hs]
  rw [integral_const_mul,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq_eq_abs]

end ASDExplicitGamma.Cold

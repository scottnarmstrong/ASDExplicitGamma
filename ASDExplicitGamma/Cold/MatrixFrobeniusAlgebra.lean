module

public import ASDExplicitGamma.Cold.SpectralPairMoment

/-! # Ordinary Frobenius algebra used by the cold graph bounds -/

@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The actual Frobenius inner product, without an operator-norm substitution. -/
def matrixFrobeniusInner {n : Type*} [Fintype n] (A B : Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, A i j*B i j

theorem matrixFrobeniusSq_nonneg {n : Type*} [Fintype n] (A : Matrix n n ℝ) :
    0 ≤ matrixFrobeniusSq A := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem matrixFrobeniusSq_add {n : Type*} [Fintype n] (A B : Matrix n n ℝ) :
    matrixFrobeniusSq (A+B) = matrixFrobeniusSq A+matrixFrobeniusSq B+2*matrixFrobeniusInner A B := by
  unfold matrixFrobeniusSq matrixFrobeniusInner
  have he (x y : ℝ) : (x+y)^2 = x^2+y^2+2*(x*y) := by ring
  simp only [Matrix.add_apply,he,Finset.sum_add_distrib,← Finset.mul_sum]

theorem matrixFrobeniusSq_sub {n : Type*} [Fintype n] (A B : Matrix n n ℝ) :
    matrixFrobeniusSq (A-B) = matrixFrobeniusSq A+matrixFrobeniusSq B-2*matrixFrobeniusInner A B := by
  unfold matrixFrobeniusSq matrixFrobeniusInner
  have he (x y : ℝ) : (x-y)^2 = x^2+y^2-2*(x*y) := by ring
  simp only [Matrix.sub_apply,he,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]

/-- For symmetric matrices the Frobenius product is the ordinary trace product. -/
theorem matrixFrobeniusInner_eq_trace_mul {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {B : Matrix n n ℝ} (hB : B.IsHermitian) :
    matrixFrobeniusInner A B = (A*B).trace := by
  unfold matrixFrobeniusInner Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j, A i j*B i j) = ∑ j, A i j*B j i
  simp_rw [hB.isSymm.apply i]

/-- The actual matrix Frobenius Cauchy--Schwarz inequality. -/
theorem abs_matrixFrobeniusInner_le {n : Type*} [Fintype n] (A B : Matrix n n ℝ) :
    |matrixFrobeniusInner A B| ≤ Real.sqrt (matrixFrobeniusSq A)*Real.sqrt (matrixFrobeniusSq B) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : n×n => A p.1 p.2) (fun p : n×n => B p.1 p.2)
  simp only [Fintype.sum_prod_type] at h
  have he : (Real.sqrt (matrixFrobeniusSq A)*Real.sqrt (matrixFrobeniusSq B))^2 =
      matrixFrobeniusSq A*matrixFrobeniusSq B := by
    rw [mul_pow,Real.sq_sqrt (matrixFrobeniusSq_nonneg A),Real.sq_sqrt (matrixFrobeniusSq_nonneg B)]
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,he]
  exact h

end ASDExplicitGamma.Cold

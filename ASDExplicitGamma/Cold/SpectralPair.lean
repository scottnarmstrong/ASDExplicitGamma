module

public import ASDExplicitGamma.Cold.EigenvalueOrder
public import ASDExplicitGamma.Cold.SpectralPairAlgebra
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.LinearAlgebra.Trace

/-! # The deterministic cold spectral-pair estimate -/

@[expose] public section

namespace ASDExplicitGamma.Cold

open Matrix
open scoped RealInnerProductSpace

/-- The Euclidean operator representation preserves the ordinary matrix trace. -/
theorem trace_toEuclideanLin {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ n) A.toEuclideanLin = A.trace :=
  Matrix.trace_toLin_eq A (EuclideanSpace.basisFun n ℝ).toBasis

/-- The squared Frobenius norm, written entrywise to avoid confusing it with
the elementwise or operator matrix norms. -/
def matrixFrobeniusSq {n : Type*} [Fintype n] (A : Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- For a real symmetric matrix the squared Frobenius norm is tr(A²). -/
theorem matrixFrobeniusSq_eq_trace_mul {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    matrixFrobeniusSq A = (A * A).trace := by
  unfold matrixFrobeniusSq Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j, A i j ^ 2) = ∑ j, A i j * A j i
  apply Finset.sum_congr rfl
  intro j _
  rw [hA.isSymm.apply j i]
  ring

/-- The trace is the sum of the eigenvalues in any orthonormal eigenbasis. -/
theorem linearMap_trace_eq_eigenbasis_sum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ}
    (b : OrthonormalBasis (Fin N) ℝ E) (T : E →ₗ[ℝ] E) (lambda : Fin N → ℝ)
    (hT : ∀ i, T (b i) = lambda i • b i) :
    LinearMap.trace ℝ E T = ∑ i, lambda i := by
  have hmat : LinearMap.toMatrix b.toBasis b.toBasis T = Matrix.diagonal lambda := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have hbj : b.toBasis j = b j := congrFun b.coe_toBasis j
    rw [hbj, hT]
    change b.repr (lambda j • b j) i = if i = j then lambda i else 0
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis, hmat, Matrix.trace_diagonal]

end ASDExplicitGamma.Cold

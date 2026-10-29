module

public import ASDExplicitGamma.Cold.MatrixFrobeniusAlgebra

/-! # The trace-square bound on a positive response gap -/

@[expose] public section
noncomputable section
open Matrix Unitary
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The actual PSD gap has Frobenius square at most its trace square. -/
theorem matrixFrobeniusSq_le_trace_sq {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) : matrixFrobeniusSq A ≤ A.trace^2 := by
  let E := EuclideanSpace ℝ n
  let T : E →ₗ[ℝ] E := A.toEuclideanLin
  have hs : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.1
  have hdim : Module.finrank ℝ E = Fintype.card n := finrank_euclideanSpace
  let b := hs.eigenvectorBasis hdim
  let lambda := hs.eigenvalues hdim
  have hT : ∀ i, T (b i) = lambda i • b i := hs.apply_eigenvectorBasis hdim
  have hn (i : Fin (Fintype.card n)) : 0 ≤ lambda i := by
    have h := hA.dotProduct_mulVec_nonneg (b i).ofLp
    have he : inner ℝ (b i) (T (b i)) = lambda i := by
      rw [hT,inner_smul_right]
      rw [real_inner_self_eq_norm_sq,b.norm_eq_one]
      norm_num
    rw [← he]
    change 0 ≤ inner ℝ (show EuclideanSpace ℝ n from b i) (A.toEuclideanLin (b i))
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, star_trivial, dotProduct_comm] using h
  have htr : A.trace = ∑ i, lambda i := by
    rw [← trace_toEuclideanLin]
    exact linearMap_trace_eq_eigenbasis_sum b T lambda hT
  have hsq : matrixFrobeniusSq A = ∑ i, (lambda i)^2 := by
    rw [matrixFrobeniusSq_eq_trace_mul hA.1,← trace_toEuclideanLin]
    apply linearMap_trace_eq_eigenbasis_sum b
    intro i
    change ((Matrix.toLpLin 2 2) (A*A)) (b i) = (lambda i)^2 • b i
    rw [Matrix.toLpLin_mul_same,LinearMap.comp_apply]
    change T (T (b i)) = _
    rw [hT,map_smul,hT,smul_smul,pow_two]
  rw [hsq,htr]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hn i)

end ASDExplicitGamma.Cold

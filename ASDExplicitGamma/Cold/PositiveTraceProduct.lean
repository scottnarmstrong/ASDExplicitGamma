module

public import ASDExplicitGamma.Cold.SpectralPair

/-! # The trace of a product of two actual positive matrices -/

@[expose] public section
noncomputable section
open Matrix Unitary
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Positive semidefinite matrices have nonnegative trace product, even if their product
is not symmetric. This is the sign retained by the cold graph argument. -/
theorem trace_mul_nonneg_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A*B).trace := by
  let U := hA.1.eigenvectorUnitary
  have hC := hB.conjTranspose_mul_mul_same (U : Matrix n n ℝ)
  have he : A = (U : Matrix n n ℝ)*Matrix.diagonal hA.1.eigenvalues*(U : Matrix n n ℝ)ᴴ := by
    simpa only [U,conjStarAlgAut_apply,star_eq_conjTranspose,RCLike.ofReal_real_eq_id,Function.comp_def,id_eq] using hA.1.spectral_theorem
  rw [he,Matrix.trace_mul_cycle,Matrix.trace_mul_cycle]
  have ht : ((U : Matrix n n ℝ)ᴴ*B*((U : Matrix n n ℝ)*Matrix.diagonal hA.1.eigenvalues)).trace =
      ∑ i, (((U : Matrix n n ℝ)ᴴ*B*(U : Matrix n n ℝ)) i i)*hA.1.eigenvalues i := by
    rw [← Matrix.mul_assoc,Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    change (((U : Matrix n n ℝ)ᴴ*B*(U : Matrix n n ℝ))*Matrix.diagonal hA.1.eigenvalues) i i = _
    rw [Matrix.mul_diagonal]
  rw [ht]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hC.diag_nonneg (i := i)) (hA.eigenvalues_nonneg i))

end ASDExplicitGamma.Cold

module

public import ASDExplicitGamma.Inverse.ClippedMatrixOperatorSum

/-! A quadratic pairing and its exact Euclidean operator-norm bound. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- The loading's squared Euclidean norm, retaining its literal dot product. -/
theorem clipped_euclidean_norm_sq {n : Type*} [Fintype n] (v : n → ℝ) :
    ‖WithLp.toLp 2 v‖^2 = dotProduct v v := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct,pow_two]

/-- Operator norm bound on the actual quadratic form, at arbitrary loads. -/
theorem clipped_quadratic_abs_le_norm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (v : n → ℝ) :
    |dotProduct v (A.mulVec v)| ≤
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A‖*dotProduct v v := by
  let x : EuclideanSpace ℝ n := WithLp.toLp 2 v
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A
  have he : inner ℝ x (T x) = dotProduct v (A.mulVec v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change dotProduct (A.mulVec v) v = _
    exact dotProduct_comm _ _
  have hn := (norm_inner_le_norm (𝕜 := ℝ) x (T x)).trans
    (mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg x))
  rw [he,Real.norm_eq_abs] at hn
  apply hn.trans_eq
  have hx : ‖x‖^2=dotProduct v v := clipped_euclidean_norm_sq v
  calc
    _ = ‖T‖*‖x‖^2 := by ring
    _ = _ := by rw [hx]

end ASDExplicitGamma.Inverse

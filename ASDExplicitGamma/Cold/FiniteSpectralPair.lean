module

public import ASDExplicitGamma.Cold.SpectralPair

/-! # Spectral pairs on arbitrary finite doubled coordinate carriers -/

@[expose] public section
noncomputable section
open Matrix
open scoped RealInnerProductSpace
namespace ASDExplicitGamma.Cold

/-- A symmetric involution acts as an isometric involution. -/
noncomputable def matrixReflectionIsometry_finite {n : Type*} [Fintype n] [DecidableEq n] (R : Matrix n n ℝ)
    (hR : R.IsHermitian) (hRR : R * R = 1) :
    EuclideanSpace ℝ n ≃ₗᵢ[ℝ] EuclideanSpace ℝ n := by
  let r := R.toEuclideanLin
  have hrr : ∀ x, r (r x) = x := by
    intro x
    have h := congrArg (fun A : Matrix n n ℝ => A.toEuclideanLin x) hRR
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
      Matrix.toLpLin_one, LinearMap.comp_apply, LinearMap.id_apply] using h
  let e : EuclideanSpace ℝ n ≃ₗ[ℝ] EuclideanSpace ℝ n :=
    { r with invFun := r, left_inv := hrr, right_inv := hrr }
  apply LinearEquiv.isometryOfInner e
  intro x y
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hR
  change ⟪r x, r y⟫ = ⟪x, y⟫
  rw [hs, hrr]

/-- The isometry has the literal matrix action. -/
theorem matrixReflectionIsometry_finite_apply {n : Type*} [Fintype n] [DecidableEq n] (R : Matrix n n ℝ)
    (hR : R.IsHermitian) (hRR : R * R = 1) (x : EuclideanSpace ℝ n) :
    matrixReflectionIsometry_finite R hR hRR x = R.toEuclideanLin x := rfl

/-- The isometry is involutive. -/
theorem matrixReflectionIsometry_finite_involutive {n : Type*} [Fintype n] [DecidableEq n] (R : Matrix n n ℝ)
    (hR : R.IsHermitian) (hRR : R * R = 1) :
    Function.Involutive (matrixReflectionIsometry_finite R hR hRR) := by
  intro x
  simp only [matrixReflectionIsometry_finite_apply]
  have h := congrArg (fun A : Matrix n n ℝ => A.toEuclideanLin x) hRR
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    Matrix.toLpLin_one, LinearMap.comp_apply, LinearMap.id_apply] using h

/-- Positivity of a matrix eigenvalue in any orthonormal eigenbasis. -/
theorem matrix_eigenbasis_eigenvalue_pos_finite {n : Type*} [Fintype n] [DecidableEq n] {N : ℕ} {A : Matrix n n ℝ}
    (hA : A.PosDef) (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ n))
    (lambda : Fin N → ℝ) (hb : ∀ i, A.toEuclideanLin (b i) = lambda i • b i) (i : Fin N) :
    0 < lambda i := by
  have hne : b i ≠ 0 := b.orthonormal.ne_zero i
  have hraw : (b i).ofLp ≠ 0 := by
    intro h
    apply hne
    apply WithLp.ofLp_injective
    exact h
  have hp := hA.dotProduct_mulVec_pos hraw
  have hi : 0 < ⟪b i, A.toEuclideanLin (b i)⟫ := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, star_trivial, dotProduct_comm] using hp
  rw [hb, inner_smul_right] at hi
  exact pos_of_mul_pos_left hi real_inner_self_nonneg

/-- The centered squared Frobenius norm is the sum of the centered squared
eigenvalues. -/
theorem matrixFrobeniusSq_sub_one_eq_eigenbasis_sum_finite {n : Type*} [Fintype n] [DecidableEq n] {N : ℕ}
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ n))
    (lambda : Fin N → ℝ) (hT : ∀ i, A.toEuclideanLin (b i) = lambda i • b i) :
    matrixFrobeniusSq (A - 1) = ∑ i, (lambda i - 1) ^ 2 := by
  rw [matrixFrobeniusSq_eq_trace_mul (hA.sub Matrix.isHermitian_one),
    ← trace_toEuclideanLin]
  apply linearMap_trace_eq_eigenbasis_sum b
  intro i
  have hc : (A - 1).toEuclideanLin (b i) = (lambda i - 1) • b i := by
    change ((Matrix.toLpLin 2 2) (A - 1)) (b i) = _
    rw [map_sub, LinearMap.sub_apply, Matrix.toLpLin_one]
    change A.toEuclideanLin (b i) - b i = _
    rw [hT, sub_smul, one_smul]
  change ((Matrix.toLpLin 2 2) ((A - 1) * (A - 1))) (b i) = _
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply, hc, map_smul, hc, smul_smul]
  rw [pow_two]

/-- CO-SPECTRAL-PAIR: inverse/reflection order forces nonnegative trace excess
and the sharp squared Frobenius estimate, with no spectral-pair premise. -/
theorem matrix_spectral_pair_finite {n : Type*} [Fintype n] [DecidableEq n] {d : ℕ}
    (hcard : Fintype.card n = 2*d)
    (A R : Matrix n n ℝ)
    (hA : A.PosDef) (hR : R.IsHermitian) (hRR : R * R = 1)
    (horder : (R * A * R - A⁻¹).PosSemidef) :
    0 ≤ A.trace - (2 * d : ℕ) ∧
      matrixFrobeniusSq (A - 1) ≤
        2 * (A.trace - (2 * d : ℕ)) + (A.trace - (2 * d : ℕ)) ^ 2 := by
  let E := EuclideanSpace ℝ n
  let T : E →ₗ[ℝ] E := A.toEuclideanLin
  let S : E →ₗ[ℝ] E := A⁻¹.toEuclideanLin
  have hsymm : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  have hdim : Module.finrank ℝ E = 2 * d := by
    simp only [E, finrank_euclideanSpace,hcard]
  let b := hsymm.eigenvectorBasis hdim
  let lambda := hsymm.eigenvalues hdim
  have hT : ∀ i, T (b i) = lambda i • b i := hsymm.apply_eigenvectorBasis hdim
  have hpos : ∀ i, 0 < lambda i := matrix_eigenbasis_eigenvalue_pos_finite hA b lambda hT
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hST : ∀ x, S (T x) = x := by
    intro x
    have h := congrArg (fun B : Matrix n n ℝ => B.toEuclideanLin x)
      (Matrix.nonsing_inv_mul A hdet)
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
      Matrix.toLpLin_one, LinearMap.comp_apply, LinearMap.id_apply] using h
  let r := matrixReflectionIsometry_finite R hR hRR
  have ho : ∀ x : E, ⟪x, S x⟫ ≤ ⟪x, r (T (r x))⟫ := by
    intro x
    have h := (Matrix.isPositive_toEuclideanLin_iff.mpr horder).2 x
    change 0 ≤ ⟪(R * A * R - A⁻¹).toEuclideanLin x, x⟫ at h
    change ⟪x, A⁻¹.toEuclideanLin x⟫ ≤ ⟪x, R.toEuclideanLin (A.toEuclideanLin (R.toEuclideanLin x))⟫
    simp only [Matrix.toEuclideanLin, map_sub, Matrix.toLpLin_mul_same,
      LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_left, real_inner_comm] at h
    exact sub_nonneg.mp h
  have hpair : ∀ i, 1 ≤ lambda i * lambda (Fin.rev i) :=
    reciprocal_eigenvalue_pair b T S r lambda (hsymm.eigenvalues_antitone hdim) hpos hT hST
      (matrixReflectionIsometry_finite_involutive R hR hRR) ho
  have htr : A.trace = ∑ i, lambda i := by
    rw [← trace_toEuclideanLin]
    exact linearMap_trace_eq_eigenbasis_sum b T lambda hT
  rw [htr, matrixFrobeniusSq_sub_one_eq_eigenbasis_sum_finite hA.isHermitian b lambda hT]
  exact reciprocal_pairs_sum_sq_le lambda hpos hpair

end ASDExplicitGamma.Cold

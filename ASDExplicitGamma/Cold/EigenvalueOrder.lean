module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Ordered eigenvalue comparison from quadratic-form order

The finite-dimensional intersection argument is proved here; spectral pairing
must not be an extra premise of the cold spectral estimate.
-/

@[expose] public section

namespace ASDExplicitGamma.Cold

open scoped RealInnerProductSpace

/-- An orthonormal eigenbasis diagonalizes the quadratic form. -/
theorem inner_apply_eq_eigenbasis_sum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {N : ℕ} (b : OrthonormalBasis (Fin N) ℝ E)
    (T : E →ₗ[ℝ] E) (lambda : Fin N → ℝ)
    (hT : ∀ i, T (b i) = lambda i • b i) (x : E) :
    ⟪x, T x⟫ = ∑ i, lambda i * (b.repr x i) ^ 2 := by
  calc
    ⟪x, T x⟫ = ⟪x, T (∑ i, b.repr x i • b i)⟫ := by rw [b.sum_repr]
    _ = _ := by
      simp only [map_sum, map_smul, hT, inner_sum, inner_smul_right,
        b.repr_apply_apply, real_inner_comm]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Parseval in the real eigenbasis coordinates. -/
theorem eigenbasis_sum_sq_eq_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {N : ℕ} (b : OrthonormalBasis (Fin N) ℝ E) (x : E) :
    (∑ i, (b.repr x i) ^ 2) = ⟪x, x⟫ := by
  simpa only [b.repr_apply_apply, real_inner_comm, pow_two] using
    b.sum_inner_mul_inner x x

/-- A nonzero vector supported on the first k+1 coordinates of one basis
and the last N-k coordinates of another. The missing coordinates impose only
N-1 linear conditions. -/
theorem exists_common_spectral_vector {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ}
    (a b : OrthonormalBasis (Fin N) ℝ E) (k : Fin N) :
    ∃ x : E, x ≠ 0 ∧ (∀ i, k < i → a.repr x i = 0) ∧
      (∀ i, i < k → b.repr x i = 0) := by
  classical
  let F : E →ₗ[ℝ] ((Set.Ioi k → ℝ) × (Set.Iio k → ℝ)) :=
    (LinearMap.pi fun i : Set.Ioi k => a.toBasis.coord i.val).prod
      (LinearMap.pi fun i : Set.Iio k => b.toBasis.coord i.val)
  have hdim : Module.finrank ℝ ((Set.Ioi k → ℝ) × (Set.Iio k → ℝ)) <
      Module.finrank ℝ E := by
    rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi,
      Module.finrank_eq_card_basis a.toBasis, Fintype.card_fin,
      Fintype.card_Ioi, Fin.card_Ioi, Fintype.card_Iio, Fin.card_Iio]
    omega
  obtain ⟨x, hx, hne⟩ := (Submodule.ne_bot_iff F.ker).mp
    (LinearMap.ker_ne_bot_of_finrank_lt (f := F) hdim)
  have hFx : F x = 0 := hx
  refine ⟨x, hne, ?_, ?_⟩
  · intro i hi
    have h := congrArg (fun y : (Set.Ioi k → ℝ) × (Set.Iio k → ℝ) =>
      y.1 ⟨i, hi⟩) hFx
    change a.toBasis.repr x i = 0 at h
    simpa only [OrthonormalBasis.coe_toBasis_repr_apply] using h
  · intro i hi
    have h := congrArg (fun y : (Set.Ioi k → ℝ) × (Set.Iio k → ℝ) =>
      y.2 ⟨i, hi⟩) hFx
    change b.toBasis.repr x i = 0 at h
    simpa only [OrthonormalBasis.coe_toBasis_repr_apply] using h

/-- Weyl monotonicity, proved from the eigenbasis intersection argument.
Both eigenvalue lists are in descending order. -/
theorem ordered_eigenvalues_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ}
    (a b : OrthonormalBasis (Fin N) ℝ E) (T S : E →ₗ[ℝ] E)
    (lambda mu : Fin N → ℝ) (hlambda : Antitone lambda) (hmu : Antitone mu)
    (hT : ∀ i, T (a i) = lambda i • a i)
    (hS : ∀ i, S (b i) = mu i • b i)
    (horder : ∀ x, ⟪x, T x⟫ ≤ ⟪x, S x⟫) (k : Fin N) :
    lambda k ≤ mu k := by
  obtain ⟨x, hne, hxA, hxB⟩ := exists_common_spectral_vector a b k
  have hlow : lambda k * ⟪x, x⟫ ≤ ⟪x, T x⟫ := by
    rw [inner_apply_eq_eigenbasis_sum a T lambda hT,
      ← eigenbasis_sum_sq_eq_inner a x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : k < i
    · rw [hxA i hi]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, le_refl]
    · exact mul_le_mul_of_nonneg_right (hlambda (le_of_not_gt hi)) (sq_nonneg _)
  have hupp : ⟪x, S x⟫ ≤ mu k * ⟪x, x⟫ := by
    rw [inner_apply_eq_eigenbasis_sum b S mu hS,
      ← eigenbasis_sum_sq_eq_inner b x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i < k
    · rw [hxB i hi]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, le_refl]
    · exact mul_le_mul_of_nonneg_right (hmu (le_of_not_gt hi)) (sq_nonneg _)
  exact (mul_le_mul_iff_left₀ (real_inner_self_pos.mpr hne)).mp
    (hlow.trans ((horder x).trans hupp))

/-- Reciprocal eigenvalue pairing follows from inverse/reflection order.
The reflection is an involutive isometry; no eigenvalue comparison is assumed. -/
theorem reciprocal_eigenvalue_pair {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ}
    (b : OrthonormalBasis (Fin N) ℝ E) (T S : E →ₗ[ℝ] E)
    (R : E ≃ₗᵢ[ℝ] E) (lambda : Fin N → ℝ)
    (hlambda : Antitone lambda) (hpos : ∀ i, 0 < lambda i)
    (hT : ∀ i, T (b i) = lambda i • b i)
    (hST : ∀ x, S (T x) = x) (hR : Function.Involutive R)
    (horder : ∀ x, ⟪x, S x⟫ ≤ ⟪x, R (T (R x))⟫) (i : Fin N) :
    1 ≤ lambda i * lambda (Fin.rev i) := by
  let a := b.reindex (Fin.revPerm : Fin N ≃ Fin N)
  let c := b.map R
  let C : E →ₗ[ℝ] E := R.toLinearMap.comp (T.comp R.toLinearMap)
  let mu : Fin N → ℝ := fun k => (lambda (Fin.rev k))⁻¹
  have hmu : Antitone mu := by
    intro k l hkl
    exact (inv_le_inv₀ (hpos _) (hpos _)).mpr
      (hlambda (Fin.rev_le_rev.mpr hkl))
  have hS : ∀ k, S (a k) = mu k • a k := by
    intro k
    simp only [a, mu, OrthonormalBasis.reindex_apply, Fin.revPerm_symm]
    change S (b (Fin.rev k)) = (lambda (Fin.rev k))⁻¹ • b (Fin.rev k)
    have h := congrArg S (hT (Fin.rev k))
    rw [hST, map_smul] at h
    calc
      S (b (Fin.rev k)) = (lambda (Fin.rev k))⁻¹ •
          (lambda (Fin.rev k) • S (b (Fin.rev k))) := by
        rw [smul_smul, inv_mul_cancel₀ (hpos _).ne', one_smul]
      _ = _ := congrArg ((lambda (Fin.rev k))⁻¹ • ·) h.symm
  have hC : ∀ k, C (c k) = lambda k • c k := by
    intro k
    change R (T (R (R (b k)))) = lambda k • R (b k)
    rw [hR, hT, map_smul]
  have hcmp := ordered_eigenvalues_le a c S C mu lambda hmu hlambda hS hC horder i
  change (lambda (Fin.rev i))⁻¹ ≤ lambda i at hcmp
  have h := mul_le_mul_of_nonneg_right hcmp (hpos (Fin.rev i)).le
  simpa only [inv_mul_cancel₀ (hpos (Fin.rev i)).ne'] using h

end ASDExplicitGamma.Cold

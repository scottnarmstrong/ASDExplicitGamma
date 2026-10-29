module

public import ASDExplicitGamma.Scalar.PhysicalResolventIdentity

/-! T4, Hilbert-space part: a maximizer of the reduced pair functional
`2⟨w,x⟩ - α‖x‖² - α⁻¹‖s - W x‖²` over `X × K` solves the pure-flux pair system with load `(0,w)`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Triadic
open scoped InnerProduct InnerProductSpace

noncomputable section

theorem fw_euler_zero {b c : ℝ} (hc : 0 ≤ c) (h : ∀ t : ℝ, 2 * t * b ≤ t ^ 2 * c) :
    b = 0 := by
  have h1 := h (b / (c + 1))
  have hc1 : 0 < c + 1 := by linarith
  by_contra hb
  have hb2 : 0 < b ^ 2 := by positivity
  have h2 : 2 * (b / (c + 1)) * b = 2 * b ^ 2 / (c + 1) := by field_simp
  have h3 : (b / (c + 1)) ^ 2 * c = b ^ 2 * c / (c + 1) ^ 2 := by field_simp
  rw [h2, h3, div_le_div_iff₀ hc1 (by positivity)] at h1
  nlinarith [mul_pos hb2 hc1, sq_nonneg c, mul_pos hb2 hc1]

theorem fw_norm_add_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v u : E) (t : ℝ) :
    ‖v + t • u‖ ^ 2 = ‖v‖ ^ 2 + 2 * t * ⟪v, u⟫_ℝ + t ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (Ks Xs : Submodule ℝ H) [Ksᗮ.HasOrthogonalProjection] [CompleteSpace Xs]
  (W : H →L[ℝ] H) (A : Xs →L[ℝ] H) (hA : ∀ x' : Xs, A x' = Ksᗮ.starProjection (W (x' : H)))

/-- The reduced pair functional. -/
def fwPhi (α : ℝ) (w x : Xs) (s : Ks) : ℝ :=
  2 * ⟪(w : H), (x : H)⟫_ℝ - α * ‖(x : H)‖ ^ 2 - α⁻¹ * ‖(s : H) - W (x : H)‖ ^ 2

include hA in
theorem fw_euler (α : ℝ) (hα : 0 < α) (w x : Xs) (s : Ks)
    (hmax : ∀ (x' : Xs) (s' : Ks), fwPhi Ks Xs W α w x' s' ≤ fwPhi Ks Xs W α w x s) :
    (α⁻¹ • ((s : H) - W (x : H))) ∈ Ksᗮ ∧
      α • (α⁻¹ • ((s : H) - W (x : H))) + A x = 0 ∧
      -(A.adjoint (α⁻¹ • ((s : H) - W (x : H)))) + α • x = w := by
  set r : H := (s : H) - W (x : H) with hr
  have hα' : 0 < α⁻¹ := inv_pos.mpr hα
  have hrK : ∀ q : Ks, ⟪r, (q : H)⟫_ℝ = 0 := by
    intro q
    have h0 := fw_euler_zero (b := -⟪r, (q : H)⟫_ℝ) (c := ‖(q : H)‖ ^ 2) (by positivity) ?_
    · linarith
    intro t
    have h := hmax x (s + t • q)
    unfold fwPhi at h
    have e1 : ((s + t • q : Ks) : H) - W (x : H) = r + t • (q : H) := by
      rw [hr]; simp only [Submodule.coe_add, Submodule.coe_smul]; abel
    rw [e1, fw_norm_add_smul] at h
    have h2 : ((s : H) - W (x : H)) = r := hr.symm
    rw [h2] at h
    have := mul_le_mul_of_nonneg_left (show α * α⁻¹ ≤ α * α⁻¹ from le_rfl) hα.le
    nlinarith [mul_pos hα' hα', mul_nonneg hα'.le (sq_nonneg t), mul_nonneg hα'.le (sq_nonneg ‖(q : H)‖),
      mul_nonneg hα'.le (mul_nonneg (sq_nonneg t) (sq_nonneg ‖(q : H)‖))]
  have hyflux : α⁻¹ • r ∈ Ksᗮ := by
    refine Submodule.smul_mem _ _ ?_
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [real_inner_comm]
    exact hrK ⟨u, hu⟩
  have hrflux : r ∈ Ksᗮ := by
    have := Submodule.smul_mem Ksᗮ α hyflux
    rwa [smul_smul, mul_inv_cancel₀ hα.ne', one_smul] at this
  -- Euler in the potential direction
  have hxX : ∀ x' : Xs,
      ⟪(w : H), (x' : H)⟫_ℝ - α * ⟪(x : H), (x' : H)⟫_ℝ + α⁻¹ * ⟪r, W (x' : H)⟫_ℝ = 0 := by
    intro x'
    have h0 := fw_euler_zero
      (b := ⟪(w : H), (x' : H)⟫_ℝ - α * ⟪(x : H), (x' : H)⟫_ℝ + α⁻¹ * ⟪r, W (x' : H)⟫_ℝ)
      (c := α * ‖(x' : H)‖ ^ 2 + α⁻¹ * ‖W (x' : H)‖ ^ 2) (by positivity) ?_
    · linarith
    intro t
    have h := hmax (x + t • x') s
    unfold fwPhi at h
    have e1 : ((x + t • x' : Xs) : H) =
        (x : H) + t • (x' : H) := by simp only [Submodule.coe_add, Submodule.coe_smul]
    have e2 : (s : H) - W ((x : H) + t • (x' : H)) =
        r + (-t) • W (x' : H) := by
      rw [map_add, map_smul, hr]; simp only [neg_smul]; abel
    rw [e1, e2, fw_norm_add_smul, fw_norm_add_smul, inner_add_right, inner_smul_right] at h
    have h2 : ((s : H) - W (x : H)) = r := hr.symm
    rw [h2] at h
    nlinarith [h, mul_nonneg hα'.le (sq_nonneg t), mul_nonneg hα.le (sq_nonneg t)]
  -- transfer through the flux projection
  have hAx := hA
  have hyinner : ∀ x' : Xs,
      ⟪r, W (x' : H)⟫_ℝ = ⟪r, A x'⟫_ℝ := by
    intro x'
    rw [hAx, ← Submodule.inner_starProjection_left_eq_right,
      (Submodule.starProjection_eq_self_iff).mpr hrflux]
  have hAdj : ∀ x' : Xs,
      ⟪r, A x'⟫_ℝ = ⟪A.adjoint r, x'⟫_ℝ := by
    intro x'
    rw [ContinuousLinearMap.adjoint_inner_left]
  refine ⟨hyflux, ?_, ?_⟩
  · -- α y + A x = 0
    rw [smul_smul, mul_inv_cancel₀ hα.ne', one_smul]
    have hs0 : Ksᗮ.starProjection (s : H) = 0 := by
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact Ks.le_orthogonal_orthogonal s.2
    have hr1 : Ksᗮ.starProjection r = r := (Submodule.starProjection_eq_self_iff).mpr hrflux
    have : Ksᗮ.starProjection r = - A x := by
      rw [hr, map_sub, hs0, hAx]; simp
    rw [hr1] at this
    rw [this]; abel
  · -- -A* y + α x = w
    have hadjy : A.adjoint (α⁻¹ • r) = α⁻¹ • A.adjoint r := map_smul _ _ _
    rw [hadjy]
    refine ext_inner_right ℝ (fun x' => ?_)
    have h1 := hxX x'
    rw [hyinner, hAdj] at h1
    rw [inner_add_left, inner_neg_left, real_inner_smul_left, real_inner_smul_left]
    have hc1 : ⟪(w : H), (x' : H)⟫_ℝ = ⟪w, x'⟫_ℝ := Submodule.coe_inner Xs w x'
    have hc2 : ⟪(x : H), (x' : H)⟫_ℝ = ⟪x, x'⟫_ℝ := Submodule.coe_inner Xs x x'
    rw [hc1, hc2] at h1
    linarith

end Generic

end

end ASDExplicitGamma.Scalar

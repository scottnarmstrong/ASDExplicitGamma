module

public import ASDExplicitGamma.Cold.GramAlgebra

/-! # The symmetrized response defect controls the full Gram quadratic form -/

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace
namespace ASDExplicitGamma.Cold

/-- The actual symmetrized defect as a Euclidean continuous operator. -/
def gramSymmetrizedDefect {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T R : E →L[ℝ] E) : E →L[ℝ] E := (1/2 : ℝ) • (T + R.comp (T.comp R)) - .id ℝ E

/-- The operator norm controls its actual quadratic form. -/
theorem inner_operator_le_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (x : E) : ⟪x, H x⟫ ≤ ‖H‖ * ⟪x,x⟫ := by
  calc
    _ ≤ |⟪x,H x⟫| := le_abs_self _
    _ ≤ ‖x‖ * ‖H x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖H‖ * ‖x‖) := mul_le_mul_of_nonneg_left (H.le_opNorm x) (norm_nonneg _)
    _ = _ := by rw [real_inner_self_eq_norm_sq]; ring

/-- Inverse/reflection order yields the reciprocal-coercivity upper bound with the actual
symmetrized defect norm, rather than an assumed near-identity estimate. -/
theorem gram_reciprocal_quadratic_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T S R : E →L[ℝ] E)
    (horder : ∀ x, ⟪x, S x⟫ ≤ ⟪x, R (T (R x))⟫) (x : E) :
    ⟪x, T x + S x⟫ ≤ 2*(1+‖gramSymmetrizedDefect T R‖)*⟪x,x⟫ := by
  have h := inner_operator_le_norm_sq (gramSymmetrizedDefect T R) x
  have heq : ⟪x, gramSymmetrizedDefect T R x⟫ =
      (1/2 : ℝ) * (⟪x,T x⟫ + ⟪x,R (T (R x))⟫) - ⟪x,x⟫ := by
    simp only [gramSymmetrizedDefect, sub_apply,
      smul_apply, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      inner_sub_right, inner_smul_right, inner_add_right]
  rw [heq] at h
  rw [inner_add_right]
  linarith only [h, horder x]

/-- The full Gram quadratic bound from the source inverse/reflection order. -/
theorem gram_reflection_quadratic_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T S R : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x,T x⟫)
    (hST : ∀ x, S (T x) = x)
    (horder : ∀ x, ⟪x,S x⟫ ≤ ⟪x,R (T (R x))⟫)
    (hR : ∀ x, ‖R x‖ = ‖x‖) {η : ℝ} (hη : 0 < η) (x : E) :
    ⟪x,T x + R x⟫ ≤
      (2*(1+η) + (2+1/(4*η))*‖gramSymmetrizedDefect T R‖) * ⟪x,x⟫ := by
  have h := gram_operator_quadratic_le T.toLinearMap S.toLinearMap hT hpos hST
    (norm_nonneg _) hη (gram_reciprocal_quadratic_le T S R horder) x
  have hr : ⟪x,R x⟫ ≤ ⟪x,x⟫ := by
    calc
      _ ≤ |⟪x,R x⟫| := le_abs_self _
      _ ≤ ‖x‖ * ‖R x‖ := abs_real_inner_le_norm _ _
      _ = _ := by rw [hR, real_inner_self_eq_norm_sq, pow_two]
  change ⟪x,T x⟫ + ⟪x,x⟫ ≤ _ at h
  rw [inner_add_right]
  linarith only [h, hr]


/-- The two sign inequalities imply the doubled block quadratic inequality. -/
theorem gram_sign_cross_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T R : E →ₗ[ℝ] E) (hR : R.IsSymmetric)
    (hplus : ∀ x, 0 ≤ ⟪x, T x + R x⟫) (hminus : ∀ x, 0 ≤ ⟪x, T x - R x⟫)
    (u v : E) : 0 ≤ ⟪u,T u⟫ + ⟪v,T v⟫ - 2*⟪u,R v⟫ := by
  have hp := hplus (u-v)
  have hm := hminus (u+v)
  simp only [map_sub, map_add, inner_add_left, inner_sub_left, inner_add_right,
    inner_sub_right] at hp hm
  have hr : ⟪v,R u⟫ = ⟪u,R v⟫ := by rw [real_inner_comm, hR]
  rw [hr] at hp hm
  linarith only [hp,hm]

/-- The inverse/reflection inequality is derived from the two sign inequalities. -/
theorem gram_inverse_order_of_sign {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T S R : E →ₗ[ℝ] E) (hR : R.IsSymmetric)
    (hTS : ∀ x, T (S x) = x) (hRR : ∀ x, R (R x) = x)
    (hplus : ∀ x, 0 ≤ ⟪x,T x + R x⟫) (hminus : ∀ x, 0 ≤ ⟪x,T x - R x⟫) (x : E) :
    ⟪x,S x⟫ ≤ ⟪x,R (T (R x))⟫ := by
  have h := gram_sign_cross_nonneg T R hR hplus hminus (S x) (R x)
  rw [hTS, hRR] at h
  have hc : ⟪S x,x⟫ = ⟪x,S x⟫ := real_inner_comm _ _
  have hr : ⟪R x,T (R x)⟫ = ⟪x,R (T (R x))⟫ := hR x _
  rw [hc, hr] at h
  linarith only [h]


/-- The two sign inequalities force strict positivity when the reflection is invertible. -/
theorem gram_positive_of_sign {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T R : E →ₗ[ℝ] E) (hR : R.IsSymmetric) (hRR : ∀ x, R (R x) = x)
    (hplus : ∀ x, 0 ≤ ⟪x,T x + R x⟫) (hminus : ∀ x, 0 ≤ ⟪x,T x - R x⟫)
    (x : E) (hx : x ≠ 0) : 0 < ⟪x,T x⟫ := by
  have hp := hplus x
  have hm := hminus x
  rw [inner_add_right] at hp
  rw [inner_sub_right] at hm
  have hn : 0 ≤ ⟪x,T x⟫ := by linarith only [hp,hm]
  by_contra hbad
  have hz : ⟪x,T x⟫ = 0 := by linarith only [hn,hbad]
  let t := (⟪R x,T (R x)⟫ + 1) / (2*⟪x,x⟫)
  have hc := gram_sign_cross_nonneg T R hR hplus hminus (t • x) (R x)
  simp only [map_smul, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial, hz, hRR, mul_zero] at hc
  have hxx : 0 < ⟪x,x⟫ := real_inner_self_pos.mpr hx
  have heq : 2*t*⟪x,x⟫ = ⟪R x,T (R x)⟫ + 1 := by
    dsimp [t]
    field_simp [hxx.ne']
  nlinarith only [hc,heq]


/-- The actual symmetrized defect is nonnegative from the two source sign inequalities. -/
theorem gramSymmetrizedDefect_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T R : E →L[ℝ] E) (hR : R.toLinearMap.IsSymmetric) (hRR : ∀ x, R (R x) = x)
    (hplus : ∀ x, 0 ≤ ⟪x,T x + R x⟫) (hminus : ∀ x, 0 ≤ ⟪x,T x - R x⟫) (x : E) :
    0 ≤ ⟪x,gramSymmetrizedDefect T R x⟫ := by
  have hp := hplus (x-R x)
  have hm := hminus (x+R x)
  simp only [map_sub,map_add,hRR,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right] at hp hm
  have hn : ⟪R x,R x⟫ = ⟪x,x⟫ := by
    calc
      _ = ⟪x,R (R x)⟫ := hR x (R x)
      _ = _ := by rw [hRR]
  have hr : ⟪R x,T (R x)⟫ = ⟪x,R (T (R x))⟫ := hR x _
  simp only [gramSymmetrizedDefect,sub_apply,smul_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,inner_sub_right,inner_smul_right,inner_add_right]
  rw [hn,hr] at hp hm
  linarith only [hp,hm]

end ASDExplicitGamma.Cold

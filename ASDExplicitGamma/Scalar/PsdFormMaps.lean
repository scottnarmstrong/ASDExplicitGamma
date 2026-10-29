module

public import ASDExplicitGamma.Scalar.PsdWick

/-! Positive-semidefinite forms built from a finite family of linear maps into
inner product spaces. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open scoped BigOperators RealInnerProductSpace

section

variable {P : Type*} [AddCommGroup P] [Module ℝ P]
  {ι : Type*} {H : ι → Type*} [∀ j, NormedAddCommGroup (H j)]
  [∀ j, InnerProductSpace ℝ (H j)]

/-- `a, b ↦ ∑ j ∈ s, w j ⟪Φ j a, Φ j b⟫`. -/
noncomputable def PsdForm.ofMaps (s : Finset ι) (Φ : ∀ j, P →ₗ[ℝ] H j) (w : ι → ℝ)
    (hw : ∀ j, 0 ≤ w j) : PsdForm P where
  form := LinearMap.mk₂ ℝ (fun a b => ∑ j ∈ s, w j * inner ℝ (Φ j a) (Φ j b))
    (by
      intro a b c
      simp only [map_add, inner_add_left, mul_add, Finset.sum_add_distrib])
    (by
      intro r a b
      simp only [map_smul, real_inner_smul_left, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring)
    (by
      intro a b c
      simp only [map_add, inner_add_right, mul_add, Finset.sum_add_distrib])
    (by
      intro r a b
      simp only [map_smul, real_inner_smul_right, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring)
  symm := by
    intro a b
    simp only [LinearMap.mk₂_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm]
  nonneg := by
    intro a
    simp only [LinearMap.mk₂_apply]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hw j) real_inner_self_nonneg

theorem PsdForm.ofMaps_apply_self (s : Finset ι) (Φ : ∀ j, P →ₗ[ℝ] H j) (w : ι → ℝ)
    (hw : ∀ j, 0 ≤ w j) (a : P) :
    (PsdForm.ofMaps s Φ w hw).form a a = ∑ j ∈ s, w j * ‖Φ j a‖ ^ 2 := by
  simp only [PsdForm.ofMaps, LinearMap.mk₂_apply, real_inner_self_eq_norm_sq]

end

end ASDExplicitGamma.Scalar

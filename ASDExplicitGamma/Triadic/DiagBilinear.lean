module

public import ASDExplicitGamma.Triadic.DiagGeometry

/-! Piecewise bilinearity of the tensor-hat interpolant. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization
open scoped BigOperators

noncomputable section

/-- Integer translates of the unit hat are affine on each mesh interval. -/
theorem diagHat_integer_cell (k z : ℤ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    diagHat ((k : ℝ) + t - z) =
      if z = k then 1 - t else if z = k + 1 then t else 0 := by
  by_cases hz : z = k
  · subst z
    rw [ite_eq_left rfl]
    have heq : (k : ℝ) + t - k = t := by ring
    rw [heq]
    exact (diagHat_on_unit ht).1
  · rw [ite_eq_right hz]
    by_cases hz' : z = k + 1
    · subst z
      rw [ite_eq_left rfl]
      rw [Int.cast_add, Int.cast_one]
      have heq : (k : ℝ) + t - (k + 1) = t - 1 := by ring
      rw [heq]
      exact (diagHat_on_unit ht).2
    · rw [ite_eq_right hz']
      apply diagHat_eq_zero
      have hcases : z ≤ k - 1 ∨ k + 2 ≤ z := by omega
      rcases hcases with h | h
      · have h' : (z : ℝ) ≤ (k : ℝ) - 1 := by exact_mod_cast h
        exact (by linarith only [h', ht.1] : 1 ≤ (k : ℝ) + t - z).trans (le_abs_self _)
      · have h' : (k : ℝ) + 2 ≤ (z : ℝ) := by exact_mod_cast h
        exact (by linarith only [h', ht.2] : 1 ≤ -((k : ℝ) + t - z)).trans (neg_le_abs _)

/-- Physical translates of the hat are affine on each physical mesh interval. -/
theorem diagHat_affine_cell (a : ℝ) {r : ℝ} (hr : 0 < r) (k z : ℤ) :
    ∃ A B : ℝ, ∀ x : ℝ, a + k * r ≤ x → x ≤ a + (k + 1) * r →
      diagHat ((x - (a + z * r)) / r) = A + B * x := by
  have h (x : ℝ) (hl : a + k * r ≤ x) (hu : x ≤ a + (k + 1) * r) :
      (x - a) / r - k ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · apply sub_nonneg.mpr
      apply (le_div_iff₀ hr).2
      linarith only [hl]
    · apply (sub_le_iff_le_add).2
      apply (div_le_iff₀ hr).2
      linarith only [hu]
  have heq (x : ℝ) : (x - (a + z * r)) / r =
      (k : ℝ) + ((x - a) / r - k) - z := by field_simp; ring
  by_cases hz : z = k
  · refine ⟨1 + a / r + k, -1 / r, ?_⟩
    intro x hl hu
    rw [heq, diagHat_integer_cell k z (h x hl hu), ite_eq_left hz]
    field_simp
    ring
  · by_cases hz' : z = k + 1
    · refine ⟨-a / r - k, 1 / r, ?_⟩
      intro x hl hu
      rw [heq, diagHat_integer_cell k z (h x hl hu), ite_eq_right hz, ite_eq_left hz']
      field_simp
      ring
    · refine ⟨0, 0, ?_⟩
      intro x hl hu
      rw [heq, diagHat_integer_cell k z (h x hl hu), ite_eq_right hz, ite_eq_right hz']
      ring

/-- Each basis function is bilinear on every mesh cell, including cells
adjacent to the parent boundary. -/
theorem diagPhysicalHat_bilinear_cell (Q : TriadicCube 2) (j : ℕ)
    (z : Fin 2 → Fin (3 ^ j - 1)) (k : Fin 2 → ℤ) :
    ∃ A B C D : ℝ, ∀ x : Vec 2,
      (∀ i, cubeCorner Q i + k i * diagMeshRadius Q j ≤ x i ∧
        x i ≤ cubeCorner Q i + (k i + 1) * diagMeshRadius Q j) →
      diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j) x =
        A + B * x 0 + C * x 1 + D * x 0 * x 1 := by
  obtain ⟨a, b, hab⟩ := diagHat_affine_cell (cubeCorner Q 0) (diagMeshRadius_pos Q j)
    (k 0) ((z 0).val + 1)
  obtain ⟨c, d, hcd⟩ := diagHat_affine_cell (cubeCorner Q 1) (diagMeshRadius_pos Q j)
    (k 1) ((z 1).val + 1)
  refine ⟨a * c, b * c, a * d, b * d, ?_⟩
  intro x hx
  unfold diagPhysicalHat tensorMultiplier
  rw [Fin.prod_univ_two]
  have h0 := hab (x 0) (hx 0).1 (hx 0).2
  have h1 := hcd (x 1) (hx 1).1 (hx 1).2
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one] at h0 h1
  change diagHat ((x 0 - (cubeCorner Q 0 + ((z 0).val + 1) * diagMeshRadius Q j)) /
      diagMeshRadius Q j) *
    diagHat ((x 1 - (cubeCorner Q 1 + ((z 1).val + 1) * diagMeshRadius Q j)) /
      diagMeshRadius Q j) = _
  rw [h0, h1]
  ring

/-- The concrete interpolant is bilinear on every mesh cell. -/
theorem diagInterpolant_bilinear_cell (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (k : Fin 2 → ℤ) :
    ∃ A B C D : ℝ, ∀ x : Vec 2,
      (∀ i, cubeCorner Q i + k i * diagMeshRadius Q j ≤ x i ∧
        x i ≤ cubeCorner Q i + (k i + 1) * diagMeshRadius Q j) →
      (diagInterpolant Q j v).toFun x = A + B * x 0 + C * x 1 + D * x 0 * x 1 := by
  classical
  choose A B C D h using fun z => diagPhysicalHat_bilinear_cell Q j z k
  let b := diagNodalValuesLinear Q j v
  refine ⟨∑ z, b z * A z,
    diagMeanGradientLinear Q v 0 + ∑ z, b z * B z,
    diagMeanGradientLinear Q v 1 + ∑ z, b z * C z, ∑ z, b z * D z, ?_⟩
  intro x hx
  rw [diagInterpolant_toFun, Fin.sum_univ_two]
  simp only [h _ x hx, mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
  dsimp only [b]
  ring

end

end ASDExplicitGamma.Triadic

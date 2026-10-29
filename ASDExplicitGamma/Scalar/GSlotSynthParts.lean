module

public import ASDExplicitGamma.Scalar.GSlotHaar

/-! Tower property and orthogonal summation of Haar increments in `L²(R)`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Filter ASDExplicitGamma.Triadic
open scoped BigOperators Topology InnerProductSpace

noncomputable section

variable (R : TriadicCube 2)

/-- The Haar increment as an operator. -/
abbrev incL (k : ℕ) := cubeIncrementL2CLM R k

/-- Tower property: `inc_j inc_k = [j = k] inc_k`. -/
theorem inc_inc (j k : ℕ) (x : Lp ℝ 2 (normalizedCubeMeasure R)) :
    incL R j (incL R k x) = if k = j then incL R k x else 0 := by
  apply ext_inner_right ℝ
  intro g
  rw [inner_inc_left, inner_inc_inc]
  by_cases h : k = j
  · subst h
    simp only [↓reduceIte]
  · simp [h]

/-- A family of increments with summable squared norms is summable. -/
theorem summable_inc (y : ℕ → Lp ℝ 2 (normalizedCubeMeasure R))
    (h : Summable (fun k => ‖incL R k (y k)‖ ^ 2)) :
    Summable (fun k => incL R k (y k)) := by
  let G : ℕ → Submodule ℝ (Lp ℝ 2 (normalizedCubeMeasure R)) := fun k => LinearMap.range (incL R k).toLinearMap
  have hV : OrthogonalFamily ℝ (fun k => ↥(G k)) (fun k => (G k).subtypeₗᵢ) := by
    intro i j hij a b
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨z, hz⟩ := b.2
    change ⟪(a : Lp ℝ 2 (normalizedCubeMeasure R)), (b : Lp ℝ 2 (normalizedCubeMeasure R))⟫_ℝ = 0
    rw [← hx, ← hz]
    simp only [ContinuousLinearMap.coe_coe]
    rw [inner_inc_inc]
    simp [hij]
  have := (hV.summable_iff_norm_sq_summable (fun k => (⟨incL R k (y k), ⟨y k, rfl⟩⟩ : G k))).2 h
  exact this

/-- The increment `j` of a sum of increments. -/
theorem inc_tsum (y : ℕ → Lp ℝ 2 (normalizedCubeMeasure R))
    (h : Summable (fun k => incL R k (y k))) (j : ℕ) :
    incL R j (∑' k, incL R k (y k)) = incL R j (y j) := by
  have h1 := (h.hasSum).mapL (incL R j)
  have h2 : (fun k => incL R j (incL R k (y k))) = fun k => if k = j then incL R j (y j) else 0 := by
    funext k
    rw [inc_inc]
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [h2] at h1
  have h3 : HasSum (fun k => if k = j then incL R j (y j) else 0) (incL R j (y j)) :=
    hasSum_ite_eq j _
  exact h1.unique h3

theorem norm_inc_le (k : ℕ) (x : Lp ℝ 2 (normalizedCubeMeasure R)) :
    ‖incL R k x‖ ≤ ‖x‖ := by
  have h := inner_inc_inc R k k x x
  simp only [↓reduceIte] at h
  have h2 : ‖incL R k x‖ ^ 2 ≤ ‖incL R k x‖ * ‖x‖ := by
    rw [← real_inner_self_eq_norm_sq, h]
    exact real_inner_le_norm _ _
  by_cases h0 : ‖incL R k x‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hp : 0 < ‖incL R k x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

end

end ASDExplicitGamma.Scalar

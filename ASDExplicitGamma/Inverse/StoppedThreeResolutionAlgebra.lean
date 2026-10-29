module

public import ASDExplicitGamma.Inverse.StoppedMidpointGradient
public import ASDExplicitGamma.Inverse.StoppedDiameterCharge

/-! The sharp planar two-group operator estimate and the literal
three-resolution square payment, with the source coefficient 2700. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
noncomputable section

theorem planar_two_group_operator_square (b : ℕ)
    (A B : Matrix (Fin 2) (Fin 2) ℝ) (z w : ℝ) (hz0 : 0 ≤ z) (hw0 : 0 ≤ w)
    (hz : z ≤ z^2) (hw : w ≤ w^2)
    (hA : ∀ i k, |A i k| ≤ 18*(3:ℝ)^b*z)
    (hB : ∀ i k, |B i k| ≤ 18*(3:ℝ)^b*w) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (1+A+B)‖^2 ≤
      1+planarGradientCharge b*(z^2+w^2) := by
  have ha := planar_euclidean_operator_bound A (18*(3:ℝ)^b*z) (by positivity) hA
  have hb := planar_euclidean_operator_bound B (18*(3:ℝ)^b*w) (by positivity) hB
  have hn : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (1+A+B)‖ ≤
      1+36*(3:ℝ)^b*(z+w) := by
    rw [map_add,map_add,map_one]
    have ht := norm_add_le
      ((1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))+Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) B)
    have ht' := norm_add_le (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A)
    rw [norm_one] at ht'
    linarith only [ht,ht',ha,hb]
  have hs := (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ 1+36*(3:ℝ)^b*(z+w) by positivity)).mpr hn
  exact hs.trans (two_mesh_square_charge b z w hz hw)

/-- The two actually active mesh resolutions inject into the literal source
three-resolution sum; no multiplicity is charged to an unrelated field. -/
theorem planar_three_resolution_operator_square (b : ℕ)
    (A B : Matrix (Fin 2) (Fin 2) ℝ) (Z : Fin 3 → ℝ) (e : Fin 3) (he : e ≠ 0)
    (hZ0 : ∀ r, 0 ≤ Z r) (hZsq : ∀ r, Z r ≤ (Z r)^2)
    (hA : ∀ i k, |A i k| ≤ 18*(3:ℝ)^b*Z 0)
    (hB : ∀ i k, |B i k| ≤ 18*(3:ℝ)^b*Z e) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (1+A+B)‖^2 ≤
      1+planarGradientCharge b*(∑ r, (Z r)^2) := by
  have hh := planar_two_group_operator_square b A B (Z 0) (Z e)
    (hZ0 0) (hZ0 e) (hZsq 0) (hZsq e) hA hB
  have hs : (Z 0)^2+(Z e)^2 ≤ ∑ r, (Z r)^2 := by
    have hsub : ({0,e} : Finset (Fin 3)) ⊆ Finset.univ := Finset.subset_univ _
    have hp := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => sq_nonneg (Z r))
    simpa only [Finset.sum_pair he.symm] using hp
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (show 0 ≤ planarGradientCharge b by unfold planarGradientCharge; positivity)))

end
end ASDExplicitGamma.Inverse

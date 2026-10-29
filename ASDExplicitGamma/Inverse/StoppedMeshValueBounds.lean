module

public import ASDExplicitGamma.Inverse.StoppedMeshHatBounds
public import ASDExplicitGamma.Triadic.DiagInterpolant
public import ASDExplicitGamma.Triadic.PlanarDirectionLinear

/-! Actual tensor-hat synthesis has mass at most one and preserves uniform
nodal bounds, independently of the total number of mesh nodes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Triadic
noncomputable section

private theorem fin_hat_mass (N : ℕ) (s : ℝ) :
    (∑ k : Fin N, diagHat (s-((k.val:ℤ)+1))) ≤ 1 := by
  let f : Fin N → ℤ := fun k => (k.val:ℤ)+1
  have hi : Function.Injective f := by intro a b h; apply Fin.ext; dsimp [f] at h; omega
  have hh := diag_hat_mesh_sum (Finset.univ.image f) s
  rw [Finset.sum_image (fun _ _ _ _ hab => hi hab)] at hh
  simpa only [f,Int.cast_add,Int.cast_natCast,Int.cast_one] using! hh

theorem diag_physical_hat_sum (Q : TriadicCube 2) (j : ℕ) (x : Vec 2) :
    (∑ z : Fin 2 → Fin (3^j-1), diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j) x) ≤ 1 := by
  let r := diagMeshRadius Q j
  let s : Fin 2 → ℝ := fun k => (x k-cubeCorner Q k)/r
  let f : Fin 2 → Fin (3^j-1) → ℝ := fun k z => diagHat (s k-((z.val:ℤ)+1))
  have hr : 0 < r := diagMeshRadius_pos Q j
  have harg (z : Fin 2 → Fin (3^j-1)) (k : Fin 2) :
      (x k-diagInteriorVertex Q j z k)/r = s k-((z k).val+1) := by
    change (x k-(cubeCorner Q k+((z k).val+1)*r))/r = (x k-cubeCorner Q k)/r-((z k).val+1)
    field_simp [hr.ne']
    ring
  have hf (z : Fin 2 → Fin (3^j-1)) :
      diagPhysicalHat (diagInteriorVertex Q j z) r x = ∏ k, f k (z k) := by
    unfold diagPhysicalHat tensorMultiplier
    simp_rw [harg]
    simp only [f,Int.cast_natCast]
  have he : (∑ z : Fin 2 → Fin (3^j-1), diagPhysicalHat (diagInteriorVertex Q j z) r x) =
      ∏ k, ∑ z, f k z := by
    simp_rw [hf]
    exact (Fintype.prod_sum f).symm
  rw [he,Fin.prod_univ_two]
  have h0 := fin_hat_mass (3^j-1) (s 0)
  have h1 := fin_hat_mass (3^j-1) (s 1)
  have h0n : 0 ≤ ∑ z, f 0 z := Finset.sum_nonneg (fun _ _ => diagHat_nonneg _)
  have h1n : 0 ≤ ∑ z, f 1 z := Finset.sum_nonneg (fun _ _ => diagHat_nonneg _)
  exact (mul_le_mul h0 h1 h1n (by norm_num : (0:ℝ) ≤ 1)).trans_eq (mul_one 1)

/-- Every actual finite nodal synthesis has its nodal uniform amplitude
bound, with no node-count or area inflation. -/
theorem diag_synthesis_value_bound (Q : TriadicCube 2) (j : ℕ)
    (b : (Fin 2 → Fin (3^j-1)) → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ z, |b z| ≤ M) (x : Vec 2) :
    |(diagSynthesisH1Linear Q j b).toFun x| ≤ M := by
  rw [diagSynthesisH1Linear_toFun]
  calc
    _ ≤ ∑ z, |b z*diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z, M*diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j) x := by
      apply Finset.sum_le_sum
      intro z _
      have hp : 0 ≤ diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j) x := by
        unfold diagPhysicalHat tensorMultiplier
        exact Finset.prod_nonneg (fun _ _ => diagHat_nonneg _)
      rw [abs_mul,abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_right (hb z) hp
    _ = M*∑ z, diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j) x :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ M*1 := mul_le_mul_of_nonneg_left (diag_physical_hat_sum Q j x) hM
    _ = M := mul_one M

end
end ASDExplicitGamma.Inverse

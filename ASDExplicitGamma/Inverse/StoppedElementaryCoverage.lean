module

public import ASDExplicitGamma.Inverse.StoppedFineBlockMap

/-! Every actual fine parent and its first two generations occur in the
literal buffered observation family. The block grid includes negative sites. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Gaussian
noncomputable section

/-- Every fine parent belongs to the exact buffered block selected by integer
division; no change of lattice origin or observation family is made. -/
theorem buffered_parent_covers (j : ℤ) (x : BlockSite) :
    ∃ i : BufferedParentIndex,
      bufferedParent j (fineBlockIndex x) i = ⟨j,x⟩ := by
  let u : ℕ := (x 0 % (2*3^40)).toNat
  let v : ℕ := (x 1 % (2*3^40)).toNat
  have hu0 := Int.emod_nonneg (x 0) (by norm_num : (2*3^40:ℤ) ≠ 0)
  have hv0 := Int.emod_nonneg (x 1) (by norm_num : (2*3^40:ℤ) ≠ 0)
  have hu : u < 2*3^40 := by
    have hh := Int.emod_lt_of_pos (x 0) (by norm_num : (0:ℤ) < 2*3^40)
    dsimp only [u]
    omega
  have hv : v < 2*3^40 := by
    have hh := Int.emod_lt_of_pos (x 1) (by norm_num : (0:ℤ) < 2*3^40)
    dsimp only [v]
    omega
  have hc : u/3^40+2*(v/3^40) < 4 := by norm_num at hu hv ⊢; omega
  let i : BufferedParentIndex :=
    (⟨u/3^40+2*(v/3^40),hc⟩,
      ⟨u%3^40,Nat.mod_lt _ (by positivity)⟩,
      ⟨v%3^40,Nat.mod_lt _ (by positivity)⟩)
  refine ⟨i,?_⟩
  change (⟨j, (bufferedParent j (fineBlockIndex x) i).index⟩ : TriadicCube 2) = ⟨j,x⟩
  congr 1
  funext d
  have he0 := Int.emod_add_mul_ediv (x 0) (2*3^40)
  have he1 := Int.emod_add_mul_ediv (x 1) (2*3^40)
  have hue : (u:ℤ) = x 0 % (2*3^40) := Int.toNat_of_nonneg hu0
  have hve : (v:ℤ) = x 1 % (2*3^40) := Int.toNat_of_nonneg hv0
  fin_cases d <;>
      simp only [bufferedParent,fineBlockIndex,i,Fin.reduceFinMk,ite_true] <;>
      norm_num at hu hv he0 he1 hue hve ⊢ <;> omega

/-- The elementary family enumerates every actual descendant through depth
two, rather than merely a population with the correct cardinality. -/
theorem elementary_cubes_cover (j : ℤ) (x : BlockSite)
    {r : ℕ} (hr : r ≤ 2) {V : TriadicCube 2}
    (hV : V ∈ descendantsAtDepth (⟨j,x⟩ : TriadicCube 2) r) :
    ∃ i : WavePlanarElementaryIndex, elementaryCube j (fineBlockIndex x) i = V := by
  obtain ⟨a,ha⟩ := buffered_parent_covers j x
  have hV' : V ∈ descendantsAtDepth (bufferedParent j (fineBlockIndex x) a) r := by
    rw [ha]
    exact hV
  let e := descendantEnumeration (bufferedParent j (fineBlockIndex x) a) r
  let z := e ⟨V,hV'⟩
  have hz : (e.symm z).val = V := congrArg Subtype.val (e.symm_apply_apply ⟨V,hV'⟩)
  interval_cases r
  · exact ⟨(a.1,a.2,.inl z),hz⟩
  · exact ⟨(a.1,a.2,.inr (.inl z)),hz⟩
  · exact ⟨(a.1,a.2,.inr (.inr z)),hz⟩

end
end ASDExplicitGamma.Inverse

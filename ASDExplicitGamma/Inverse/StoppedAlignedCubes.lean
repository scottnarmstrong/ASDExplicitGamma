module

public import ASDExplicitGamma.Inverse.StoppedCubeGeodesic
public import Mathlib.Data.Int.DivMod

/-! Exact finite populations and aligned cube observations of planar marked paths. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- All actual sites of a discrete cube; negative cube bases are allowed. -/
def blockCubeSites (a : BlockSite) (side : ℕ) : Finset BlockSite :=
  Finset.univ.image (fun i : Fin 2 → Fin side => fun d => a d+(i d).val)

/-- The finite enumeration has the literal half-open cube carrier. -/
theorem mem_cube_sites (a x : BlockSite) (side : ℕ) :
    x ∈ blockCubeSites a side ↔ x ∈ blockCube a side := by
  constructor
  · intro hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    intro d
    have hi := (i d).isLt
    change a d ≤ a d+(i d).val ∧ a d+(i d).val < a d+(side:ℤ)
    constructor <;> omega
  · intro hx
    let i : Fin 2 → Fin side := fun d => ⟨(x d-a d).toNat,by
      have hd := hx d
      omega⟩
    apply Finset.mem_image.mpr
    refine ⟨i,Finset.mem_univ _,?_⟩
    funext d
    have hd := hx d
    have he := Int.toNat_of_nonneg (show 0 ≤ x d-a d by omega)
    change a d+((x d-a d).toNat:ℤ) = x d
    omega

/-- There is no extra site inflation in a positive-label activation cube. -/
theorem block_cube_sites_card (a : BlockSite) (side : ℕ) :
    (blockCubeSites a side).card = side^2 := by
  have hi : Function.Injective (fun i : Fin 2 → Fin side => fun d => a d+(i d).val) := by
    intro i k hik
    funext d
    apply Fin.ext
    have hd : a d+(i d).val = a d+(k d).val := congrFun hik d
    omega
  rw [blockCubeSites,Finset.card_image_of_injective _ hi]
  simp

/-- Each site has a deterministic aligned cube index. -/
def alignedCubeIndex (side : ℕ) (x : BlockSite) : BlockSite := fun d => x d/(side:ℤ)

/-- The actual physical base of an aligned discrete cube. -/
def alignedCubeBase (side : ℕ) (i : BlockSite) : BlockSite := fun d => (side:ℤ)*i d

/-- Euclidean integer division places every site in its actual aligned cube,
including sites with negative coordinates. -/
theorem mem_own_aligned_cube (side : ℕ) (hs : 0 < side) (x : BlockSite) :
    x ∈ blockCube (alignedCubeBase side (alignedCubeIndex side x)) side := by
  intro d
  have hsZ : (0:ℤ) < side := by exact_mod_cast hs
  have hr := Int.emod_nonneg (x d) hsZ.ne'
  have hl := Int.emod_lt_of_pos (x d) hsZ
  have he := Int.emod_add_mul_ediv (x d) (side:ℤ)
  change (side:ℤ)*(x d/(side:ℤ)) ≤ x d ∧ x d < (side:ℤ)*(x d/(side:ℤ))+(side:ℤ)
  constructor <;> omega

/-- The aligned cube partition identifies every site's unique cube index. -/
theorem aligned_cube_index_iff (side : ℕ) (hs : 0 < side) (x i : BlockSite) :
    alignedCubeIndex side x = i ↔ x ∈ blockCube (alignedCubeBase side i) side := by
  constructor
  · intro he
    rw [← he]
    exact mem_own_aligned_cube side hs x
  · intro hx
    funext d
    have hsZ : (0:ℤ) < side := by exact_mod_cast hs
    apply (Int.ediv_eq_iff_of_pos hsZ).mpr
    simpa only [alignedCubeBase,mul_comm] using! hx d

/-- A finite path visits at most its vertex count distinct aligned cubes at
any fixed label. This finite deterministic population is used before averaging. -/
theorem visited_cube_card_le {I : Type*} [Fintype I]
    (side : ℕ) (v : I → BlockSite) :
    (Finset.univ.image (fun i => alignedCubeIndex side (v i))).card ≤ Fintype.card I :=
  (Finset.card_image_le).trans_eq (Finset.card_univ)

end ASDExplicitGamma.Inverse

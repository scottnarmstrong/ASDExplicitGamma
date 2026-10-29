module

public import ASDExplicitGamma.Inverse.StoppedResidueGeometry
public import ASDExplicitGamma.Inverse.StoppedMarkGroups

/-! Actual finite parity/residue populations for one fixed candidate path. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open scoped BigOperators
noncomputable section

/-- A fixed bijection names the nine genuine planar residue classes. -/
def residueEquiv : (Fin 2 → Fin 3) ≃ Fin 9 := Fintype.equivFinOfCardEq (by decide)

def blockColor (i : BlockSite) : Fin 9 := residueEquiv (blockResidue i)

theorem block_color_eq_iff (i j : BlockSite) :
    blockColor i = blockColor j ↔ blockResidue i = blockResidue j :=
  residueEquiv.injective.eq_iff

/-- Every candidate vertex belongs to one literal parity subpopulation. -/
def localRouteGroup (nv : ℕ) (c : Fin 2) : Finset (Fin nv) :=
  Finset.univ.filter (fun k => k.val%2 = c.val)

/-- Distinct aligned cubes met by the path, restricted to one genuine residue class. -/
def positiveRouteGroup {nv : ℕ} (v : Fin nv → BlockSite) (n : ℕ) (c : Fin 9) : Finset BlockSite :=
  (Finset.univ.image (fun k => alignedCubeIndex (3^(n+1)) (v k))).filter (fun i => blockColor i = c)

/-- The groups retain their actual finite populations, before taking any expectation. -/
abbrev RouteGroupIndex {nv : ℕ} (v : Fin nv → BlockSite) (N : ℕ) : MarkGroup N → Type
  | none => Empty
  | some (.inl c) => localRouteGroup nv c
  | some (.inr p) => positiveRouteGroup v p.1.val p.2

instance routeGroupIndexFintype {nv : ℕ} (v : Fin nv → BlockSite) (N : ℕ) (g : MarkGroup N) :
    Fintype (RouteGroupIndex v N g) := by
  cases g with
  | none => exact inferInstanceAs (Fintype Empty)
  | some g =>
    cases g with
    | inl c => exact inferInstanceAs (Fintype (localRouteGroup nv c))
    | inr p => exact inferInstanceAs (Fintype (positiveRouteGroup v p.1.val p.2))

/-- Both parity and residue populations have at most the path's vertex count. -/
theorem route_group_card_le {nv : ℕ} (v : Fin nv → BlockSite) (N : ℕ) (g : MarkGroup N) :
    Fintype.card (RouteGroupIndex v N g) ≤ nv := by
  cases g with
  | none => change Fintype.card Empty ≤ nv; simp
  | some g =>
    cases g with
    | inl c =>
      change Fintype.card (localRouteGroup nv c) ≤ nv
      rw [Fintype.card_coe]
      exact (Finset.card_filter_le _ _).trans_eq (by simp)
    | inr p =>
      change Fintype.card (positiveRouteGroup v p.1.val p.2) ≤ nv
      rw [Fintype.card_coe]
      exact (Finset.card_filter_le _ _).trans (by
        simpa only [Fintype.card_fin] using visited_cube_card_le (3^(p.1.val+1)) v)

/-- The local group membership pins the actual parity of every observed site. -/
theorem local_route_group_parity {nv : ℕ} (c : Fin 2) (i j : localRouteGroup nv c) :
    i.val.val%2 = j.val.val%2 :=
  (Finset.mem_filter.mp i.property).2.trans (Finset.mem_filter.mp j.property).2.symm

end
end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Inverse.StoppedRouteGroupEvents
public import ASDExplicitGamma.Inverse.StoppedIndependentMarks

/-! The exact local-plus-side-weighted charge, partitioned into its true finite color groups. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open scoped BigOperators
noncomputable section

def routeParity {nv : ℕ} (i : Fin nv) : Fin 2 := ⟨i.val%2,Nat.mod_lt _ (by decide)⟩

/-- The two local groups partition the actual vertex population exactly. -/
theorem local_group_sum (nv : ℕ) (f : Fin nv → ℝ) :
    (∑ c : Fin 2, ∑ i : localRouteGroup nv c, f i.val) = ∑ i, f i := by
  have hg (c : Fin 2) : localRouteGroup nv c =
      Finset.univ.filter (fun i : Fin nv => routeParity i = c) := by
    ext i
    simp only [localRouteGroup,Finset.mem_filter,Finset.mem_univ,true_and,
      Fin.ext_iff,routeParity]
  simp only [hg,Finset.sum_coe_sort]
  exact Finset.sum_fiberwise Finset.univ routeParity f

/-- The nine colors partition exactly the distinct aligned cubes met by a path. -/
theorem positive_group_sum {nv : ℕ} (v : Fin nv → BlockSite) (n : ℕ) (f : BlockSite → ℝ) :
    (∑ c : Fin 9, ∑ i : positiveRouteGroup v n c, f i.val) =
      ∑ i ∈ Finset.univ.image (fun k => alignedCubeIndex (3^(n+1)) (v k)), f i := by
  simp_rw [Finset.sum_coe_sort]
  simpa only [positiveRouteGroup] using!
    Finset.sum_fiberwise (Finset.univ.image (fun k => alignedCubeIndex (3^(n+1)) (v k))) blockColor f

/-- The actual finite marked-path charge; this retains side, not volume, for
positive aligned cubes, as required by shortest occupied path geometry. -/
def routeCharge {Ω : Type*} {nv : ℕ} (B : PlanarMarks Ω)
    (v : Fin nv → BlockSite) (N : ℕ) (ω : Ω) : ℝ :=
  (∑ k, markIndicator (B.localMark (v k)) ω)+
    ∑ n ∈ Finset.range N, (positiveLabelSide n)*
      ∑ i ∈ Finset.univ.image (fun k => alignedCubeIndex (3^(n+1)) (v k)),
        markIndicator (positiveActivation B n i) ω

/-- Grouping by parity and genuine residue classes changes no pathwise charge. -/
theorem route_group_charge_eq {Ω : Type*} {nv : ℕ} (B : PlanarMarks Ω)
    (v : Fin nv → BlockSite) (N : ℕ) (ω : Ω) :
    (∑ g : MarkGroup N, routeGroupCoefficient N g*
      ∑ i : RouteGroupIndex v N g, markIndicator (routeGroupEvent B v N g i) ω) =
      routeCharge B v N ω := by
  simp only [MarkGroup,Fintype.sum_option,Fintype.sum_sum_type,Fintype.sum_prod_type,
    routeGroupCoefficient,routeGroupEvent,RouteGroupIndex,zero_mul,one_mul,zero_add]
  rw [local_group_sum nv (fun k => markIndicator (B.localMark (v k)) ω)]
  unfold routeCharge
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun n => positiveLabelSide n*
    ∑ i ∈ Finset.univ.image (fun k => alignedCubeIndex (3^(n+1)) (v k)),
      markIndicator (positiveActivation B n i) ω) N]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.mul_sum,positive_group_sum v n.val
    (fun i => markIndicator (positiveActivation B n.val i) ω)]

end
end ASDExplicitGamma.Inverse

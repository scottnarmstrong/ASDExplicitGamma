module

public import ASDExplicitGamma.Inverse.StoppedAlignedCubes
public import Mathlib.MeasureTheory.Measure.Real

/-! The actual local marks, aligned positive activations, and occupied planar field. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped BigOperators
noncomputable section

/-- The source's mark data: label zero and each positive raw blocked mark.
No independent-oracle or cluster-tail premise is contained in this structure. -/
structure PlanarMarks (Ω : Type*) where
  localMark : BlockSite → Set Ω
  positiveMark : ℕ → BlockSite → Set Ω

/-- Label n+1 occupies its full aligned cube as soon as one of its raw marks fires. -/
def cubeActivation {Ω : Type*} (E : BlockSite → Set Ω) (a : BlockSite) (side : ℕ) : Set Ω :=
  ⋃ x ∈ blockCubeSites a side, E x

/-- The literal aligned positive activation, with side 3^(n+1). -/
def positiveActivation {Ω : Type*} (B : PlanarMarks Ω) (n : ℕ) (i : BlockSite) : Set Ω :=
  cubeActivation (B.positiveMark n) (alignedCubeBase (3^(n+1)) i) (3^(n+1))

/-- The full occupied field is the union of local sites and completely occupied
active aligned cubes, with no independence asserted across labels. -/
def markedOccupied {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω) : Set BlockSite :=
  {x | ω ∈ B.localMark x ∨ ∃ n i, ω ∈ positiveActivation B n i ∧
    x ∈ blockCube (alignedCubeBase (3^(n+1)) i) (3^(n+1))}

/-- The finite-label observation increases to the full occupied field. -/
def markedOccupiedThrough {Ω : Type*} (B : PlanarMarks Ω) (N : ℕ) (ω : Ω) : Set BlockSite :=
  {x | ω ∈ B.localMark x ∨ ∃ n < N, ∃ i, ω ∈ positiveActivation B n i ∧
    x ∈ blockCube (alignedCubeBase (3^(n+1)) i) (3^(n+1))}

/-- Every active aligned cube really is wholly occupied, supplying the
shortcut hypothesis of the shortest-path visit bound. -/
theorem active_cube_occupied {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    (n : ℕ) (i : BlockSite) (hi : ω ∈ positiveActivation B n i) :
    blockCube (alignedCubeBase (3^(n+1)) i) (3^(n+1)) ⊆ markedOccupied B ω :=
  fun _ hx => Or.inr ⟨n,i,hi,hx⟩

/-- A finite cube union has precisely the source side-squared probability cost. -/
theorem cube_activation_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : BlockSite → Set Ω)
    (a : BlockSite) (side : ℕ) (p : ℝ) (hE : ∀ x, μ.real (E x) ≤ p) :
    μ.real (cubeActivation E a side) ≤ (side:ℝ)^2*p := by
  calc
    _ ≤ ∑ x ∈ blockCubeSites a side, μ.real (E x) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ blockCubeSites a side, p := Finset.sum_le_sum fun x _ => hE x
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,block_cube_sites_card,Nat.cast_pow]

/-- Every full occupied site is already seen at a finite label cutoff. -/
theorem marked_occupied_eq_union {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω) :
    markedOccupied B ω = ⋃ N, markedOccupiedThrough B N ω := by
  ext x
  constructor
  · intro hx
    rcases hx with hlocal | ⟨n,i,hi,hx⟩
    · exact Set.mem_iUnion.mpr ⟨0,Or.inl hlocal⟩
    · exact Set.mem_iUnion.mpr ⟨n+1,Or.inr ⟨n,by omega,i,hi,hx⟩⟩
  · intro hx
    obtain ⟨N,hx⟩ := Set.mem_iUnion.mp hx
    rcases hx with hlocal | ⟨n,_,i,hi,hx⟩
    · exact Or.inl hlocal
    · exact Or.inr ⟨n,i,hi,hx⟩

/-- Truncated occupations increase with the actual observed label cutoff. -/
theorem marked_occupied_through_mono {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω) :
    Monotone (fun N => markedOccupiedThrough B N ω) := by
  intro N M hNM x hx
  rcases hx with hlocal | ⟨n,hn,i,hi,hx⟩
  · exact Or.inl hlocal
  · exact Or.inr ⟨n,lt_of_lt_of_le hn hNM,i,hi,hx⟩

end
end ASDExplicitGamma.Inverse

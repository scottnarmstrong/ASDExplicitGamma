module

public import ASDExplicitGamma.Inverse.ResetChronology
public import Algsuperdiff.Section3.Provider.Whitney.PartitionCovering
public import Homogenization.Geometry.OriginCubeMeasureBridge
public import Homogenization.Geometry.TriadicCubeTranslation

/-! The literal infinite source Whitney partition at the root-relative depths. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3.Provider

/-- Fine subdivision below macro-layer k: ceil(k/3)+H+3. -/
def whitneyProfile (H k : ℕ) : ℕ := (k + 2) / 3 + H + 3

/-- Source layer k, finalized by subdividing exactly the newly interior macro-cubes. -/
noncomputable def bankWhitneyLayer (l : ℤ) (H k : ℕ) : Finset (TriadicCube 2) :=
  Whitney.whitneyLayer l (whitneyProfile H) k

/-- All layers of the source partition; this is the complete countable family. -/
def bankWhitneyPartition (l : ℤ) (H : ℕ) : Set (TriadicCube 2) :=
  Whitney.whitneyPartition l (whitneyProfile H)

theorem whitney_profile_mono (H : ℕ) : Monotone (whitneyProfile H) := by
  intro a b hab
  unfold whitneyProfile
  omega

theorem whitney_profile_step (H k : ℕ) :
    whitneyProfile H k ≤ whitneyProfile H (k + 1) ∧
    whitneyProfile H (k + 1) ≤ whitneyProfile H k + 1 := by
  unfold whitneyProfile
  omega

/-- The fine cube depth is exactly k+ceil(k/3)+H+3, matching reset chronology. -/
theorem whitney_layer_scale (l : ℤ) (H k : ℕ) {Q : TriadicCube 2}
    (hQ : Q ∈ bankWhitneyLayer l H k) : Q.scale = l - resetDepth H k := by
  have hs := Whitney.scale_eq_of_mem_whitneyLayer hQ
  change Q.scale = l - (k : ℤ) - (whitneyProfile H k : ℤ) at hs
  unfold resetDepth whitneyProfile at *
  push_cast at hs
  omega

/-- The literal Whitney family covers the open root exactly. -/
theorem whitney_cover (l : ℤ) (H : ℕ) :
    openCubeSet (originCube 2 l) = ⋃ Q ∈ bankWhitneyPartition l H, cubeSet Q :=
  Whitney.openCubeSet_originCube_eq_iUnion_whitneyPartition l (whitneyProfile H)

theorem whitney_pairwise_disjoint (l : ℤ) (H : ℕ) :
    (bankWhitneyPartition l H).PairwiseDisjoint cubeSet :=
  Whitney.whitneyPartition_pairwiseDisjoint_cubeSet l (whitneyProfile H)

/-- Every finalized source cell lies strictly inside the root. -/
theorem whitney_interior (l : ℤ) (H : ℕ) {Q : TriadicCube 2}
    (hQ : Q ∈ bankWhitneyPartition l H) : cubeSet Q ⊆ openCubeSet (originCube 2 l) :=
  Whitney.cubeSet_subset_openCubeSet_of_mem_whitneyPartition hQ

/-- Every translated triadic root has the same actual partition, shifted by
its physical root translation. -/
theorem whitney_translated_cover (Q : TriadicCube 2) (H : ℕ) :
    openCubeSet Q = ⋃ P ∈ bankWhitneyPartition Q.scale H,
      translateSet (triadicCubeShift Q) (cubeSet P) := by
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube]
  ext x
  simp only [mem_translateSet_iff_sub_mem, Set.mem_iUnion]
  simpa only [Set.mem_iUnion] using
    Set.ext_iff.mp (whitney_cover Q.scale H) (x - triadicCubeShift Q)

/-- Translating the whole source family preserves pairwise disjointness. -/
theorem whitney_translated_disjoint (Q : TriadicCube 2) (H : ℕ) :
    (bankWhitneyPartition Q.scale H).PairwiseDisjoint
      (fun P => translateSet (triadicCubeShift Q) (cubeSet P)) := by
  intro P hP R hR hPR
  apply Set.disjoint_left.mpr
  intro x hxP hxR
  have hp := (mem_translateSet_iff_sub_mem.mp hxP)
  have hr := (mem_translateSet_iff_sub_mem.mp hxR)
  exact Set.disjoint_left.mp (whitney_pairwise_disjoint Q.scale H hP hR hPR) hp hr

end ASDExplicitGamma.Inverse

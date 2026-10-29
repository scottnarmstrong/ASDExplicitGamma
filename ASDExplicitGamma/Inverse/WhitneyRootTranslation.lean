module

public import ASDExplicitGamma.Inverse.WhitneyLayerMass

/-! Actual triadic-cell realization of the source Whitney partition at every root. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory

/-- Translate a finer triadic cube by the physical translation of its root.
The scale restriction is part of the intended source carrier. -/
def rootTranslatedCube (Q : TriadicCube 2) (P : {P : TriadicCube 2 // P.scale ≤ Q.scale}) :
    TriadicCube 2 :=
  translateCube (descendantTranslationShift (Q.scale - P.1.scale).toNat Q.index) P.1

/-- The translated fine cube represents exactly the physical root translation. -/
theorem root_translated_cube_set (Q : TriadicCube 2)
    (P : {P : TriadicCube 2 // P.scale ≤ Q.scale}) :
    cubeSet (rootTranslatedCube Q P) = translateSet (triadicCubeShift Q) (cubeSet P.1) := by
  have hpow : (3 : ℝ) ^ (Q.scale - P.1.scale).toNat * (3 : ℝ) ^ P.1.scale =
      (3 : ℝ) ^ Q.scale := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  have he : (fun i : Fin 2 =>
      ((descendantTranslationShift (Q.scale - P.1.scale).toNat Q.index i : ℤ) : ℝ) *
        cubeScaleFactor P.1) = triadicCubeShift Q := by
    funext i
    simp only [descendantTranslationShift, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
      triadicCubeShift, cubeScaleFactor]
    calc
      _ = (Q.index i : ℝ) * ((3 : ℝ) ^ (Q.scale - P.1.scale).toNat * (3 : ℝ) ^ P.1.scale) := by ring
      _ = _ := by rw [hpow]
  ext x
  change x ∈ cubeSet (translateCube _ P.1) ↔ _
  rw [mem_cubeSet_translateCube_iff, mem_translateSet_iff_sub_mem, he]

/-- Every source Whitney tile has a strictly smaller scale than its root. -/
theorem whitney_scale_le (l : ℤ) (H : ℕ) {P : TriadicCube 2}
    (hP : P ∈ bankWhitneyPartition l H) : P.scale ≤ l := by
  obtain ⟨k, hk⟩ := hP
  have hs := whitney_layer_scale l H k hk
  unfold resetDepth at hs
  omega

/-- The translated source partition consists of actual triadic cubes. -/
def whitneyRootPartition (Q : TriadicCube 2) (H : ℕ) : Set (TriadicCube 2) :=
  {R | ∃ (P : TriadicCube 2) (hP : P ∈ bankWhitneyPartition Q.scale H),
    R = rootTranslatedCube Q ⟨P, whitney_scale_le Q.scale H hP⟩}

/-- Actual triadic cells of the root-relative family cover every translated root. -/
theorem whitney_root_partition_cover (Q : TriadicCube 2) (H : ℕ) :
    openCubeSet Q = ⋃ R ∈ whitneyRootPartition Q H, cubeSet R := by
  rw [whitney_translated_cover Q H]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨P, hP, hx⟩
    refine ⟨rootTranslatedCube Q ⟨P, whitney_scale_le Q.scale H hP⟩,
      ⟨P, hP, rfl⟩, ?_⟩
    rwa [root_translated_cube_set]
  · rintro ⟨R, ⟨P, hP, rfl⟩, hx⟩
    refine ⟨P, hP, ?_⟩
    rwa [root_translated_cube_set] at hx

/-- The actual translated source cells are pairwise disjoint. -/
theorem whitney_root_partition_disjoint (Q : TriadicCube 2) (H : ℕ) :
    (whitneyRootPartition Q H).PairwiseDisjoint cubeSet := by
  rintro R ⟨P, hP, rfl⟩ S ⟨T, hT, rfl⟩ hRS
  change Disjoint (cubeSet (rootTranslatedCube Q ⟨P, _⟩))
    (cubeSet (rootTranslatedCube Q ⟨T, _⟩))
  rw [root_translated_cube_set, root_translated_cube_set]
  apply whitney_translated_disjoint Q H hP hT
  intro hPT
  subst T
  exact hRS rfl

/-- Every translated root retains exactly the same physical layer fractions. -/
theorem whitney_root_layer_volume_fraction (Q : TriadicCube 2) (H n : ℕ) :
    (∑ P ∈ bankWhitneyLayer Q.scale H (n + 1),
      (volume (translateSet (triadicCubeShift Q) (cubeSet P))).toReal) /
        (volume (cubeSet Q)).toReal = bankLayerWeight n := by
  simp_rw [volume_translateSet_eq]
  have hv : (volume (cubeSet Q)).toReal = (volume (cubeSet (originCube 2 Q.scale))).toReal := by
    simp only [volume_cubeSet_toReal, cubeVolume_eq_pow_scale, originCube]
  rw [hv]
  exact whitney_layer_volume_fraction Q.scale H n

end ASDExplicitGamma.Inverse

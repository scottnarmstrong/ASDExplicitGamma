module

public import ASDExplicitGamma.Inverse.ContainedTriangleRootResponse
public import ASDExplicitGamma.Inverse.WhitneyRootLayerGeometry

/-! Exact first-depth indexing and physical weights of translated triangles. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Multiscale
noncomputable section

/-- First-contained cubes remain actual descendants after translating the root. -/
theorem triangle_first_root_descendant (Q : TriadicCube 2) (pi : Equiv.Perm (Fin 2))
    (n : ℕ) {P : TriadicCube 2} (hP : P ∈ triangleFirstCubes Q.scale pi n) :
    rootTranslateCube Q P ∈ descendantsAtDepth Q (n+1) :=
  root_translate_descendant Q (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).1

/-- An open physical triangle has the same area as its canonical half-open
triangle before translation. -/
theorem triangle_root_open_volume (Q : TriadicCube 2) (pi : Equiv.Perm (Fin 2)) :
    volume (Whitney.KuhnCell.mk Q pi).openCarrier =
      volume (Whitney.KuhnCell.mk (originCube 2 Q.scale) pi).carrier := by
  rw [triangle_open_translate,volume_translateSet_eq]
  symm
  apply measure_congr
  apply ae_eq_set.mpr
  exact ⟨volume_carrier_diff_openCarrier _,by
    rw [Set.sdiff_eq_empty.mpr (Whitney.KuhnCell.openCarrier_subset_carrier _),measure_empty]⟩

/-- Translation and removal of cube boundaries preserve the exact volume. -/
theorem root_translate_open_volume (Q P : TriadicCube 2) (hP : P.scale ≤ Q.scale) :
    volume (openCubeSet (rootTranslateCube Q P))=volume (cubeSet P) := by
  change volume (openCubeSet (rootTranslatedCube Q ⟨P,hP⟩))=_
  rw [root_translated_open_cube_set,volume_translateSet_eq]
  exact (measure_congr (cubeSet_ae_eq_openCubeSet P)).symm

/-- The actual translated first-depth layer has normalized mass 2*3^(-n-1). -/
theorem triangle_root_first_weights (Q : TriadicCube 2) (pi : Equiv.Perm (Fin 2)) (n : ℕ) :
    (∑ P ∈ triangleFirstCubes Q.scale pi n,
      (volume (openCubeSet (rootTranslateCube Q P))).toReal /
        (volume (Whitney.KuhnCell.mk Q pi).openCarrier).toReal)=2*(1/3:ℝ)^(n+1) := by
  rw [triangle_root_open_volume]
  have he (P : TriadicCube 2) (hP : P ∈ triangleFirstCubes Q.scale pi n) :
      volume (openCubeSet (rootTranslateCube Q P))=volume (cubeSet P) := by
    have hs := scale_eq_sub_of_mem_descendantsAtDepth
      (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).1
    exact root_translate_open_volume Q P (by change P.scale=Q.scale-(n+1:ℕ) at hs; omega)
  rw [Finset.sum_congr rfl (fun P hP => by rw [he P hP]),← Finset.sum_div]
  exact triangle_first_area_fraction Q.scale pi n

/-- First-depth indexing is equivalent to the full physical cube partition;
depth uniqueness follows from the actual cube scale. -/
def triangleFirstEquiv (l : ℤ) (pi : Equiv.Perm (Fin 2)) :
    (Σ n : ℕ, ↥(triangleFirstCubes l pi n)) ≃ ↥(triangleCubePartition l pi) :=
  Equiv.ofBijective (fun P => ⟨P.2.val,⟨P.1,P.2.property⟩⟩) (by
    constructor
    · intro ⟨n,P⟩ ⟨m,R⟩ he
      have hv : P.val=R.val := congrArg Subtype.val he
      have hn := scale_eq_sub_of_mem_descendantsAtDepth
        (Finset.mem_filter.mp (Finset.mem_filter.mp P.property).1).1
      have hm := scale_eq_sub_of_mem_descendantsAtDepth
        (Finset.mem_filter.mp (Finset.mem_filter.mp R.property).1).1
      have hnm : n=m := by rw [hv] at hn; change R.val.scale=l-(n+1:ℕ) at hn; change R.val.scale=l-(m+1:ℕ) at hm; omega
      subst m
      congr 1
      exact Subtype.ext hv
    · intro ⟨P,hP⟩
      obtain ⟨n,hn⟩ := hP
      exact ⟨⟨n,⟨P,hn⟩⟩,rfl⟩)

end
end ASDExplicitGamma.Inverse

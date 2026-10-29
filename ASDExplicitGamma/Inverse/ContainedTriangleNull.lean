module

public import ASDExplicitGamma.Inverse.ContainedTriangleCover
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The full contained-cube family covers its actual source triangle up to null ties. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3.Provider

/-- Coordinate ties form a proper linear subspace and have zero area. -/
theorem triangle_ties_null (pi : Equiv.Perm (Fin 2)) :
    volume {x : Vec 2 | x (pi 0) = x (pi 1)} = 0 := by
  let L : (Vec 2) →ₗ[ℝ] ℝ := (LinearMap.proj (pi 0) : (Vec 2) →ₗ[ℝ] ℝ) -
    (LinearMap.proj (pi 1) : (Vec 2) →ₗ[ℝ] ℝ)
  have hn : pi 0 ≠ pi 1 := fun he => (by decide : (0 : Fin 2) ≠ 1) (pi.injective he)
  have hproper : L.ker ≠ ⊤ := by
    intro he
    have hm : Pi.single (pi 0) (1 : ℝ) ∈ L.ker := by rw [he]; trivial
    change (Pi.single (pi 0) (1 : ℝ) : Vec 2) (pi 0) - (Pi.single (pi 0) (1 : ℝ) : Vec 2) (pi 1) = 0 at hm
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hn.symm, sub_zero, one_ne_zero] at hm
  have hset : (L.ker : Set (Vec 2)) = {x | x (pi 0) = x (pi 1)} := by
    ext x
    change x (pi 0) - x (pi 1) = 0 ↔ _
    exact sub_eq_zero
  rw [← hset]
  exact Measure.addHaar_submodule volume L.ker hproper

/-- The actual half-open Kuhn triangle is covered by its complete first-contained
cube family outside a null set. No finite-depth cutoff is used. -/
theorem triangle_partition_cover_ae (l : ℤ) (pi : Equiv.Perm (Fin 2)) :
    ({supportCube := originCube 2 l, order := pi} : Whitney.KuhnCell 2).carrier =ᵐ[volume]
      ⋃ R ∈ triangleCubePartition l pi, cubeSet R := by
  have hae : ∀ᵐ x : Vec 2 ∂volume, x (pi 0) ≠ x (pi 1) := by
    apply ae_iff.mpr
    simpa only [not_not] using triangle_ties_null pi
  filter_upwards [hae] with x hne
  apply propext
  constructor
  · intro hx
    have ho := (Tuple.monotone_sort (Whitney.triadicLocalCoordinate (originCube 2 l) x))
      (show (0 : Fin 2) ≤ 1 by decide)
    have hsort := hx.2
    change pi = Tuple.sort (Whitney.triadicLocalCoordinate (originCube 2 l) x) at hsort
    rw [← hsort] at ho
    change Whitney.triadicLocalCoordinate (originCube 2 l) x (pi 0) ≤
      Whitney.triadicLocalCoordinate (originCube 2 l) x (pi 1) at ho
    simp only [Whitney.triadicLocalCoordinate, originCube, Pi.zero_apply, Int.cast_zero,
      zero_mul, sub_zero] at ho
    obtain ⟨n, R, hR, hxR⟩ := triangle_first_cover l pi x hx.1 (lt_of_le_of_ne ho hne)
    exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨⟨n, hR⟩, hxR⟩⟩
  · intro hx
    obtain ⟨R, ⟨n, hR⟩, hxR⟩ := Set.mem_iUnion₂.mp hx
    exact triangle_contained_cube l pi (n + 1) (Finset.mem_filter.mp hR).1 hxR

end ASDExplicitGamma.Inverse

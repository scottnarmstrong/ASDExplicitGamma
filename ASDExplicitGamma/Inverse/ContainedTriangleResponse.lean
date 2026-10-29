module

public import ASDExplicitGamma.Inverse.ContainedTriangleOpen
public import Algsuperdiff.Section3.Provider.Multiscale.SimplexResponseBound

/-! Full-matrix variational comparison on the complete contained-cube dissection. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Homogenization.Book
open Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Multiscale

/-- Each variational cube is contained in its actual triangle domain. -/
theorem triangle_cube_domain_subset (l : ℤ) (pi : Equiv.Perm (Fin 2))
    (R : ↥(triangleCubePartition l pi)) :
    (Ch02.cubeDomain R.1 : Set (Vec 2)) ⊆
      (kuhnCellDomain ⟨originCube 2 l, pi⟩ : Set (Vec 2)) := by
  obtain ⟨n, hR⟩ := R.2
  exact triangle_contained_open_cube l pi (n + 1) (Finset.mem_filter.mp hR).1

end ASDExplicitGamma.Inverse

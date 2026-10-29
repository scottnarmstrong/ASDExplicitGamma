module

public import Homogenization.Geometry.CubeMeasure

/-! The fixed-origin half-open/open cube boundary bridge. -/
@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory

/-- The source cube conventions agree in measure, at the same origin and scale. -/
theorem origin_cube_boundary_adapter (d : ℕ) (k : ℤ) :
    cubeSet (originCube d k) =ᵐ[volume] openCubeSet (originCube d k) ∧
    volume (cubeBoundary (originCube d k)) = 0 ∧
    volume.restrict (cubeSet (originCube d k)) =
      volume.restrict (openCubeSet (originCube d k)) :=
  ⟨cubeSet_ae_eq_openCubeSet _,volume_cubeBoundary_eq_zero _,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet _⟩

end ASDExplicitGamma.Variational

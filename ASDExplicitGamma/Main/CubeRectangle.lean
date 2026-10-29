module

public import ASDExplicitGamma.Gaussian.RectangleDomain
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.NhdsWithin

/-! Exact geometry between the model trace square and the q3 factor rectangle. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian Set

/-- The closed representative of an origin cube is exactly the source
closed rectangle, with the same physical length in both coordinates. -/
theorem main_origin_cube_closure_rectangle (n : ℤ) :
    closure (cubeSet (originCube 2 n)) =
      closedRectangle (-(cubeScaleFactor (originCube 2 n))/2) (cubeScaleFactor (originCube 2 n)/2)
        (-(cubeScaleFactor (originCube 2 n))/2) (cubeScaleFactor (originCube 2 n)/2) := by
  let R := cubeScaleFactor (originCube 2 n)
  have hR : 0 < R := by dsimp [R, cubeScaleFactor]; positivity
  have hc : cubeSet (originCube 2 n) = Set.pi Set.univ (fun _ : Fin 2 => Ico (-R/2) (R/2)) := by
    ext x
    simp [cubeSet, originCube, Set.mem_pi, R, cubeScaleFactor, div_eq_mul_inv, mul_comm]

  rw [hc, closure_pi_set]
  have hne : -R/2 ≠ R/2 := by linarith only [hR]
  simp_rw [closure_Ico hne]
  ext x
  simp only [Set.mem_pi, Set.mem_univ, forall_const, closedRectangle, Set.mem_ofPred_eq]
  exact Fin.forall_fin_two

end ASDExplicitGamma.Main

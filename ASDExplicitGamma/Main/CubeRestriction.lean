module

public import ASDExplicitGamma.Main.CubeRectangle
public import ASDExplicitGamma.Gaussian.ModelHeatResponse

/-! Continuous restrictions on the exact main square. -/

@[expose] public section

namespace ASDExplicitGamma.Main
open Homogenization ASDExplicitGamma.Gaussian MeasureTheory Set
open scoped Topology

noncomputable def mainCubeHalfSide (n : ℤ) : ℝ := cubeScaleFactor (originCube 2 n)/2

/-- Only the identical physical square is reparametrized as a rectangle. -/
noncomputable def mainCubeRestriction (n : ℤ) :
    C(closedRectangle (-mainCubeHalfSide n) (mainCubeHalfSide n)
      (-mainCubeHalfSide n) (mainCubeHalfSide n), ℝ) →L[ℝ]
        C(closure (cubeSet (originCube 2 n)), ℝ) :=
  ContinuousMap.compCLM ℝ ℝ
    ⟨fun x => ⟨x.1, by
      have heq : closure (cubeSet (originCube 2 n)) =
          closedRectangle (-mainCubeHalfSide n) (mainCubeHalfSide n)
            (-mainCubeHalfSide n) (mainCubeHalfSide n) := by
        simpa only [mainCubeHalfSide, neg_div] using main_origin_cube_closure_rectangle n
      exact Eq.mp (congrArg (fun U : Set (Vec 2) => x.1 ∈ U) heq) x.2⟩, by fun_prop⟩

end ASDExplicitGamma.Main

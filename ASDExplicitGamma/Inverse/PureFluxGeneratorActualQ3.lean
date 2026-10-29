module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorSource
public import ASDExplicitGamma.Main.CubeDirections
public import ASDExplicitGamma.Gaussian.GeneratorAlgebra

/-! The four-load Hessian expansion specialized to the actual q3 heat
directions on the main trace cube. -/

@[expose] public section

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open ASDExplicitGamma.Inverse

namespace ASDExplicitGamma.Inverse

/-- The actual coefficient directions from the main cube H3 realization. -/
noncomputable def pureFluxMainCubeQ3Directions (n : ℤ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    ℕ → C(closure (cubeSet (originCube 2 n)), ℝ) :=
  fun j => mainCubeH3Value n b L (mainCubeQ3Directions n b L j)

end ASDExplicitGamma.Inverse

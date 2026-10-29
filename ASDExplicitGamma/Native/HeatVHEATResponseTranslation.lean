module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorOpenBridge
public import ASDExplicitGamma.Native.HeatVHEATSourceHistoryTransport
public import Homogenization.Geometry.TriadicCubeTranslation

/-! Translation covariance of the actual bounded-continuous response field on
triadic observation cubes. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Inverse

/-- The closed observation set follows the same translation as the cube. -/
theorem nativeHeat_cubeSet_translateCube_eq_responseTranslation
    (z : Fin 2 → ℤ) (Q : TriadicCube 2) :
    cubeSet (translateCube z Q) =
      translateSet (nativeHeatCubeTranslationVector z Q) (cubeSet Q) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  rw [mem_cubeSet_translateCube_iff]
  rfl

end ASDExplicitGamma.Native

end

module

public import ASDExplicitGamma.Main.HeatCarrier
public import ASDExplicitGamma.Main.CubeDirections
public import ASDExplicitGamma.Main.HeatIdentity

/-! The main heat identities in the actual spatially regular q3 factor. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3 Set

/-- Both actual OLD-frame heat identities use the physical q3 H3 factor,
whose every direction has the proved W^{2,∞} representative above.
The actual fresh law is supplied internally, with no realization premise. -/
theorem main_actual_q3_heat_identities (n : ℤ) (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m : ℤ) :
    let b := q3ModelAmplitude M h (m+1)
    let L := q3ModelLength (m+1)
    let H := fun j => mainCubeH3Value n b L (mainCubeQ3Directions n b L j)
    mainHeatPanelIdentity (modelTraceHeatAverage n M m)
      (fun t => (1/2:ℝ)*modelHeatTraceAverage (closure (cubeSet (originCube 2 n))) M m
        (modelTraceObservable n M.nu (Annealed.sigmaBar M m : ℝ)) H t) ∧
    mainHeatPanelIdentity (mainInverseHeatAverage n M m)
      (fun t => (1/2:ℝ)*modelHeatTraceAverage (closure (cubeSet (originCube 2 n))) M m
        (mainInverseObservable n M.nu (Annealed.sigmaBar M m : ℝ)) H t) := by
  intro b L H
  let K := closure (cubeSet (originCube 2 n))
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hA := mainCubeQ3Directions_summable n b L
  have hlaw := main_actual_fresh_cube_factor_law n M h hM m
  have htrace := @main_c1On_modelHeatAverage_of_realization (MainCubeH3 n b L)
    inferInstance (mainCubeH3InnerProductSpace n b L) inferInstance inferInstance inferInstance inferInstance
    K inferInstance M ell m hK (mainCubeQ3Directions n b L) hA (mainCubeH3Value n b L) hlaw
    (modelTraceObservable n M.nu (Annealed.sigmaBar M m : ℝ))
    (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu _ M.nu_pos (Annealed.sigmaBar M m).2)
  have hinverse := @main_c1On_modelHeatAverage_of_realization (MainCubeH3 n b L)
    inferInstance (mainCubeH3InnerProductSpace n b L) inferInstance inferInstance inferInstance inferInstance
    K inferInstance M ell m hK (mainCubeQ3Directions n b L) hA (mainCubeH3Value n b L) hlaw
    (mainInverseObservable n M.nu (Annealed.sigmaBar M m : ℝ))
    (mainInverseObservable_hasPolynomiallyBoundedC2Derivatives n M.nu _ M.nu_pos (Annealed.sigmaBar M m).2)
  constructor
  · rw [modelTraceHeatAverage_eq]
    exact mainHeatPanelIdentity_of_C1 htrace.2.1 htrace.2.2.1 htrace.2.2.2
  · rw [mainInverseHeatAverage_eq]
    exact mainHeatPanelIdentity_of_C1 hinverse.2.1 hinverse.2.2.1 hinverse.2.2.2

end ASDExplicitGamma.Main

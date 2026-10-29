module

public import ASDExplicitGamma.Triadic.DiagEstimates

/-! MA-INTERPOLANT-CONTRACTION for the actual source DIAG interpolant. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

local instance mainInterpolantFiniteMeasure (Q : TriadicCube 2) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Squared form of the same actual interpolant comparison. -/
theorem main_interpolant_energy_contraction (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) :
    let w := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    lemmaVTiledPositiveEnergy Q j (diagInterpolant Q j w).grad ≤
      lemmaVTiledWeakEnergy Q j w.grad :=
  diagInterpolant_gradient_energy_le Q j p u

end ASDExplicitGamma.Main

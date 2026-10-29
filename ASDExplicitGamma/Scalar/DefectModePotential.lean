module

public import ASDExplicitGamma.Scalar.ChaosDefectEnvelope
public import ASDExplicitGamma.Scalar.DefectPotentialMap
public import ASDExplicitGamma.Scalar.DefectEnergyHilbert

/-! The zero-trace first potential of a first-response defect mode as a measurable function of
the OLD coefficient: `P (first block of the mode)` for the continuous potential map `P`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Variational

noncomputable section

/-- A chosen continuous potential map (left inverse of the gradient). -/
def potMap (Q : TriadicCube 2) :
    HilbertVectorL2 (openCubeSet Q) →L[ℝ] H10GraphClosedSpace (openCubeSet Q) :=
  Classical.choose (exists_potential_map Q)

theorem potMap_spec (Q : TriadicCube 2) (z : H10GraphClosedSpace (openCubeSet Q)) :
    potMap Q (H10GraphClosed.gradientCLM z) = z :=
  Classical.choose_spec (exists_potential_map Q) z

end

end ASDExplicitGamma.Scalar

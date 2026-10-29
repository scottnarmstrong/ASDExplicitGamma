module

public import ASDExplicitGamma.Scalar.OldCutoffCoefficient
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! The actual complementary weighted projection for arbitrary source fields. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory

/-- The genuine doubled-energy realization in the fixed physical frame. -/
noncomputable def scalarFrameRealization (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    MuHilbertRealization (openCubeSet Q) (responseFramePlanarCoefficientField ν σ k) := by
  letI finiteScalarProjectionVolume : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hv : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  exact (responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q) hv ν σ hν hσ k).toMuHilbertRealization

/-- The actual coercive source energy installed as a Hilbert inner product. -/
noncomputable def scalarFrameEnergyData (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) : EnergyHilbertData (H := HilbertBlockL2 (openCubeSet Q)) :=
  responseEnergyHilbertData (scalarFrameRealization Q ν σ hν hσ k)

/-- The genuine closed zero-trace/zero-normal-trace correction space in the weighted Hilbert carrier. -/
noncomputable def scalarFrameVariationSpace (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    ClosedSubmodule ℝ (EnergyCarrier (scalarFrameEnergyData Q ν σ hν hσ k)) :=
  responseEnergyCorrectionSpace (scalarFrameRealization Q ν σ hν hσ k) (scalarFrameEnergyData Q ν σ hν hσ k)

/-- The literal source complementary projection Q_a F = F - Pi_V^A F. -/
noncomputable def scalarProjectionResidual (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (F : HilbertBlockL2 (openCubeSet Q)) :
    HilbertBlockL2 (openCubeSet Q) :=
  let D := scalarFrameEnergyData Q ν σ hν hσ k
  let K := scalarFrameVariationSpace Q ν σ hν hσ k
  (responseEnergyUp D F-K.toSubmodule.starProjection (responseEnergyUp D F)).down

end ASDExplicitGamma.Scalar

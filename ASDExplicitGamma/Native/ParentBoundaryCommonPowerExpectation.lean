module

public import ASDExplicitGamma.Native.ParentBoundaryCommonTraceMoments
public import ASDExplicitGamma.Native.ParentBoundaryCommonDirectionRepresentation
public import ASDExplicitGamma.Native.ParentBoundaryCommonTraceGenerator
public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeGauge
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandBank
public import ASDExplicitGamma.Native.ParentBoundaryBandRegular
public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeFrame
public import ASDExplicitGamma.Inverse.PureFluxGeneratorRowSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTiledProjected
public import ASDExplicitGamma.Inverse.PureFluxFeedbackCoefficient
public import ASDExplicitGamma.Gaussian.CovarianceRow
public import ASDExplicitGamma.Gaussian.ModelHeatPower
public import ASDExplicitGamma.Native.ParentBoundaryRareMixedHolder

/-! Actual root-compatible correlated expectation of each common-center shell generator. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Literal physical shell coefficient in the common-center p20 drift. -/
def parentBoundaryCommonShellCoefficient (M : ABKModel 2) (h : ℝ)
    (P Q : TriadicCube 2) (n : ℤ) (height : ℕ) (i : Fin height) : ℝ :=
  let J := n+((i.val+1:ℕ):ℤ)
  let σ : ℝ := Annealed.sigmaBar M n
  let b := q3ModelAmplitude M h J
  let L := q3ModelLength J
  let A := parentBoundaryCommonRowCoefficient P Q b L 0
  let κ := lemmaVH2Bn (cubeScaleFactor P/L.val) (diagMeshRadius Q 0/L.val)
  σ⁻¹^2*(σ/(Annealed.sigmaBar M Q.scale:ℝ))^2*((232/125:ℝ)*A^2+38*b^2*κ^2)

end
end ASDExplicitGamma.Native

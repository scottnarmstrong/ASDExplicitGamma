module

public import ASDExplicitGamma.Native.ParentBoundaryBandLocalProxy
public import ASDExplicitGamma.Native.OldSignedPureSecondPairing
public import ASDExplicitGamma.Native.OldSignedAffineIdentification
public import ASDExplicitGamma.Native.OldSignedFlatCellBounds
public import ASDExplicitGamma.Native.OldSignedLoadSeriesBudget
public import ASDExplicitGamma.Native.OldSignedAffineContribution
public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport
public import ASDExplicitGamma.Native.OldSignedFlatDirectionalProxy
public import ASDExplicitGamma.Native.ParentBoundaryBandHistoryStationarity
public import ASDExplicitGamma.Native.OldSignedFlatJointL2

/-! The complete spatial, covariance and probability direct sum for the
actual parent source, retaining the flat two-family Hodge gain. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- The actual signed affine proxies on the whole comparison tiling. -/
def parentBoundaryBandJointSpatialProxy (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (omega : Cutoff.CutoffSample 2) : ℝ :=
  descendantsAverage (originCube 2 n) r (fun U =>
    oldSignedFlatDirectionalMeanProxy (originCube 2 n) U
      (parentBoundaryBandFrameField M n height t omega) b L true+
    oldSignedFlatDirectionalMeanProxy (originCube 2 n) U
      (parentBoundaryBandFrameField M n height t omega) b L false)

end
end ASDExplicitGamma.Native

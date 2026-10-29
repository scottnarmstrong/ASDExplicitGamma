module

public import ASDExplicitGamma.Native.ParentBoundaryBandAffineUpper
public import ASDExplicitGamma.Native.ParentBoundaryBandEnergy

/-! The complete finite-shell affine bill on the actual simultaneous law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

/-- Literal complete affine term for all fresh physical shells. -/
def parentBoundaryBandAffineBill (M : ABKModel 2) (h : ℝ) (n : ℤ) (height depth : ℕ)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) : ℝ :=
  ∑ i : Fin height,oldSignedFlatAffineContribution (originCube 2 n) depth
    (parentBoundaryBandFrameField M n height t omega)
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
    (q3ModelLength (n+((i.val+1:ℕ):ℤ)))

/-- Actual sum of the shell derivative variances in the starting frame. -/
def parentBoundaryBandDerivativeVariance (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ) : ℝ :=
  ∑ i : Fin height,mainFlatSigmaSq
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
    (q3ModelLength (n+((i.val+1:ℕ):ℤ)))

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Main.EOscillationFlatOscillationCaps
public import ASDExplicitGamma.Native.OldSignedCenteredPositive
public import ASDExplicitGamma.Native.ParentBoundaryChargeProxy
public import ASDExplicitGamma.Native.OldSignedErrorProfiles
public import ASDExplicitGamma.Variational.LemmaVTiles

/-! The exact joint oscillation profile in the native OLD source bill, with
the descendant average paired against its actual OLD source amplitude. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
open scoped BigOperators

noncomputable section

/-- The oscillation factor in the native joint mixed-feedback source bill. -/
def mainOldJointOscillationProfile
    (Q U : TriadicCube 2) (ν σ : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) : ℝ :=
  let a := responseFramePlanarCoefficientField ν σ k
  Real.sqrt
    ((oldSignedInverseHistory U a + 1) ^ 2 *
        oldSignedFlatOscillationSize Q U b L true ^ 2 +
      oldSignedInverseHistory U a * oldSignedResponseHistory U a *
        oldSignedFlatOscillationSize Q U b L false ^ 2)

end
end ASDExplicitGamma.Main

module

public import ASDExplicitGamma.Native.OldSignedTrialFields
public import ASDExplicitGamma.Native.OldSignedQ3SourceEnergy
public import ASDExplicitGamma.Native.OldSignedFlatProfiles

/-! The actual four-load OLD error profiles V_U,G_U,d_U used by AN (5.1).
All gradients remain those of the parent physical minimizers. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- Joint weak size of all four parent first-gradient errors on this cell. -/
def oldSignedPrimalErrorSize (Q U : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) : ℝ :=
  Real.sqrt (∑ a : BlockCoord 2,vectorWeakHaarNorm U (fun x =>
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis a) x).1-(blockBasis a).1)^2)

/-- Joint weak size of the same four parent reciprocal-gradient errors.
No affine or cell solution replaces the actual parent minimizer. -/
def oldSignedReciprocalErrorSize (Q U : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) : ℝ :=
  Real.sqrt (∑ a : BlockCoord 2,vectorWeakHaarNorm U (fun x =>
    (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis a) x)).2-(blockBasis a).2)^2)

/-- Complete positive size of the actual localized OLD-error source for
all four parent loads, with its literal uncentered fresh multiplier. -/
def oldSignedOldSourceSize (Q U : TriadicCube 2) (mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  Real.sqrt (∑' n : whiteBasisIndex,∑ a : BlockCoord 2,vectorPositiveHaarNorm U
    (fun x => (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n (blockBasis a) x).2)^2)

/-- The complete actual d_U budget is genuinely summable on every chosen
DIAG cell. Source data supply convergence rather than assuming it. -/
theorem old_signed_old_source_budget_series (m : ℤ) (mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) mesh) :
    Summable (fun n : whiteBasisIndex => ∑ a : BlockCoord 2,vectorPositiveHaarNorm U
      (fun x => (oldSignedFrameOldErrorSource (originCube 2 m) mesh nu sigma hnu hsigma k b L n (blockBasis a) x).2)^2) := by
  apply summable_sum
  intro a _
  exact old_signed_old_error_source_cell_energy_summable m mesh
    (responseFramePlanarCoefficientField nu sigma k)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet (originCube 2 m))
      nu sigma hnu hsigma k) (blockBasis a) b L U hU

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.HeatInitialRefinedAssemblyGen
public import ASDExplicitGamma.Native.HeatInitialRefinedGaussianGen
public import ASDExplicitGamma.Native.HeatInitialRefinedCrossGen
public import ASDExplicitGamma.Native.HeatInitialRefinedRareGen

/-! The premise-free refined initial heat moment row for `ns` shells, relative to the
numeric certificates of the configured row: the proofs of the Gaussian center
quadratic, shear cross and depth-four rare quadratic are instantiated in the
Hölder/root-sum assembly. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native

/-- NA-INITIAL-HEAT-MOMENTS, refined, for `ns` inserted shells and any Gaussian-series
realization `Ffam` of them: at the carrier's source start every moment row through
degree twenty is bounded by the configured `initial` row built from
`nativeHeatVariance ns` and its Gaussian moment list. -/
theorem nativeHeatQ3RefinedCarrierSourceInitialMoment_of_numerics_Gen
    (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns)
    (hstate : nativeInductionState M h (m + 1))
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (k : ℕ) (hk20 : k ≤ 20) :
    nativeHeatQ3RefinedCarrierSourceMomentGen M m ns Ffam k (nativeHeatTheta : ℝ) 0 ≤
      ((nativeHeatInitialAt nativeHeatParametersData (nativeHeatGenQm ns)
        (nativeHeatGenVariance ns) k : ℚ) : ℝ) :=
  nativeHeatQ3RefinedCarrierSourceInitialMoment_le_009_of_providers_Gen ns hnum
    M h hM hg m Ffam hpast
    (fun j hj1 hj20 =>
      nativeHeatQ3RefinedCarrierSourceCenterQuadraticMoment_le_009_Gen ns hnum
        M h hM hg m hstate j hj1 hj20)
    (fun j hj2 hj20 =>
      nativeHeatQ3RefinedCarrierSourceShearCrossMoment_le_009_Gen ns hnum
        M h hM m hg hstate hpast j hj2 hj20)
    (fun j hj1 hj20 =>
      nativeHeatQ3RefinedCarrierSourceRareQuadraticMoment_le_009_depth4_Gen ns hnum
        M h hM m hg hstate hpast j hj1 hj20)
    k hk20

end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.HeatVHEATRefinedCarrier
public import ASDExplicitGamma.Native.HeatVHEATRefinedStart
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrier
public import ASDExplicitGamma.Native.HeatInitialProduct
public import ASDExplicitGamma.Native.HeatInitialCrossRow
public import ASDExplicitGamma.Native.HeatInitialMoments
public import ASDExplicitGamma.Native.HeatFiniteBandCenters
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.Heat009Initial
public import ASDExplicitGamma.Native.HeatInitialDescendants
public import ASDExplicitGamma.Gaussian.NormalEvenMoments
public import ASDExplicitGamma.Numerics.Native.Heat

/-! The source-normalized fresh vector and its three refined child averages. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational
open ASDExplicitGamma.Numerics.Native
open scoped BigOperators

/-- The actual fresh-band value at each depth-ten child center. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceFreshRaw
    (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    nativeHeatQ3RefinedCarrierIndex → ℝ :=
  nativeHeatQ3RefinedCarrierSourceCenterMap m
    (modelBand (nativeHeatQ3RefinedCarrierDomain m)
      (nativeHeatQ3RefinedCarrierPhysicalShells m) ω)

/-- The source-inflated fresh center, normalized in the true frame
`sigmaBar(m+1)`. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceZ
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    nativeHeatQ3RefinedCarrierIndex → ℝ :=
  fun i => (Real.sqrt (1 + (nativeHeatTheta : ℝ)) *
      nativeHeatQ3RefinedCarrierSourceFreshRaw m ω i) /
    (Annealed.sigmaBar M (m + 1) : ℝ)

/-- The finite-grid source center quadratic. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceCenterQuadratic
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
    ∑ i : nativeHeatQ3RefinedCarrierIndex,
      (nativeHeatQ3RefinedCarrierSourceZ M m ω i) ^ 2

/-- The source shear cross term, averaged over the actual depth-ten children. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceShearCross
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  2 * ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
    ∑ i : nativeHeatQ3RefinedCarrierIndex,
      nativeHeatQ3RefinedCarrierSourceZ M m ω i *
        Variational.shearTraceLinear
          (coarseBlockMatrix
            (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
            (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun))

end ASDExplicitGamma.Native

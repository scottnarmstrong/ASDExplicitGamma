module

public import ASDExplicitGamma.Native.HeatVHEATRefinedVectorD4
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen

/-! The `ns`-shell source-normalized fresh vector and its refined child averages. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational
open ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Inverse
open scoped BigOperators


/-- The actual fresh-band value at each depth-ten child center. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceFreshRawGen (ns : ℕ)
    (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    nativeHeatQ3RefinedCarrierIndex → ℝ :=
  nativeHeatQ3RefinedCarrierSourceCenterMap m
    (modelBand (nativeHeatQ3RefinedCarrierDomain m)
      (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) ω)

/-- The source-inflated fresh center, normalized in the true frame
`sigmaBar(m+1)`. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceZGen (ns : ℕ)
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    nativeHeatQ3RefinedCarrierIndex → ℝ :=
  fun i => (Real.sqrt (1 + (nativeHeatTheta : ℝ)) *
      nativeHeatQ3RefinedCarrierSourceFreshRawGen ns m ω i) /
    (Annealed.sigmaBar M (m + 1) : ℝ)

/-- The finite-grid source center quadratic. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen (ns : ℕ)
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
    ∑ i : nativeHeatQ3RefinedCarrierIndex,
      (nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i) ^ 2

/-- The source shear cross term, averaged over the actual depth-ten children. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceShearCrossGen (ns : ℕ)
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  2 * ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
    ∑ i : nativeHeatQ3RefinedCarrierIndex,
      nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i *
        Variational.shearTraceLinear
          (coarseBlockMatrix
            (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
            (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun))

/-- The refined source rare quadratic term with the depth-four remainder. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen (ns : ℕ)
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  2 * ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
    ∑ i : nativeHeatQ3RefinedCarrierIndex,
      nativeHeatOldInverseRemainderD4 M
        (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω *
          (nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i) ^ 2)

end ASDExplicitGamma.Native

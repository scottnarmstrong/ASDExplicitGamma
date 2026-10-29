module

public import ASDExplicitGamma.Native.HeatVHEATRefinedVector

/-! The depth-four local-root OLD remainder at the refined cutoff `m + 1`:
the child has scale `m`, so its depth-four local roots have scale spread five
with respect to the cutoff, inside the local inverse bank. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Inverse

/-- The positive-truncation remainder of the depth-four local root bank. -/
noncomputable def nativeHeatOldInverseRemainderD4 (M : ABKModel 2)
    (Q : TriadicCube 2) (n : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  inverseBankPopulationRemainder .localInverse (bankLocalRoots Q 4) M n (n + 1)
    (fun _ => 0) ω

/-- The refined source rare quadratic term with the depth-four remainder. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceRareQuadraticD4
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  2 * ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
    ∑ i : nativeHeatQ3RefinedCarrierIndex,
      nativeHeatOldInverseRemainderD4 M
        (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω *
          (nativeHeatQ3RefinedCarrierSourceZ M m ω i) ^ 2)

end ASDExplicitGamma.Native

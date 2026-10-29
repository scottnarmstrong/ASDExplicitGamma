module

public import ASDExplicitGamma.Native.ParentBoundaryHistoryGauge
public import ASDExplicitGamma.Native.GenericSourceBandInverse
public import ASDExplicitGamma.Native.HeatVHEATNumericAdapter
public import ASDExplicitGamma.Numerics.Native.Heat011Passes
public import ASDExplicitGamma.Numerics.Native.Gap012Certificate
public import ASDExplicitGamma.Numerics.Native.Heat009Passes
public import ASDExplicitGamma.Numerics.Native.Gap010Certificate
public import ASDExplicitGamma.Numerics.Native.Systems
public import ASDExplicitGamma.Native.GenericSourceBandBank
public import ASDExplicitGamma.Native.GenericSourceBankAdapter
public import Mathlib.MeasureTheory.Measure.Prod

/-! The actual OLD rare bank on cutoff law times auxiliary Gaussian law.
No independence between the physical trace and its reciprocal history is
introduced when the original remainder is lifted to this probability space. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Triadic
open Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The enlarged probability space of the backward heat test. -/
def nativeHeatRemainderJointLaw (M : ABKModel 2) :
    Measure (Cutoff.CutoffSample 2 × (ℕ → ℝ)) :=
  (Cutoff.cutoffSampleLaw M).toMeasure.prod standardGaussianInfinitePi

end
end ASDExplicitGamma.Native

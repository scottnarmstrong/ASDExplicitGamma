module

public import ASDExplicitGamma.Inverse.BankLpArithmetic
public import ASDExplicitGamma.Inverse.BankResponseMeasurable
public import ASDExplicitGamma.Inverse.FixedSelectedHeight
public import ASDExplicitGamma.Inverse.PositivePopulation

/-! The root and fixed-height interfaces give moment bounds for each literal
attenuated inverse response. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal

noncomputable def bankFiniteRootResponseMax (s : Finset (TriadicCube 2))
    (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  historyFiniteMax (Finset.univ : Finset ↥s) (fun Q ω =>
    ENNReal.ofReal (rootInverseResponse M Q.1 m J weights ω)) ω

end ASDExplicitGamma.Inverse

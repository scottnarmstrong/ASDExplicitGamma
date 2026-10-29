module

public import ASDExplicitGamma.Scalar.FlatSourceQ3PositiveHaar
public import ASDExplicitGamma.Scalar.FlatSourceFiniteChaos
public import ASDExplicitGamma.Scalar.ChaosHilbertSymmetrization
public import ASDExplicitGamma.Scalar.FlatSourceC1Multiplier
public import ASDExplicitGamma.Main.CMRegularity
public import ASDExplicitGamma.Gaussian.Q3SobolevOperator
public import ASDExplicitGamma.Gaussian.Q3ModelH3Realization

/-! Transfer the fixed physical flat-source moment bound to the actual shell
law on the completed cutoff carrier. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization Filter
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal Topology

namespace ASDExplicitGamma.Scalar

/-- The fixed physical Wick representative on a parent cube: the actual q3
shell scalar multiplied by its actual Dirichlet projected-load field. -/
noncomputable def flatSourceQ3ActualWickRepresentative
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀) (e : Vec 2) (k : ℤ)
    (ω : Cutoff.CutoffSample 2) : HilbertVectorL2 (openCubeSet Q) :=
  flatSourceQ3ShellProduct Q hab hcd e
    (shellFieldScalarRestriction (closedRectangle a₀ b₀ c₀ d₀) (ω.1 k))

end ASDExplicitGamma.Scalar

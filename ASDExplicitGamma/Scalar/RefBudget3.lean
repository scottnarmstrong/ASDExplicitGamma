module

public import ASDExplicitGamma.Scalar.RefBudget2

/-! The hΛ1 budget of the corrected defect (conditional on the forced-part interface). -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators ENNReal

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

section Budget

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

end Budget

end

end ASDExplicitGamma.Scalar

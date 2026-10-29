module

public import ASDExplicitGamma.Scalar.RefFinalAux

/-! Successor of the physical defect fourth-moment theorem for the corrected reference. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

noncomputable section

section Final

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

end Final

end

end ASDExplicitGamma.Scalar

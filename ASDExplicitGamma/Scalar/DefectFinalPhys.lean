module

public import ASDExplicitGamma.Scalar.DefectFinalAux
public import ASDExplicitGamma.Scalar.DefectHolder
public import ASDExplicitGamma.Scalar.DefectShellCoupling
public import ASDExplicitGamma.Scalar.DefectFinal2

/-! The physical defect fourth moment of the literal NEW resolvent. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

noncomputable section

/-- Closure of the response square lies in the source rectangle. -/
theorem hQcl' {a b c d : ℝ} (hab : a < b) (hcd : c < d) (Q : TriadicCube 2)
    (hQ : openCubeSet Q ⊆ openRectangle a b c d) :
    closure (openCubeSet Q) ⊆ closedRectangle a b c d := by
  rw [← rectangle_closure a b c d hab hcd]
  exact closure_mono hQ

/-- The typing data of the defect source at label `m`. -/
def finalCfg (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2) :
    Cfg'' :=
  Cfg''.ofModel (m + 129) hab hcd (hQcl' hab hcd _ hQ) M h m e

section Final

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

end Final

end

end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Scalar.DefectActual
public import ASDExplicitGamma.Scalar.DefectKappa
public import ASDExplicitGamma.Scalar.DefectWeakCont
public import ASDExplicitGamma.Scalar.GSlotMeas2
public import ASDExplicitGamma.Scalar.DefectLimit

/-! Wick bounds, budgets and measurability for the final assembly. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse
open scoped InnerProductSpace BigOperators

noncomputable section

/-- The mesh radius at depth 134 of `Q_{m+129}` is at most `L/3^6` for the shell length
`L = 3^(m+1)`. -/
theorem mesh' (m : ℤ) :
    diagMeshRadius (originCube 2 (m + 129)) 134 ≤ (q3ModelLength (m + 1)).1 / 729 := by
  unfold diagMeshRadius
  have h1 : cubeScaleFactor (originCube 2 (m + 129)) = (3 : ℝ) ^ (m + 129) := by
    simp [cubeScaleFactor, originCube]
  rw [h1]
  change (3 : ℝ) ^ (m + 129) / (3 : ℝ) ^ 134 ≤ (3 : ℝ) ^ (m + 1) / 729
  have h2 : (3 : ℝ) ^ (m + 129) = (3 : ℝ) ^ (m + 1) * (3 : ℝ) ^ (128 : ℤ) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; congr 1; ring
  rw [h2]
  have hp : (0 : ℝ) < (3 : ℝ) ^ (m + 1) := zpow_pos (by norm_num) _
  rw [mul_div_assoc]
  refine le_of_eq ?_
  congr 1
  norm_num

theorem eOpt_inj_fin (n : ℕ) :
    ∀ i j : Fin n, ∀ l, eOpt i = some l → eOpt j = some l → i = j :=
  fun i j l hi hj => Fin.ext (eOpt_inj i j l hi hj)

namespace Cfg''

variable (C : Cfg'')

end Cfg''

namespace Cfg''

variable (C : Cfg'')

end Cfg''

end

end ASDExplicitGamma.Scalar

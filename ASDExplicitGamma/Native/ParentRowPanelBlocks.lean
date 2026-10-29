module

public import ASDExplicitGamma.Native.ParentRowGeneratorExpectation
public import ASDExplicitGamma.Native.ParentRowHistoryPanel
public import ASDExplicitGamma.Numerics.Native.PanelReadable

/-! Exact readable blocks of the certified parent panel, with both boundary signs. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Main Triadic Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- The stored weak allowance, before any stochastic scaling. -/
def parentRowPanelWeak (j : Fin 16) (t : ℝ) : ℝ :=
  (parentRowFields j).getD 15 0+(parentRowFields j).getD 12 0*t

/-- The exact readable four-block panel error. The derivative contribution
is collected algebraically to keep the finite-shell comparison explicit. -/
def parentRowPanelError (j : Fin 16) (t : ℝ) : ℝ :=
  let f := fun k => (parentRowFields j).getD k 0
  let X := parentRowPanelWeak j t
  let H := parentRowPanelHistory j t
  let A := 1+2*H+Real.sqrt (2*H)
  let D := 1+inverseHistoryDiscount
  let B := (3683/2500:ℝ)
  let c := Real.sqrt (B*A)+1
  let R := Real.sqrt ((B+1)^2*(f 4)^2+B*A*(f 5)^2)
  let flat := Real.sqrt 2*Real.sqrt X*f 8*f 4+2*Real.sqrt 2*Real.sqrt (D*A*H)*f 9*f 5+B*(f 4)^2+A*(f 5)^2
  let source := (f 2)^2*(B*X)+2*f 2*(X*Real.sqrt (f 0))+2*f 2*(Real.sqrt X*R)
  let deriv := (2*f 3)*(X*f 8+X*f 9+Real.sqrt X*f 9+D*f 2*B*X+
    Real.sqrt 2*(Real.sqrt X*(c*f 5+D*B*(f 4+f 2))+c*f 5))
  let charge := 2*f 6*Real.sqrt X+2*f 7*Real.sqrt (2*X)
  flat+source+deriv+charge

/-- The selected panel weak allowance is nonnegative throughout the heat interval. -/
theorem parent_row_panel_weak_nonneg (j : Fin 16) (t : ℝ) (ht : 0≤t) :
    0≤parentRowPanelWeak j t := by
  exact add_nonneg (nativeList_getD_nonneg _ (parent_row_fields_valid j).2 15)
    (mul_nonneg (nativeList_getD_nonneg _ (parent_row_fields_valid j).2 12) ht)

/-- Restoring the source's collected derivative terms only increases the
contracted cap, since sqrt(2)>=1. -/
theorem parent_row_derivative_collected_le
    (kd k op om x y X c D B : ℝ)
    (hkd : 0≤kd) (hk : 0≤k) (hop : 0≤op) (hom : 0≤om) (hc : 0≤c) (hD : 0≤D) (hB : 0≤B) :
    (2*kd)*(X*x+X*y+Real.sqrt X*(c*om)+(D*(op+k))*(B*Real.sqrt X)+
      (D*k)*(B*X)+Real.sqrt X*y+c*om)≤
    (2*kd)*(X*x+X*y+Real.sqrt X*y+D*k*B*X+
      Real.sqrt 2*(Real.sqrt X*(c*om+D*B*(op+k))+c*om)) := by
  have hs : 1≤Real.sqrt (2:ℝ) := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hT : 0≤Real.sqrt X*(c*om+D*B*(op+k))+c*om :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (mul_nonneg hc hom)
      (mul_nonneg (mul_nonneg hD hB) (add_nonneg hop hk)))) (mul_nonneg hc hom)
  have hh := mul_le_mul_of_nonneg_right hs hT
  rw [one_mul] at hh
  have hh' := add_le_add (le_refl (X*x+X*y+Real.sqrt X*y+D*k*B*X)) hh
  exact (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left hh' (mul_nonneg (by norm_num) hkd))

end
end ASDExplicitGamma.Native

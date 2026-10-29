module

public import ASDExplicitGamma.Gaussian.RectangleDomain
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # The closed source rectangle is the closure of its interior -/

@[expose] public section

open Homogenization Set MeasureTheory

namespace ASDExplicitGamma.Gaussian

theorem rectangle_closure (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    closure (openRectangle a b c d) = closedRectangle a b c d := by
  change closure ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹' (Ioo a b ×ˢ Ioo c d)) = _
  rw [← Homeomorph.preimage_closure, closure_prod_eq, closure_Ioo hab.ne, closure_Ioo hcd.ne]
  rfl

/-- A continuous representative on the closed source rectangle is determined by its ordinary
Lebesgue a.e. values on the open rectangle. -/
theorem rectangle_value_eq_zero (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (f : C(closedRectangle a b c d, ℝ)) (g : Vec 2 → ℝ)
    (hg : ∀ x : closedRectangle a b c d, g x.1 = f x)
    (hz : g =ᵐ[volume.restrict (openRectangle a b c d)] 0) : f = 0 := by
  have hcont : ContinuousOn g (closedRectangle a b c d) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact f.continuous.congr (fun x => (hg x).symm)
  have hsub : openRectangle a b c d ⊆ closedRectangle a b c d :=
    fun _ hx => ⟨Ioo_subset_Icc_self hx.1, Ioo_subset_Icc_self hx.2⟩
  have he := MeasureTheory.Measure.eqOn_open_of_ae_eq hz (openRectangle_isOpen a b c d)
    (hcont.mono hsub) continuousOn_const
  have heK := he.of_subset_closure hcont continuousOn_const hsub
    (show closedRectangle a b c d ⊆ closure (openRectangle a b c d) by
      rw [rectangle_closure a b c d hab hcd])
  ext x
  exact (hg x).symm.trans (heK x.2)

end ASDExplicitGamma.Gaussian

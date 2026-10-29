module

public import ASDExplicitGamma.Native.ParentRowPanelIdentification
public import ASDExplicitGamma.Native.ParentRowDerivativeCapComparison

/-! Final four-block algebra for the parent panel. The two block
comparisons are explicit in-node inputs until they are proved. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Main Triadic Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- Combine the proved source/derivative sums with the independently owned
flat and paired-boundary comparisons. This is an in-node helper, not the
final row theorem. -/
theorem parent_row_band_error_panel_of_flat_charge
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (hw : parentRowWeakAllowance (j.val+1) t≤parentRowPanelWeak j t)
    (hflat :
      let f := fun k => (parentRowFields j).getD k 0
      let X := parentRowPanelWeak j t
      let H := parentRowPanelHistory j t
      let A := 1+2*H+Real.sqrt (2*H)
      (∑ i : Fin (j.val+1),parentRowFlatCap M n (j.val+1) 5 t
        (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ))))≤
        theta M*(Real.sqrt 2*Real.sqrt X*f 8*f 4+
          2*Real.sqrt 2*Real.sqrt ((1+inverseHistoryDiscount)*A*H)*f 9*f 5+
          (3683/2500:ℝ)*(f 4)^2+A*(f 5)^2))
    (hcharge :
      let f := fun k => (parentRowFields j).getD k 0
      let X := parentRowPanelWeak j t
      (∑ i : Fin (j.val+1),parentRowChargeCap M n (j.val+1) 5 t
        (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ))))≤
        theta M*(2*f 6*Real.sqrt X+2*f 7*Real.sqrt (2*X))) :
    parentRowBandErrorCap M h n (j.val+1) 5 t≤theta M*parentRowPanelError j t := by
  let f := fun k => (parentRowFields j).getD k 0
  let X := parentRowPanelWeak j t
  let H := parentRowPanelHistory j t
  let A := 1+2*H+Real.sqrt (2*H)
  let c := Real.sqrt ((3683/2500:ℝ)*A)+1
  have hf (k) : 0≤f k := nativeList_getD_nonneg _ (parent_row_fields_valid j).2 k
  have hs := parent_row_band_source_cap M h hg n hstate j t ht hw
  have hd := parent_row_band_derivative_cap_contracted M h hg n hstate j t ht hw
  have hdc := parent_row_derivative_collected_le (f 3) (f 2) (f 4) (f 5) (f 8) (f 9) X c
    (1+inverseHistoryDiscount) (3683/2500) (hf 3) (hf 2) (hf 4) (hf 5)
    (add_nonneg (Real.sqrt_nonneg _) (by norm_num))
    (add_nonneg (by norm_num) inverse_history_discount_range.1.le) (by norm_num)
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hdc (cold_theta_pos M).le)
  have hh := add_le_add (add_le_add (add_le_add hflat hs) hd') hcharge
  unfold parentRowBandErrorCap parentRowErrorCap
  simp only [Finset.sum_add_distrib]
  exact hh.trans_eq (by dsimp only [parentRowPanelError,f,X,H,A,c,parentRowPanelWeak]; ring)

end
end ASDExplicitGamma.Native

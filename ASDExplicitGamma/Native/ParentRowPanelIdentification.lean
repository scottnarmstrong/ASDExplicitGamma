module

public import ASDExplicitGamma.Native.ParentRowPanelBlocks

/-! Exact identification of the assembled real parent bill with its certified program. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Main Triadic Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- The selected panel consists of its seventeen literal stored fields. -/
theorem parent_row_fields_list (j : Fin 16) :
    let f := fun k => (parentRowFields j).getD k 0
    parentRowFields j=[f 0,f 1,f 2,f 3,f 4,f 5,f 6,f 7,f 8,f 9,f 10,f 11,f 12,f 13,f 14,f 15,f 16] := by
  intro f
  have hlen := (parent_row_fields_valid j).1
  apply List.ext_getElem
  · exact hlen
  · intro i hi _
    have hi17 : i<17 := by omega
    rw [←List.getD_eq_getElem (parentRowFields j) 0 hi]
    interval_cases i <;> rfl

/-- The real collected bill is exactly the unchanged certified parent
program, retaining the distinct boundary entries and the exact Y field. -/
theorem parent_row_panel_blocks_eq (j : Fin 16) (t : ℝ) (ht : 0≤t) :
    parentRowPanelAffine j t+parentRowPanelError j t=nativePanelValue (parentRowFields j) t := by
  let f := fun k => (parentRowFields j).getD k 0
  have hfields := parent_row_fields_list j
  conv_rhs => rw [hfields,nativePanelValue_readable]
  have hquarter : Real.sqrt (Real.sqrt (3:ℝ))=(3:ℝ)^(1/4:ℝ) := by
    simp only [Real.sqrt_eq_rpow]
    rw [←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
    norm_num
  have hD : 1+1/Real.sqrt (Real.sqrt (3:ℝ))=1+inverseHistoryDiscount := by
    rw [hquarter,one_div,inverse_history_discount_eq]
  have hX := parent_row_panel_weak_nonneg j t ht
  have hA : 0≤1+2*parentRowPanelHistory j t+Real.sqrt (2*parentRowPanelHistory j t) :=
    add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (sq_nonneg _))) (Real.sqrt_nonneg _)
  have hBA := mul_nonneg (by norm_num : (0:ℝ)≤3683/2500) hA
  change _=nativeOldBoundaryPanel (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
    (f 8) (f 9) (f 10) (f 11) (f 12) (f 13) (f 14) (f 15) (f 16) t
  dsimp only [nativeOldBoundaryPanel]
  rw [hD]
  dsimp only [parentRowPanelHistory] at hBA
  rw [Real.sq_sqrt hBA]
  unfold parentRowPanelAffine parentRowPanelError
  dsimp only [parentRowPanelWeak,parentRowPanelHistory] at hX ⊢
  simp_rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  dsimp only [f] at *
  generalize hweak : ((parentRowFields j).getD 15 0+(parentRowFields j).getD 12 0*t)=X at hX ⊢
  have hs : Real.sqrt (2:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  simp only [add_mul]
  field_simp [hs]
  ring_nf
  simp only [Real.sq_sqrt hX]
  ring

end
end ASDExplicitGamma.Native

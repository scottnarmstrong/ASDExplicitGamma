module

public import ASDExplicitGamma.Native.HeatIndividualRowRounding

/-! The integrated split bill fits the exact rounded individual source row. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
noncomputable section

/-- Rounding all three coefficients is legitimate because the two ordinary
moments are nonnegative. Every first- and second-order rare term is retained. -/
theorem heat_individual_bill_le_rounded_row (height k : ℕ) (old : NativeOldRow)
    (previous current : ℝ) (hprev : 0 ≤ previous) (hcur : 0 ≤ current) :
    let c : ℚ := 1975/1000+2*((k-1:ℕ):ℚ)*(1565/1000)
    let d : ℚ := 2*(height:ℚ)+4*(k-1)*((height:ℚ)+521/1000)
    let j1p : ℝ := nativeRareJ old.x old.f 1 (k-1)
    let j1 : ℝ := nativeRareJ old.x old.f 1 k
    let j2p : ℝ := nativeRareJ old.x old.f 2 (k-1)
    let j2 : ℝ := nativeRareJ old.x old.f 2 k
    let row := nativeIndividualRow height k old
    (k:ℝ)*(old.e:ℝ)*(((d:ℝ)*(nativeB:ℝ)+4*(2*(521/1000)*(nativeB:ℝ)+(c:ℝ)*(nativeB:ℝ)^2))*previous+
      (2*(521/1000)*(nativeB:ℝ)+(c:ℝ)*(nativeB:ℝ)^2)*current+
      (d:ℝ)*j1p+(2*(521/1000)+2*(nativeB:ℝ)*(c:ℝ))*(4*j1p+j1)+(c:ℝ)*(4*j2p+j2)) ≤
        (nativeA:ℝ)*(row.1:ℝ)*previous+(row.2.1:ℝ)*current+(nativeA:ℝ)^k*(row.2.2:ℝ) := by
  obtain ⟨ha,hb,he⟩ := heat_individual_row_coefficients height k old
  have hbound := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_right ha hprev) (mul_le_mul_of_nonneg_right hb hcur)) he
  dsimp only at hbound ⊢
  push_cast at hbound ⊢
  calc
    _ = _ := by ring
    _ ≤ _ := hbound

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.HeatIndividualRareRounding

/-! Source coefficient rounding before the already-proved matrix unscaling. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
noncomputable section

/-- Outward rounding remains outward after undoing a positive scale. -/
theorem heat_individual_scaled_up (a u : ℚ) (ha : 0 < a) :
    (u:ℝ) ≤ (a:ℝ)*(nativeUp (u/a):ℝ) := by
  have h := mul_le_mul_of_nonneg_left (nativeUp_ge (u/a)) ha.le
  rw [mul_div_cancel₀ _ ha.ne'] at h
  exact_mod_cast h

/-- Each of the three rounded individual coefficients dominates the exact
source coefficient after its physical scale is restored. -/
theorem heat_individual_row_coefficients (height k : ℕ) (old : NativeOldRow) :
    let c : ℚ := 1975/1000+2*((k-1:ℕ):ℚ)*(1565/1000)
    let d : ℚ := 2*(height:ℚ)+4*(k-1)*((height:ℚ)+521/1000)
    let row := nativeIndividualRow height k old
    ((k:ℚ)*old.e*(d*nativeB+4*(2*(521/1000)*nativeB+c*nativeB^2)):ℝ) ≤
      (nativeA:ℝ)*(row.1:ℝ) ∧
    ((k:ℚ)*old.e*(2*(521/1000)*nativeB+c*nativeB^2):ℝ) ≤ (row.2.1:ℝ) ∧
    ((k:ℚ)*old.e*(d*nativeRareJ old.x old.f 1 (k-1)+
      (2*(521/1000)+2*nativeB*c)*(4*nativeRareJ old.x old.f 1 (k-1)+nativeRareJ old.x old.f 1 k)+
      c*(4*nativeRareJ old.x old.f 2 (k-1)+nativeRareJ old.x old.f 2 k)):ℝ) ≤
      (nativeA:ℝ)^k*(row.2.2:ℝ) := by
  dsimp only [nativeIndividualRow]
  refine ⟨?_,?_,?_⟩
  · have h := heat_individual_scaled_up nativeA
      ((k:ℚ)*old.e*((2*(height:ℚ)+4*(k-1)*((height:ℚ)+521/1000))*nativeB+
        4*(2*(521/1000)*nativeB+(1975/1000+2*((k-1:ℕ):ℚ)*(1565/1000))*nativeB^2)))
      (by norm_num [nativeA])
    push_cast at h ⊢
    exact h
  · have h := nativeUp_ge ((k:ℚ)*old.e*(2*(521/1000)*nativeB+
      (1975/1000+2*((k-1:ℕ):ℚ)*(1565/1000))*nativeB^2))
    have hR := (Rat.cast_le (K:=ℝ)).2 h
    push_cast at hR ⊢
    exact hR
  · have h := heat_individual_scaled_up (nativeA^k)
      ((k:ℚ)*old.e*((2*(height:ℚ)+4*(k-1)*((height:ℚ)+521/1000))*nativeRareJ old.x old.f 1 (k-1)+
        (2*(521/1000)+2*nativeB*(1975/1000+2*((k-1:ℕ):ℚ)*(1565/1000)))*
          (4*nativeRareJ old.x old.f 1 (k-1)+nativeRareJ old.x old.f 1 k)+
        (1975/1000+2*((k-1:ℕ):ℚ)*(1565/1000))*
          (4*nativeRareJ old.x old.f 2 (k-1)+nativeRareJ old.x old.f 2 k)))
      (pow_pos (by norm_num [nativeA]) k)
    push_cast at h ⊢
    exact h

end
end ASDExplicitGamma.Native

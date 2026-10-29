module

public import ASDExplicitGamma.Native.OldSignedCellDerivativeBounds

/-! Monotone replacement of inverse and matrix histories in OLD derivative feedback. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- The complete derivative block increases when the two history
multipliers are replaced by their common-bank and matrix majorants. -/
theorem old_signed_derivative_cell_majorant
    (B₀ A₀ B A G d p q op om D k : ℝ)
    (hB₀ : 0≤B₀) (hA₀ : 0≤A₀) (hB : B₀≤B) (hA : A₀≤A)
    (hG : 0≤G) (hd : 0≤d) (hop : 0≤op) (hom : 0≤om) (hD : 0≤D) (hk : 0≤k) :
    2*(k*G*(Real.sqrt p+D*B₀*op))+
      2*(k*(Real.sqrt 2+G)*(D*B₀*d))+
      2*(k*(Real.sqrt 2+G)*(Real.sqrt q+(Real.sqrt (B₀*A₀)+1)*om))≤
    2*(k*G*(Real.sqrt p+D*B*op))+
      2*(k*(Real.sqrt 2+G)*(D*B*d))+
      2*(k*(Real.sqrt 2+G)*(Real.sqrt q+(Real.sqrt (B*A)+1)*om)) := by
  have hDB := mul_le_mul_of_nonneg_left hB hD
  have hfirst := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl (Real.sqrt p)) (mul_le_mul_of_nonneg_right hDB hop)) (mul_nonneg hk hG))
        (by norm_num : (0:ℝ)≤2)
  have hkg : 0≤k*(Real.sqrt 2+G) := mul_nonneg hk (add_nonneg (Real.sqrt_nonneg _) hG)
  have hsecond := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hDB hd) hkg) (by norm_num : (0:ℝ)≤2)
  have hBA := mul_le_mul hB hA hA₀ (hB₀.trans hB)
  have hoff := mul_le_mul_of_nonneg_right (add_le_add (Real.sqrt_le_sqrt hBA) (le_refl (1:ℝ))) hom
  have hthird := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl (Real.sqrt q)) hoff) hkg) (by norm_num : (0:ℝ)≤2)
  exact add_le_add (add_le_add hfirst hsecond) hthird

end
end ASDExplicitGamma.Native

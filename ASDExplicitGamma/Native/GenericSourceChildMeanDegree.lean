module

public import ASDExplicitGamma.Native.GenericSourceChildBandMeanCap

/-! Positive degree bookkeeping for the actual child mean forcing. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- The complete child forcing is nonnegative on nonnegative inputs. -/
theorem native_source_child_mean_L_nonneg (height : ℕ) (epsilon x e : ℝ)
    (heps : 0 ≤ epsilon) (hx : 0 ≤ x) (he : 0 ≤ e) :
    0 ≤ nativeSourceChildMeanL height epsilon x e := by
  unfold nativeSourceChildMeanL nativeSourceChildMeanR nativeSourceChildMeanC
  positivity

/-- The child forcing has degree one in the physical variance. The rare
reserve stays fixed, while its trace argument is endpoint dominated. -/
theorem native_source_child_mean_L_degree
    (height : ℕ) (theta epsilon x x0 e e0 : ℝ)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) (heps : 0 ≤ epsilon)
    (hx : 0 ≤ x) (hx0 : 0 ≤ x0) (hxx : x ≤ theta*x0)
    (he0 : 0 ≤ e0) (hecap : e ≤ theta*e0) :
    nativeSourceChildMeanL height epsilon x e ≤
      theta*nativeSourceChildMeanL height epsilon x0 e0 := by
  let B := fun z : ℝ => 2*(height:ℝ)*(3683/2500:ℝ)+4*nativeSourceChildMeanC+
    2*(height:ℝ)*epsilon+
    (2*(65399707/10^9:ℝ)+2*(3683/2500)*(259713047/10^9))*(4*epsilon+epsilon*z)+
    (259713047/10^9:ℝ)*(4*epsilon^2+epsilon^2*z)
  have hxle : x ≤ x0 := hxx.trans ((mul_le_mul_of_nonneg_right ht1 hx0).trans_eq (one_mul _))
  have hBx : 0 ≤ B x := by dsimp [B,nativeSourceChildMeanC]; positivity
  have h1 := add_le_add (le_refl (4*epsilon)) (mul_le_mul_of_nonneg_left hxle heps)
  have h2 := add_le_add (le_refl (4*epsilon^2)) (mul_le_mul_of_nonneg_left hxle (sq_nonneg epsilon))
  have hB : B x ≤ B x0 := add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 (by norm_num)))
    (mul_le_mul_of_nonneg_left h2 (by norm_num))
  have hL (z E : ℝ) : nativeSourceChildMeanL height epsilon z E=E*B z := by
    dsimp [nativeSourceChildMeanL,nativeSourceChildMeanR,B]
    ring
  rw [hL,hL]
  calc
    e*B x ≤ (theta*e0)*B x := mul_le_mul_of_nonneg_right hecap hBx
    _ ≤ (theta*e0)*B x0 := mul_le_mul_of_nonneg_left hB (mul_nonneg ht0 he0)
    _ = theta*(e0*B x0) := by ring

end
end ASDExplicitGamma.Native

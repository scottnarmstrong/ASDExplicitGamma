module

public import ASDExplicitGamma.Native.GenericSourceChildAuxInputs
public import ASDExplicitGamma.Native.GenericSourceChildBandRefinedDerivative

/-! The actual child p20 increment obeys the power-certified strict budget
under the genuine physical variance and full-response bounds. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Algsuperdiff.Section3
noncomputable section

/-- The child p20 increment is at most 70 theta or 119 theta on the
corresponding auxiliary norm barrier. No actual-law cap is assumed here. -/
theorem native_source_child_aux_cost
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (height : ℕ) (high : Bool)
    (hh : height ≤ nativeSourceChildAuxHeight high) :
    nativeSourceChildRefinedMomentIncrement height (nativeSourceRawShellVarianceCap M.gamma height)
      (nativeSourceChildFullResponseCap M.gamma height) (theta M*(nativeSourceChildAuxNorm high:ℝ)) ≤
      theta M*(nativeSourceChildAuxCost high:ℝ) := by
  let H := nativeSourceChildAuxHeight high
  let e0 := nativeSourceChildAuxVariance high
  let f0 := nativeSourceChildAuxResponse high
  let X0 := nativeSourceChildAuxNorm high
  let u := nativeSourceChildAuxU1 high
  let v := nativeSourceChildAuxU2 high
  let e := nativeSourceRawShellVarianceCap M.gamma height
  let f := nativeSourceChildFullResponseCap M.gamma height
  let x := theta M*(X0:ℝ)
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have ht1 : theta M ≤ 1 := (div_le_one (by norm_num [gammaZero])).mpr hg
  rcases native_source_child_aux_certificate high with ⟨he0,hf0,hX0,_,hu,hv,hp1,hp2,hpay,_⟩
  have he0R : (0:ℝ) ≤ e0 := by exact_mod_cast he0
  have hf0R : (0:ℝ) ≤ f0 := by exact_mod_cast hf0
  have hX0R : (0:ℝ) ≤ X0 := by exact_mod_cast hX0
  have huR : (0:ℝ) ≤ u := by exact_mod_cast hu
  have hvR : (0:ℝ) ≤ v := by exact_mod_cast hv
  have hx : 0 ≤ x := mul_nonneg ht0 hX0R
  have hxx : x ≤ (X0:ℝ) := (mul_le_mul_of_nonneg_right ht1 hX0R).trans_eq (one_mul _)
  have he : e ≤ theta M*(e0:ℝ) := native_source_child_aux_variance M hg height high hh
  have hf : f ≤ (f0:ℝ) := native_source_child_aux_response M hg height high hh
  have hfpos : 0 ≤ f := by dsimp [f,nativeSourceChildFullResponseCap]; positivity
  have hpow1 : (X0:ℝ)^22*(f0:ℝ)^5 ≤ (u:ℝ)^27 := by exact_mod_cast hp1
  have hpow2 : (X0:ℝ)^17*(f0:ℝ)^10 ≤ (v:ℝ)^27 := by exact_mod_cast hp2
  have h1 := native_source_rpow_product_cap X0 f0 u 22 5 27 hX0R hf0R huR (by norm_num) hpow1
  have h2 := native_source_rpow_product_cap X0 f0 v 17 10 27 hX0R hf0R hvR (by norm_num) hpow2
  have hm := native_source_interpolation_caps_monotone (theta := 1) (by norm_num)
    hx hX0R (by simpa only [one_mul] using hxx) hfpos hf
  have hD : nativeSourceInterpolationD x ≤ 2*(3683/2500:ℝ) := min_le_left _ _
  have hD0 : 0 ≤ nativeSourceInterpolationD x := by unfold nativeSourceInterpolationD nativeSourceB128; positivity
  have hU1 : nativeSourceInterpolationU1 x f ≤ 4+(u:ℝ) := by
    apply hm.2.1.trans
    apply (min_le_right _ _).trans
    apply add_le_add le_rfl
    convert h1 using 1; norm_num [nativeSourceEll]
  have hU2 : nativeSourceInterpolationU2 x f ≤ 4+(v:ℝ) := by
    apply hm.2.2.trans
    apply (min_le_right _ _).trans
    apply add_le_add le_rfl
    convert h2 using 1; norm_num [nativeSourceEll]
  have hhR : (height:ℝ) ≤ (H:ℝ) := by exact_mod_cast hh
  have hDterm := mul_le_mul
    (show 39*(height:ℝ)+38*(65399707/10^9:ℝ) ≤ 39*(H:ℝ)+38*(65399707/10^9:ℝ) by linarith only [hhR])
    hD hD0 (by positivity)
  let B := (39*(height:ℝ)+38*(65399707/10^9:ℝ))*nativeSourceInterpolationD x+
    2*(65399707/10^9:ℝ)*(3683/2500)*nativeSourceInterpolationU1 x f+
    ((259713047/10^9:ℝ)+38*((259713047/10^9:ℝ)+(65399707/10^9:ℝ)))*(3683/2500)^2*
      nativeSourceInterpolationU2 x f
  let B0 := (39*(H:ℝ)+38*(65399707/10^9:ℝ))*(2*(3683/2500:ℝ))+
    2*(65399707/10^9:ℝ)*(3683/2500)*(4+(u:ℝ))+
    ((259713047/10^9:ℝ)+38*((259713047/10^9:ℝ)+(65399707/10^9:ℝ)))*(3683/2500)^2*(4+(v:ℝ))
  have hB : B ≤ B0 := add_le_add (add_le_add hDterm
    (mul_le_mul_of_nonneg_left hU1 (by norm_num))) (mul_le_mul_of_nonneg_left hU2 (by norm_num))
  have hBpos : 0 ≤ B := by
    dsimp [B,nativeSourceInterpolationU1,nativeSourceInterpolationU2]
    positivity
  have hpayR : (e0:ℝ)*B0 ≤ (nativeSourceChildAuxCost high:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hpay
    norm_num only [Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast] at hh
    convert hh using 1; norm_num [e0,B0,H,u,v]
  calc
    _ = e*B := rfl
    _ ≤ (theta M*(e0:ℝ))*B := mul_le_mul_of_nonneg_right he hBpos
    _ ≤ (theta M*(e0:ℝ))*B0 := mul_le_mul_of_nonneg_left hB (mul_nonneg ht0 he0R)
    _ = theta M*((e0:ℝ)*B0) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpayR ht0

end
end ASDExplicitGamma.Native

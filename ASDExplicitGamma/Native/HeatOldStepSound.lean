module

public import ASDExplicitGamma.Native.HeatOldInterpolation

/-! One OLD producer refinement preserves the real source-envelope bound. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
noncomputable section

/-- The same minimum used by the literal producer dominates a real OLD
refinement whenever the preceding increment and three radicals are certified. -/
theorem heat_old_step_sound (height : ℕ) (f e hc : ℚ)
    (hf : 0 ≤ f) (he : 0 ≤ e) (hvalid : HeatOldStepValid f hc)
    (H : ℝ) (hH : 0 ≤ (7/2)*(nativeA:ℝ)+H) (hHc : H ≤ (hc:ℝ)) :
    min H (nativeSourceRefinedMomentIncrement height e f ((7/2)*(nativeA:ℝ)+H)) ≤
      (nativeOldStep height f e hc:ℝ) := by
  let x : ℚ := (7/2)*nativeA+hc
  let u1 := min f (4+x*nativeRootUp ((f/x)^5) 27)
  let u2 := min f (4+x*nativeRootUp ((f/x)^10) 27)
  let d := min (2*nativeB) (2+x+nativeRootUp (2*x))
  let N : ℚ := e*(((2*20-1)*height+2*19*(521/1000))*d+
    2*(521/1000)*nativeB*u1+((1975/1000)+2*19*(1565/1000))*nativeB^2*u2)
  have hhc := hvalid.1
  have haQ : 0 ≤ nativeA := by norm_num [nativeA]
  have haR : 0 ≤ (nativeA:ℝ) := by exact_mod_cast haQ
  have hx : 0 ≤ (x:ℝ) := by
    have hxQ : 0 ≤ x := by dsimp [x]; positivity
    exact_mod_cast hxQ
  have hxx : (7/2)*(nativeA:ℝ)+H ≤ (x:ℝ) := by
    dsimp [x]
    push_cast
    exact add_le_add le_rfl hHc
  have hm := native_source_interpolation_caps_monotone (theta:=1)
    (x:=(7/2)*(nativeA:ℝ)+H) (x0:=(x:ℝ)) (by norm_num)
    hH
    hx (by simpa only [one_mul] using hxx) (by exact_mod_cast hf) (le_refl (f:ℝ))
  have hp := heat_old_interpolation_le f hc hf hvalid
  have hD := hm.1.trans hp.1
  have hU1 := hm.2.1.trans hp.2.1
  have hU2 := hm.2.2.trans hp.2.2
  have hcost := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hD (by positivity : (0:ℝ) ≤ 39*(height:ℝ)+38*(521/1000)))
      (mul_le_mul_of_nonneg_left hU1 (by norm_num [nativeB] : (0:ℝ) ≤ 2*(521/1000)*(nativeB:ℝ))))
      (mul_le_mul_of_nonneg_left hU2 (by norm_num [nativeB] : (0:ℝ) ≤ (1975/1000+38*(1565/1000))*(nativeB:ℝ)^2)))
    (show 0 ≤ (e:ℝ) by exact_mod_cast he)
  have hN : nativeSourceRefinedMomentIncrement height e f ((7/2)*(nativeA:ℝ)+H) ≤ (N:ℝ) := by
    convert hcost using 1 <;>
      dsimp [N,d,u1,u2,x,nativeSourceRefinedMomentIncrement,nativeSourceK,nativeSourceM,nativeSourceQ,nativeSourceB128,nativeB] <;>
      push_cast <;> ring
  have hround : (N:ℝ) ≤ (nativeUp N:ℝ) := by exact_mod_cast nativeUp_ge N
  have hh := min_le_min hHc (hN.trans hround)
  simpa only [nativeOldStep,N,x,u1,u2,d,Rat.cast_min] using hh

end
end ASDExplicitGamma.Native

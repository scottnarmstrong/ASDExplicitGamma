module

public import ASDExplicitGamma.Native.HeatOldStepCertificates

/-! Real soundness of every rational OLD interpolation radical. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
noncomputable section

/-- The three analytic interpolation factors lie below the exact rational
producer factors once their integer-power certificates have been checked. -/
theorem heat_old_interpolation_le (f hc : ℚ) (hf : 0 ≤ f)
    (hvalid : HeatOldStepValid f hc) :
    let x := (7/2)*nativeA+hc
    nativeSourceInterpolationD x ≤
      (min (2*nativeB) (2+x+nativeRootUp (2*x)):ℝ) ∧
    nativeSourceInterpolationU1 x f ≤
      (min f (4+x*nativeRootUp ((f/x)^5) 27):ℝ) ∧
    nativeSourceInterpolationU2 x f ≤
      (min f (4+x*nativeRootUp ((f/x)^10) 27):ℝ) := by
  let x : ℚ := (7/2)*nativeA+hc
  let u : ℚ := x*nativeRootUp ((f/x)^5) 27
  let v : ℚ := x*nativeRootUp ((f/x)^10) 27
  let d : ℚ := nativeRootUp (2*x)
  change 0 ≤ hc ∧ 0 < x ∧ 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ d ∧
    x^22*f^5 ≤ u^27 ∧ x^17*f^10 ≤ v^27 ∧ 2*x ≤ d^2 at hvalid
  obtain ⟨hhc,hx,hu,hv,hd,hp1,hp2,hpd⟩ := hvalid
  have hxR : 0 ≤ (x:ℝ) := by exact_mod_cast hx.le
  have hfR : 0 ≤ (f:ℝ) := by exact_mod_cast hf
  have huR : 0 ≤ (u:ℝ) := by exact_mod_cast hu
  have hvR : 0 ≤ (v:ℝ) := by exact_mod_cast hv
  have hp1R : (x:ℝ)^22*(f:ℝ)^5 ≤ (u:ℝ)^27 := by exact_mod_cast hp1
  have hp2R : (x:ℝ)^17*(f:ℝ)^10 ≤ (v:ℝ)^27 := by exact_mod_cast hp2
  have h1 := native_source_rpow_product_cap x f u 22 5 27 hxR hfR huR (by norm_num) hp1R
  have h2 := native_source_rpow_product_cap x f v 17 10 27 hxR hfR hvR (by norm_num) hp2R
  have hD : Real.sqrt (2*(x:ℝ)) ≤ (d:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by exact_mod_cast hd,by exact_mod_cast hpd⟩
  refine ⟨?_,?_,?_⟩
  · change nativeSourceInterpolationD (x:ℝ) ≤ _
    simp only [nativeSourceInterpolationD,nativeSourceB128]
    have h := min_le_min (le_refl (2*(3683/2500:ℝ))) (add_le_add (le_refl (2+(x:ℝ))) hD)
    simpa only [x,d,nativeB,Rat.cast_min,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] using h
  · change nativeSourceInterpolationU1 (x:ℝ) (f:ℝ) ≤ _
    have hp : (x:ℝ)^(1-nativeSourceEll)*(f:ℝ)^nativeSourceEll ≤ (u:ℝ) := by
      convert h1 using 1 <;> norm_num [nativeSourceEll]
    have h := min_le_min (le_refl (f:ℝ)) (add_le_add (le_refl (4:ℝ)) hp)
    simpa only [nativeSourceInterpolationU1,x,u,Rat.cast_min,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat] using h
  · change nativeSourceInterpolationU2 (x:ℝ) (f:ℝ) ≤ _
    have hp : (x:ℝ)^(1-2*nativeSourceEll)*(f:ℝ)^(2*nativeSourceEll) ≤ (v:ℝ) := by
      convert h2 using 1 <;> norm_num [nativeSourceEll]
    have h := min_le_min (le_refl (f:ℝ)) (add_le_add (le_refl (4:ℝ)) hp)
    simpa only [nativeSourceInterpolationU2,x,v,Rat.cast_min,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat] using h

end
end ASDExplicitGamma.Native

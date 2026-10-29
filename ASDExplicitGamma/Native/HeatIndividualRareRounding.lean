module

public import ASDExplicitGamma.Native.HeatIndividualBillIntegral

/-! Outward rounding of the individual branch's original OLD rare reserve. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
noncomputable section

/-- A checked root pays the exact generalized Holder exponent, for any
nonnegative rational ratio and any integral numerator. -/
theorem heat_individual_ratio_root (q : ℚ) (hq : 0 ≤ q) (j : ℕ)
    (hroot : nativeRootValid (q^(5*j)) 27 = true) :
    (q:ℝ)^(((j*20:ℕ):ℝ)/((128-20:ℕ):ℝ)) ≤
      (nativeRootUp (q^(5*j)) 27:ℝ) := by
  have hqR : 0 ≤ (q:ℝ) := by exact_mod_cast hq
  have he : (((j*20:ℕ):ℝ)/((128-20:ℕ):ℝ)) = ((5*j:ℕ):ℝ)*(27:ℝ)⁻¹ := by
    push_cast
    ring
  rw [he,Real.rpow_natCast_mul hqR]
  simpa only [Rat.cast_pow,Nat.cast_ofNat] using nativeRoot_sound hroot

/-- Original OLD rare moments use nativeEps, without silently increasing the
reserve to the later constant-sheared heat frame. -/
theorem heat_individual_rareJ_top (x f : ℚ) (hx : 0 < x) (hf : 0 ≤ f) (j : ℕ)
    (hroot : nativeRootValid ((f/x)^(5*j)) 27 = true) :
    nativeHeatVHEATJ (nativeEps:ℝ) x f 20 j 20 ≤ (nativeRareJ x f j 20:ℝ) := by
  have hp := heat_individual_ratio_root (f/x) (div_nonneg hf hx.le) j hroot
  have he : 0 ≤ (nativeEps:ℝ) := by norm_num [nativeEps]
  have hxR : 0 ≤ (x:ℝ) := by exact_mod_cast hx.le
  have hu : ((nativeEps^j*x^20*nativeRootUp ((f/x)^(5*j)) 27:ℚ):ℝ) ≤
      (nativeRareJ x f j 20:ℝ) := by
    exact_mod_cast (show nativeEps^j*x^20*nativeRootUp ((f/x)^(5*j)) 27 ≤
      nativeRareJ x f j 20 from by simpa [nativeRareJ] using (nativeUp_ge
        (nativeEps^j*x^20*nativeRootUp ((f/x)^(5*j)) 27)))
  rw [nativeHeatVHEATJ_top]
  have hp' : ((f:ℝ)/(x:ℝ))^(((j*20:ℕ):ℝ)/((128-20:ℕ):ℝ)) ≤
      (nativeRootUp ((f/x)^(5*j)) 27:ℝ) := by simpa only [Rat.cast_div] using hp
  calc
    _ ≤ (nativeEps:ℝ)^j*(x:ℝ)^20*(nativeRootUp ((f/x)^(5*j)) 27:ℝ) :=
      mul_le_mul_of_nonneg_left hp' (by positivity)
    _ ≤ _ := by simpa only [Rat.cast_mul,Rat.cast_pow] using hu

/-- Every individual rare row is dominated by its rounded producer entry. -/
theorem heat_individual_rareJ_le (x f : ℚ) (hx : 0 < x) (hf : 0 ≤ f)
    (j l : ℕ) (hl : l ≤ 20)
    (hroot : nativeRootValid ((f/x)^(5*j)) 27 = true) :
    nativeHeatVHEATJ (nativeEps:ℝ) x f 20 j l ≤ (nativeRareJ x f j l:ℝ) := by
  rcases lt_or_eq_of_le hl with hlt | rfl
  · rw [nativeHeatVHEATJ_of_lt _ _ _ _ _ _ hlt]
    have hround := nativeUp_ge (nativeEps^j*x^l)
    have hr : nativeEps^j*x^l ≤ nativeRareJ x f j l := by
      simpa [nativeRareJ,show l ≠ 20 by omega] using hround
    exact_mod_cast hr
  · exact heat_individual_rareJ_top x f hx hf j hroot

end
end ASDExplicitGamma.Native

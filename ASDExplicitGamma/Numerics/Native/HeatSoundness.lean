module
public import ASDExplicitGamma.Numerics.Native.Heat
public import ASDExplicitGamma.Numerics.ExpSqrt
import Mathlib.Tactic.NormNum

/-! Scalar exponential checks used by the affine native heat flow. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

def nativeHeatExpCheck (c upper : ℚ) : Bool :=
  decide (|c| ≤ 1 ∧ expPolyQ c 49+expErrQ c 49 ≤ upper)

theorem nativeHeatExpCheck_sound {c upper : ℚ} (h : nativeHeatExpCheck c upper = true) :
    Real.exp (c : ℝ) ≤ (upper : ℝ) := by
  rcases of_decide_eq_true h with ⟨hc,hbound⟩
  have hcR : |(c : ℝ)| ≤ 1 := by exact_mod_cast hc
  have hs := (exp_enclosure_rat hcR (by decide : 0 < 49)).2
  apply hs.trans
  have hb := (Rat.cast_le (K := ℝ)).2 hbound
  simpa only [Rat.cast_add] using hb

noncomputable def nativeHeatHnReal (p : NativeHeatParameters) (q : ℚ) : ℝ :=
  (nativeQstar : ℝ)*((p.hp/nativeQstar : ℚ) : ℝ)^((20*(q-1)/(q*19) : ℚ) : ℝ)

noncomputable def nativeHeatCrossReal (p : NativeHeatParameters) (k : ℕ) : ℝ :=
  2*Real.sqrt ((((k-1)*9^2 : ℕ)/(9^10 : ℚ) : ℚ) : ℝ)*
    Real.sqrt (2*((nativeHeatB : ℝ)*nativeHeatHnReal p ((k : ℚ)/2)+
      ((nativeHeatEps*p.hp : ℚ) : ℝ)))

/-- Root powers and an upper Hölder moment suffice for the literal source cross coefficient. -/
theorem nativeHeatCross_real_bound (p : NativeHeatParameters) (k : ℕ) (hn u v : ℚ)
    (hhn : nativeHeatHnReal p ((k : ℚ)/2) ≤ (hn : ℝ))
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hfirst : ((k-1)*9^2 : ℕ)/(9^10 : ℚ) ≤ u^2)
    (hsecond : 2*(nativeHeatB*hn+nativeHeatEps*p.hp) ≤ v^2)
    (hproduct : 2*u*v ≤ p.cross.getD k 0) :
    nativeHeatCrossReal p k ≤ ((p.cross.getD k 0 : ℚ) : ℝ) := by
  have hB : (0 : ℝ) ≤ nativeHeatB := by
    have hq : (0 : ℚ) ≤ nativeHeatB := by decide +kernel
    exact_mod_cast hq
  have hupper : 2*((nativeHeatB : ℝ)*nativeHeatHnReal p ((k : ℚ)/2)+
      ((nativeHeatEps*p.hp : ℚ) : ℝ)) ≤
      ((2*(nativeHeatB*hn+nativeHeatEps*p.hp) : ℚ) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hhn hB) (le_refl (((nativeHeatEps*p.hp : ℚ) : ℝ))))
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat] using hm
  have hroot1 : Real.sqrt ((((k-1)*9^2 : ℕ)/(9^10 : ℚ) : ℚ) : ℝ) ≤ (u : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact_mod_cast hu
    · exact_mod_cast hfirst
  have hroot2 : Real.sqrt (2*((nativeHeatB : ℝ)*nativeHeatHnReal p ((k : ℚ)/2)+
      ((nativeHeatEps*p.hp : ℚ) : ℝ))) ≤ (v : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact_mod_cast hv
    · exact hupper.trans (by exact_mod_cast hsecond)
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hroot1 (by norm_num : (0 : ℝ) ≤ 2))
    hroot2 (Real.sqrt_nonneg _) (by exact_mod_cast (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) hu))
  have hc := (Rat.cast_le (K := ℝ)).2 hproduct
  unfold nativeHeatCrossReal
  exact hm.trans (by simpa only [Rat.cast_mul, Rat.cast_ofNat] using hc)

end ASDExplicitGamma.Numerics.Native

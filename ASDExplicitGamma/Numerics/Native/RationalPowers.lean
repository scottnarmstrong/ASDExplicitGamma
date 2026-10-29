module
public import ASDExplicitGamma.Numerics.Native.Basic
import Mathlib.Tactic.NormNum

/-! Integer cross-product certificates for high-degree rational root enclosures.
These avoid re-running a root-finding algorithm: the displayed powers themselves certify
both the magnitude and the direction of every outward witness.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem native_rational_pow_le_of_cross (a b u v n d : ℕ) (hb : 0 < b) (hv : 0 < v)
    (h : a^n*v^d ≤ u^d*b^n) :
    ((a : ℚ)/b)^n ≤ ((u : ℚ)/v)^d := by
  rw [div_pow, div_pow]
  apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < (b : ℚ)^n)
    (by positivity : (0 : ℚ) < (v : ℚ)^d)).2
  exact_mod_cast h

theorem native_real_rpow_le_of_cross (a b u v n d : ℕ) (hb : 0 < b) (hv : 0 < v)
    (hd : 0 < d) (h : a^n*v^d ≤ u^d*b^n) :
    ((a : ℝ)/b)^((n : ℝ)/d) ≤ (u : ℝ)/v := by
  have hq := native_rational_pow_le_of_cross a b u v n d hb hv h
  have hr : ((a : ℝ)/b)^n ≤ ((u : ℝ)/v)^d := by
    have hc := (Rat.cast_le (K := ℝ)).2 hq
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_natCast] using hc
  have ha0 : (0 : ℝ) ≤ (a : ℝ)/b := by positivity
  have hu0 : (0 : ℝ) ≤ (u : ℝ)/v := by positivity
  have hp := Real.rpow_le_rpow (pow_nonneg ha0 n) hr (by positivity : (0 : ℝ) ≤ (d : ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast hu0 (Nat.ne_of_gt hd)] at hp
  have he : (((a : ℝ)/b)^n)^((d : ℝ)⁻¹) = ((a : ℝ)/b)^((n : ℝ)/d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha0]
    rfl
  exact he ▸ hp

end ASDExplicitGamma.Numerics.Native

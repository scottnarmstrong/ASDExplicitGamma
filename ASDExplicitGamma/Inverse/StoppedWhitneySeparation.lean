module

public import ASDExplicitGamma.Inverse.StoppedWhitneyLift

/-! The exact physical diameter payment in the stopped two-layer argument. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- The fine depth pays the macro-layer exponent without replacing the
source ceil(k/3) profile by a different Whitney sequence. -/
theorem whitney_separation_exponent (H a : ℕ) :
    (a:ℝ)-3*((a+whitneyProfile H a:ℕ):ℝ)/4 ≤ -3*((H:ℝ)+3)/4 := by
  have hc : a ≤ 3*((a+2)/3) := by omega
  have hcR : (a:ℝ) ≤ 3*(((a+2)/3:ℕ):ℝ) := by exact_mod_cast hc
  simp only [whitneyProfile,Nat.cast_add,Nat.cast_ofNat]
  linarith only [hcR]

/-- The literal factor four, including the two touching widths, is smaller
than one third of the macro-layer side at every source entrance. -/
theorem whitney_separation_gate (l : ℤ) (H a : ℕ) (hH : 1 ≤ H) :
    4*(3:ℝ)^(((a+whitneyProfile H a:ℕ):ℝ)/4)*
      (3:ℝ)^(l-((a+whitneyProfile H a:ℕ):ℤ)) < (1/3:ℝ)*(3:ℝ)^(l-(a:ℤ)) := by
  have he := whitney_separation_exponent H a
  have hHR : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hexp : (a:ℝ)-3*((a+whitneyProfile H a:ℕ):ℝ)/4 ≤ -3 := by linarith only [he,hHR]
  have hr : (3:ℝ)^((a:ℝ)-3*((a+whitneyProfile H a:ℕ):ℝ)/4) ≤ 1/27 := by
    convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hexp using 1
    norm_num [Real.rpow_neg,Real.rpow_ofNat]
  have hid :
      (3:ℝ)^(((a+whitneyProfile H a:ℕ):ℝ)/4)*
        (3:ℝ)^(l-((a+whitneyProfile H a:ℕ):ℤ)) =
      (3:ℝ)^((a:ℝ)-3*((a+whitneyProfile H a:ℕ):ℝ)/4)*(3:ℝ)^(l-(a:ℤ)) := by
    simp only [← Real.rpow_intCast,Int.cast_sub,Int.cast_natCast]
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3),← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    congr 1
    ring
  rw [mul_assoc 4,hid,← mul_assoc]
  have hside : (0:ℝ) < (3:ℝ)^(l-(a:ℤ)) := zpow_pos (by norm_num) _
  apply mul_lt_mul_of_pos_right _ hside
  linarith only [hr]

end
end ASDExplicitGamma.Inverse

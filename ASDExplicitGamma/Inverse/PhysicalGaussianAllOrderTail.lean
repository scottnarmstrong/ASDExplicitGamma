module

public import ASDExplicitGamma.Inverse.PhysicalGaussianFastTail
public import ASDExplicitGamma.Inverse.StoppedSelectedWaveExactFamily

/-! The literal full selected-wave tail converges at every finite order.
This supplies the common physical input for all three rows and each
restarted band, before any first-term numerical bound is consumed. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
noncomputable section

/-- Complete source (9.4) tail convergence without p<=256. -/
theorem physical_selected_exact_tail_summable (γ p : ℝ) (H0 : ℕ)
    (hp : 0 < p) (hH : 333 ≤ H0) (j : Fin 2) :
    Summable (fun n : ℕ => (selectedFirstClock H0+(n:ℝ))^j.val*
      (3:ℝ)^(4*γ*(selectedFirstClock H0+(n:ℝ)))*(selectedTailProbability H0 n)^(1/(2*p):ℝ)) := by
  let z := selectedFirstClock H0
  let a : ℝ := (3:ℝ)^(4*γ)
  let A := (heightExponent (H0+11)/32)/(2*p)
  let b : ℝ := (3:ℝ)^(1/4:ℝ)
  let K : ℝ := (3:ℝ)^(4*γ*selectedFirstClock H0)
  have hz : 1 ≤ z := by
    have hh : (333:ℝ) ≤ H0 := by exact_mod_cast hH
    unfold z selectedFirstClock
    linarith only [hh]
  have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hA : 0 < A := by unfold A heightExponent; positivity
  have hb : 1 < b := Real.one_lt_rpow (by norm_num : (1:ℝ) < 3) (by norm_num : (0:ℝ) < 1/4)
  have hs := physical_fast_tail_summable z (Real.log a) A b hz hA hb j
  have he (n : ℕ) : physicalFastTailTerm z (Real.log a) A b j n=
      (z+(n:ℝ))^j.val*a^n*Real.exp (-A*b^n) := by
    unfold physicalFastTailTerm
    rw [sub_eq_add_neg,Real.exp_add]
    have hn : Real.exp (Real.log a*(n:ℝ))=a^n := by
      rw [mul_comm,Real.exp_nat_mul,Real.exp_log ha]
    rw [hn]
    simp only [mul_assoc,neg_mul]
  have hf : (fun n : ℕ => (selectedFirstClock H0+(n:ℝ))^j.val*
      (3:ℝ)^(4*γ*(selectedFirstClock H0+(n:ℝ)))*(selectedTailProbability H0 n)^(1/(2*p):ℝ))=
      fun n => K*physicalFastTailTerm z (Real.log a) A b j n := by
    funext n
    calc
      _ = K*((z+(n:ℝ))^j.val*a^n*Real.exp (-A*b^n)) := selected_wave_tail_factor γ p H0 n j
      _ = K*physicalFastTailTerm z (Real.log a) A b j n := congrArg (fun s : ℝ => K*s) (he n).symm
  rw [hf]
  exact hs.mul_left K

end
end ASDExplicitGamma.Inverse

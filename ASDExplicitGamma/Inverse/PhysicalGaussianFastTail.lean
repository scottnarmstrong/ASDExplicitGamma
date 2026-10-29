module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! Complete selected-height tail convergence at arbitrary finite order.
A geometric clock times exp(-A*b^n), b>1, is summable even when its clock
exponent is large. No finite-order restriction enters this analytic lemma. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Filter Topology
noncomputable section

def physicalFastTailTerm (z C A b : ℝ) (j : Fin 2) (n : ℕ) : ℝ :=
  (z+(n:ℝ))^j.val*Real.exp (C*(n:ℝ)-A*b^n)

theorem physical_fast_tail_term_nonneg (z C A b : ℝ) (hz : 1 ≤ z) (j : Fin 2) (n : ℕ) :
    0 ≤ physicalFastTailTerm z C A b j n := by
  have hzn : 0 ≤ z+(n:ℝ) := add_nonneg (by linarith only [hz]) (Nat.cast_nonneg n)
  exact mul_nonneg (pow_nonneg hzn _) (Real.exp_pos _).le

private theorem fast_tail_polynomial_step (z : ℝ) (hz : 1 ≤ z) (j : Fin 2) (n : ℕ) :
    (z+((n+1:ℕ):ℝ))^j.val ≤ 2*(z+(n:ℝ))^j.val := by
  fin_cases j
  · norm_num
  · simp only [pow_one,Nat.cast_add,Nat.cast_one]
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith only [hz,hn]

private theorem fast_tail_ratio (z C A b : ℝ) (hz : 1 ≤ z) (j : Fin 2) (n : ℕ) :
    physicalFastTailTerm z C A b j (n+1) ≤
      (2*Real.exp C*Real.exp (-A*(b-1)*b^n))*physicalFastTailTerm z C A b j n := by
  have hex : C*((n+1:ℕ):ℝ)-A*b^(n+1)=
      (C*(n:ℝ)-A*b^n)+C+(-A*(b-1)*b^n) := by
    rw [pow_succ]
    push_cast
    ring
  have hp := fast_tail_polynomial_step z hz j n
  calc
    _ = (z+((n+1:ℕ):ℝ))^j.val*Real.exp (C*(n:ℝ)-A*b^n)*Real.exp C*Real.exp (-A*(b-1)*b^n) := by
      rw [physicalFastTailTerm,hex,Real.exp_add,Real.exp_add]
      ring
    _ ≤ (2*(z+(n:ℝ))^j.val)*Real.exp (C*(n:ℝ)-A*b^n)*Real.exp C*Real.exp (-A*(b-1)*b^n) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) (Real.exp_pos _).le)
        (Real.exp_pos _).le
    _ = _ := by unfold physicalFastTailTerm; ring

/-- The full double-exponential selected tail converges at every finite
moment order, independently of any numerical first-term bound. -/
theorem physical_fast_tail_summable (z C A b : ℝ) (hz : 1 ≤ z) (hA : 0 < A) (hb : 1 < b) (j : Fin 2) :
    Summable (physicalFastTailTerm z C A b j) := by
  have hpow : Tendsto (fun n : ℕ => b^n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hb
  have hmul : Tendsto (fun n : ℕ => (A*(b-1))*b^n) atTop atTop :=
    hpow.const_mul_atTop (mul_pos hA (sub_pos.mpr hb))
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
  have he' : Tendsto (fun n : ℕ => 2*Real.exp C*Real.exp (-A*(b-1)*b^n)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,neg_mul,mul_zero] using he.const_mul (2*Real.exp C)
  have hsmall : ∀ᶠ n : ℕ in atTop, 2*Real.exp C*Real.exp (-A*(b-1)*b^n) ≤ (1/2:ℝ) :=
    ((tendsto_order.mp he').2 (1/2) (by norm_num)).mono (fun _ hn => hn.le)
  apply summable_of_ratio_norm_eventually_le (r := (1/2:ℝ)) (by norm_num)
  filter_upwards [hsmall] with n hn
  rw [Real.norm_of_nonneg (physical_fast_tail_term_nonneg z C A b hz j (n+1)),
    Real.norm_of_nonneg (physical_fast_tail_term_nonneg z C A b hz j n)]
  exact (fast_tail_ratio z C A b hz j n).trans
    (mul_le_mul_of_nonneg_right hn (physical_fast_tail_term_nonneg z C A b hz j n))

end
end ASDExplicitGamma.Inverse

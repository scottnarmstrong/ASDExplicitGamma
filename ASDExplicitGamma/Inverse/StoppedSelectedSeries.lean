module

public import ASDExplicitGamma.Inverse.StoppedHeightExponent

/-! Complete supergeometric selected-height series with their physical clock factors. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- A physical clock with consecutive ratio at most three is paid by the
complete selected-height supergeometric penalty, retaining the first term. -/
theorem selected_clock_series (a x r : ℝ) (ha : 0 ≤ a) (ha3 : a ≤ 3)
    (hx : 10000 ≤ x) (hr : 13/10 ≤ r) :
    Summable (fun n : ℕ => a^n*Real.exp (-x*r^n)) ∧
      (∑' n : ℕ, a^n*Real.exp (-x*r^n)) ≤ (1000/999)*Real.exp (-x) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hr0 : -1 ≤ r := le_trans (by norm_num) hr
  let A := x*(r-1)
  have hA : 3000 ≤ A := by
    have hh := mul_le_mul hx (show (3/10:ℝ) ≤ r-1 by linarith only [hr])
      (by norm_num : (0:ℝ) ≤ 3/10) hx0.le
    dsimp only [A]
    norm_num at hh
    exact hh
  have he : Real.exp (-A) ≤ (1/3000:ℝ) := by
    have hE : (3000:ℝ) ≤ Real.exp A := by linarith only [hA,Real.add_one_le_exp A]
    simpa only [Real.exp_neg,one_div] using!
      one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3000) hE
  have hratio : a*Real.exp (-A) ≤ (1/1000:ℝ) := by
    have hh := mul_le_mul ha3 he (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 3)
    norm_num at hh
    exact hh
  have hmajor (n : ℕ) : a^n*Real.exp (-x*r^n) ≤ Real.exp (-x)*(1/1000:ℝ)^n := by
    have hb := one_add_mul_sub_le_pow hr0 n
    have hex : -x*r^n ≤ -x+(n:ℝ)*(-A) := by
      have hh := mul_le_mul_of_nonneg_left hb hx0.le
      dsimp only [A]
      nlinarith only [hh]
    calc
      _ ≤ a^n*Real.exp (-x+(n:ℝ)*(-A)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) (pow_nonneg ha n)
      _ = Real.exp (-x)*(a*Real.exp (-A))^n := by
        rw [Real.exp_add,Real.exp_nat_mul,mul_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg ha (Real.exp_pos _).le) hratio n) (Real.exp_pos _).le
  have hg := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/1000:ℝ)‖ < 1)).mul_left
    (Real.exp (-x))
  have hs := hg.summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg ha n) (Real.exp_pos _).le) hmajor
  refine ⟨hs,(hs.tsum_le_tsum hmajor hg.summable).trans_eq ?_⟩
  rw [hg.tsum_eq]
  norm_num
  ring

/-- The literal first clock moment is bounded without dropping its z+n
factor; doubling the consecutive clock ratio pays it completely. -/
theorem selected_linear_clock_series (a x r z : ℝ) (ha : 0 ≤ a) (ha3 : 2*a ≤ 3)
    (hx : 10000 ≤ x) (hr : 13/10 ≤ r) (hz : 1 ≤ z) :
    Summable (fun n : ℕ => (z+n)*a^n*Real.exp (-x*r^n)) ∧
      (∑' n : ℕ, (z+n)*a^n*Real.exp (-x*r^n)) ≤ z*(1000/999)*Real.exp (-x) := by
  have hbase := selected_clock_series (2*a) x r (by positivity) ha3 hx hr
  have hmajor (n : ℕ) : (z+n)*a^n*Real.exp (-x*r^n) ≤ z*((2*a)^n*Real.exp (-x*r^n)) := by
    have hpow : (1:ℝ)+(n:ℝ) ≤ (2:ℝ)^n := by
      have hh := one_add_mul_le_pow (a := (1:ℝ)) (by norm_num) n
      norm_num at hh
      exact hh
    have hz0 : 0 ≤ z := le_trans (by norm_num) hz
    have hn := mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg n)
    have hh := mul_le_mul_of_nonneg_left hpow hz0
    have hlin : z+n ≤ z*(2:ℝ)^n := by nlinarith only [hn,hh]
    have hm := mul_le_mul_of_nonneg_right hlin
      (mul_nonneg (pow_nonneg ha n) (Real.exp_pos (-x*r^n)).le)
    simpa only [mul_pow,mul_assoc] using! hm
  have hz0 : 0 ≤ z := le_trans (by norm_num) hz
  have hm := hbase.1.mul_left z
  have hs := hm.of_nonneg_of_le (fun n => by positivity) hmajor
  refine ⟨hs,(hs.tsum_le_tsum hmajor hm).trans ?_⟩
  rw [tsum_mul_left]
  have hh := mul_le_mul_of_nonneg_left hbase.2 hz0
  simpa only [mul_assoc] using! hh

end
end ASDExplicitGamma.Inverse

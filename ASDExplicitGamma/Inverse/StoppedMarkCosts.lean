module

public import ASDExplicitGamma.Inverse.StoppedPositiveTilt
public import ASDExplicitGamma.Numerics.Mirror.GridExp

/-! Conservative exponential costs retaining the source marked-path radius constants. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- A rational kernel certificate for the local-mark tilt at twenty. -/
theorem exp_twenty_le : Real.exp 20 ≤ (1000000000:ℝ) := by
  have hc : Numerics.Mirror.expPointUpper 4 25 20 ≤ (1000000000:ℚ) := by decide +kernel
  have he := (Numerics.Mirror.expPoint_bounds 4 25 (q := 20) (by decide) (by norm_num) (by norm_num)).2
  exact he.trans (by exact_mod_cast hc)

/-- This deliberately relaxed local cost still leaves the source radius margin
when all 8^n routes are counted, instead of only the induced ones. -/
theorem local_mark_tilt_cost (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000) :
    q*(Real.exp 20-1) ≤ 1/10 := by
  calc
    _ ≤ q*1000000000 := mul_le_mul_of_nonneg_left
      (by linarith only [exp_twenty_le] : Real.exp 20-1 ≤ 1000000000) hq0
    _ ≤ (1/10000000000:ℝ)*1000000000 := mul_le_mul_of_nonneg_right hq (by norm_num)
    _ = _ := by norm_num

/-- The actual rate-1200 activation tail easily absorbs the full nine-color
tilt. Only a degree-two exponential lower bound is needed for this budget. -/
theorem positive_mark_tilt_cost (s z t : ℝ) (hs : 3 ≤ s) (hz : 0 ≤ z) (hzsq : z^2 = s)
    (ht : t ≤ 123*s*z) :
    s^2*Real.exp (-1200*s*z)*(Real.exp t-1) ≤ 1/10 := by
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs
  have hx : 0 ≤ 1077*s*z := by positivity
  have he := Real.sum_le_exp_of_nonneg hx 3
  have hpoly : (1077*s*z)^2 = 1077^2*s^3 := by rw [mul_pow,mul_pow,hzsq]; ring
  have hcube : 3*s^2 ≤ s^3 := by
    have hh := mul_le_mul_of_nonneg_right hs (sq_nonneg s)
    nlinarith only [hh]
  have hlarge : 10*s^2 ≤ Real.exp (1077*s*z) := by
    norm_num [Finset.sum_range_succ,Nat.factorial] at he
    nlinarith only [he,hpoly,hcube,sq_nonneg s,hx]
  have hcost : s^2*Real.exp (-(1077*s*z)) ≤ 1/10 := by
    rw [Real.exp_neg]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith only [hlarge]
  calc
    _ ≤ s^2*Real.exp (-1200*s*z)*Real.exp (123*s*z) :=
      mul_le_mul_of_nonneg_left ((sub_le_self _ (by norm_num : (0:ℝ) ≤ 1)).trans
        (Real.exp_le_exp.mpr ht)) (by positivity)
    _ = s^2*Real.exp (-(1077*s*z)) := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
    _ ≤ _ := hcost

end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Inverse.FullResponseSelectedTailNumerics

/-! Tiny full-row selected root-clock tails at orders 64 and 128. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The norm of the complete first root-tail majorant is uniformly tiny
on the two certified orders and the interval between them. -/
theorem full_response_root_tail_norm_tiny (γ p : ℝ) (hg : γ ≤ gammaZero)
    (hp : 64 ≤ p) (hp128 : p ≤ 128) :
    (selectedRootMomentBudget γ p 377)^(1/p:ℝ) ≤ (1/10^100:ℝ) := by
  have hp0 : 0 < p := by linarith only [hp]
  have hip : 1/p ≤ 1 := (div_le_one hp0).mpr (by linarith only [hp])
  have hclock : (3:ℝ)^(2*γ*351) ≤ 3 := by
    have he : 2*γ*351 ≤ 1 := by change γ ≤ 17/50000 at hg; linarith only [hg]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) he
  have hcoef : (1000/999:ℝ)^(1/p:ℝ) ≤ 2 :=
    (Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ) ≤ 1000/999) hip).trans (by norm_num)
  have hfactor : (selectedRootMomentBudget γ p 377)^(1/p:ℝ) =
      (1000/999:ℝ)^(1/p:ℝ)*(3:ℝ)^(2*γ*351)*Real.exp (-(3^57/32:ℝ)/p) := by
    unfold selectedRootMomentBudget
    rw [show selectedFirstClock 377=351 by norm_num [selectedFirstClock]]
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le,
      Real.mul_rpow (by norm_num) (by positivity),← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
      ← Real.exp_mul]
    have hpowe : (2*p*γ*351)*(1/p)=2*γ*351 := by field_simp [hp0.ne']
    have hexpe : (-heightExponent (377+11)/32)*(1/p)=-(3^57/32:ℝ)/p := by
      rw [show -heightExponent (377+11)/32=-(heightExponent (377+11)/32) by ring,
        full_response_first_tail_argument]
      ring
    rw [hpowe,hexpe]
  have hden : (3^57/32:ℝ)/128 ≤ (3^57/32:ℝ)/p :=
    div_le_div_of_nonneg_left (by positivity) hp0 hp128
  have ht := inv_exp_neg_factorial_bound ((3^57/32:ℝ)/128) (by norm_num) 8
  have he := (Real.exp_le_exp.mpr (neg_le_neg hden)).trans ht
  rw [← neg_div] at he
  rw [hfactor]
  calc
    _ ≤ (2:ℝ)*3*((Nat.factorial 8:ℝ)/((3^57/32:ℝ)/128)^8) :=
      mul_le_mul (mul_le_mul hcoef hclock (by positivity) (by norm_num)) he (Real.exp_pos _).le (by norm_num)
    _ ≤ _ := by norm_num

/-- The exact complete selected Jp is the bounded-height clock plus a
10^-100 tail at the finite full-response orders. -/
theorem full_response_selected_Jp_le (γ p : ℝ) (hg : γ ≤ gammaZero)
    (hp : 64 ≤ p) (hp128 : p ≤ 128) :
    selectedJp γ p 377 ≤ (3:ℝ)^(2*γ*350)+(1/10^100:ℝ) := by
  have hp0 : 0 < p := by linarith only [hp]
  have ht0 : 0 ≤ selectedRootExactMoment γ p 377 := by
    unfold selectedRootExactMoment
    apply tsum_nonneg
    intro n
    unfold selectedTailProbability
    positivity
  have ht := (selected_root_tail_series γ p hg hp0 (by linarith only [hp128]) 377 (by norm_num)).2
  change selectedRootExactMoment γ p 377 ≤ selectedRootMomentBudget γ p 377 at ht
  have htail := (Real.rpow_le_rpow ht0 ht (by positivity : (0:ℝ) ≤ 1/p)).trans
    (full_response_root_tail_norm_tiny γ p hg hp hp128)
  unfold selectedJp
  have hh := Real.rpow_add_le_add_rpow
    (by positivity : (0:ℝ) ≤ (3:ℝ)^(2*p*γ*((377:ℝ)-27))) ht0
    (by positivity : (0:ℝ) ≤ 1/p) ((div_le_one hp0).mpr (by linarith only [hp]))
  have he : ((3:ℝ)^(2*p*γ*((377:ℝ)-27)))^(1/p:ℝ)=(3:ℝ)^(2*γ*350) := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    field_simp [hp0.ne']
    ring
  rw [he] at hh
  exact hh.trans (add_le_add le_rfl htail)

end
end ASDExplicitGamma.Inverse

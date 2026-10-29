module

public import ASDExplicitGamma.Inverse.FullResponseHistoryExports
public import ASDExplicitGamma.Numerics.Inverse.RealBounds

/-! Complete full64 future-history envelopes, including every tail and first
history moment. The p64 factors are also valid for the separate p128 row. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Inverse ASDExplicitGamma.Inverse
noncomputable section

/-- The outward endpoint ratio for the full trace history. -/
def nativeFullResponseHistoryRatio : ℝ :=
  (invHistoryRoot:ℝ)*(invE (22/5*invGamma):ℝ)

/-- Both signs of the complete geometric ratio gate, without truncation. -/
theorem native_full_response_history_ratio_gate :
    0 ≤ nativeFullResponseHistoryRatio ∧ nativeFullResponseHistoryRatio < 1 := by
  constructor
  · change (0:ℝ) ≤ (invHistoryRoot:ℝ)*(invE (22/5*invGamma):ℝ)
    exact_mod_cast (show (0:ℚ) ≤ invHistoryRoot*invE (22/5*invGamma) by decide +kernel)
  · have hh := full_response_history_factor_caps.1
    change nativeFullResponseHistoryRatio < 1
    dsimp only [nativeFullResponseHistoryRatio]
    linarith only [hh]

/-- Exact complete tail of a positive affine profile under a geometric weight.
No finite-depth tail is discarded. -/
theorem native_full_response_affine_tail_hasSum (a R A B : ℝ) (J : ℕ)
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    HasSum (fun j : ℕ => (1-a)*R^(J+j)*(A+B*((J+j:ℕ):ℝ)))
      (R^J*((A+B*(J:ℝ))*((1-a)/(1-R))+B*((1-a)*R/(1-R)^2))) := by
  have hg := hasSum_geometric_of_lt_one hR0 hR1
  have hj := hasSum_coe_mul_geometric_of_norm_lt_one
    (show ‖R‖ < 1 by rwa [Real.norm_eq_abs,abs_of_nonneg hR0])
  convert! (((hg.mul_left (A+B*(J:ℝ))).add (hj.mul_left B)).mul_left ((1-a)*R^J)) using 1
  · ext j
    rw [pow_add,Nat.cast_add]
    ring
  · simp only [div_eq_mul_inv]
    ring

/-- The complete endpoint full64 history tail in the literal certified S0,S1
form. This identity covers every future depth J, including J=0. -/
theorem native_full_response_history_tail_hasSum (A B : ℝ) (J : ℕ) :
    HasSum (fun j : ℕ => (1-(invAlphaLower:ℝ))*nativeFullResponseHistoryRatio^(J+j)*
      (A+B*((J+j:ℕ):ℝ)))
      (nativeFullResponseHistoryRatio^J*
        ((A+B*(J:ℝ))*(invS0:ℝ)+B*(invS1:ℝ))) := by
  have hh := native_full_response_affine_tail_hasSum (invAlphaLower:ℝ)
    nativeFullResponseHistoryRatio A B J native_full_response_history_ratio_gate.1
      native_full_response_history_ratio_gate.2
  convert hh using 1
  simp only [invS0,invS1,Rat.cast_div,Rat.cast_sub,Rat.cast_one,Rat.cast_mul,Rat.cast_pow,
    nativeFullResponseHistoryRatio]

end
end ASDExplicitGamma.Native

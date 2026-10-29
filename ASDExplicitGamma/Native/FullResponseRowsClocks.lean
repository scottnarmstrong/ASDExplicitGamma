module

public import ASDExplicitGamma.Native.FullResponseRowsHistory

/-! Physical full64 history clocks are bounded by the certified complete
geometric envelopes, with their dimension-two population root retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The exact dimension-two p64 population/history root is bounded by the
certificate's fixed outward bracket. -/
theorem native_full_response_population_root :
    (3:ℝ)^(-(7/32:ℝ)) ≤ (invHistoryRoot:ℝ) := by
  have hh := inv_root_upper (x := 1/3^7) (u := invHistoryRoot)
    (by norm_num) invHistoryRoot_bracket.1.le (by norm_num : 32 ≠ 0)
    invHistoryRoot_bracket.2
  have he : (((1/3^7:ℚ):ℝ)^((32:ℝ)⁻¹)) = (3:ℝ)^(-(7/32:ℝ)) := by
    have hp : (((1/3^7:ℚ):ℝ)) = (3:ℝ)^(-(7:ℝ)) := by norm_num
    rw [hp,← Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
    norm_num
  norm_num only [Nat.cast_ofNat] at hh
  norm_num at he
  rw [he] at hh
  exact hh.le

/-- Every smaller-gamma true full-history ratio fits the same endpoint ratio. -/
theorem native_full_response_physical_history_ratio_le (γ : ℝ)
    (hγ : 0 ≤ γ) (hg : γ ≤ 17/50000) :
    (3:ℝ)^(-(7/32:ℝ)+4*γ) ≤ nativeFullResponseHistoryRatio := by
  have hc := inv_three_power_bound (4*γ) (by positivity) (by linarith only [hg])
  have hden : (0:ℝ) < 1-(11/10)*(4*γ) := by linarith only [hg]
  have hb : 1/(1-(11/10)*(4*γ)) ≤ (invE (22/5*invGamma):ℝ) := by
    norm_num [invE,invGamma]
    rw [← one_div,div_le_iff₀ hden]
    linarith only [hg]
  rw [Real.rpow_add (by norm_num : (0:ℝ)<3)]
  exact mul_le_mul native_full_response_population_root (hc.trans hb)
    (Real.rpow_nonneg (by norm_num) _) (by norm_num [invHistoryRoot])

/-- The exact normalized history prefactor has the expected positive
outward bracket. -/
theorem native_full_response_history_prefactor :
    0 ≤ 1-(3:ℝ)^(-(1/4:ℝ)) ∧
      1-(3:ℝ)^(-(1/4:ℝ)) ≤ 1-(invAlphaLower:ℝ) := by
  have hα : (invAlphaLower:ℝ) ≤ (3:ℝ)^(-(1/4:ℝ)) := by
    have hh := inv_alpha_real.1.le
    have he : (1/3:ℝ)^(1/4:ℝ) = (3:ℝ)^(-(1/4:ℝ)) := by
      rw [show -(1/4:ℝ)=(-1)*(1/4:ℝ) by ring,Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
      norm_num
    rwa [he] at hh
  have ht : (3:ℝ)^(-(1/4:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by norm_num) (by norm_num)
  exact ⟨sub_nonneg.mpr ht,sub_le_sub_left hα _⟩

/-- The physical future-history tail is genuinely summable at every depth;
its real tsum bound therefore cannot hide a divergent positive series. -/
theorem native_full_response_physical_history_tail_summable (γ A B : ℝ) (J : ℕ)
    (hγ : 0 ≤ γ) (hg : γ ≤ 17/50000) :
    Summable (fun j : ℕ => (1-(3:ℝ)^(-(1/4:ℝ)))*
      ((3:ℝ)^(-(7/32:ℝ)+4*γ))^(J+j)*(A+B*((J+j:ℕ):ℝ))) := by
  exact (native_full_response_affine_tail_hasSum ((3:ℝ)^(-(1/4:ℝ)))
    ((3:ℝ)^(-(7/32:ℝ)+4*γ)) A B J (Real.rpow_nonneg (by norm_num) _)
    ((native_full_response_physical_history_ratio_le γ hγ hg).trans_lt
      native_full_response_history_ratio_gate.2)).summable

/-- All physical future-history tails, including the depth moment, are paid
by the literal S0/S1 envelope. -/
theorem native_full_response_physical_history_tail_le (γ A B : ℝ) (J : ℕ)
    (hγ : 0 ≤ γ) (hg : γ ≤ 17/50000) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∑' j : ℕ, (1-(3:ℝ)^(-(1/4:ℝ)))*
      ((3:ℝ)^(-(7/32:ℝ)+4*γ))^(J+j)*(A+B*((J+j:ℕ):ℝ))) ≤
      nativeFullResponseHistoryRatio^J*((A+B*(J:ℝ))*(invS0:ℝ)+B*(invS1:ℝ)) := by
  let f := fun j : ℕ => (1-(3:ℝ)^(-(1/4:ℝ)))*
    ((3:ℝ)^(-(7/32:ℝ)+4*γ))^(J+j)*(A+B*((J+j:ℕ):ℝ))
  let g := fun j : ℕ => (1-(invAlphaLower:ℝ))*nativeFullResponseHistoryRatio^(J+j)*
    (A+B*((J+j:ℕ):ℝ))
  have hs := native_full_response_history_tail_hasSum A B J
  have hf0 (j : ℕ) : 0 ≤ f j := by
    exact mul_nonneg (mul_nonneg native_full_response_history_prefactor.1
      (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)) (by positivity)
  have hfg (j : ℕ) : f j ≤ g j := by
    apply mul_le_mul_of_nonneg_right _ (by positivity : 0≤A+B*((J+j:ℕ):ℝ))
    exact mul_le_mul native_full_response_history_prefactor.2
      (pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
        (native_full_response_physical_history_ratio_le γ hγ hg) _)
      (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
      (native_full_response_history_prefactor.1.trans native_full_response_history_prefactor.2)
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hfg hs.summable
  exact (hf.tsum_le_tsum hfg hs.summable).trans_eq hs.tsum_eq

end
end ASDExplicitGamma.Native

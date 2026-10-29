module

public import ASDExplicitGamma.Numerics.AllOrder.Profile
public import ASDExplicitGamma.Numerics.AllOrder.GeometricMoments
public import ASDExplicitGamma.Numerics.Scalar.Frames
public import Mathlib.Algebra.Order.Floor.Ring

/-! Exact bulk, rare-rate, transfer and frame allocations from E5 and the two 340 producers. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.AllOrder
open Mirror Scalar

/-- NU-AO-BULK-HISTORY: separate complete bulk and rare-polynomial allocations. -/
theorem bulk_history_allocations :
    ((333/2)*900000+72*4350000 : ℚ) = 463050000 ∧
    (463050000 : ℕ) < 2^29 ∧
    (3*64*((3/2)+6+16+(64/3)) : ℚ) = 8608 ∧
    (8608 : ℕ) < 2^14 ∧ (2^14/8^3 : ℚ) = 32 := by
  decide +kernel

/-- NU-AO-RARE-RATES: preserve the successful 1350 hierarchy rather than the failed 1400 splice. -/
theorem rare_rate_margins :
    ((69/100)*(1/32-1/64)-11*(17/50000) : ℚ) = 5633/800000 ∧
    (0 : ℚ) < 5633/800000 ∧
    ((69/100)*(1/64-1/1350)-(17/50000)*((7/2)+3*(163/20)) : ℚ) = 27617/36000000 ∧
    (0 : ℚ) < 27617/36000000 ∧
    ((69/100)*(1/2700-1/8192)-(17/50000)/2 : ℚ) = 1223/921600000 ∧
    (0 : ℚ) < 1223/921600000 ∧
    (32 : ℕ) < 64 ∧ (64 : ℕ) < 1350 ∧ (1350 : ℕ) < 1500 ∧
    (1350 : ℕ) < 8192 ∧ (3*2^29 : ℕ) = 1610612736 ∧ (1610612736 : ℕ) < 2^32 := by
  decide +kernel

theorem log_two_gt_69 : (69/100 : ℝ) < Real.log 2 := by
  linarith only [log_two_enclosure.1]

theorem source_bulk_root : Real.sqrt (Real.exp 1*2^29) < (2^16 : ℝ) := by
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2^16)).mpr
  have h := mul_lt_mul_of_pos_right Real.exp_one_lt_three (by norm_num : (0 : ℝ) < 2^29)
  linarith only [h]

/-- NU-AO-TRANSFER-GATES: all deterministic allocation precursors. -/
theorem transfer_rational_gates :
    (4340722.72 : ℚ) < 4350000 ∧ (1161645 : ℚ) < min 4350000 2700000 ∧
    (1468000 : ℚ) < 1800000 ∧ (1466148 : ℚ) < 2700000 ∧
    (8*1.812 : ℚ) < 15 ∧
    (4*2810*22*1.812 : ℚ) = 448071.36 ∧ (448071.36 : ℚ) < 449000 ∧
    (4*2810*1.812 : ℚ) = 20366.88 ∧ (20366.88 : ℚ) < 20367 ∧
    (4*(2+2810*0.14)*1.812 : ℚ) < 2866 ∧
    (20*(1/327680) : ℚ) = 1/16384 ∧
    ((9/10)*(1/16384) : ℚ) > 1/19000 := by
  decide +kernel

/-- The real-order seed is quantitatively positive for every γ>0, without an endpoint scan. -/
theorem seed_order_gates (gamma : ℝ) (hg : 0 < gamma) :
    let P := max 20 (2*(⌊(1/16384 : ℝ)/(2*gamma)⌋ : ℝ))
    gamma*P > 1/19000 ∧ 48 ≤ 4*P := by
  let P := max 20 (2*(⌊(1/16384 : ℝ)/(2*gamma)⌋ : ℝ))
  have hP : (20 : ℝ) ≤ P := le_max_left _ _
  have hPf : 2*(⌊(1/16384 : ℝ)/(2*gamma)⌋ : ℝ) ≤ P := le_max_right _ _
  constructor
  · by_cases hsmall : gamma ≤ 1/327680
    · have hf := Int.sub_one_lt_floor ((1/16384 : ℝ)/(2*gamma))
      have hm := mul_lt_mul_of_pos_left hf (by linarith only [hg] : 0 < 2*gamma)
      rw [mul_sub, mul_div_cancel₀ _ (by linarith only [hg] : (2*gamma : ℝ) ≠ 0), mul_one] at hm
      have hmul := mul_le_mul_of_nonneg_left hPf hg.le
      linarith only [hm,hmul,hsmall]
    · have hmul := mul_le_mul_of_nonneg_left hP hg.le
      linarith only [hmul, hsmall]
  · linarith only [hP]

/-- Exact exp bracket used only to prove log(50000/17)<163/20. -/
theorem transfer_exp_kernel_check :
    (50000/17 : ℚ) < expPointLower 32 25 (163/20) := by
  decide +kernel

theorem transfer_log_gates :
    Real.exp 1 < (3 : ℝ) ∧ Real.log 3 < (11/10 : ℝ) ∧
    Real.log 32 < (7/2 : ℝ) ∧ Real.log (50000/17) < (163/20 : ℝ) := by
  refine ⟨Real.exp_one_lt_three, log_three_small.2, ?_, ?_⟩
  · rw [show (32 : ℝ) = (2 : ℝ)^5 by norm_num, Real.log_pow]
    linarith only [log_two_enclosure.2]
  · apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 50000/17)).mpr
    have he := (expPoint_bounds 32 25 (q := (163/20 : ℚ)) (by decide) (by norm_num) (by norm_num)).1
    have hl : ((50000/17 : ℚ) : ℝ) < (expPointLower 32 25 (163/20) : ℝ) :=
      (Rat.cast_lt (K := ℝ)).mpr transfer_exp_kernel_check
    norm_num at he hl
    exact hl.trans_le he

/-- NU-AO-FRAME-GATES: reuse the scalar frame exports and preserve the corrected upper factor. -/
theorem allorder_frame_gates :
    (65/22 : ℝ) < 3 ∧ (1+(13/8)*(1251/1250) : ℝ) = 26263/10000 ∧
    (26263/10000 : ℝ) < 3 ∧
    (3 : ℝ)^(2*(17/50000 : ℝ)) ≤ 1/(1-(11/5)*(17/50000)) ∧
    (1/(1-(11/5)*(17/50000)) : ℝ) < 1.0008 ∧
    (9/2 : ℝ)*(49/100) > 2*Real.log 3 := by
  have h := one_shell_factor
  have h1 : (3 : ℝ)^(2*(17/50000 : ℝ)) ≤ 1/(1-(11/5)*(17/50000)) := by
    linarith only [h.1]
  exact ⟨frame_ratio_constants.1, by norm_num, by norm_num, h1, by norm_num,
    lower_clock_margins.2⟩

end ASDExplicitGamma.Numerics.AllOrder

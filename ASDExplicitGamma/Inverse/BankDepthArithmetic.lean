module

public import ASDExplicitGamma.Inverse.BankInverseProfiles

/-! Exact depth scaling of the source inverse-bank majorants. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal

noncomputable def bankDepthFrame (M : ABKModel 2) (j : ℕ) : ℝ :=
  (3:ℝ)^(2*M.gamma*(j:ℝ))

noncomputable def bankDepthPopulation (j : ℕ) : ℝ := (9:ℝ)^((j:ℝ)/256)

noncomputable def inverseBankDepthA (r : InverseBankRow) (M : ABKModel 2) (j : ℕ) : ℝ :=
  (inverseBankA r:ℝ)*bankDepthFrame M j

noncomputable def inverseBankDepthE (r : InverseBankRow) (M : ABKModel 2) (j : ℕ) : ℝ :=
  (inverseBankE r:ℝ)*bankDepthFrame M j*bankDepthPopulation j

noncomputable def inverseBankDepthSlack (M : ABKModel 2) (j : ℕ) : ℝ :=
  (1/2000:ℝ)*bankDepthFrame M j

noncomputable def inverseBankDepthReserve (r : InverseBankRow) (M : ABKModel 2) (j : ℕ) : ℝ :=
  (inverseBankReserve r:ℝ)*bankDepthFrame M j*(9:ℝ)^((j:ℝ)/128)

noncomputable def inverseBankRootErrorCap (r : InverseBankRow) : ℝ≥0∞ :=
  ENNReal.ofReal (invE (11/5*invGamma):ℝ) * ENNReal.ofReal (invE (11*invGamma):ℝ) *
    ENNReal.ofReal (inverseBankRho r:ℝ)*ENNReal.ofReal (invSR:ℝ)

theorem inverse_bank_baseline_ofReal (r : InverseBankRow) :
    ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
      ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal (inverseBankLi r:ℝ) *
      ENNReal.ofReal (invE (11/5*invGamma*inverseBankHeight r):ℝ) *
      ENNReal.ofReal (invSB:ℝ) = ENNReal.ofReal (inverseBankA r:ℝ) := by
  rcases inverse_bank_profile_nonneg r with ⟨_,_,hLi0,_,hHeight0⟩
  have hf0 : 0 ≤ (invE (11/5*invGamma):ℝ) := by norm_num [invE,invGamma]
  have hg0 : 0 ≤ (invE (11*invGamma):ℝ) := by norm_num [invE,invGamma]
  rw [(inverse_bank_source_formulas r).1]
  simp only [Rat.cast_mul]
  repeat rw [ENNReal.ofReal_mul (by positivity)]

theorem inverse_bank_remainder_ofReal (r : InverseBankRow) :
    (ENNReal.ofReal (509/500:ℝ)*ENNReal.ofReal (invPopulationRoot:ℝ)) *
      inverseBankRootErrorCap r = ENNReal.ofReal (inverseBankE r:ℝ) := by
  have hrho := (inverse_bank_profile_nonneg r).2.2.2.1
  have hf0 : 0 ≤ (invE (11/5*invGamma):ℝ) := by norm_num [invE,invGamma]
  have hg0 : 0 ≤ (invE (11*invGamma):ℝ) := by norm_num [invE,invGamma]
  have hp0 : 0 ≤ (invPopulationRoot:ℝ) := by norm_num [invPopulationRoot]
  have heq : ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
      ENNReal.ofReal (509/500:ℝ) * ENNReal.ofReal (invE (11*invGamma):ℝ) *
      ENNReal.ofReal (invPopulationRoot:ℝ) * ENNReal.ofReal (inverseBankRho r:ℝ) *
      ENNReal.ofReal (invSR:ℝ) = ENNReal.ofReal (inverseBankE r:ℝ) := by
    rw [(inverse_bank_source_formulas r).2]
    simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat]
    repeat rw [ENNReal.ofReal_mul (by positivity)]
  rw [← heq]
  unfold inverseBankRootErrorCap
  ac_rfl

theorem inverse_bank_root_baseline_cap (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m : ℤ) (r : InverseBankRow)
    (hQ : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) :
    bankRootInverseBaselineHistory Q M m (inverseBankRootRow r) ≤ ENNReal.ofReal (inverseBankA r:ℝ) :=
  (bank_offset_baseline_profile_cap M Q Q.scale m (inverseBankRootRow r)
    (inverseBankLi r:ℝ) (invE (11/5*invGamma*inverseBankHeight r):ℝ)
    rfl hQ hgap hg (inverse_bank_Li_bound M hg r) (inverse_bank_height_bound M hg r)).trans_eq
      (inverse_bank_baseline_ofReal r)

theorem inverse_bank_root_remainder_budget_cap (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m : ℤ) (r : InverseBankRow)
    (hQ : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) :
    bankRootInverseRemainderHistoryL256Bound M Q m (inverseBankRootRow r) ≤ inverseBankRootErrorCap r :=
  bank_offset_remainder_profile_cap M Q Q.scale m (inverseBankRootRow r)
    (inverseBankRho r:ℝ) rfl hQ hgap hg (inverse_bank_error_bound M hg r)

theorem inverse_bank_depth_baseline_cap (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m : ℤ) (j : ℕ) (r : InverseBankRow)
    (hQ : Q.scale ≤ m-(j:ℤ)) (hgap : (m-(j:ℤ))-Q.scale ≤ 5) :
    bankRootInverseBaselineHistory Q M m (inverseBankRootRow r) ≤ ENNReal.ofReal (inverseBankDepthA r M j) := by
  have hs := bank_root_inverse_baseline_history_frame_shift M Q (m-(j:ℤ)) m
    (inverseBankRootRow r) hQ (by omega)
  have hd : m-(m-(j:ℤ)) = (j:ℤ) := by omega
  rw [hd, Int.cast_natCast] at hs
  rw [hs]
  have hb := inverse_bank_root_baseline_cap M hg Q (m-(j:ℤ)) r hQ hgap
  calc
    _ ≤ ENNReal.ofReal (bankDepthFrame M j)*ENNReal.ofReal (inverseBankA r:ℝ) :=
      mul_le_mul_of_nonneg_left hb bot_le
    _ = _ := by
      rw [inverseBankDepthA, ENNReal.ofReal_mul (inverse_bank_profile_nonneg r).1]
      exact mul_comm _ _

theorem inverse_bank_depth_remainder_budget_cap (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m : ℤ) (j : ℕ) (r : InverseBankRow)
    (hQ : Q.scale ≤ m-(j:ℤ)) (hgap : (m-(j:ℤ))-Q.scale ≤ 5) :
    bankRootInverseRemainderHistoryL256Bound M Q m (inverseBankRootRow r) ≤
      ENNReal.ofReal (bankDepthFrame M j)*inverseBankRootErrorCap r := by
  have hs := bank_root_inverse_remainder_history_budget_frame_shift M Q (m-(j:ℤ)) m
    (inverseBankRootRow r) hQ (by omega)
  have hd : m-(m-(j:ℤ)) = (j:ℤ) := by omega
  rw [hd, Int.cast_natCast] at hs
  rw [hs]
  exact mul_le_mul_of_nonneg_left
    (inverse_bank_root_remainder_budget_cap M hg Q (m-(j:ℤ)) r hQ hgap) bot_le

theorem bank_root_population_payment_depth (n j : ℕ) (hn : n ≤ 6*9^(45+j)) :
    (n:ℝ≥0∞)^(1/256:ℝ) ≤
      (ENNReal.ofReal (509/500:ℝ)*ENNReal.ofReal (invPopulationRoot:ℝ)) *
        (9:ℝ≥0∞)^((j:ℝ)/256) := by
  have hn' : n ≤ (6*9^45)*9^j := by simpa only [pow_add, mul_assoc] using hn
  have hcard : (n:ℝ≥0∞) ≤ (6*9^45:ℝ≥0∞)*(9:ℝ≥0∞)^j := by exact_mod_cast hn'
  have hh := ENNReal.rpow_le_rpow hcard (by norm_num : (0:ℝ) ≤ 1/256)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/256)] at hh
  have he : ((9:ℝ≥0∞)^j)^(1/256:ℝ) = (9:ℝ≥0∞)^((j:ℝ)/256) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    ring
  rw [he] at hh
  have hpay : (6*9^45:ℝ≥0∞)^(1/256:ℝ) ≤
      ENNReal.ofReal (509/500:ℝ)*ENNReal.ofReal (invPopulationRoot:ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      bank_root_population_payment (6*9^45) le_rfl
  exact hh.trans (mul_le_mul_of_nonneg_right hpay bot_le)

theorem bankDepthFrame_pos (M : ABKModel 2) (j : ℕ) : 0 < bankDepthFrame M j := by
  unfold bankDepthFrame
  positivity

theorem inverse_bank_depth_E_ofReal (r : InverseBankRow) (M : ABKModel 2) (j : ℕ) :
    ENNReal.ofReal (inverseBankE r:ℝ)*ENNReal.ofReal (bankDepthFrame M j)*
      (9:ℝ≥0∞)^((j:ℝ)/256) = ENNReal.ofReal (inverseBankDepthE r M j) := by
  have he := (inverse_bank_profile_nonneg r).2.1
  have hc := (bankDepthFrame_pos M j).le
  rw [inverseBankDepthE, ENNReal.ofReal_mul (mul_nonneg he hc), ENNReal.ofReal_mul he,
    bankDepthPopulation, ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ) < 9)]
  norm_num

theorem inverse_bank_depth_nonneg (r : InverseBankRow) (M : ABKModel 2) (j : ℕ) :
    0 ≤ inverseBankDepthA r M j ∧ 0 ≤ inverseBankDepthE r M j ∧
      0 < inverseBankDepthSlack M j := by
  have hA := (inverse_bank_profile_nonneg r).1
  have he := (inverse_bank_profile_nonneg r).2.1
  have hc := bankDepthFrame_pos M j
  have hp : 0 ≤ bankDepthPopulation j := by unfold bankDepthPopulation; positivity
  exact ⟨mul_nonneg hA hc.le, mul_nonneg (mul_nonneg he hc.le) hp,
    mul_pos (by norm_num : (0:ℝ) < 1/2000) hc⟩

private theorem bank_depth_quadratic_cancel (e c v : ℝ) (hc : c ≠ 0) :
    (e*c*v)^2/(4*((1/2000:ℝ)*c)) = e^2/(4*(1/2000:ℝ))*c*v^2 := by
  field_simp [hc]

theorem inverse_bank_depth_profile_bounds (r : InverseBankRow) (M : ABKModel 2) (j : ℕ) :
    inverseBankDepthA r M j+inverseBankDepthSlack M j ≤
        (inverseBankCap r:ℝ)*bankDepthFrame M j ∧
      (inverseBankDepthE r M j)^2/(4*inverseBankDepthSlack M j) ≤
        inverseBankDepthReserve r M j := by
  have hc := bankDepthFrame_pos M j
  have hnum := inverse_bank_numeric_bounds r
  have hpop : bankDepthPopulation j ^ 2 = (9:ℝ)^((j:ℝ)/128) := by
    unfold bankDepthPopulation
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 9)]
    congr 1
    ring
  constructor
  · unfold inverseBankDepthA inverseBankDepthSlack
    calc
      _ = ((inverseBankA r:ℝ)+1/2000)*bankDepthFrame M j := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hnum.2.1.le hc.le
  · unfold inverseBankDepthE inverseBankDepthSlack inverseBankDepthReserve
    rw [bank_depth_quadratic_cancel _ _ _ hc.ne', hpop]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hnum.2.2.le hc.le) (by positivity)

theorem bank_root_frame_factor_cap (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m : ℤ) (hQ : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) :
    bankRootFrameFactor M Q m ≤ ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
      ENNReal.ofReal (invE (11*invGamma):ℝ) := by
  have hs := bank_root_frame_factor_shift M Q Q.scale m le_rfl hQ
  have hself : bankRootFrameFactor M Q Q.scale = ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) := by
    simp only [bankRootFrameFactor, sub_self, zero_add, Int.cast_one, abs_one, mul_one]
  rw [hs, hself]
  have hg' : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
  calc
    _ ≤ ENNReal.ofReal (invE (11*invGamma):ℝ)*ENNReal.ofReal (invE (11/5*invGamma):ℝ) :=
      mul_le_mul (bank_frame_shift_le M Q.scale m hgap hg)
        (ENNReal.ofReal_le_ofReal (bank_history_frame_step_le_invSB_den M.gamma
          M.shellPrefix.gamma_pos.le hg')) bot_le bot_le
    _ = _ := mul_comm _ _

theorem inverse_bank_root_response_baseline_cap (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m : ℤ) (r : InverseBankRow)
    (hQ : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) :
    bankRootResponseBaseline M Q m (inverseBankRootRow r) ≤ ENNReal.ofReal (inverseBankA r:ℝ) := by
  have hLi := ENNReal.ofReal_le_ofReal (inverse_bank_Li_bound M hg r)
  have hH := ENNReal.ofReal_le_ofReal (inverse_bank_height_bound M hg r)
  have hSB : (1:ℝ≥0∞) ≤ ENNReal.ofReal (invSB:ℝ) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    norm_num [invSB, invAlphaLower, invAlphaUpper, invE, invGamma]
  calc
    _ ≤ (ENNReal.ofReal (invE (11/5*invGamma):ℝ)*ENNReal.ofReal (invE (11*invGamma):ℝ))*
        (ENNReal.ofReal (inverseBankLi r:ℝ)*
          ENNReal.ofReal (invE (11/5*invGamma*inverseBankHeight r):ℝ)) :=
      mul_le_mul (bank_root_frame_factor_cap M hg Q m hQ hgap)
        (mul_le_mul hLi hH bot_le bot_le) bot_le bot_le
    _ ≤ ((ENNReal.ofReal (invE (11/5*invGamma):ℝ)*ENNReal.ofReal (invE (11*invGamma):ℝ))*
        (ENNReal.ofReal (inverseBankLi r:ℝ)*
          ENNReal.ofReal (invE (11/5*invGamma*inverseBankHeight r):ℝ)))*ENNReal.ofReal (invSB:ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hSB (by positivity : (0:ℝ≥0∞) ≤ _)
    _ = _ := by rw [← inverse_bank_baseline_ofReal r]; ac_rfl

theorem inverse_bank_depth_response_baseline_cap (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m : ℤ) (j : ℕ) (r : InverseBankRow)
    (hQ : Q.scale ≤ m-(j:ℤ)) (hgap : (m-(j:ℤ))-Q.scale ≤ 5) :
    bankRootResponseBaseline M Q m (inverseBankRootRow r) ≤ ENNReal.ofReal (inverseBankDepthA r M j) := by
  have hs := bank_root_response_baseline_frame_shift M Q (m-(j:ℤ)) m
    (inverseBankRootRow r) hQ (by omega)
  have hd : m-(m-(j:ℤ)) = (j:ℤ) := by omega
  rw [hd, Int.cast_natCast] at hs
  rw [hs]
  calc
    _ ≤ ENNReal.ofReal (bankDepthFrame M j)*ENNReal.ofReal (inverseBankA r:ℝ) :=
      mul_le_mul_of_nonneg_left
        (inverse_bank_root_response_baseline_cap M hg Q (m-(j:ℤ)) r hQ hgap) bot_le
    _ = _ := by
      rw [inverseBankDepthA, ENNReal.ofReal_mul (inverse_bank_profile_nonneg r).1]
      exact mul_comm _ _

theorem bank_root_depth_frame_factor_cap (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m : ℤ) (j : ℕ)
    (hQ : Q.scale ≤ m-(j:ℤ)) (hgap : (m-(j:ℤ))-Q.scale ≤ 5) :
    bankRootFrameFactor M Q m ≤ ENNReal.ofReal (bankDepthFrame M j) *
      (ENNReal.ofReal (invE (11/5*invGamma):ℝ)*ENNReal.ofReal (invE (11*invGamma):ℝ)) := by
  have hs := bank_root_frame_factor_shift M Q (m-(j:ℤ)) m hQ (by omega)
  have hd : m-(m-(j:ℤ)) = (j:ℤ) := by omega
  rw [hd, Int.cast_natCast] at hs
  rw [hs]
  exact mul_le_mul_of_nonneg_left
    (bank_root_frame_factor_cap M hg Q (m-(j:ℤ)) hQ hgap) bot_le

theorem bank_depth_population_budget (r : InverseBankRow) (M : ABKModel 2)
    (n j : ℕ) (hn : n ≤ 6*9^(45+j)) :
    (n:ℝ≥0∞)^(1/256:ℝ) *
      (ENNReal.ofReal (bankDepthFrame M j)*inverseBankRootErrorCap r) ≤
        ENNReal.ofReal (inverseBankDepthE r M j) := by
  calc
    _ ≤ ((ENNReal.ofReal (509/500:ℝ)*ENNReal.ofReal (invPopulationRoot:ℝ))*
          (9:ℝ≥0∞)^((j:ℝ)/256))*
        (ENNReal.ofReal (bankDepthFrame M j)*inverseBankRootErrorCap r) :=
      mul_le_mul_of_nonneg_right (bank_root_population_payment_depth n j hn) bot_le
    _ = ENNReal.ofReal (inverseBankE r:ℝ)*ENNReal.ofReal (bankDepthFrame M j)*
        (9:ℝ≥0∞)^((j:ℝ)/256) := by
      rw [← inverse_bank_remainder_ofReal r]
      ac_rfl
    _ = _ := inverse_bank_depth_E_ofReal r M j

end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Inverse.BankFrame
public import ASDExplicitGamma.Inverse.BankHistoryProfileArithmetic

/-! The source six-generation frame cost and finite root-population payment. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal

theorem bank_frame_shift_le (M : ABKModel 2) (ell m : ℤ)
    (hgap : m-ell ≤ 5) (hg : M.gamma ≤ gammaZero) :
    ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((m-ell:ℤ):ℝ))) ≤
      ENNReal.ofReal (invE (11*invGamma):ℝ) := by
  have hgapR : ((m-ell:ℤ):ℝ) ≤ 5 := by exact_mod_cast hgap
  have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hγ₀ : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
  have hfive := bank_history_height_cap M.gamma 5 hγ hγ₀ (by norm_num)
  have hfive' : (3:ℝ)^(2*M.gamma*5) ≤ (invE (11*invGamma):ℝ) := by
    convert hfive using 1
    norm_num [invE]
    ring
  apply ENNReal.ofReal_le_ofReal
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
    (mul_le_mul_of_nonneg_left hgapR (by positivity : 0 ≤ 2*M.gamma))).trans hfive'

theorem bank_offset_baseline_profile_cap (M : ABKModel 2) (Q : TriadicCube 2)
    (ell m : ℤ) (r : RootRow) (LiCap HCap : ℝ)
    (hQ : Q.scale = ell) (hell : ell ≤ m) (hgap : m-ell ≤ 5)
    (hg : M.gamma ≤ gammaZero) (hLi : rootLi M.gamma r ≤ LiCap)
    (hHeight : (3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27)) ≤ HCap) :
    bankRootInverseBaselineHistory Q M m r ≤
      ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
        ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal LiCap *
          ENNReal.ofReal HCap * ENNReal.ofReal (invSB:ℝ) := by
  have hγ₀ : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
  have hstep := bank_history_frame_step_le_invSB_den M.gamma M.shellPrefix.gamma_pos.le hγ₀
  have hbase := bank_root_inverse_baseline_history_cap M Q ell r LiCap HCap hQ hLi hHeight hstep
  rw [bank_root_inverse_baseline_history_shift M Q ell m r hQ hell]
  calc
    _ ≤ ENNReal.ofReal (invE (11*invGamma):ℝ) *
        (ENNReal.ofReal (invSB:ℝ) * (ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
          (ENNReal.ofReal LiCap * ENNReal.ofReal HCap))) :=
      mul_le_mul (bank_frame_shift_le M ell m hgap hg) hbase bot_le bot_le
    _ = _ := by ac_rfl

theorem bank_offset_remainder_profile_cap (M : ABKModel 2) (Q : TriadicCube 2)
    (ell m : ℤ) (r : RootRow) (rho : ℝ)
    (hQ : Q.scale = ell) (hell : ell ≤ m) (hgap : m-ell ≤ 5)
    (hg : M.gamma ≤ gammaZero)
    (hProfile : rootLi M.gamma r*selectedRootTiny (rootH0 r) +
      (rootMatrixErrorBudget M.gamma 256 r+rootDensityErrorBudget M.gamma r) ≤ rho) :
    bankRootInverseRemainderHistoryL256Bound M Q m r ≤
      ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
        ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal rho *
          ENNReal.ofReal (invSR:ℝ) := by
  have hγ₀ : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
  have hgeom := bank_root_remainder_history_profile_bound M Q ell r rho hQ hγ₀ hProfile
  have hstep := ENNReal.ofReal_le_ofReal
    (bank_history_frame_step_le_invSB_den M.gamma M.shellPrefix.gamma_pos.le hγ₀)
  have hSR : ENNReal.ofReal (3/2:ℝ) ≤ ENNReal.ofReal (invSR:ℝ) := by
    apply ENNReal.ofReal_le_ofReal
    norm_num [invSR, invAlphaLower, invBetaUpper, invE, invGamma]
  have hinner : ENNReal.ofReal (3/2:ℝ) *
      (ENNReal.ofReal ((3:ℝ)^(2*M.gamma))*ENNReal.ofReal rho) ≤
      ENNReal.ofReal (invSR:ℝ) *
        (ENNReal.ofReal (invE (11/5*invGamma):ℝ)*ENNReal.ofReal rho) :=
    mul_le_mul hSR (mul_le_mul_of_nonneg_right hstep bot_le) bot_le bot_le
  rw [bank_root_inverse_remainder_history_budget_shift M Q ell m r hQ hell]
  calc
    _ ≤ ENNReal.ofReal (invE (11*invGamma):ℝ) *
        (ENNReal.ofReal (invSR:ℝ) *
          (ENNReal.ofReal (invE (11/5*invGamma):ℝ)*ENNReal.ofReal rho)) :=
      mul_le_mul (bank_frame_shift_le M ell m hgap hg)
        (hgeom.trans hinner) bot_le bot_le
    _ = _ := by ac_rfl

/-- The source population is paid conservatively at order 128 even though
the pretruncation histories use order 256. -/
theorem bank_root_population_payment (n : ℕ) (hn : n ≤ 6*9^45) :
    (n:ℝ≥0∞)^(1/256:ℝ) ≤
      ENNReal.ofReal (509/500:ℝ)*ENNReal.ofReal (invPopulationRoot:ℝ) := by
  let N : ℝ := (509/500:ℝ)*(invPopulationRoot:ℝ)
  have hN0 : 0 ≤ N := by norm_num [N, invPopulationRoot]
  have hpay : (9:ℝ)^45 < N^128 := by
    dsimp only [N]
    rw [mul_pow]
    calc
      (9:ℝ)^45 = 9*9^44 := by ring
      _ < (509/500:ℝ)^128*(invPopulationRoot:ℝ)^128 :=
        mul_lt_mul positive_population_payments.2.1 positive_population_payments.1.le
          (by positivity) (by positivity)
  have hpay256 : (6:ℝ)*9^45 ≤ N^256 := by
    calc
      (6:ℝ)*9^45 ≤ (9:ℝ)^45*9^45 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ N^128*N^128 := mul_le_mul hpay.le hpay.le (by positivity) (by positivity)
      _ = N^256 := by rw [← pow_add]
  have hcard : (n:ℝ≥0∞) ≤ (6:ℝ≥0∞)*9^45 := by exact_mod_cast hn
  have hbudget : (6:ℝ≥0∞)*9^45 ≤ (ENNReal.ofReal N)^256 := by
    have hh := ENNReal.ofReal_le_ofReal hpay256
    simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 6),
      ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 9),
      ENNReal.ofReal_pow hN0, ENNReal.ofReal_ofNat] using hh
  have hh := ENNReal.rpow_le_rpow (hcard.trans hbudget) (by norm_num : (0:ℝ) ≤ 1/256)
  have he : ((ENNReal.ofReal N)^256)^(1/256:ℝ) = ENNReal.ofReal N := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [he] at hh
  simpa only [N, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 509/500)] using hh

end ASDExplicitGamma.Inverse

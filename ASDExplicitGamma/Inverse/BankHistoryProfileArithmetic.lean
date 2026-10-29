module

public import ASDExplicitGamma.Inverse.BankRemainderProfiles

/-! Geometric arithmetic for summing the positive inverse-history profiles. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal

private theorem bank_depth_population_root_256 :
    (9:ℝ≥0∞)^(1/256:ℝ) ≤ ENNReal.ofReal (509/500:ℝ) := by
  rw [show (9:ℝ≥0∞) = ENNReal.ofReal (9:ℝ) by norm_num,
    ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ) < 9)]
  apply ENNReal.ofReal_le_ofReal
  have hroot : (9:ℝ)^(1/128:ℝ) < (509/500:ℝ) := by
    have hp := inv_root_upper (x := 9) (u := 509/500) (by norm_num)
      (by norm_num) (by norm_num : 128 ≠ 0)
      (by norm_num [invPopulation_payment.2.1])
    norm_num at hp ⊢
    exact hp
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 9)
    (by norm_num : (1/256:ℝ) ≤ 1/128)).trans hroot.le

private theorem bank_depth_population_factor_le (j : ℕ) :
    ((9:ℝ≥0∞)^j)^(1/256:ℝ) ≤ ENNReal.ofReal ((509/500:ℝ)^j) := by
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  rw [show (j:ℝ)*(1/256:ℝ) = (1/256:ℝ)*(j:ℝ) by ring,
    ENNReal.rpow_mul_natCast]
  calc
    ((9:ℝ≥0∞)^(1/256:ℝ))^j ≤ (ENNReal.ofReal (509/500:ℝ))^j :=
      pow_le_pow_left' bank_depth_population_root_256 j
    _ = ENNReal.ofReal ((509/500:ℝ)^j) := by
      rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (509/500:ℝ))]

private theorem bank_history_ratio_le (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ₀ : γ ≤ 17/50000) :
    (3:ℝ)^(-(1/4:ℝ)) * (509/500:ℝ) * (3:ℝ)^(2*γ) ≤ 5/6 := by
  have hAlpha : (3:ℝ)^(-(1/4:ℝ)) < (invAlphaUpper:ℝ) := by
    have h := inv_alpha_real.2
    have heq : (3:ℝ)^(-(1/4:ℝ)) = (1/3:ℝ)^(1/4:ℝ) := by
      rw [show -(1/4:ℝ) = (-1)*(1/4:ℝ) by ring,
        Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
      norm_num
    rw [heq]
    exact h
  have hFrame : (3:ℝ)^(2*γ) ≤ 51/50 := by
    have hdom : (11/10:ℝ)*(2*γ) < 1 := by nlinarith
    have h := inv_three_power_bound (2*γ) (by positivity) hdom
    have hden : 0 < 1-(11/5:ℝ)*γ := by nlinarith
    have hrat : 1/(1-(11/5:ℝ)*γ) ≤ 51/50 := by
      rw [div_le_iff₀ hden]
      nlinarith
    calc
      (3:ℝ)^(2*γ) ≤ 1/(1-(11/10:ℝ)*(2*γ)) := by
        exact h
      _ = 1/(1-(11/5:ℝ)*γ) := by congr 1; ring
      _ ≤ 51/50 := hrat
  apply le_of_lt
  calc
    _ < (invAlphaUpper:ℝ)*(509/500)*(51/50) := by
      have hmul :
          (3:ℝ)^(-(1/4:ℝ))*(509/500:ℝ) < (invAlphaUpper:ℝ)*(509/500:ℝ) :=
        mul_lt_mul_of_pos_right hAlpha (by norm_num)
      have hmul' :
          (3:ℝ)^(-(1/4:ℝ))*(509/500:ℝ)*(3:ℝ)^(2*γ) <
            (invAlphaUpper:ℝ)*(509/500:ℝ)*(3:ℝ)^(2*γ) := by
        exact mul_lt_mul_of_pos_right hmul (by positivity)
      have hframe' :
          (invAlphaUpper:ℝ)*(509/500:ℝ)*(3:ℝ)^(2*γ) ≤
            (invAlphaUpper:ℝ)*(509/500:ℝ)*(51/50:ℝ) := by
        exact mul_le_mul_of_nonneg_left hFrame (by norm_num [invAlphaUpper])
      exact hmul'.trans_le hframe'
    _ < 5/6 := by norm_num [invAlphaUpper]

private theorem bank_history_ratio_ennreal (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ₀ : γ ≤ 17/50000) :
    bankHistoryAlpha * ENNReal.ofReal (509/500:ℝ) *
      ENNReal.ofReal ((3:ℝ)^(2*γ)) ≤ ENNReal.ofReal (5/6:ℝ) := by
  have h := ENNReal.ofReal_le_ofReal (bank_history_ratio_le γ hγ hγ₀)
  calc
    _ = ENNReal.ofReal ((3:ℝ)^(-(1/4:ℝ)) *
        ((509/500:ℝ) * (3:ℝ)^(2*γ))) := by
      rw [bankHistoryAlpha]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)^(-(1/4:ℝ)))]
      rw [← ENNReal.ofReal_mul
        (by positivity : 0 ≤ (3:ℝ)^(-(1/4:ℝ))*(509/500:ℝ))]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (5/6:ℝ) := by simpa [mul_assoc] using h

private theorem bank_history_frame_factor (M : ABKModel 2) (Q : TriadicCube 2)
    (m : ℤ) (j : ℕ) (hQ : Q.scale = m) :
    ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) =
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) *
        ENNReal.ofReal ((3:ℝ)^(2*M.gamma))^j := by
  have harg : ((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ) = (j:ℝ)+1 := by
    have hz : m-(Q.scale-(j:ℤ))+1 = (j:ℤ)+1 := by
      rw [hQ]
      omega
    exact_mod_cast hz
  have hpow : (3:ℝ)^(2*M.gamma*((j:ℝ)+1)) =
      (3:ℝ)^(2*M.gamma) * ((3:ℝ)^(2*M.gamma))^j := by
    rw [show 2*M.gamma*((j:ℝ)+1) = 2*M.gamma + 2*M.gamma*(j:ℝ) by ring,
      Real.rpow_add (by norm_num : (0:ℝ) < 3),
      Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]
  rw [harg]
  have habs : |(j:ℝ)+1| = (j:ℝ)+1 := by
    apply abs_of_nonneg
    positivity
  rw [habs, hpow, ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)^(2*M.gamma)),
    ENNReal.ofReal_pow (by positivity : 0 ≤ (3:ℝ)^(2*M.gamma))]

private theorem bank_history_prefactor_le_fourth :
    bankHistoryPrefactor ≤ ENNReal.ofReal (1/4:ℝ) := by
  have hAlpha : (3:ℝ)^(-(1/4:ℝ)) > 3/4 := by
    have h := inv_alpha_real.1
    have hnum : (3/4:ℝ) < (invAlphaLower:ℝ) := by norm_num [invAlphaLower]
    have heq : (3:ℝ)^(-(1/4:ℝ)) = (1/3:ℝ)^(1/4:ℝ) := by
      rw [show -(1/4:ℝ) = (-1)*(1/4:ℝ) by ring,
        Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
      norm_num
    rw [heq]
    exact hnum.trans h
  unfold bankHistoryPrefactor
  apply ENNReal.ofReal_le_ofReal
  linarith

private theorem bank_root_remainder_history_term_le
    (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ) (r : RootRow) (rho : ℝ)
    (j : ℕ) (hQ : Q.scale = m)
    (hγ₀ : M.gamma ≤ 17/50000)
    (hProfile : rootLi M.gamma r * selectedRootTiny (rootH0 r) +
      (rootMatrixErrorBudget M.gamma 256 r +
        rootDensityErrorBudget M.gamma r) ≤ rho) :
    bankHistoryAlpha^j * (((descendantsAtDepth Q j).card:ℝ≥0∞)^(1/256:ℝ) *
      (ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) *
        (ENNReal.ofReal (rootLi M.gamma r * selectedRootTiny (rootH0 r)) +
          ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
            rootDensityErrorBudget M.gamma r)))) ≤
      (ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) * ENNReal.ofReal rho) *
        ENNReal.ofReal (5/6:ℝ)^j := by
  have hparts :
      ENNReal.ofReal (rootLi M.gamma r * selectedRootTiny (rootH0 r)) +
        ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
          rootDensityErrorBudget M.gamma r) ≤ ENNReal.ofReal rho := by
    have hLi := bank_root_Li_nonneg M.gamma r
    have hTiny : 0 ≤ selectedRootTiny (rootH0 r) := by
      unfold selectedRootTiny
      split <;> positivity
    have hErr : 0 ≤ rootMatrixErrorBudget M.gamma 256 r +
        rootDensityErrorBudget M.gamma r :=
      add_nonneg (bank_root_matrix_error_budget_nonneg M.gamma r)
        (bank_root_density_error_budget_nonneg M.gamma r hγ₀)
    rw [← ENNReal.ofReal_add (mul_nonneg hLi hTiny) hErr]
    exact ENNReal.ofReal_le_ofReal hProfile
  have hpop : ((descendantsAtDepth Q j).card:ℝ≥0∞)^(1/256:ℝ) ≤
      ENNReal.ofReal ((509/500:ℝ)^j) := by
    have hcard : (descendantsAtDepth Q j).card = 9^j := by
      rw [descendantsAtDepth_card]
      simp
    rw [hcard]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using bank_depth_population_factor_le j
  have hframe := bank_history_frame_factor M Q m j hQ
  have hratio := bank_history_ratio_ennreal M.gamma M.shellPrefix.gamma_pos.le hγ₀
  let a : ℝ≥0∞ := bankHistoryAlpha
  let p : ℝ≥0∞ := ENNReal.ofReal (509/500:ℝ)
  let t : ℝ≥0∞ := ENNReal.ofReal ((3:ℝ)^(2*M.gamma))
  let q : ℝ≥0∞ := a*p*t
  have hpop' : ((descendantsAtDepth Q j).card:ℝ≥0∞)^(1/256:ℝ) ≤
      (ENNReal.ofReal (509/500:ℝ))^j := by
    rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (509/500:ℝ))] at hpop
    exact hpop
  calc
    _ ≤ a^j * ((ENNReal.ofReal (509/500:ℝ))^j *
        (t * (t^j * ENNReal.ofReal rho))) := by
      dsimp [a, t]
      rw [hframe]
      have hinner :
          ((descendantsAtDepth Q j).card:ℝ≥0∞)^(1/256:ℝ) *
              (ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) *
                (ENNReal.ofReal ((3:ℝ)^(2*M.gamma))^j *
                  (ENNReal.ofReal (rootLi M.gamma r *
                    selectedRootTiny (rootH0 r)) +
                    ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
                      rootDensityErrorBudget M.gamma r)))) ≤
            (ENNReal.ofReal (509/500:ℝ))^j *
              (ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) *
                (ENNReal.ofReal ((3:ℝ)^(2*M.gamma))^j * ENNReal.ofReal rho)) := by
        have hclock :
            ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) *
                (ENNReal.ofReal ((3:ℝ)^(2*M.gamma))^j *
                  (ENNReal.ofReal (rootLi M.gamma r *
                    selectedRootTiny (rootH0 r)) +
                    ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
                      rootDensityErrorBudget M.gamma r))) ≤
              ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) *
                (ENNReal.ofReal ((3:ℝ)^(2*M.gamma))^j * ENNReal.ofReal rho) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hparts (by positivity)
        calc
          _ ≤ (ENNReal.ofReal (509/500:ℝ))^j *
              (ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) *
                (ENNReal.ofReal ((3:ℝ)^(2*M.gamma))^j *
                  (ENNReal.ofReal (rootLi M.gamma r *
                    selectedRootTiny (rootH0 r)) +
                    ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
                      rootDensityErrorBudget M.gamma r)))) :=
            mul_le_mul_of_nonneg_right hpop' (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left hclock (by positivity)
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left hinner (by positivity))
    _ = (t * ENNReal.ofReal rho) * q^j := by
      dsimp [q, a, p, t]
      rw [mul_pow, mul_pow]
      ac_rfl
    _ ≤ (t * ENNReal.ofReal rho) * ENNReal.ofReal (5/6:ℝ)^j := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left' hratio j

private theorem bank_history_prefactor_le_invSB_num :
    bankHistoryPrefactor ≤ ENNReal.ofReal (1-(invAlphaLower:ℝ)) := by
  have heq : (3:ℝ)^(-(1/4:ℝ)) = (1/3:ℝ)^(1/4:ℝ) := by
    rw [show -(1/4:ℝ) = (-1)*(1/4:ℝ) by ring,
      Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have hAlpha : (invAlphaLower:ℝ) < (3:ℝ)^(-(1/4:ℝ)) := by
    rw [heq]
    exact inv_alpha_real.1
  unfold bankHistoryPrefactor
  apply ENNReal.ofReal_le_ofReal
  linarith

theorem bank_history_frame_step_le_invSB_den (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ₀ : γ ≤ 17/50000) :
    (3:ℝ)^(2*γ) ≤ (invE (11/5*invGamma):ℝ) := by
  have hdom : (11/10:ℝ)*(2*γ) < 1 := by nlinarith
  have h := inv_three_power_bound (2*γ) (by positivity) hdom
  have hden : 0 < 1-(11/5:ℝ)*γ := by nlinarith
  have hden0 : 0 < 1-(11/5:ℝ)*(invGamma:ℝ) := by norm_num [invGamma]
  have hcompare : 1/(1-(11/5:ℝ)*γ) ≤ 1/(1-(11/5:ℝ)*(invGamma:ℝ)) := by
    rw [div_le_div_iff₀ hden hden0]
    have hg : γ ≤ (invGamma:ℝ) := by simpa [invGamma] using hγ₀
    nlinarith
  calc
    (3:ℝ)^(2*γ) ≤ 1/(1-(11/5:ℝ)*γ) := by
      convert h using 1; ring
    _ ≤ 1/(1-(11/5:ℝ)*(invGamma:ℝ)) := hcompare
    _ = (invE (11/5*invGamma):ℝ) := by norm_num [invE]

private theorem bank_history_baseline_geom_coefficient :
    bankHistoryPrefactor *
      (∑' j : ℕ,
        ENNReal.ofReal ((invAlphaUpper:ℝ)*(invE (11/5*invGamma):ℝ))^j) ≤
      ENNReal.ofReal (invSB:ℝ) := by
  let q : ℝ := (invAlphaUpper:ℝ)*(invE (11/5*invGamma):ℝ)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    apply mul_nonneg
    · norm_num [invAlphaUpper]
    · norm_num [invE, invGamma]
  have hq1 : q < 1 := by
    norm_num [q, invAlphaUpper, invE, invGamma]
  have hden : 1-ENNReal.ofReal q = ENNReal.ofReal (1-q) := by
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub (1:ℝ) (by exact hq0)]
  have hpos : 0 < 1-q := sub_pos.mpr hq1
  have hmul : ENNReal.ofReal (1-q)*ENNReal.ofReal ((1-q)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hpos.le]
    simp [hpos.ne']
  have hInv : (ENNReal.ofReal (1-q))⁻¹ = ENNReal.ofReal ((1-q)⁻¹) := by
    exact (ENNReal.ofReal_inv_of_pos hpos).symm
  have hnum : 0 ≤ 1-(invAlphaLower:ℝ) := by norm_num [invAlphaLower]
  have hfactor :
      ENNReal.ofReal (1-(invAlphaLower:ℝ))*ENNReal.ofReal ((1-q)⁻¹) =
        ENNReal.ofReal (invSB:ℝ) := by
    rw [← ENNReal.ofReal_mul hnum]
    congr 1
    norm_num [invSB, q, invE, invGamma]
    rw [div_eq_mul_inv]
    rfl
  calc
    _ ≤ ENNReal.ofReal (1-(invAlphaLower:ℝ)) *
        (∑' j : ℕ, ENNReal.ofReal q^j) := by
      exact mul_le_mul_of_nonneg_right bank_history_prefactor_le_invSB_num
        (by positivity)
    _ = ENNReal.ofReal (1-(invAlphaLower:ℝ)) * (1-ENNReal.ofReal q)⁻¹ := by
      rw [ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (invSB:ℝ) := by rw [hden, hInv, hfactor]

theorem bank_history_height_cap (γ : ℝ) (d : ℕ)
    (hγ : 0 ≤ γ) (hγ₀ : γ ≤ 17/50000)
    (hd350 : d ≤ 350) :
    (3:ℝ)^(2*γ*(d:ℝ)) ≤ (invE (11/5*invGamma*d):ℝ) := by
  have hdR : (d:ℝ) ≤ 350 := by exact_mod_cast hd350
  have hdom : (11/10:ℝ)*(2*γ*(d:ℝ)) < 1 := by nlinarith
  have h := inv_three_power_bound (2*γ*(d:ℝ)) (by positivity) hdom
  have hden : 0 < 1-(11/5:ℝ)*γ*(d:ℝ) := by nlinarith
  have hden0 : 0 < 1-(11/5:ℝ)*(invGamma:ℝ)*(d:ℝ) := by
    have hγ' : (invGamma:ℝ) = 17/50000 := by norm_num [invGamma]
    rw [hγ']
    nlinarith [hdR]
  have hcompare : 1/(1-(11/5:ℝ)*γ*d) ≤
      1/(1-(11/5:ℝ)*(invGamma:ℝ)*(d:ℝ)) := by
    rw [div_le_div_iff₀ hden hden0]
    have hg : γ ≤ (invGamma:ℝ) := by simpa [invGamma] using hγ₀
    nlinarith
  calc
    (3:ℝ)^(2*γ*(d:ℝ)) ≤ 1/(1-(11/5:ℝ)*γ*(d:ℝ)) := by
      convert h using 1; ring
    _ ≤ 1/(1-(11/5:ℝ)*(invGamma:ℝ)*(d:ℝ)) := by
      convert hcompare using 1
    _ = (invE (11/5*invGamma*d):ℝ) := by
      norm_num [invE, invGamma]

private theorem bank_history_baseline_term_le
    (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ) (r : RootRow)
    (j : ℕ) (LiCap HCap : ℝ) (hQ : Q.scale = m)
    (hLi : rootLi M.gamma r ≤ LiCap)
    (hHeight : (3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27)) ≤ HCap)
    (hFrame : (3:ℝ)^(2*M.gamma) ≤ (invE (11/5*invGamma):ℝ)) :
    bankHistoryAlpha^j * bankRootDepthBaseline M Q m r j ≤
      (ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
        (ENNReal.ofReal LiCap * ENNReal.ofReal HCap)) *
        ENNReal.ofReal ((invAlphaUpper:ℝ)*(invE (11/5*invGamma):ℝ))^j := by
  have hframe := bank_history_frame_factor M Q m j hQ
  have hLi' : ENNReal.ofReal (rootLi M.gamma r) ≤ ENNReal.ofReal LiCap :=
    ENNReal.ofReal_le_ofReal hLi
  have hHeight' :
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27))) ≤ ENNReal.ofReal HCap :=
    ENNReal.ofReal_le_ofReal hHeight
  have hFrame' : ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) ≤
      ENNReal.ofReal (invE (11/5*invGamma):ℝ) := ENNReal.ofReal_le_ofReal hFrame
  have hstep : bankHistoryAlpha * ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) ≤
      ENNReal.ofReal ((invAlphaUpper:ℝ)*(invE (11/5*invGamma):ℝ)) := by
    have hAlpha : (3:ℝ)^(-(1/4:ℝ)) ≤ (invAlphaUpper:ℝ) := by
      have h := inv_alpha_real.2
      have heq : (3:ℝ)^(-(1/4:ℝ)) = (1/3:ℝ)^(1/4:ℝ) := by
        rw [show -(1/4:ℝ) = (-1)*(1/4:ℝ) by ring,
          Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
        norm_num
      rw [heq]
      exact h.le
    have hmul := mul_le_mul hAlpha hFrame (by positivity)
      (by norm_num [invAlphaUpper] : 0 ≤ (invAlphaUpper:ℝ))
    simpa only [bankHistoryAlpha, ← ENNReal.ofReal_mul
      (by positivity : 0 ≤ (3:ℝ)^(-(1/4:ℝ))), ← ENNReal.ofReal_mul
      (by norm_num [invAlphaUpper] : 0 ≤ (invAlphaUpper:ℝ)), mul_assoc] using
        ENNReal.ofReal_le_ofReal hmul
  have hstepPow : bankHistoryAlpha^j * ENNReal.ofReal ((3:ℝ)^(2*M.gamma))^j ≤
      ENNReal.ofReal ((invAlphaUpper:ℝ)*(invE (11/5*invGamma):ℝ))^j := by
    calc
      _ = (bankHistoryAlpha * ENNReal.ofReal ((3:ℝ)^(2*M.gamma)))^j := by rw [mul_pow]
      _ ≤ _ := pow_le_pow_left' hstep j
  have hcoeff :
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) *
        (ENNReal.ofReal (rootLi M.gamma r) *
          ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27)))) ≤
      ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
        (ENNReal.ofReal LiCap * ENNReal.ofReal HCap) := by
    have hLiClock :
        ENNReal.ofReal (rootLi M.gamma r) *
          ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27))) ≤
        ENNReal.ofReal LiCap * ENNReal.ofReal HCap := by
      calc
        _ ≤ ENNReal.ofReal LiCap *
            ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27))) :=
          mul_le_mul_of_nonneg_right hLi' (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hHeight' (by positivity)
    calc
      _ ≤ ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
          (ENNReal.ofReal (rootLi M.gamma r) *
            ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27)))) :=
        mul_le_mul_of_nonneg_right hFrame' (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hLiClock (by positivity)
  calc
    _ = (ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) *
        (ENNReal.ofReal (rootLi M.gamma r) *
          ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27)))))*
        (bankHistoryAlpha^j * ENNReal.ofReal ((3:ℝ)^(2*M.gamma))^j) := by
      dsimp [bankRootDepthBaseline]
      rw [hframe]
      simp only [mul_assoc, mul_left_comm, mul_comm]
    _ ≤ (ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
        (ENNReal.ofReal LiCap * ENNReal.ofReal HCap)) *
        ENNReal.ofReal ((invAlphaUpper:ℝ)*(invE (11/5*invGamma):ℝ))^j :=
      mul_le_mul hcoeff hstepPow (by positivity) (by positivity)

/-- Sum a deterministic baseline profile after the true-frame shift is fixed.
The only rowwise inputs are its Li cap and its height cap. -/
theorem bank_root_inverse_baseline_history_cap
    (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ) (r : RootRow)
    (LiCap HCap : ℝ) (hQ : Q.scale = m)
    (hLi : rootLi M.gamma r ≤ LiCap)
    (hHeight : (3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27)) ≤ HCap)
    (hFrame : (3:ℝ)^(2*M.gamma) ≤ (invE (11/5*invGamma):ℝ)) :
    bankRootInverseBaselineHistory Q M m r ≤
      ENNReal.ofReal (invSB:ℝ) *
        (ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
          (ENNReal.ofReal LiCap * ENNReal.ofReal HCap)) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
    (ENNReal.ofReal LiCap * ENNReal.ofReal HCap)
  let q : ℝ := (invAlphaUpper:ℝ)*(invE (11/5*invGamma):ℝ)
  have hterms :
      (∑' j : ℕ, bankHistoryAlpha^j * bankRootDepthBaseline M Q m r j) ≤
        ∑' j : ℕ, C * ENNReal.ofReal q^j := by
    apply ENNReal.tsum_le_tsum
    intro j
    simpa [C, q] using
      bank_history_baseline_term_le M Q m r j LiCap HCap hQ hLi hHeight hFrame
  calc
    bankRootInverseBaselineHistory Q M m r =
        bankHistoryPrefactor *
          (∑' j : ℕ, bankHistoryAlpha^j * bankRootDepthBaseline M Q m r j) := rfl
    _ ≤ bankHistoryPrefactor * (∑' j : ℕ, C * ENNReal.ofReal q^j) :=
      mul_le_mul_of_nonneg_left hterms bot_le
    _ = C * (bankHistoryPrefactor *
        (∑' j : ℕ, ENNReal.ofReal q^j)) := by
      rw [ENNReal.tsum_mul_left]
      ac_rfl
    _ ≤ C * ENNReal.ofReal (invSB:ℝ) :=
      mul_le_mul_of_nonneg_left bank_history_baseline_geom_coefficient bot_le
    _ = _ := by dsimp [C]; ac_rfl

private theorem bank_history_baseline_coefficient_le_full_source
    (LiCap HCap SourceCap : ℝ) (hLi0 : 0 ≤ LiCap)
    (hSource : SourceCap = (invSB:ℝ) *
      ((invE (11*invGamma):ℝ) * (LiCap * HCap))) :
    ENNReal.ofReal (invSB:ℝ) *
      (ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
        (ENNReal.ofReal LiCap * ENNReal.ofReal HCap)) ≤ ENNReal.ofReal SourceCap := by
  have hFrame : (invE (11/5*invGamma):ℝ) ≤ (invE (11*invGamma):ℝ) := by
    norm_num [invE, invGamma]
  have hRatio : ENNReal.ofReal (invE (11/5*invGamma):ℝ) ≤
      ENNReal.ofReal (invE (11*invGamma):ℝ) := ENNReal.ofReal_le_ofReal hFrame
  have hLiHeight : ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
        (ENNReal.ofReal LiCap * ENNReal.ofReal HCap) ≤
      ENNReal.ofReal (invE (11*invGamma):ℝ) *
        (ENNReal.ofReal LiCap * ENNReal.ofReal HCap) :=
    mul_le_mul_of_nonneg_right hRatio bot_le
  have hSB0 : 0 ≤ (invSB:ℝ) := by
    norm_num [invSB, invE, invGamma, invAlphaLower, invAlphaUpper]
  have hE110 : 0 ≤ (invE (11*invGamma):ℝ) := by
    norm_num [invE, invGamma]
  have hcombine :
      ENNReal.ofReal (invSB:ℝ) *
        (ENNReal.ofReal (invE (11*invGamma):ℝ) *
          (ENNReal.ofReal LiCap * ENNReal.ofReal HCap)) =
        ENNReal.ofReal ((invSB:ℝ) *
          ((invE (11*invGamma):ℝ) * (LiCap * HCap))) := by
    rw [← ENNReal.ofReal_mul hLi0, ← ENNReal.ofReal_mul hE110,
      ← ENNReal.ofReal_mul hSB0]
  calc
    _ ≤ ENNReal.ofReal (invSB:ℝ) *
        (ENNReal.ofReal (invE (11*invGamma):ℝ) *
          (ENNReal.ofReal LiCap * ENNReal.ofReal HCap)) :=
      mul_le_mul_of_nonneg_left hLiHeight bot_le
    _ = ENNReal.ofReal ((invSB:ℝ) *
        ((invE (11*invGamma):ℝ) * (LiCap * HCap))) := hcombine
    _ = ENNReal.ofReal SourceCap := by rw [← hSource]

theorem bank_root_remainder_history_profile_bound
    (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ) (r : RootRow) (rho : ℝ)
    (hQ : Q.scale = m) (hγ₀ : M.gamma ≤ 17/50000)
    (hProfile : rootLi M.gamma r * selectedRootTiny (rootH0 r) +
      (rootMatrixErrorBudget M.gamma 256 r +
        rootDensityErrorBudget M.gamma r) ≤ rho) :
    bankRootInverseRemainderHistoryL256Bound M Q m r ≤
      ENNReal.ofReal (3/2:ℝ) *
        (ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) * ENNReal.ofReal rho) := by
  let A : ℝ≥0∞ := ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) * ENNReal.ofReal rho
  let q : ℝ≥0∞ := ENNReal.ofReal (5/6:ℝ)
  have hsum :
      (∑' j : ℕ, bankHistoryAlpha^j *
        (((descendantsAtDepth Q j).card:ℝ≥0∞)^(1/256:ℝ) *
          (ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) *
            (ENNReal.ofReal (rootLi M.gamma r * selectedRootTiny (rootH0 r)) +
              ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
                rootDensityErrorBudget M.gamma r))))) ≤
        ∑' j : ℕ, A*q^j := by
    apply ENNReal.tsum_le_tsum
    intro j
    simpa [A, q] using bank_root_remainder_history_term_le M Q m r rho j hQ hγ₀ hProfile
  have hgeom : (∑' j : ℕ, A*q^j) = A*6 := by
    dsimp [q]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    have hsub : 1-ENNReal.ofReal (5/6:ℝ) = ENNReal.ofReal (1/6:ℝ) := by
      rw [← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub (1:ℝ) (by norm_num : 0 ≤ (5/6:ℝ))]
      norm_num
    have hmul : ENNReal.ofReal (1/6:ℝ) * 6 = 1 := by
      rw [show (6:ℝ≥0∞) = ENNReal.ofReal (6:ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1/6:ℝ))]
      norm_num
    have hInv : ENNReal.ofReal (1/6:ℝ) = (6:ℝ≥0∞)⁻¹ :=
      ENNReal.eq_inv_of_mul_eq_one_left hmul
    have hInv6 : (ENNReal.ofReal (1/6:ℝ))⁻¹ = 6 := by
      calc
        (ENNReal.ofReal (1/6:ℝ))⁻¹ = ((6:ℝ≥0∞)⁻¹)⁻¹ := congrArg Inv.inv hInv
        _ = 6 := by simp
    calc
      A*(1-ENNReal.ofReal (5/6:ℝ))⁻¹ = A*(ENNReal.ofReal (1/6:ℝ))⁻¹ := by rw [hsub]
      _ = A*6 := by rw [hInv6]
  have hpref : bankHistoryPrefactor*6 ≤ ENNReal.ofReal (3/2:ℝ) := by
    calc
      bankHistoryPrefactor*6 ≤ ENNReal.ofReal (1/4:ℝ)*6 :=
        mul_le_mul_of_nonneg_right bank_history_prefactor_le_fourth (by norm_num)
      _ = ENNReal.ofReal (3/2:ℝ) := by
        have h6 : (6:ℝ≥0∞) = ENNReal.ofReal (6:ℝ) := by norm_num
        rw [h6, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1/4:ℝ))]
        norm_num
  unfold bankRootInverseRemainderHistoryL256Bound
  calc
    _ ≤ bankHistoryPrefactor*(A*6) := by
      exact mul_le_mul_of_nonneg_left (hsum.trans_eq hgeom) bot_le
    _ = (bankHistoryPrefactor*6)*A := by ac_rfl
    _ ≤ ENNReal.ofReal (3/2:ℝ)*A :=
      mul_le_mul_of_nonneg_right hpref (by positivity)

private theorem bank_history_frame_base_le (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ₀ : γ ≤ 17/50000) :
    (3:ℝ)^(2*γ) ≤ (invE (11*invGamma):ℝ) := by
  have hdom : (11/10:ℝ)*(2*γ) < 1 := by nlinarith
  have h := inv_three_power_bound (2*γ) (by positivity) hdom
  have hden : 0 < 1-(11/5:ℝ)*γ := by nlinarith
  have hden0 : 0 < 1-(11:ℝ)*(invGamma:ℝ) := by norm_num [invGamma]
  have hcompare : 1/(1-(11/5:ℝ)*γ) ≤ 1/(1-(11:ℝ)*(invGamma:ℝ)) := by
    rw [div_le_div_iff₀ hden hden0]
    have hg : γ ≤ (invGamma:ℝ) := by simpa [invGamma] using hγ₀
    nlinarith
  calc
    (3:ℝ)^(2*γ) ≤ 1/(1-(11/5:ℝ)*γ) := by
      convert h using 1; ring
    _ ≤ 1/(1-(11:ℝ)*(invGamma:ℝ)) := hcompare
    _ = (invE (11*invGamma):ℝ) := by norm_num [invE]

theorem bank_root_remainder_history_profile_bound_invSR
    (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ) (r : RootRow) (rho : ℝ)
    (hQ : Q.scale = m) (hγ₀ : M.gamma ≤ 17/50000)
    (hProfile : rootLi M.gamma r * selectedRootTiny (rootH0 r) +
      (rootMatrixErrorBudget M.gamma 256 r +
        rootDensityErrorBudget M.gamma r) ≤ rho) :
    bankRootInverseRemainderHistoryL256Bound M Q m r ≤
      ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal rho *
        ENNReal.ofReal (invSR:ℝ) := by
  have hgeom := bank_root_remainder_history_profile_bound M Q m r rho hQ hγ₀ hProfile
  have hFrame := bank_history_frame_base_le M.gamma M.shellPrefix.gamma_pos.le hγ₀
  have hFrame' : ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) ≤
      ENNReal.ofReal (invE (11*invGamma):ℝ) := ENNReal.ofReal_le_ofReal hFrame
  have hSR : (3/2:ℝ) ≤ (invSR:ℝ) := by
    norm_num [invSR, invAlphaLower, invBetaUpper, invE, invGamma]
  have hSR' : ENNReal.ofReal (3/2:ℝ) ≤ ENNReal.ofReal (invSR:ℝ) :=
    ENNReal.ofReal_le_ofReal hSR
  have hFrameStep := mul_le_mul_of_nonneg_left hFrame'
    (by positivity : (0:ℝ≥0∞) ≤ ENNReal.ofReal (3/2:ℝ))
  have hFrameStepRho :
      ENNReal.ofReal (3/2:ℝ) *
        (ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) * ENNReal.ofReal rho) ≤
      ENNReal.ofReal (3/2:ℝ) *
        (ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal rho) := by
    have h := mul_le_mul_of_nonneg_right hFrameStep
      (by positivity : (0:ℝ≥0∞) ≤ ENNReal.ofReal rho)
    simpa [mul_assoc] using h
  have hSRStep := mul_le_mul_of_nonneg_right hSR'
    (by positivity : (0:ℝ≥0∞) ≤
      ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal rho)
  calc
    _ ≤ ENNReal.ofReal (3/2:ℝ) *
        (ENNReal.ofReal ((3:ℝ)^(2*M.gamma)) * ENNReal.ofReal rho) := hgeom
    _ ≤ ENNReal.ofReal (3/2:ℝ) *
        (ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal rho) := hFrameStepRho
    _ ≤ ENNReal.ofReal (invSR:ℝ) *
        (ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal rho) := hSRStep
    _ = _ := by ac_rfl

theorem bank_root_inverse_remainder_history_L256_cap_of_profile
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (m J : ℤ)
    (hQscale : Q.scale = m) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hweights : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (r : RootRow) (rho : ℝ)
    (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m r)
    (hPointwiseRoot : ∀ (Q' : TriadicCube 2) (m' J' : ℤ)
      (_hQ' : Q'.scale ≤ m') (_hmJ' : m' ≤ J') (weights' : ℤ → ℝ)
      (_hweights' : ∀ k ∈ Finset.Ioc m' J', 0 ≤ weights' k ∧ weights' k ≤ 1)
      (r' : RootRow) (_hpast' : ∀ n < m', nativeInductionState M h n)
      (_hmean' : ClippedInverseMeanInput M m' r'),
      PointwiseRootConclusion M Q' m' J' weights' r')
    (hProfile : rootLi M.gamma r * selectedRootTiny (rootH0 r) +
      (rootMatrixErrorBudget M.gamma 256 r +
        rootDensityErrorBudget M.gamma r) ≤ rho) :
    eLpNorm (bankRootInverseRemainderHistory Q M m r) 256
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal rho *
        ENNReal.ofReal (invSR:ℝ) := by
  have hγ₀ : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
  have hhistory := bank_root_inverse_remainder_history_L256_of_pointwise M h hM hg Q m J
    hQscale.le hmJ weights hweights r hpast hmean hPointwiseRoot
  have hnumeric := bank_root_remainder_history_profile_bound_invSR M Q m r rho
    hQscale hγ₀ hProfile
  simpa [bankRootInverseRemainderHistoryL256Bound] using hhistory.trans hnumeric

theorem bank_full_root_inverse_remainder_history_L256_cap_of_pointwise
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (m J : ℤ)
    (hQscale : Q.scale = m) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hweights : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m .full)
    (hPointwiseRoot : ∀ (Q' : TriadicCube 2) (m' J' : ℤ)
      (_hQ' : Q'.scale ≤ m') (_hmJ' : m' ≤ J') (weights' : ℤ → ℝ)
      (_hweights' : ∀ k ∈ Finset.Ioc m' J', 0 ≤ weights' k ∧ weights' k ≤ 1)
      (r' : RootRow) (_hpast' : ∀ n < m', nativeInductionState M h n)
      (_hmean' : ClippedInverseMeanInput M m' r'),
      PointwiseRootConclusion M Q' m' J' weights' r') :
    eLpNorm (bankRootInverseRemainderHistory Q M m .full) 256
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal (invFullRho:ℝ) *
        ENNReal.ofReal (invSR:ℝ) := by
  have hγ₀ : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
  have hprofile := bank_full_root_error_plus_tiny_bound M.gamma
    M.shellPrefix.gamma_pos.le hγ₀
  exact bank_root_inverse_remainder_history_L256_cap_of_profile M h hM hg Q m J
    hQscale hmJ weights hweights .full (invFullRho:ℝ) hpast hmean
    hPointwiseRoot hprofile

theorem bank_full_root_inverse_baseline_history_cap
    (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ)
    (hQscale : Q.scale = m) (hg : M.gamma ≤ gammaZero) :
    bankRootInverseBaselineHistory Q M m .full ≤
      ENNReal.ofReal (invFullB0:ℝ) := by
  have hγ₀ : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
  have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hLi := bank_full_root_Li_bound M.gamma hγ hγ₀
  have hHeight0 := bank_history_height_cap M.gamma 350 hγ hγ₀ (by norm_num)
  have hheightIndex : (rootH0 .full:ℝ)-27 = 350 := by
    norm_num [rootH0]
  have hHeight : (3:ℝ)^(2*M.gamma*((rootH0 .full:ℝ)-27)) ≤
      (invE (11/5*invGamma*350):ℝ) := by
    rw [hheightIndex]
    exact hHeight0
  have hFrame := bank_history_frame_step_le_invSB_den M.gamma hγ hγ₀
  have hbase := bank_root_inverse_baseline_history_cap M Q m .full
    (invFullLi:ℝ) (invE (11/5*invGamma*350):ℝ) hQscale hLi hHeight hFrame
  have hLi0 : 0 ≤ (invFullLi:ℝ) := by
    have hroot := bank_root_Li_nonneg M.gamma .full
    linarith
  have hSource : (invFullB0:ℝ) = (invSB:ℝ) *
      ((invE (11*invGamma):ℝ) *
        ((invFullLi:ℝ) * (invE (11/5*invGamma*350):ℝ))) := by
    norm_num [invFullB0]
    ring
  exact hbase.trans (bank_history_baseline_coefficient_le_full_source
    (invFullLi:ℝ) (invE (11/5*invGamma*350):ℝ) (invFullB0:ℝ) hLi0 hSource)

/-- Assemble a same-scale single-root history split with its separate
deterministic baseline and positive-remainder caps. The sole geometric input
is the exact universal pointwise-root interface. -/
theorem bank_root_inverse_history_L128_split_of_caps
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (m J : ℤ)
    (hQ : Q.scale ≤ m) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hweights : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (r : RootRow) (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m r)
    (hPointwiseRoot : ∀ (Q' : TriadicCube 2) (m' J' : ℤ)
      (_hQ' : Q'.scale ≤ m') (_hmJ' : m' ≤ J') (weights' : ℤ → ℝ)
      (_hweights' : ∀ k ∈ Finset.Ioc m' J', 0 ≤ weights' k ∧ weights' k ≤ 1)
      (r' : RootRow) (_hpast' : ∀ n < m', nativeInductionState M h n)
      (_hmean' : ClippedInverseMeanInput M m' r'),
      PointwiseRootConclusion M Q' m' J' weights' r')
    (A δ e : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) (he : 0 ≤ e)
    (hBase : bankRootInverseBaselineHistory Q M m r ≤ ENNReal.ofReal A)
    (hRemainder : eLpNorm (bankRootInverseRemainderHistory Q M m r) 256
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal e) :
    eLpNorm (fun ω => (bankRootInverseHistory Q M m J weights ω).toReal) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal A + ENNReal.ofReal e ∧
      eLpNorm (fun ω => positiveSplitRemainder
        (bankRootInverseHistory Q M m J weights ω).toReal A δ) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
          ENNReal.ofReal (1 / (4 * δ)) * ENNReal.ofReal e ^ 2 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Y : Cutoff.CutoffSample 2 → ℝ≥0∞ :=
    bankRootInverseHistory Q M m J weights
  let R : Cutoff.CutoffSample 2 → ℝ≥0∞ :=
    bankRootInverseRemainderHistory Q M m r
  have hY : Measurable Y := bank_root_inverse_history_measurable Q M m J weights
  have hR : Measurable R := bank_root_inverse_remainder_history_measurable
    M h hM hg Q m J hQ hmJ weights hweights r hpast hmean hPointwiseRoot
  have hAffine : ∀ᵐ ω ∂μ, Y ω ≤ ENNReal.ofReal A + R ω := by
    filter_upwards [bank_root_inverse_history_split_of_pointwise M h Q m J hQ hmJ
      weights hweights r hpast hmean hPointwiseRoot] with ω hω
    exact hω.trans (add_le_add_left hBase (R ω))
  have hresult := bank_ennreal_positive_split_L128_of_affine μ Y R hY hR
    A δ e hA hδ he hAffine hRemainder
  simpa only [μ, Y, R] using hresult

/-- Real budget corresponding to a row's certified order-256 remainder cap. -/
noncomputable def bankRootHistoryRemainderAllowance (rho : ℝ) : ℝ :=
  (ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal rho *
    ENNReal.ofReal (invSR:ℝ)).toReal

theorem bankRootHistoryRemainderAllowance_ofReal (rho : ℝ) :
    ENNReal.ofReal (bankRootHistoryRemainderAllowance rho) =
      ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal rho *
        ENNReal.ofReal (invSR:ℝ) := by
  exact ENNReal.ofReal_toReal (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top)

end ASDExplicitGamma.Inverse

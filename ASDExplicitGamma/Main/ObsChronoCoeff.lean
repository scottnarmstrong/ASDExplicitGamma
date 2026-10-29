module

public import ASDExplicitGamma.Main.ErrorCorrected
public import ASDExplicitGamma.Main.SourcePrefixGates

/-! STEP-MA-CHRONOLOGY-V-MONOTONE, part 1: the explicit v-dependent coefficients of the main
loads and slopes are nondecreasing in `v ≥ 0` (for `0 ≤ γ ≤ γ₀`). -/

@[expose] public section

namespace ASDExplicitGamma.Main

noncomputable section

theorem chrono_mainA2_mono {v w : ℝ} (h : v ≤ w) : mainA2 v ≤ mainA2 w := by
  unfold mainA2; gcongr

theorem chrono_mainA4_mono {v w : ℝ} (h : v ≤ w) : mainA4 v ≤ mainA4 w := by
  unfold mainA4; gcongr

theorem chrono_mainA2_nonneg {v : ℝ} (h : 0 ≤ v) : 0 ≤ mainA2 v := by
  unfold mainA2; positivity

theorem chrono_mainA4_nonneg {v : ℝ} (h : 0 ≤ v) : 0 ≤ mainA4 v := by
  unfold mainA4; positivity

theorem chrono_mainKa_mono {v w : ℝ} (hv : 0 ≤ v) (h : v ≤ w) : mainKa v ≤ mainKa w := by
  unfold mainKa
  have h2 := chrono_mainA2_mono h
  have h4 := chrono_mainA4_mono h
  gcongr

theorem chrono_mainKd_mono {v w : ℝ} (hv : 0 ≤ v) (h : v ≤ w) : mainKd v ≤ mainKd w := by
  unfold mainKd
  have h2 := chrono_mainA2_mono h
  have h4 := chrono_mainA4_mono h
  gcongr

theorem chrono_mainKrem_mono {v w : ℝ} (hv : 0 ≤ v) (h : v ≤ w) : mainKrem v ≤ mainKrem w := by
  unfold mainKrem
  have h2 := chrono_mainA2_mono h
  have h4 := chrono_mainA4_mono h
  gcongr

theorem chrono_mainOp_mono {v w : ℝ} (hv : 0 ≤ v) (h : v ≤ w) : mainOp v ≤ mainOp w := by
  unfold mainOp
  have h2 := chrono_mainA2_mono h
  gcongr

theorem chrono_mainOm_mono {v w : ℝ} (hv : 0 ≤ v) (h : v ≤ w) : mainOm v ≤ mainOm w := by
  unfold mainOm
  have h2 := chrono_mainA2_mono h
  gcongr

theorem chrono_alpha_sq : mainAlpha ^ 2 = (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold mainAlpha
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem chrono_alpha_pos : 0 < mainAlpha := by unfold mainAlpha; positivity

theorem chrono_alpha_lt_one : mainAlpha < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- `α² 3^(rγ - n) ∈ [0,1)` on the source gamma interval. -/
theorem chrono_q_range {gamma r n : ℝ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hr : r ≤ 10) (hn : 0 ≤ n) :
    0 ≤ mainAlpha ^ 2 * (3 : ℝ) ^ (r * gamma - n) ∧
      mainAlpha ^ 2 * (3 : ℝ) ^ (r * gamma - n) < 1 := by
  refine ⟨by positivity, ?_⟩
  rw [chrono_alpha_sq, ← Real.rpow_add (by norm_num)]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  have hg' : gamma ≤ 17 / 50000 := by simpa [gammaZero] using hg
  nlinarith [mul_le_mul_of_nonneg_right hr hg0]

theorem chrono_rawA_nonneg {gamma : ℝ} (hg0 : 0 ≤ gamma) : 0 ≤ mainRawA gamma := by
  unfold mainRawA; positivity

theorem chrono_rawS_nonneg {gamma : ℝ} (hg0 : 0 ≤ gamma) : 0 ≤ mainRawS gamma := by
  unfold mainRawS; positivity

theorem chrono_rawFactor_nonneg (gamma : ℝ) : 0 ≤ mainRawFactor gamma := by
  unfold mainRawFactor; positivity

theorem chrono_rawGeo_nonneg {gamma q : ℝ} (hg0 : 0 ≤ gamma) (hq0 : 0 ≤ q) (hq : q < 1) :
    0 ≤ mainRawGeo gamma q := by
  unfold mainRawGeo
  have h1 : 0 < 1 - q := by linarith
  have := chrono_rawA_nonneg hg0
  have := chrono_rawS_nonneg hg0
  positivity

theorem chrono_rawW_nonneg {gamma r : ℝ} {n : ℕ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hr : r ≤ 10) : 0 ≤ mainRawW gamma r n := by
  unfold mainRawW
  have hq := chrono_q_range (n := (n : ℝ)) hg0 hg hr (by positivity)
  have h1 : 0 ≤ 1 - mainAlpha ^ 2 := by
    have := chrono_alpha_lt_one; have := chrono_alpha_pos; nlinarith
  exact mul_nonneg h1 (chrono_rawGeo_nonneg hg0 hq.1 hq.2)

theorem chrono_W_nonneg {gamma r : ℝ} {n : ℕ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hr : r ≤ 10) : 0 ≤ mainW gamma r n := by
  unfold mainW
  have hq := chrono_q_range (n := (n : ℝ)) hg0 hg hr (by positivity)
  have h1 : 0 ≤ 1 - mainAlpha ^ 2 := by
    have := chrono_alpha_lt_one; have := chrono_alpha_pos; nlinarith
  have h2 : 0 < 1 - mainAlpha ^ 2 * (3 : ℝ) ^ (r * gamma - n) := by linarith [hq.2]
  positivity

theorem chrono_beta_prime_range {gamma c : ℝ} {i : ℕ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hc : c ≤ 8) :
    0 ≤ mainBetaPrime * (3 : ℝ) ^ (c * gamma - i) ∧
      mainBetaPrime * (3 : ℝ) ^ (c * gamma - i) < 1 := by
  refine ⟨by unfold mainBetaPrime; positivity, ?_⟩
  unfold mainBetaPrime
  rw [← Real.rpow_add (by norm_num)]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  have hg' : gamma ≤ 17 / 50000 := by simpa [gammaZero] using hg
  have : (0 : ℝ) ≤ (i : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hc hg0]

theorem chrono_Pa_nonneg {v : ℝ} (hv : 0 ≤ v) (i : Fin 3) : 0 ≤ mainPa v i := by
  have h2 := chrono_mainA2_nonneg hv
  have h4 := chrono_mainA4_nonneg hv
  fin_cases i <;> simp [mainPa] <;> positivity

theorem chrono_Pa_mono {v w : ℝ} (hv : 0 ≤ v) (h : v ≤ w) (i : Fin 3) :
    mainPa v i ≤ mainPa w i := by
  have h2 := chrono_mainA2_mono h
  have h4 := chrono_mainA4_mono h
  fin_cases i <;> simp [mainPa] <;> gcongr

theorem chrono_Kf_mono {v w : ℝ} (h : v ≤ w) : mainKf v ≤ mainKf w := by
  unfold mainKf
  have := chrono_mainA2_mono h
  gcongr

theorem chrono_Kf_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ mainKf v := by
  unfold mainKf
  have := chrono_mainA2_nonneg hv
  positivity

theorem chrono_J0_mono {gamma v w : ℝ} (hg0 : 0 ≤ gamma) (h : v ≤ w) :
    mainJ0 v gamma ≤ mainJ0 w gamma := by
  unfold mainJ0 mainBetaOld; gcongr

theorem chrono_J0_nonneg {gamma v : ℝ} (hg0 : 0 ≤ gamma) (hv : 0 ≤ v) : 0 ≤ mainJ0 v gamma := by
  have := chrono_rawA_nonneg hg0
  have := chrono_rawFactor_nonneg gamma
  unfold mainJ0 mainBetaOld; positivity

theorem chrono_K0_mono {gamma v w : ℝ} (hg0 : 0 ≤ gamma) (h : v ≤ w) :
    mainK0 v gamma ≤ mainK0 w gamma := by
  unfold mainK0 mainBetaOld; gcongr

theorem chrono_K0_nonneg {gamma v : ℝ} (hg0 : 0 ≤ gamma) (hv : 0 ≤ v) : 0 ≤ mainK0 v gamma := by
  have := chrono_rawA_nonneg hg0
  have := chrono_rawFactor_nonneg gamma
  unfold mainK0 mainBetaOld; positivity

theorem chrono_mu_mono {gamma v w : ℝ} (hg0 : 0 ≤ gamma) (hv : 0 ≤ v) (h : v ≤ w) :
    mainMu v gamma ≤ mainMu w gamma := by
  have p0 := chrono_Pa_nonneg hv 0; have p1 := chrono_Pa_nonneg hv 1; have p2 := chrono_Pa_nonneg hv 2
  have m0 := chrono_Pa_mono hv h 0; have m1 := chrono_Pa_mono hv h 1; have m2 := chrono_Pa_mono hv h 2
  have hJ := chrono_J0_nonneg hg0 hv
  have hK := chrono_K0_nonneg hg0 hv
  have hKf := chrono_Kf_nonneg hv
  have mJ := chrono_J0_mono hg0 h
  have mK := chrono_K0_mono hg0 h
  have mKf := chrono_Kf_mono h
  have p0w := p0.trans m0; have p1w := p1.trans m1; have p2w := p2.trans m2
  have hKfw := hKf.trans mKf
  have hKw := hK.trans mK
  have hJw := hJ.trans mJ
  have hbo : 0 ≤ mainBetaOld + Real.sqrt 3 * mainEpsOld := by
    unfold mainBetaOld mainEpsOld; positivity
  unfold mainMu
  gcongr

theorem chrono_xiCoeff_nonneg {v : ℝ} (hv : 0 ≤ v) (i : Fin 3) : 0 ≤ mainXiCoefficients v i := by
  have p0 := chrono_Pa_nonneg hv 0; have p1 := chrono_Pa_nonneg hv 1; have p2 := chrono_Pa_nonneg hv 2
  fin_cases i <;> simp [mainXiCoefficients] <;> positivity

theorem chrono_xiCoeff_mono {v w : ℝ} (hv : 0 ≤ v) (h : v ≤ w) (i : Fin 3) :
    mainXiCoefficients v i ≤ mainXiCoefficients w i := by
  have p0 := chrono_Pa_nonneg hv 0; have p1 := chrono_Pa_nonneg hv 1; have p2 := chrono_Pa_nonneg hv 2
  have m0 := chrono_Pa_mono hv h 0; have m1 := chrono_Pa_mono hv h 1; have m2 := chrono_Pa_mono hv h 2
  have p0w := p0.trans m0; have p1w := p1.trans m1; have p2w := p2.trans m2
  fin_cases i <;> simp [mainXiCoefficients] <;> gcongr

theorem chrono_chi_mono {gamma v w : ℝ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hv : 0 ≤ v) (h : v ≤ w) : mainChi v gamma ≤ mainChi w gamma := by
  have hfac := chrono_rawFactor_nonneg gamma
  have hKf := chrono_Kf_nonneg hv
  have mKf := chrono_Kf_mono h
  have hKfw := hKf.trans mKf
  have hg' : gamma ≤ 17 / 50000 := by simpa [gammaZero] using hg
  have hlt : mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64) < 1 := by
    rw [chrono_alpha_sq, ← Real.rpow_add (by norm_num)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have h1a : 0 ≤ 1 - mainAlpha ^ 2 := by
    have := chrono_alpha_lt_one; have := chrono_alpha_pos; nlinarith
  have hden2 : 0 ≤ 1 - mainAlpha ^ 2 * (3 : ℝ) ^ (4 * gamma + 1 / 64) := by linarith
  have hW (i : Fin 3) : 0 ≤ mainW gamma 8 (i.val + 2) :=
    chrono_W_nonneg hg0 hg (by norm_num)
  have hRW (i : Fin 3) : 0 ≤ mainRawW gamma 10 (i.val + 2) :=
    chrono_rawW_nonneg hg0 hg (by norm_num)
  have hW6 : 0 ≤ mainW gamma 6 2 := chrono_W_nonneg hg0 hg (by norm_num)
  have hRW8 : 0 ≤ mainRawW gamma 8 2 := chrono_rawW_nonneg hg0 hg (by norm_num)
  have hW4 : 0 ≤ mainW gamma 4 0 := chrono_W_nonneg hg0 hg (by norm_num)
  have hε : 0 ≤ mainEpsOld := by unfold mainEpsOld; norm_num
  unfold mainChi
  gcongr with i hi
  all_goals
    first
    | exact chrono_xiCoeff_mono hv h i
    | exact chrono_xiCoeff_nonneg (hv.trans h) i
    | exact chrono_xiCoeff_nonneg hv i
    | exact hW i
    | exact hRW i
    | exact h1a
    | exact hden2
    | exact hε
    | (have h1 := hRW i; have h2 := hW i; have h3 := chrono_xiCoeff_nonneg hv i
       have h4 := chrono_xiCoeff_nonneg (hv.trans h) i
       unfold mainBetaOld; positivity)
    | (unfold mainBetaOld; positivity)

theorem chrono_envA_mono {gamma a0 t v w : ℝ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hv : 0 ≤ v) (h : v ≤ w) (ht : 0 ≤ t) :
    mainEnvelopeA v gamma a0 t ≤ mainEnvelopeA w gamma a0 t := by
  unfold mainEnvelopeA
  have := chrono_mu_mono hg0 hv h
  gcongr

theorem chrono_envXi_mono {gamma xiPre theta t v w : ℝ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hv : 0 ≤ v) (h : v ≤ w) (ht : 0 ≤ t) :
    mainEnvelopeXi v gamma xiPre theta t ≤ mainEnvelopeXi w gamma xiPre theta t := by
  unfold mainEnvelopeXi
  have := chrono_chi_mono hg0 hg hv h
  gcongr

theorem chrono_mainOp_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ mainOp v := by
  have := chrono_mainA2_nonneg hv; unfold mainOp; positivity

theorem chrono_mainOm_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ mainOm v := by
  have := chrono_mainA2_nonneg hv; unfold mainOm; positivity

theorem chrono_mainKd_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ mainKd v := by
  have := chrono_mainA2_nonneg hv; have := chrono_mainA4_nonneg hv; unfold mainKd; positivity

theorem chrono_mainKrem_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ mainKrem v := by
  have := chrono_mainA2_nonneg hv; have := chrono_mainA4_nonneg hv; unfold mainKrem; positivity

theorem chrono_mainKa_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ mainKa v := by
  have := chrono_mainA2_nonneg hv; have := chrono_mainA4_nonneg hv; unfold mainKa; positivity

end

end ASDExplicitGamma.Main

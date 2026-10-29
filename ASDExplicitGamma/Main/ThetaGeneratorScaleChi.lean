module

public import ASDExplicitGamma.Main.ThetaGeneratorScaleCoeff

/-! MA-THETA-CONTINUATION, coefficient scaling for the weak-history slope `χ`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

noncomputable section

theorem th_xiCoeff_scale {θ v : ℝ} (hθ : 0 ≤ θ) (i : Fin 3) :
    mainXiCoefficients (θ * v) i = θ * mainXiCoefficients v i := by
  have hs := th_sqrt_sq hθ
  have e0 := th_Pa_scale (v := v) hθ 0
  have e1 := th_Pa_scale (v := v) hθ 1
  have e2 := th_Pa_scale (v := v) hθ 2
  fin_cases i
  · show (232 / 125 : ℝ) * (mainPa (θ * v) 0 + mainPa (θ * v) 1) ^ 2 =
      θ * ((232 / 125 : ℝ) * (mainPa v 0 + mainPa v 1) ^ 2)
    rw [e0, e1]
    linear_combination (232 / 125 : ℝ) * (mainPa v 0 + mainPa v 1) ^ 2 * hs
  · show (464 / 125 : ℝ) * (mainPa (θ * v) 0 + mainPa (θ * v) 1) * mainPa (θ * v) 2 =
      θ * ((464 / 125 : ℝ) * (mainPa v 0 + mainPa v 1) * mainPa v 2)
    rw [e0, e1, e2]
    linear_combination (464 / 125 : ℝ) * (mainPa v 0 + mainPa v 1) * mainPa v 2 * hs
  · show (232 / 125 : ℝ) * mainPa (θ * v) 2 ^ 2 = θ * ((232 / 125 : ℝ) * mainPa v 2 ^ 2)
    rw [e2]
    linear_combination (232 / 125 : ℝ) * mainPa v 2 ^ 2 * hs

theorem th_chi_gamma_mono {v g g' : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ g') (hg' : g' ≤ gammaZero)
    (hv : 0 ≤ v) : mainChi v g ≤ mainChi v g' := by
  have hgz : g ≤ gammaZero := hg.trans hg'
  have hg'0 : 0 ≤ g' := hg0.trans hg
  have hF := th_rawFactor_mono hg
  have hF0 := chrono_rawFactor_nonneg g
  have hF0' := chrono_rawFactor_nonneg g'
  have hKf := chrono_Kf_nonneg hv
  have hg1 : g' ≤ 17 / 50000 := by simpa [gammaZero] using hg'
  have hlt : mainAlpha ^ 2 * (3 : ℝ) ^ (4 * g' + 1 / 64) < 1 := by
    rw [chrono_alpha_sq, ← Real.rpow_add (by norm_num)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have hpow : (3 : ℝ) ^ (4 * g + 1 / 64) ≤ (3 : ℝ) ^ (4 * g' + 1 / 64) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h1a : 0 ≤ 1 - mainAlpha ^ 2 := by
    have := chrono_alpha_lt_one; have := chrono_alpha_pos; nlinarith
  have hden : 0 < 1 - mainAlpha ^ 2 * (3 : ℝ) ^ (4 * g' + 1 / 64) := by linarith
  have hden' : 1 - mainAlpha ^ 2 * (3 : ℝ) ^ (4 * g' + 1 / 64) ≤
      1 - mainAlpha ^ 2 * (3 : ℝ) ^ (4 * g + 1 / 64) := by
    have : 0 ≤ mainAlpha ^ 2 := sq_nonneg _
    nlinarith
  have hW (i : Fin 3) : 0 ≤ mainW g 8 (i.val + 2) := chrono_W_nonneg hg0 hgz (by norm_num)
  have hW' (i : Fin 3) : 0 ≤ mainW g' 8 (i.val + 2) := chrono_W_nonneg hg'0 hg' (by norm_num)
  have hRW (i : Fin 3) : 0 ≤ mainRawW g 10 (i.val + 2) := chrono_rawW_nonneg hg0 hgz (by norm_num)
  have hRW' (i : Fin 3) : 0 ≤ mainRawW g' 10 (i.val + 2) := chrono_rawW_nonneg hg'0 hg' (by norm_num)
  have mW (i : Fin 3) : mainW g 8 (i.val + 2) ≤ mainW g' 8 (i.val + 2) :=
    th_W_mono hg0 hg hg' (by norm_num) (by norm_num)
  have mRW (i : Fin 3) : mainRawW g 10 (i.val + 2) ≤ mainRawW g' 10 (i.val + 2) :=
    th_rawW_mono hg0 hg hg' (by norm_num) (by norm_num)
  have hW6 := chrono_W_nonneg (r := 6) (n := 2) hg0 hgz (by norm_num)
  have hW6' := chrono_W_nonneg (r := 6) (n := 2) hg'0 hg' (by norm_num)
  have mW6 : mainW g 6 2 ≤ mainW g' 6 2 := th_W_mono hg0 hg hg' (by norm_num) (by norm_num)
  have hRW8 := chrono_rawW_nonneg (r := 8) (n := 2) hg0 hgz (by norm_num)
  have hRW8' := chrono_rawW_nonneg (r := 8) (n := 2) hg'0 hg' (by norm_num)
  have mRW8 : mainRawW g 8 2 ≤ mainRawW g' 8 2 :=
    th_rawW_mono hg0 hg hg' (by norm_num) (by norm_num)
  have hW4 := chrono_W_nonneg (r := 4) (n := 0) hg0 hgz (by norm_num)
  have hW4' := chrono_W_nonneg (r := 4) (n := 0) hg'0 hg' (by norm_num)
  have mW4 : mainW g 4 0 ≤ mainW g' 4 0 := th_W_mono hg0 hg hg' (by norm_num) (by norm_num)
  have hε : 0 ≤ mainEpsOld := by unfold mainEpsOld; norm_num
  have hxi (i : Fin 3) := chrono_xiCoeff_nonneg hv i
  unfold mainChi
  gcongr with i hi
  all_goals
    first
    | exact hxi i
    | exact hW i
    | exact hW' i
    | exact hRW i
    | exact hRW' i
    | exact mW i
    | exact mRW i
    | exact hW6'
    | exact hRW8'
    | exact hW4'
    | exact h1a
    | exact hden
    | exact hden'
    | exact hε
    | exact hF
    | exact hF0'
    | exact hF0
    | (have h1 := hRW i; have h2 := hW i; have h3 := hxi i
       unfold mainBetaOld; positivity)
    | (unfold mainBetaOld; positivity)

theorem th_chi_hom {θ v g : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hg0 : 0 ≤ g) (hg : g ≤ gammaZero)
    (hv : 0 ≤ v) : mainChi (θ * v) g ≤ θ * mainChi v g := by
  have hθv : θ * v ≤ v := by nlinarith
  have hF0 := chrono_rawFactor_nonneg g
  have hKf := chrono_Kf_nonneg hv
  have hW (i : Fin 3) : 0 ≤ mainW g 8 (i.val + 2) := chrono_W_nonneg hg0 hg (by norm_num)
  have hRW (i : Fin 3) : 0 ≤ mainRawW g 10 (i.val + 2) := chrono_rawW_nonneg hg0 hg (by norm_num)
  have hW6 := chrono_W_nonneg (r := 6) (n := 2) hg0 hg (by norm_num)
  have hRW8 := chrono_rawW_nonneg (r := 8) (n := 2) hg0 hg (by norm_num)
  have hxi (i : Fin 3) := chrono_xiCoeff_nonneg hv i
  have hsum : ∑ i : Fin 3, mainXiCoefficients (θ * v) i *
      ((26 / 25) * mainBetaOld ^ 3 * mainRawFactor g * mainRawW g 10 (i.val + 2) +
        52 * (θ * v) * Real.sqrt 3 * mainBetaOld ^ 4 * mainW g 8 (i.val + 2)) ≤
      θ * ∑ i : Fin 3, mainXiCoefficients v i *
      ((26 / 25) * mainBetaOld ^ 3 * mainRawFactor g * mainRawW g 10 (i.val + 2) +
        52 * v * Real.sqrt 3 * mainBetaOld ^ 4 * mainW g 8 (i.val + 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [th_xiCoeff_scale hθ, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hθ
    apply mul_le_mul_of_nonneg_left _ (hxi i)
    have := hRW i; have := hW i
    have : 52 * (θ * v) * Real.sqrt 3 * mainBetaOld ^ 4 * mainW g 8 (i.val + 2) ≤
        52 * v * Real.sqrt 3 * mainBetaOld ^ 4 * mainW g 8 (i.val + 2) := by
      unfold mainBetaOld; gcongr
    linarith
  have h2 : 2 * (θ * mainKf v) *
      ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor g * mainRawW g 8 2 +
        52 * (θ * v) * Real.sqrt 3 * mainBetaOld ^ 3 * mainW g 6 2) ≤
      θ * (2 * mainKf v *
      ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor g * mainRawW g 8 2 +
        52 * v * Real.sqrt 3 * mainBetaOld ^ 3 * mainW g 6 2)) := by
    have : 52 * (θ * v) * Real.sqrt 3 * mainBetaOld ^ 3 * mainW g 6 2 ≤
        52 * v * Real.sqrt 3 * mainBetaOld ^ 3 * mainW g 6 2 := by
      unfold mainBetaOld; gcongr
    have h3 : 0 ≤ mainKf v := hKf
    have h4 : (26 / 25) * mainBetaOld ^ 2 * mainRawFactor g * mainRawW g 8 2 +
        52 * (θ * v) * Real.sqrt 3 * mainBetaOld ^ 3 * mainW g 6 2 ≤
        (26 / 25) * mainBetaOld ^ 2 * mainRawFactor g * mainRawW g 8 2 +
        52 * v * Real.sqrt 3 * mainBetaOld ^ 3 * mainW g 6 2 := by linarith
    calc _ = θ * (2 * mainKf v *
        ((26 / 25) * mainBetaOld ^ 2 * mainRawFactor g * mainRawW g 8 2 +
          52 * (θ * v) * Real.sqrt 3 * mainBetaOld ^ 3 * mainW g 6 2)) := by ring
      _ ≤ _ := by gcongr
  unfold mainChi
  rw [th_Kf_scale]
  have e3 : 2 * (θ * v) * mainBetaOld ^ 2 * mainW g 4 0 =
      θ * (2 * v * mainBetaOld ^ 2 * mainW g 4 0) := by ring
  have e4 : 2 * (θ * v) * mainBetaOld * Real.sqrt 3 * mainEpsOld * (1 - mainAlpha ^ 2) /
      (1 - mainAlpha ^ 2 * (3 : ℝ) ^ (4 * g + 1 / 64)) =
      θ * (2 * v * mainBetaOld * Real.sqrt 3 * mainEpsOld * (1 - mainAlpha ^ 2) /
      (1 - mainAlpha ^ 2 * (3 : ℝ) ^ (4 * g + 1 / 64))) := by ring
  rw [e3, e4]
  nlinarith [hsum, h2]

theorem th_chi_scale_le {θ v w g g' : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hg0 : 0 ≤ g)
    (hg : g ≤ g') (hg' : g' ≤ gammaZero) (hv : 0 ≤ v) (hw : 0 ≤ w) (hvw : v ≤ θ * w) :
    mainChi v g ≤ θ * mainChi w g' := by
  calc mainChi v g ≤ mainChi (θ * w) g := chrono_chi_mono hg0 (hg.trans hg') hv hvw
    _ ≤ mainChi (θ * w) g' := th_chi_gamma_mono hg0 hg hg' (hv.trans hvw)
    _ ≤ θ * mainChi w g' := th_chi_hom hθ hθ1 (hg0.trans hg) hg' hw

end

end ASDExplicitGamma.Main

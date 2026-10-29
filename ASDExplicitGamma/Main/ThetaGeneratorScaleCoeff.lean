module

public import ASDExplicitGamma.Main.ObsChronoCoeff
public import ASDExplicitGamma.Main.ObsChronoError

/-! MA-THETA-CONTINUATION, coefficient scaling: for `v ≤ θ w` and `γ ≤ γ'` (both below `γ₀`), the
ordinary-mean slope `μ(v,γ)` and the weak-history slope `χ(v,γ)` are at most `θ μ(w,γ')`,
`θ χ(w,γ')`.  Monotone in `γ`, and of degree at least one in the clock. -/

@[expose] public section

namespace ASDExplicitGamma.Main

noncomputable section

theorem th_rawFactor_mono {g g' : ℝ} (h : g ≤ g') : mainRawFactor g ≤ mainRawFactor g' := by
  unfold mainRawFactor
  have : (3 : ℝ) ^ (26 * g) ≤ (3 : ℝ) ^ (26 * g') :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  linarith

theorem th_rawA_mono {g g' : ℝ} (h : g ≤ g') : mainRawA g ≤ mainRawA g' := by
  unfold mainRawA; linarith

theorem th_rawS_mono {g g' : ℝ} (h : g ≤ g') : mainRawS g ≤ mainRawS g' := by
  unfold mainRawS; linarith

theorem th_rawGeo_mono {g g' q q' : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ g') (hq0 : 0 ≤ q)
    (hqq : q ≤ q') (hq' : q' < 1) : mainRawGeo g q ≤ mainRawGeo g' q' := by
  have hA := th_rawA_mono hg
  have hS := th_rawS_mono hg
  have hA0 := chrono_rawA_nonneg hg0
  have hS0 := chrono_rawS_nonneg hg0
  have h1 : 0 < 1 - q' := by linarith
  have h2 : 1 - q' ≤ 1 - q := by linarith
  have hA0' := hA0.trans hA
  have hS0' := hS0.trans hS
  have hSq : 0 ≤ mainRawS g' * q' := mul_nonneg hS0' (hq0.trans hqq)
  unfold mainRawGeo
  gcongr

theorem th_rawW_mono {g g' r : ℝ} {n : ℕ} (hg0 : 0 ≤ g) (hg : g ≤ g') (hg' : g' ≤ gammaZero)
    (hr0 : 0 ≤ r) (hr : r ≤ 10) : mainRawW g r n ≤ mainRawW g' r n := by
  have hq := chrono_q_range (n := (n : ℝ)) (r := r) hg0 (hg.trans hg') hr (by positivity)
  have hq' := chrono_q_range (n := (n : ℝ)) (r := r) (hg0.trans hg) hg' hr (by positivity)
  have hpow : (3 : ℝ) ^ (r * g - n) ≤ (3 : ℝ) ^ (r * g' - n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hqq : mainAlpha ^ 2 * (3 : ℝ) ^ (r * g - n) ≤ mainAlpha ^ 2 * (3 : ℝ) ^ (r * g' - n) := by
    gcongr
  have h1 : 0 ≤ 1 - mainAlpha ^ 2 := by
    have := chrono_alpha_lt_one; have := chrono_alpha_pos; nlinarith
  unfold mainRawW
  exact mul_le_mul_of_nonneg_left (th_rawGeo_mono hg0 hg hq.1 hqq hq'.2) h1

theorem th_W_mono {g g' r : ℝ} {n : ℕ} (hg0 : 0 ≤ g) (hg : g ≤ g') (hg' : g' ≤ gammaZero)
    (hr0 : 0 ≤ r) (hr : r ≤ 10) : mainW g r n ≤ mainW g' r n := by
  have hq := chrono_q_range (n := (n : ℝ)) (r := r) hg0 (hg.trans hg') hr (by positivity)
  have hq' := chrono_q_range (n := (n : ℝ)) (r := r) (hg0.trans hg) hg' hr (by positivity)
  have hpow : (3 : ℝ) ^ (r * g - n) ≤ (3 : ℝ) ^ (r * g' - n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hqq : mainAlpha ^ 2 * (3 : ℝ) ^ (r * g - n) ≤ mainAlpha ^ 2 * (3 : ℝ) ^ (r * g' - n) := by
    gcongr
  have h1 : 0 ≤ 1 - mainAlpha ^ 2 := by
    have := chrono_alpha_lt_one; have := chrono_alpha_pos; nlinarith
  have hd : 0 < 1 - mainAlpha ^ 2 * (3 : ℝ) ^ (r * g' - n) := by linarith [hq'.2]
  unfold mainW
  apply div_le_div_of_nonneg_left h1 hd
  linarith

theorem th_J0_gamma_mono {v g g' : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ g') :
    mainJ0 v g ≤ mainJ0 v g' := by
  have hF := th_rawFactor_mono hg
  have hA := th_rawA_mono hg
  have hF0 := chrono_rawFactor_nonneg g
  have hA0 := chrono_rawA_nonneg hg0
  have hF0' := hF0.trans hF
  unfold mainJ0 mainBetaOld
  gcongr

theorem th_K0_gamma_mono {v g g' : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ g') :
    mainK0 v g ≤ mainK0 v g' := by
  have hF := th_rawFactor_mono hg
  have hA := th_rawA_mono hg
  have hF0 := chrono_rawFactor_nonneg g
  have hA0 := chrono_rawA_nonneg hg0
  have hF0' := hF0.trans hF
  unfold mainK0 mainBetaOld
  gcongr

theorem th_mu_gamma_mono {v g g' : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ g') (hv : 0 ≤ v) :
    mainMu v g ≤ mainMu v g' := by
  have p0 := chrono_Pa_nonneg hv 0; have p1 := chrono_Pa_nonneg hv 1
  have p2 := chrono_Pa_nonneg hv 2
  have hJ := th_J0_gamma_mono (v := v) hg0 hg
  have hK := th_K0_gamma_mono (v := v) hg0 hg
  have hKf := chrono_Kf_nonneg hv
  have hJ0 := chrono_J0_nonneg hg0 hv
  have hK0 := chrono_K0_nonneg hg0 hv
  unfold mainMu
  gcongr

theorem th_Pa_scale {θ v : ℝ} (hθ : 0 ≤ θ) (i : Fin 3) :
    mainPa (θ * v) i = Real.sqrt θ * mainPa v i := by
  have hA2 : mainA2 (θ * v) = θ * mainA2 v := by unfold mainA2; ring
  have hA4 : mainA4 (θ * v) = θ * mainA4 v := by unfold mainA4; ring
  fin_cases i
  · show Real.sqrt (39 / 5 * mainA2 (θ * v)) = Real.sqrt θ * Real.sqrt (39 / 5 * mainA2 v)
    rw [hA2, show 39 / 5 * (θ * mainA2 v) = θ * (39 / 5 * mainA2 v) by ring, Real.sqrt_mul hθ]
  · show 36 / 25 * Real.sqrt (156 / 5 * mainA2 (θ * v)) =
      Real.sqrt θ * (36 / 25 * Real.sqrt (156 / 5 * mainA2 v))
    rw [hA2, show 156 / 5 * (θ * mainA2 v) = θ * (156 / 5 * mainA2 v) by ring, Real.sqrt_mul hθ]
    ring
  · show 57 / 200 * Real.sqrt (46488 / 25 * mainA4 (θ * v)) =
      Real.sqrt θ * (57 / 200 * Real.sqrt (46488 / 25 * mainA4 v))
    rw [hA4, show 46488 / 25 * (θ * mainA4 v) = θ * (46488 / 25 * mainA4 v) by ring,
      Real.sqrt_mul hθ]
    ring

theorem th_Kf_scale (θ v : ℝ) : mainKf (θ * v) = θ * mainKf v := by
  unfold mainKf mainA2; ring

theorem th_sqrt_sq {θ : ℝ} (hθ : 0 ≤ θ) : Real.sqrt θ * Real.sqrt θ = θ :=
  Real.mul_self_sqrt hθ

theorem th_J0_scale_le {θ v g : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hg0 : 0 ≤ g) (hv : 0 ≤ v) :
    mainJ0 (θ * v) g ≤ mainJ0 v g := by
  have hF0 := chrono_rawFactor_nonneg g
  have hA0 := chrono_rawA_nonneg hg0
  have : θ * v ≤ v := by nlinarith
  exact chrono_J0_mono hg0 this

theorem th_K0_scale_le {θ v g : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hg0 : 0 ≤ g) (hv : 0 ≤ v) :
    mainK0 (θ * v) g ≤ mainK0 v g := by
  have : θ * v ≤ v := by nlinarith
  exact chrono_K0_mono hg0 this

theorem th_mu_hom {θ v g : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hg0 : 0 ≤ g) (hv : 0 ≤ v) :
    mainMu (θ * v) g ≤ θ * mainMu v g := by
  have hS : (mainPa (θ * v) 0 + mainPa (θ * v) 1 + mainPa (θ * v) 2) ^ 2 =
      θ * (mainPa v 0 + mainPa v 1 + mainPa v 2) ^ 2 := by
    rw [th_Pa_scale hθ, th_Pa_scale hθ, th_Pa_scale hθ]
    calc _ = (Real.sqrt θ * Real.sqrt θ) * (mainPa v 0 + mainPa v 1 + mainPa v 2) ^ 2 := by ring
      _ = _ := by rw [th_sqrt_sq hθ]
  have hJ := th_J0_scale_le hθ hθ1 hg0 hv
  have hK := th_K0_scale_le hθ hθ1 hg0 hv
  have p0 := chrono_Pa_nonneg hv 0; have p1 := chrono_Pa_nonneg hv 1
  have p2 := chrono_Pa_nonneg hv 2
  have hKf := chrono_Kf_nonneg hv
  have hrest : 0 ≤ mainBetaOld + Real.sqrt 3 * mainEpsOld := by
    unfold mainBetaOld mainEpsOld; positivity
  have hS0 : 0 ≤ (mainPa v 0 + mainPa v 1 + mainPa v 2) ^ 2 := sq_nonneg _
  unfold mainMu
  rw [hS, th_Kf_scale]
  have e1 : (232 / 125 : ℝ) * (θ * (mainPa v 0 + mainPa v 1 + mainPa v 2) ^ 2) * mainJ0 (θ * v) g ≤
      (232 / 125 : ℝ) * (θ * (mainPa v 0 + mainPa v 1 + mainPa v 2) ^ 2) * mainJ0 v g := by
    gcongr
  have e2 : 2 * (θ * mainKf v) * mainK0 (θ * v) g ≤ 2 * (θ * mainKf v) * mainK0 v g := by
    gcongr
  nlinarith [e1, e2]

theorem th_mu_scale_le {θ v w g g' : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hg0 : 0 ≤ g)
    (hg : g ≤ g') (hv : 0 ≤ v) (hw : 0 ≤ w) (hvw : v ≤ θ * w) :
    mainMu v g ≤ θ * mainMu w g' := by
  calc mainMu v g ≤ mainMu (θ * w) g := chrono_mu_mono hg0 hv hvw
    _ ≤ mainMu (θ * w) g' := th_mu_gamma_mono hg0 hg (hv.trans hvw)
    _ ≤ θ * mainMu w g' := th_mu_hom hθ hθ1 (hg0.trans hg) hw

end

end ASDExplicitGamma.Main

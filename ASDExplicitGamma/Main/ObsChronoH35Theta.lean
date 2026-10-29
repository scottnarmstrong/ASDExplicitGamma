module

public import ASDExplicitGamma.Main.EnvelopeHSharpEnv
public import ASDExplicitGamma.Main.ObsChronoCoeff
public import ASDExplicitGamma.Main.ObsChronoError

/-! The envelope `H35`: theta-scaling of the slope `δ'_H`, and the shape needed by the
theta-scaled source error. -/

@[expose] public section

namespace ASDExplicitGamma.Main

noncomputable section

/-- `δ'_H(γ) = γ · G(γ)`. -/
def chronoG35 (gamma : ℝ) : ℝ :=
  (1 - mainAlpha) *
    ((540 * (3 : ℝ) ^ (12 * gamma)) / (1 - mainBetaPrime * (3 : ℝ) ^ (2 * gamma)) +
      ((9 / 10 : ℝ) * (3 : ℝ) ^ (48 * gamma)) *
        (mainRawA gamma / (1 - mainBetaPrime * (3 : ℝ) ^ (8 * gamma) * (1 / 9 : ℝ)) +
          mainRawS gamma * ((mainBetaPrime * (3 : ℝ) ^ (8 * gamma) * (1 / 9 : ℝ)) /
            (1 - mainBetaPrime * (3 : ℝ) ^ (8 * gamma) * (1 / 9 : ℝ)) ^ 2)))

theorem chrono_deltaH35_eq (gamma : ℝ) : mainDeltaH35 gamma = gamma * chronoG35 gamma := by
  unfold mainDeltaH35 chronoG35; ring

theorem chrono_betaPrime_pos : 0 < mainBetaPrime := by unfold mainBetaPrime; positivity

theorem chrono_denom0 {gamma : ℝ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) :
    0 < 1 - mainBetaPrime * (3 : ℝ) ^ (2 * gamma) := by
  have := chrono_beta_prime_range (i := 0) (c := 2) hg0 hg (by norm_num)
  have h := this.2
  simp at h
  linarith

theorem chrono_denom1 {gamma : ℝ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) :
    0 < 1 - mainBetaPrime * (3 : ℝ) ^ (8 * gamma) * (1 / 9 : ℝ) := by
  have := chrono_beta_prime_range (i := 0) (c := 8) hg0 hg (by norm_num)
  have h := this.2
  have h0 := this.1
  simp at h h0
  linarith

theorem chrono_G35_mono {g g' : ℝ} (hg0 : 0 ≤ g) (hgg : g ≤ g') (hg' : g' ≤ gammaZero) :
    chronoG35 g ≤ chronoG35 g' := by
  have hg'0 : 0 ≤ g' := hg0.trans hgg
  have hgz : g ≤ gammaZero := hgg.trans hg'
  have d0 := chrono_denom0 hg0 hgz
  have d0' := chrono_denom0 hg'0 hg'
  have d1 := chrono_denom1 hg0 hgz
  have d1' := chrono_denom1 hg'0 hg'
  have hbp := chrono_betaPrime_pos
  have hA : mainRawA g ≤ mainRawA g' := by unfold mainRawA; gcongr
  have hS : mainRawS g ≤ mainRawS g' := by unfold mainRawS; gcongr
  have hA0 := chrono_rawA_nonneg hg0
  have hS0 := chrono_rawS_nonneg hg0
  have p2 : (3 : ℝ) ^ (2 * g) ≤ (3 : ℝ) ^ (2 * g') :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have p8 : (3 : ℝ) ^ (8 * g) ≤ (3 : ℝ) ^ (8 * g') :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have p12 : (3 : ℝ) ^ (12 * g) ≤ (3 : ℝ) ^ (12 * g') :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have p48 : (3 : ℝ) ^ (48 * g) ≤ (3 : ℝ) ^ (48 * g') :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hα : 0 ≤ 1 - mainAlpha := by have := chrono_alpha_lt_one; linarith
  have e0 : 1 - mainBetaPrime * (3 : ℝ) ^ (2 * g') ≤ 1 - mainBetaPrime * (3 : ℝ) ^ (2 * g) := by
    nlinarith
  have e1 : 1 - mainBetaPrime * (3 : ℝ) ^ (8 * g') * (1 / 9 : ℝ) ≤
      1 - mainBetaPrime * (3 : ℝ) ^ (8 * g) * (1 / 9 : ℝ) := by nlinarith
  have r1 : mainBetaPrime * (3 : ℝ) ^ (8 * g) * (1 / 9 : ℝ) ≤
      mainBetaPrime * (3 : ℝ) ^ (8 * g') * (1 / 9 : ℝ) := by gcongr
  have r10 : 0 ≤ mainBetaPrime * (3 : ℝ) ^ (8 * g) * (1 / 9 : ℝ) := by positivity
  have hA0' := chrono_rawA_nonneg hg'0
  have hS0' := chrono_rawS_nonneg hg'0
  have r10' : 0 ≤ mainBetaPrime * (3 : ℝ) ^ (8 * g') * (1 / 9 : ℝ) := by positivity
  unfold chronoG35
  gcongr
  all_goals first | positivity | linarith | skip

theorem mainDeltaH35_theta_scale_le {g : ℝ} (hg0 : 0 < g) (hg : g ≤ gammaZero) :
    mainDeltaH35 g ≤ (g / gammaZero) * mainDeltaH35 gammaZero := by
  have hz : (0 : ℝ) < gammaZero := by norm_num [gammaZero]
  have hG := chrono_G35_mono hg0.le hg le_rfl
  rw [chrono_deltaH35_eq, chrono_deltaH35_eq]
  calc g * chronoG35 g ≤ g * chronoG35 gammaZero := mul_le_mul_of_nonneg_left hG hg0.le
    _ = _ := by field_simp

theorem chrono_envH35_nonneg (v gamma t : ℝ) : 0 ≤ mainEnvelopeH35 v gamma t := sq_nonneg _

/-- `H35` is nondecreasing in `v` (for `t ≥ 0`). -/
theorem chrono_envH35_mono {gamma t v w : ℝ} (ht : 0 ≤ t) (h : v ≤ w) :
    mainEnvelopeH35 v gamma t ≤ mainEnvelopeH35 w gamma t := by
  unfold mainEnvelopeH35
  have hbo : 0 ≤ (3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
      (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld := by positivity
  gcongr

/-- The theta-scaled `H35`: the initial strong-history size `H₀` carries the degree `θ`
(`strong20 ≤ (2379/2500) θ`), the slope is `δ'_H(γ)`. -/
def mainEnvelopeH35Theta (theta v gamma t : ℝ) : ℝ :=
  (Real.sqrt (theta * mainH0 + mainDeltaH35 gamma * t) + Real.sqrt (2 * v * t) *
    ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
      (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld)) ^ 2

/-- Degree-one scaling of the envelope: for `0 < γ ≤ γ₀`, `θ = γ/γ₀`, `t ≥ 0` and
`v ≤ θ · w`, `H35_θ(v, γ, t) ≤ θ · H35(w, γ₀, t)`. -/
theorem chrono_envH35Theta_scale_le {gamma t v w : ℝ} (hg0 : 0 < gamma) (hg : gamma ≤ gammaZero)
    (ht : 0 ≤ t) (hw : 0 ≤ w) (hv : v ≤ gamma / gammaZero * w) :
    mainEnvelopeH35Theta (gamma / gammaZero) v gamma t ≤
      gamma / gammaZero * mainEnvelopeH35 w gammaZero t := by
  have hz : (0 : ℝ) < gammaZero := by norm_num [gammaZero]
  set θ := gamma / gammaZero with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hg0.le hz.le
  have hδ : mainDeltaH35 gamma ≤ θ * mainDeltaH35 gammaZero := mainDeltaH35_theta_scale_le hg0 hg
  set K := (3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
      (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld with hK
  have hK0 : 0 ≤ K := by positivity
  have hH0 : 0 ≤ mainH0 := by unfold mainH0; positivity
  have h1 : θ * mainH0 + mainDeltaH35 gamma * t ≤ θ * (mainH0 + mainDeltaH35 gammaZero * t) := by
    nlinarith [mul_le_mul_of_nonneg_right hδ ht]
  have s1 : Real.sqrt (θ * mainH0 + mainDeltaH35 gamma * t) ≤
      Real.sqrt θ * Real.sqrt (mainH0 + mainDeltaH35 gammaZero * t) := by
    rw [← Real.sqrt_mul hθ0]; exact Real.sqrt_le_sqrt h1
  have h2 : 2 * v * t ≤ θ * (2 * w * t) := by nlinarith [mul_le_mul_of_nonneg_right hv ht]
  have s2 : Real.sqrt (2 * v * t) ≤ Real.sqrt θ * Real.sqrt (2 * w * t) := by
    rw [← Real.sqrt_mul hθ0]; exact Real.sqrt_le_sqrt h2
  unfold mainEnvelopeH35Theta mainEnvelopeH35
  have hsum : Real.sqrt (θ * mainH0 + mainDeltaH35 gamma * t) + Real.sqrt (2 * v * t) * K ≤
      Real.sqrt θ * (Real.sqrt (mainH0 + mainDeltaH35 gammaZero * t) +
        Real.sqrt (2 * w * t) * K) := by
    nlinarith [mul_le_mul_of_nonneg_right s2 hK0]
  have hnn : 0 ≤ Real.sqrt (θ * mainH0 + mainDeltaH35 gamma * t) + Real.sqrt (2 * v * t) * K := by
    positivity
  calc (Real.sqrt (θ * mainH0 + mainDeltaH35 gamma * t) + Real.sqrt (2 * v * t) * K) ^ 2
      ≤ (Real.sqrt θ * (Real.sqrt (mainH0 + mainDeltaH35 gammaZero * t) +
        Real.sqrt (2 * w * t) * K)) ^ 2 := pow_le_pow_left₀ hnn hsum 2
    _ = θ * (Real.sqrt (mainH0 + mainDeltaH35 gammaZero * t) +
        Real.sqrt (2 * w * t) * K) ^ 2 := by rw [mul_pow, Real.sq_sqrt hθ0]

end

end ASDExplicitGamma.Main

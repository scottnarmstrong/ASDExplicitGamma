module

public import ASDExplicitGamma.Main.ThetaGeneratorErrorFixedQ

/-! The proportional-clock scaling of the literal source error.
It is derived from the original scaling theorem plus the exact difference
`mainError' - mainError = 2 (k_rem R₁ + k_d t₀) t₀ (√(v+vq/4) - √v)`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

theorem mainError_sub_mainError_Fq (v a f H xi Lq ecov AG be kd krem op om q : ℝ) :
    mainError' v a f H xi Lq ecov AG be kd krem op om q =
      mainError v a f H xi Lq ecov AG be kd krem op om +
        2 * (krem * mainR1 a f H + kd * mainT0 xi) * mainT0 xi *
          (Real.sqrt (v + v * q / 4) - Real.sqrt v) := by
  unfold mainError' mainError
  ring

theorem mainSourceError_sub_mainSourceError_Fq (v a f H xi q : ℝ) :
    mainSourceError' v a f H xi q =
      mainSourceError v a f H xi q +
        2 * (mainKrem v * mainR1 a f H + mainKd v * mainT0 xi) * mainT0 xi *
          (Real.sqrt (v + v * q / 4) - Real.sqrt v) := by
  unfold mainSourceError' mainSourceError
  exact mainError_sub_mainError_Fq ..

/-- The covariance residual factor under proportional scaling of the clock, with the
covariance cap scaled as well (as in `mainSourceError_theta_scale_le_Fq'`). -/
theorem mainErrResidual_theta_le_Fq {theta v q : ℝ} (hθ : 0 ≤ theta) (hθ1 : theta ≤ 1)
    (hv : 0 ≤ v) (hq : 0 ≤ q) :
    Real.sqrt (theta * v + theta * v * q / 4) ≤
      Real.sqrt theta * Real.sqrt (v + v * q / 4) := by
  rw [← Real.sqrt_mul hθ]
  apply Real.sqrt_le_sqrt
  have hvq : 0 ≤ v * q := mul_nonneg hv hq
  nlinarith only [mul_nonneg (sub_nonneg.mpr hθ1) (mul_nonneg hθ hvq)]

/-- The corrected seven-row source error is sublinear under the proportional clock. -/
theorem mainSourceError_theta_scale_le_Fq {theta v a f H xi q : ℝ}
    (hθ : 0 ≤ theta) (hθ1 : theta ≤ 1) (hv : 0 ≤ v)
    (hH : 0 ≤ H) (hq : 0 ≤ q) :
    mainSourceError' (theta * v) (theta * a) (theta * f) (theta * H)
        (theta * xi) q ≤
      theta * mainSourceError' v a f H xi q := by
  have h0 := mainSourceError_theta_scale_le_Fq' (a := a) (f := f) (xi := xi) hθ hθ1 hv hH hq
  rw [mainSourceError_sub_mainSourceError_Fq, mainSourceError_sub_mainSourceError_Fq]
  set c := 2 * (mainKrem v * mainR1 a f H + mainKd v * mainT0 xi) * mainT0 xi with hc
  have hR1 : 0 ≤ mainR1 a f H := Real.sqrt_nonneg _
  have hT0 : 0 ≤ mainT0 xi := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := by
    rw [hc]
    have := mainKd_nonneg v
    have := mainKrem_nonneg v
    positivity
  have hscale : 2 * (mainKrem (theta * v) * mainR1 (theta * a) (theta * f) (theta * H) +
      mainKd (theta * v) * mainT0 (theta * xi)) * mainT0 (theta * xi) =
      theta * Real.sqrt theta * c := by
    rw [mainKrem_theta_scale_Fq hθ, mainR1_theta_scale_Fq hθ, mainKd_theta_scale_Fq hθ,
      mainT0_theta_scale_Fq hθ, hc]
    have hs : Real.sqrt theta * Real.sqrt theta = theta := Real.mul_self_sqrt hθ
    calc _ = (Real.sqrt theta * Real.sqrt theta) * Real.sqrt theta *
          (2 * (mainKrem v * mainR1 a f H + mainKd v * mainT0 xi) * mainT0 xi) := by ring
      _ = _ := by rw [hs]
  rw [hscale]
  have hΔ : 0 ≤ Real.sqrt (v + v * q / 4) - Real.sqrt v := by
    have : v ≤ v + v * q / 4 := by nlinarith only [mul_nonneg hv hq]
    linarith only [Real.sqrt_le_sqrt this]
  have hres := mainErrResidual_theta_le_Fq hθ hθ1 hv hq
  have hsq : Real.sqrt (theta * v) = Real.sqrt theta * Real.sqrt v := Real.sqrt_mul hθ v
  have hs : Real.sqrt theta * Real.sqrt theta = theta := Real.mul_self_sqrt hθ
  have hst : 0 ≤ Real.sqrt theta := Real.sqrt_nonneg _
  have hdiff : Real.sqrt (theta * v + theta * v * q / 4) - Real.sqrt (theta * v) ≤
      Real.sqrt theta * (Real.sqrt (v + v * q / 4) - Real.sqrt v) := by
    rw [hsq]; nlinarith only [hres]
  have hmain : theta * Real.sqrt theta * c *
      (Real.sqrt (theta * v + theta * v * q / 4) - Real.sqrt (theta * v)) ≤
      theta * (c * (Real.sqrt (v + v * q / 4) - Real.sqrt v)) := by
    have h1 : theta * Real.sqrt theta * c *
        (Real.sqrt (theta * v + theta * v * q / 4) - Real.sqrt (theta * v)) ≤
        theta * Real.sqrt theta * c * (Real.sqrt theta * (Real.sqrt (v + v * q / 4) - Real.sqrt v)) :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    have h2 : theta * Real.sqrt theta * c * (Real.sqrt theta * (Real.sqrt (v + v * q / 4) - Real.sqrt v))
        = theta * theta * (c * (Real.sqrt (v + v * q / 4) - Real.sqrt v)) := by
      calc _ = theta * (Real.sqrt theta * Real.sqrt theta) *
            (c * (Real.sqrt (v + v * q / 4) - Real.sqrt v)) := by ring
        _ = _ := by rw [hs]
    have h3 : theta * theta * (c * (Real.sqrt (v + v * q / 4) - Real.sqrt v)) ≤
        theta * (c * (Real.sqrt (v + v * q / 4) - Real.sqrt v)) :=
      by nlinarith only [mul_nonneg (mul_nonneg hθ (sub_nonneg.mpr hθ1)) (mul_nonneg hc0 hΔ)]
    linarith only [h1, h2, h3]
  nlinarith only [h0, hmain]

end ASDExplicitGamma.Main

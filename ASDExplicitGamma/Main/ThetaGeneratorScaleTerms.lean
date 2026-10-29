module

public import ASDExplicitGamma.Main.ThetaGeneratorScaleChi
public import ASDExplicitGamma.Main.ThetaGeneratorErrorProportionalClock
public import ASDExplicitGamma.Main.ThetaGeneratorHotGeneratorIntegrated
public import ASDExplicitGamma.Main.ObsChronoH35Theta
public import ASDExplicitGamma.Main.EnvelopeHTheta
public import ASDExplicitGamma.Main.CalibratedError

/-! MA-THETA-CONTINUATION: scaling of the affine term, the inverse-deficit term and the source
clock under `v ≤ θ v̄`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Model Algsuperdiff.Section3

noncomputable section

/-- The `γ₀` affine term `aff_{γ₀}(t)` at the clock `v̄ = mainSourceClock γ₀`, with the
unscaled mean prefix. -/
def mainAffineTermGamma0 (q t : ℝ) : ℝ :=
  (mainSourceClock gammaZero / 2) *
      mainEnvelopeA (mainSourceClock gammaZero) gammaZero mainSourceMeanPrefix t +
    (mainSourceClock gammaZero * q) * (mainBeta - 1) +
      (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * mainA2 (mainSourceClock gammaZero) / 9

theorem th_clock_le {g : ℝ} (hg0 : 0 < g) (hg : g ≤ gammaZero) :
    mainSourceClock g ≤ g / gammaZero * mainSourceClock gammaZero := by
  unfold mainSourceClock
  have hz : (0 : ℝ) < gammaZero := by norm_num [gammaZero]
  have hp : (3 : ℝ) ^ (2 * g) ≤ (3 : ℝ) ^ (2 * gammaZero) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have e : g / gammaZero * (443 / 125 * gammaZero * (3 : ℝ) ^ (2 * gammaZero)) =
      443 / 125 * g * (3 : ℝ) ^ (2 * gammaZero) := by field_simp
  rw [e]
  have : 0 ≤ 443 / 125 * g := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hp this]

theorem th_inverseAbs_scale {v w θ t : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hv : 0 ≤ v)
    (hw : 0 ≤ w) (hvw : v ≤ θ * w) (ht : 0 ≤ t) :
    mainInverseAbs v (mainInverseMuMinusSource v) t ≤
      θ * mainInverseAbs w (mainInverseMuMinusSource w) t := by
  have hθw : θ * w ≤ w := by nlinarith
  refine (chrono_inverseAbs_mono hv hvw ht).trans ?_
  have hk := chrono_kappa_mono (chrono_muMinus_mono (hv.trans hvw) hθw)
  have hρ : 0 ≤ 2 + mainRho := by unfold mainRho mainEpsNew mainBeta; positivity
  have hexp : Real.exp (-(mainKappa (mainInverseMuMinusSource w) * t)) ≤
      Real.exp (-(mainKappa (mainInverseMuMinusSource (θ * w)) * t)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hk ht])
  unfold mainInverseAbs
  have h0 : 0 ≤ θ * w * (2 + mainRho) := by positivity
  calc θ * w * (2 + mainRho) *
        (1 - Real.exp (-(mainKappa (mainInverseMuMinusSource (θ * w)) * t)))
      ≤ θ * w * (2 + mainRho) *
        (1 - Real.exp (-(mainKappa (mainInverseMuMinusSource w) * t))) :=
        mul_le_mul_of_nonneg_left (by linarith) h0
    _ = _ := by ring

theorem th_affine_scale (M : ABKModel 2) {b q t : ℝ} (hg0 : 0 < M.gamma)
    (hg : M.gamma ≤ gammaZero) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hb : b ^ 2 ≤ theta M * mainSourceClock gammaZero) :
    mainAffineTerm_Th M b q t ≤ theta M * mainAffineTermGamma0 q t := by
  have hz : (0 : ℝ) < gammaZero := by norm_num [gammaZero]
  have hθdef : theta M = M.gamma / gammaZero := rfl
  have hθ0 : 0 ≤ theta M := by rw [hθdef]; positivity
  have hθ1 : theta M ≤ 1 := by rw [hθdef, div_le_one hz]; exact hg
  have hv : 0 ≤ b ^ 2 := sq_nonneg b
  have hvbar : 0 ≤ mainSourceClock gammaZero := (mainSourceClock_pos hz).le
  have hbv : b ^ 2 ≤ mainSourceClock gammaZero := hb.trans (by nlinarith)
  have hmu := th_mu_scale_le hθ0 hθ1 hg0.le hg hv hvbar hb
  have hpre : 0 ≤ mainSourceMeanPrefix := by
    have := mainSourceMeanPrefix_gate; linarith
  have hmu0 : 0 ≤ mainMu (b ^ 2) M.gamma := chrono_mu_nonneg hg0.le hv
  have hA : mainEnvelopeA (b ^ 2) M.gamma (theta M * mainSourceMeanPrefix) t ≤
      theta M * mainEnvelopeA (mainSourceClock gammaZero) gammaZero mainSourceMeanPrefix t := by
    unfold mainEnvelopeA
    nlinarith [mul_le_mul_of_nonneg_left hmu ht]
  have hA0 : 0 ≤ mainEnvelopeA (b ^ 2) M.gamma (theta M * mainSourceMeanPrefix) t := by
    unfold mainEnvelopeA; positivity
  have hA2 : mainA2 (b ^ 2) ≤ theta M * mainA2 (mainSourceClock gammaZero) := by
    have : mainA2 (b ^ 2) ≤ mainA2 (theta M * mainSourceClock gammaZero) :=
      chrono_mainA2_mono hb
    unfold mainA2 at this ⊢
    nlinarith
  have hβ : 0 ≤ mainBeta - 1 := by unfold mainBeta; norm_num
  unfold mainAffineTerm_Th mainAffineTermGamma0
  have t1 : b ^ 2 / 2 * mainEnvelopeA (b ^ 2) M.gamma (theta M * mainSourceMeanPrefix) t ≤
      mainSourceClock gammaZero / 2 *
        (theta M * mainEnvelopeA (mainSourceClock gammaZero) gammaZero mainSourceMeanPrefix t) := by
    gcongr
  have t2 : b ^ 2 * q * (mainBeta - 1) ≤ theta M * mainSourceClock gammaZero * q * (mainBeta - 1) := by
    gcongr
  have hc : 0 ≤ (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) / 9 := by positivity
  have t3 := mul_le_mul_of_nonneg_left hA2 hc
  nlinarith [t1, t2, t3]

end

end ASDExplicitGamma.Main

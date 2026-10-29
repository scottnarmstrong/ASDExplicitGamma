module

public import ASDExplicitGamma.Main.ErrorCoefficients
public import ASDExplicitGamma.Main.ErrorCorrected

/-! Proportional-clock scaling for the scalar coefficients in the literal
source-error profile. -/

@[expose] public section

namespace ASDExplicitGamma.Main

private theorem mainA2_theta_Fq (theta v : ℝ) :
    mainA2 (theta * v) = theta * mainA2 v := by
  unfold mainA2
  ring

private theorem mainA4_theta_Fq (theta v : ℝ) :
    mainA4 (theta * v) = theta * mainA4 v := by
  unfold mainA4
  ring

private theorem main_sqrt_A2_theta_Fq {theta v c : ℝ} (hθ : 0 ≤ theta) :
    Real.sqrt (c * mainA2 (theta * v)) =
      Real.sqrt theta * Real.sqrt (c * mainA2 v) := by
  rw [mainA2_theta_Fq]
  rw [show c * (theta * mainA2 v) = theta * (c * mainA2 v) by ring]
  exact Real.sqrt_mul hθ _

private theorem main_sqrt_A4_theta_Fq {theta v c : ℝ} (hθ : 0 ≤ theta) :
    Real.sqrt (c * mainA4 (theta * v)) =
      Real.sqrt theta * Real.sqrt (c * mainA4 v) := by
  rw [mainA4_theta_Fq]
  rw [show c * (theta * mainA4 v) = theta * (c * mainA4 v) by ring]
  exact Real.sqrt_mul hθ _

/-- `mainKd` has degree one half in the variance clock. -/
theorem mainKd_theta_scale_Fq {theta v : ℝ} (hθ : 0 ≤ theta) :
    mainKd (theta * v) = Real.sqrt theta * mainKd v := by
  unfold mainKd
  rw [main_sqrt_A2_theta_Fq hθ, main_sqrt_A4_theta_Fq hθ]
  ring

/-- The remainder coefficient has degree one half in the variance clock. -/
theorem mainKrem_theta_scale_Fq {theta v : ℝ} (hθ : 0 ≤ theta) :
    mainKrem (theta * v) = Real.sqrt theta * mainKrem v := by
  unfold mainKrem
  rw [main_sqrt_A2_theta_Fq hθ, main_sqrt_A4_theta_Fq hθ]
  ring

/-- The plus oscillation coefficient has degree one half in the clock. -/
theorem mainOp_theta_scale_Fq {theta v : ℝ} (hθ : 0 ≤ theta) :
    mainOp (theta * v) = Real.sqrt theta * mainOp v := by
  unfold mainOp
  rw [main_sqrt_A2_theta_Fq hθ]
  ring

/-- The minus oscillation coefficient has degree one half in the clock. -/
theorem mainOm_theta_scale_Fq {theta v : ℝ} (hθ : 0 ≤ theta) :
    mainOm (theta * v) = Real.sqrt theta * mainOm v := by
  unfold mainOm
  rw [main_sqrt_A2_theta_Fq hθ]
  ring

/-- The history moment factor is antitone under decreasing its input clock. -/
theorem mainM0_theta_le_Fq {theta H : ℝ}
    (hθ1 : theta ≤ 1) (hH : 0 ≤ H) :
    mainM0 (theta * H) ≤ mainM0 H := by
  have hθH : theta * H ≤ H := by nlinarith
  unfold mainM0
  have hsqrt : Real.sqrt (2 * (theta * H)) ≤ Real.sqrt (2 * H) :=
    Real.sqrt_le_sqrt (by nlinarith)
  nlinarith

/-- The history fluctuation factor is at most degree one half in the clock. -/
theorem mainTm_theta_le_Fq {theta H : ℝ} (hθ : 0 ≤ theta)
    (hθ1 : theta ≤ 1) (hH : 0 ≤ H) :
    mainTm (theta * H) ≤ Real.sqrt theta * mainTm H := by
  have hM0θ : 0 ≤ mainM0 (theta * H) := by
    unfold mainM0
    positivity
  have hM0 : 0 ≤ mainM0 H := by
    unfold mainM0
    positivity
  have hM0le := mainM0_theta_le_Fq hθ1 hH
  have hrad : mainD * mainM0 (theta * H) * (theta * H) ≤
      theta * (mainD * mainM0 H * H) := by
    have hD : 0 ≤ mainD := by unfold mainD mainAlpha; positivity
    calc
      mainD * mainM0 (theta * H) * (theta * H) =
          theta * (mainD * mainM0 (theta * H) * H) := by ring
      _ ≤ theta * (mainD * mainM0 H * H) := by
        gcongr
  unfold mainTm
  calc
    Real.sqrt (mainD * mainM0 (theta * H) * (theta * H)) ≤
        Real.sqrt (theta * (mainD * mainM0 H * H)) := Real.sqrt_le_sqrt hrad
    _ = Real.sqrt theta * Real.sqrt (mainD * mainM0 H * H) := by
      rw [Real.sqrt_mul hθ]

/-- The history-dependent multiplier `mainC` does not increase under clock
decrease. -/
theorem mainC_theta_le_Fq {theta H : ℝ}
    (hθ1 : theta ≤ 1) (hH : 0 ≤ H) :
    mainC (theta * H) ≤ mainC H := by
  have hrad : mainBeta * mainM0 (theta * H) ≤ mainBeta * mainM0 H := by
    exact mul_le_mul_of_nonneg_left (mainM0_theta_le_Fq hθ1 hH) (by
      unfold mainBeta
      positivity)
  unfold mainC mainBm
  exact add_le_add (Real.sqrt_le_sqrt hrad) le_rfl

/-- The inverse square-root envelope scales exactly with degree one half. -/
theorem mainT0_theta_scale_Fq {theta xi : ℝ} (hθ : 0 ≤ theta) :
    mainT0 (theta * xi) = Real.sqrt theta * mainT0 xi := by
  unfold mainT0
  rw [show theta * xi = theta * xi by rfl, Real.sqrt_mul hθ]

/-- The first source remainder radical is homogeneous under proportional
scaling of its mean, argument, and history inputs. -/
theorem mainR1_theta_scale_Fq {theta a f H : ℝ} (hθ : 0 ≤ theta) :
    mainR1 (theta * a) (theta * f) (theta * H) =
      Real.sqrt theta * mainR1 a f H := by
  unfold mainR1 mainHd
  rw [show mainBeta * (theta * a - theta * f) +
      mainEpsNew * (theta * H / (1 - mainAlpha)) =
        theta * (mainBeta * (a - f) + mainEpsNew * (H / (1 - mainAlpha))) by ring,
    Real.sqrt_mul hθ]

/-- The second source remainder radical is homogeneous under proportional
scaling of its mean, argument, and history inputs. -/
theorem mainR2_theta_scale_Fq {theta a f H : ℝ} (hθ : 0 ≤ theta) :
    mainR2 (theta * a) (theta * f) (theta * H) =
      Real.sqrt theta * mainR2 a f H := by
  unfold mainR2 mainHd
  rw [show mainBeta ^ 2 * (theta * a - theta * f) +
      (2 * mainBeta * mainEpsNew + mainEpsNew ^ 2) *
        (theta * H / (1 - mainAlpha)) =
        theta * (mainBeta ^ 2 * (a - f) +
          (2 * mainBeta * mainEpsNew + mainEpsNew ^ 2) *
            (H / (1 - mainAlpha))) by ring,
    Real.sqrt_mul hθ]

/-- The OLD-frame gap radical is homogeneous in the inverse envelope and the
mean deficit. -/
theorem mainV_theta_scale_Fq {theta xi f : ℝ} (hθ : 0 ≤ theta) :
    mainV (theta * xi) (theta * f) = Real.sqrt theta * mainV xi f := by
  unfold mainV
  rw [show theta * xi - mainBetaOld * (theta * f) =
      theta * (xi - mainBetaOld * f) by ring,
    Real.sqrt_mul hθ]

private theorem mainOp_nonneg_Fq' (v : ℝ) : 0 ≤ mainOp v := by
  unfold mainOp mainA2
  positivity

private theorem mainOm_nonneg_Fq' (v : ℝ) : 0 ≤ mainOm v := by
  unfold mainOm mainA2
  positivity

private theorem sqrt_theta_le_one_Fq {theta : ℝ}
    (hθ1 : theta ≤ 1) : Real.sqrt theta ≤ 1 := by
  exact (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith⟩

/-- The four-load parent-gap coefficient is sublinear under the proportional
clock; its fixed additive boundary constant is paid by `sqrt theta ≤ 1`. -/
theorem mainBe_theta_le_Fq {theta v q : ℝ} (hθ : 0 ≤ theta)
    (hθ1 : theta ≤ 1) (hv : 0 ≤ v) :
    mainBe (theta * v) q ≤ theta * mainBe v q := by
  unfold mainBe
  exact le_of_eq (by ring)

/-- The two-coordinate covariance coefficient is at most degree one in the
clock. Its raw covariance coordinate is degree 3/2; its DIAG term is degree 1. -/
theorem mainEcov_theta_le_Fq {theta v q : ℝ} (hθ : 0 ≤ theta)
    (hθ1 : theta ≤ 1) (hv : 0 ≤ v) (hq : 0 ≤ q) :
    mainEcov (theta * v) q ≤ theta * mainEcov v q := by
  have hsθ := sqrt_theta_le_one_Fq hθ1
  have hA2 : 0 ≤ mainA2 v := by unfold mainA2; positivity
  have hfirst : Real.sqrt ((theta * v) * ((theta * v) * q / 2)) ≤
      theta * Real.sqrt (v * (v * q) / 2) := by
    have hθ3 : theta ^ 3 ≤ theta ^ 2 := by nlinarith [sq_nonneg (theta - 1)]
    have hbase : 0 ≤ v * (v * q) / 2 := by positivity
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · calc
        (theta * v) * ((theta * v) * q / 2) =
            theta ^ 2 * (v * (v * q) / 2) := by ring
        _ ≤ theta ^ 2 * (v * (v * q) / 2) := le_rfl
        _ = (theta * Real.sqrt (v * (v * q) / 2)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hbase]
  have hsecondA : (319 / 1000 : ℝ) *
      Real.sqrt ((156 / 5 : ℝ) * mainA2 (theta * v)) * mainOp (theta * v) =
        theta * ((319 / 1000 : ℝ) *
          Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOp v) := by
    rw [main_sqrt_A2_theta_Fq hθ, mainOp_theta_scale_Fq hθ]
    calc
      (319 / 1000 : ℝ) * (Real.sqrt theta * Real.sqrt ((156 / 5 : ℝ) * mainA2 v)) *
          (Real.sqrt theta * mainOp v) =
        Real.sqrt theta ^ 2 * ((319 / 1000 : ℝ) *
          Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOp v) := by ring
      _ = theta * ((319 / 1000 : ℝ) *
          Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOp v) := by
        rw [Real.sq_sqrt hθ]
  have hfirstNonneg : 0 ≤ Real.sqrt (v * (v * q) / 2) := Real.sqrt_nonneg _
  have hsecondNonneg : 0 ≤ (319 / 1000 : ℝ) *
      Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOp v := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (mainOp_nonneg_Fq' v)
  have hOpθ : 0 ≤ mainOp (theta * v) := mainOp_nonneg_Fq' (theta * v)
  have hOmθ : 0 ≤ mainOm (theta * v) := mainOm_nonneg_Fq' (theta * v)
  have hcoord₁ : 0 ≤ Real.sqrt ((theta * v) * ((theta * v) * q / 2)) +
      (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 (theta * v)) *
        mainOp (theta * v) := by positivity
  have hcoord₂ : 0 ≤ Real.sqrt ((theta * v) * ((theta * v) * q / 2)) +
      (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 (theta * v)) *
        mainOm (theta * v) := by positivity
  have hcoord₁le : Real.sqrt ((theta * v) * ((theta * v) * q / 2)) +
      (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 (theta * v)) *
        mainOp (theta * v) ≤ theta * (Real.sqrt (v * (v * q) / 2) +
          (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOp v) := by
    calc
      _ = Real.sqrt ((theta * v) * ((theta * v) * q / 2)) +
          theta * ((319 / 1000 : ℝ) *
            Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOp v) := by rw [hsecondA]
      _ ≤ theta * Real.sqrt (v * (v * q) / 2) +
          theta * ((319 / 1000 : ℝ) *
            Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOp v) := by
        exact add_le_add hfirst le_rfl
      _ = _ := by ring
  have hsecondB : (319 / 1000 : ℝ) *
      Real.sqrt ((156 / 5 : ℝ) * mainA2 (theta * v)) * mainOm (theta * v) =
        theta * ((319 / 1000 : ℝ) *
          Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOm v) := by
    rw [main_sqrt_A2_theta_Fq hθ, mainOm_theta_scale_Fq hθ]
    calc
      (319 / 1000 : ℝ) * (Real.sqrt theta * Real.sqrt ((156 / 5 : ℝ) * mainA2 v)) *
          (Real.sqrt theta * mainOm v) =
        Real.sqrt theta ^ 2 * ((319 / 1000 : ℝ) *
          Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOm v) := by ring
      _ = theta * ((319 / 1000 : ℝ) *
          Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOm v) := by
        rw [Real.sq_sqrt hθ]
  have hcoord₂le : Real.sqrt ((theta * v) * ((theta * v) * q / 2)) +
      (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 (theta * v)) *
        mainOm (theta * v) ≤ theta * (Real.sqrt (v * (v * q) / 2) +
          (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOm v) := by
    calc
      _ = Real.sqrt ((theta * v) * ((theta * v) * q / 2)) +
          theta * ((319 / 1000 : ℝ) *
            Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOm v) := by rw [hsecondB]
      _ ≤ theta * Real.sqrt (v * (v * q) / 2) +
          theta * ((319 / 1000 : ℝ) *
            Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOm v) := by
        exact add_le_add hfirst le_rfl
      _ = _ := by ring
  unfold mainEcov
  have hθcoord₁ : 0 ≤ theta * (Real.sqrt (v * (v * q) / 2) +
      (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOp v) := by
    exact mul_nonneg hθ (add_nonneg (Real.sqrt_nonneg _) hsecondNonneg)
  have hθcoord₂ : 0 ≤ theta * (Real.sqrt (v * (v * q) / 2) +
      (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOm v) := by
    have hsecondOm : 0 ≤ (319 / 1000 : ℝ) *
        Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOm v :=
      mul_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (mainOm_nonneg_Fq' v)
    exact mul_nonneg hθ (add_nonneg (Real.sqrt_nonneg _) hsecondOm)
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have h₁sq := mul_le_mul hcoord₁le hcoord₁le hcoord₁ hθcoord₁
    have h₂sq := mul_le_mul hcoord₂le hcoord₂le hcoord₂ hθcoord₂
    have h₁sq' : (Real.sqrt ((theta * v) * ((theta * v) * q / 2)) +
        (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 (theta * v)) *
          mainOp (theta * v)) ^ 2 ≤
        (theta * (Real.sqrt (v * (v * q) / 2) +
          (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOp v)) ^ 2 := by
      nlinarith [h₁sq]
    have h₂sq' : (Real.sqrt ((theta * v) * ((theta * v) * q / 2)) +
        (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 (theta * v)) *
          mainOm (theta * v)) ^ 2 ≤
        (theta * (Real.sqrt (v * (v * q) / 2) +
          (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOm v)) ^ 2 := by
      nlinarith [h₂sq]
    have hsum0 : 0 ≤
        (Real.sqrt (v * (v * q) / 2) +
          (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOp v) ^ 2 +
        (Real.sqrt (v * (v * q) / 2) +
          (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOm v) ^ 2 := by
      positivity
    have hradarg : (theta * v) * ((theta * v) * q / 2) =
        (theta * v * ((theta * v) * q)) / 2 := by ring
    rw [hradarg] at h₁sq' h₂sq'
    calc
      _ ≤ (theta * (Real.sqrt (v * (v * q) / 2) +
            (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOp v)) ^ 2 +
          (theta * (Real.sqrt (v * (v * q) / 2) +
            (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOm v)) ^ 2 :=
              add_le_add h₁sq' h₂sq'
      _ = (theta * Real.sqrt ((Real.sqrt (v * (v * q) / 2) +
            (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOp v) ^ 2 +
          (Real.sqrt (v * (v * q) / 2) +
            (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOm v) ^ 2)) ^ 2 := by
              let X := Real.sqrt (v * (v * q) / 2) +
                (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOp v
              let Y := Real.sqrt (v * (v * q) / 2) +
                (319 / 1000 : ℝ) * Real.sqrt ((156 / 5 : ℝ) * mainA2 v) * mainOm v
              have hsquare : Real.sqrt (X ^ 2 + Y ^ 2) ^ 2 = X ^ 2 + Y ^ 2 := by
                exact Real.sq_sqrt (by dsimp [X, Y]; positivity)
              change (theta * X) ^ 2 + (theta * Y) ^ 2 =
                (theta * Real.sqrt (X ^ 2 + Y ^ 2)) ^ 2
              calc
                (theta * X) ^ 2 + (theta * Y) ^ 2 =
                    theta ^ 2 * (X ^ 2 + Y ^ 2) := by ring
                _ = theta ^ 2 * Real.sqrt (X ^ 2 + Y ^ 2) ^ 2 := by rw [hsquare]
                _ = (theta * Real.sqrt (X ^ 2 + Y ^ 2)) ^ 2 := by ring

private theorem mainKa_theta_scale_Fq {theta v : ℝ} (hθ : 0 ≤ theta) :
    mainKa (theta * v) = Real.sqrt theta * mainKa v := by
  unfold mainKa
  rw [Real.sqrt_mul hθ, main_sqrt_A2_theta_Fq hθ, main_sqrt_A4_theta_Fq hθ]
  ring

private theorem main_sqrtTheta_sq_Fq {theta : ℝ} (hθ : 0 ≤ theta) :
    Real.sqrt theta * Real.sqrt theta = theta := by
  calc
    Real.sqrt theta * Real.sqrt theta = (Real.sqrt theta) ^ 2 := by ring
    _ = theta := Real.sq_sqrt hθ

private theorem mainErrorSourceRoot_theta_scale_Fq {theta H xi : ℝ}
    (hθ : 0 ≤ theta) :
    mainErrorSourceRoot (theta * H) (theta * xi) =
      Real.sqrt theta * mainErrorSourceRoot H xi := by
  unfold mainErrorSourceRoot
  have harg : mainBeta * (theta * xi) +
      mainEpsNew * mainD * mainBeta * (theta * H) =
      theta * (mainBeta * xi + mainEpsNew * mainD * mainBeta * H) := by ring
  rw [harg, Real.sqrt_mul hθ]

private theorem mainG_theta_scale_Fq {theta xi : ℝ} (hθ : 0 ≤ theta) :
    mainG (theta * xi) = Real.sqrt theta * mainG xi := by
  unfold mainG
  rw [show 2 * (theta * xi) = theta * (2 * xi) by ring,
    Real.sqrt_mul hθ]

private theorem mainRec_theta_scale_Fq {theta xi : ℝ} (hθ : 0 ≤ theta) :
    mainRec (theta * xi) = Real.sqrt theta * mainRec xi := by
  unfold mainRec
  rw [show 2 * mainBeta * (theta * xi) =
      theta * (2 * mainBeta * xi) by ring, Real.sqrt_mul hθ]

private theorem mainLoadD_theta_scale_Fq {theta v a f H xi : ℝ}
    (hθ : 0 ≤ theta) :
    mainLoadD (theta * v) (theta * a) (theta * f) (theta * H)
      (theta * xi) (mainKd (theta * v)) =
      theta * mainLoadD v a f H xi (mainKd v) := by
  unfold mainLoadD
  rw [mainKa_theta_scale_Fq hθ, mainR1_theta_scale_Fq hθ,
    mainKd_theta_scale_Fq hθ, mainT0_theta_scale_Fq hθ]
  calc
    _ = (Real.sqrt theta * Real.sqrt theta) *
          (mainKa v * mainR1 a f H) +
        (Real.sqrt theta * Real.sqrt theta) * (mainKd v * mainT0 xi) := by ring
    _ = theta * mainLoadD v a f H xi (mainKd v) := by
        rw [main_sqrtTheta_sq_Fq hθ]
        unfold mainLoadD
        ring

private theorem mainLoadZ_theta_scale_Fq {theta v a f H xi : ℝ}
    (hθ : 0 ≤ theta) :
    mainLoadZ (theta * v) (theta * a) (theta * f) (theta * H)
      (theta * xi) (mainKd (theta * v)) =
      theta * mainLoadZ v a f H xi (mainKd v) := by
  simp only [mainLoadZ]
  rw [mainKa_theta_scale_Fq hθ, mainR2_theta_scale_Fq hθ,
    mainKd_theta_scale_Fq hθ]
  have hroot : Real.sqrt (mainBeta * (theta * xi) +
      mainEpsNew * mainD * mainBeta * (theta * H)) =
      Real.sqrt theta * Real.sqrt (mainBeta * xi +
        mainEpsNew * mainD * mainBeta * H) := by
    calc
      _ = mainErrorSourceRoot (theta * H) (theta * xi) := rfl
      _ = Real.sqrt theta * mainErrorSourceRoot H xi :=
        mainErrorSourceRoot_theta_scale_Fq hθ
      _ = _ := rfl
  rw [hroot]
  calc
    _ = (Real.sqrt theta * Real.sqrt theta) *
          (mainKa v * mainR2 a f H) +
        (Real.sqrt theta * Real.sqrt theta) *
          (mainKd v * Real.sqrt (mainBeta * xi +
            mainEpsNew * mainD * mainBeta * H)) := by ring
    _ = theta * (mainKa v * mainR2 a f H +
        mainKd v * Real.sqrt (mainBeta * xi +
          mainEpsNew * mainD * mainBeta * H)) := by
        rw [main_sqrtTheta_sq_Fq hθ]
        ring
    _ = theta * mainLoadZ v a f H xi (mainKd v) := rfl

private theorem mainLoadQ_theta_le_Fq {theta v H : ℝ}
    (hθ : 0 ≤ theta) (hθ1 : theta ≤ 1) (hH : 0 ≤ H) :
    mainLoadQ (theta * H) (mainOp (theta * v)) (mainOm (theta * v)) ≤
      Real.sqrt theta * mainLoadQ H (mainOp v) (mainOm v) := by
  have hM0 := mainM0_theta_le_Fq hθ1 hH
  have hβ : 0 ≤ mainBeta := by norm_num [mainBeta]
  have hrad :
      (mainBeta + 1) ^ 2 * mainOp (theta * v) ^ 2 +
          mainBeta * mainM0 (theta * H) * mainOm (theta * v) ^ 2 ≤
        theta * ((mainBeta + 1) ^ 2 * mainOp v ^ 2 +
          mainBeta * mainM0 H * mainOm v ^ 2) := by
    rw [mainOp_theta_scale_Fq hθ, mainOm_theta_scale_Fq hθ,
      mul_pow, mul_pow, Real.sq_sqrt hθ]
    calc
      _ = theta * ((mainBeta + 1) ^ 2 * mainOp v ^ 2) +
          theta * (mainBeta * mainM0 (theta * H) * mainOm v ^ 2) := by ring
      _ ≤ theta * ((mainBeta + 1) ^ 2 * mainOp v ^ 2) +
          theta * (mainBeta * mainM0 H * mainOm v ^ 2) := by
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hM0 hβ)
                  (sq_nonneg (mainOm v))) hθ)
      _ = theta * ((mainBeta + 1) ^ 2 * mainOp v ^ 2 +
          mainBeta * mainM0 H * mainOm v ^ 2) := by ring
  unfold mainLoadQ
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · calc
      (mainBeta + 1) ^ 2 * mainOp (theta * v) ^ 2 +
          mainBeta * mainM0 (theta * H) * mainOm (theta * v) ^ 2 ≤
        theta * ((mainBeta + 1) ^ 2 * mainOp v ^ 2 +
          mainBeta * mainM0 H * mainOm v ^ 2) := hrad
      _ = (Real.sqrt theta *
          Real.sqrt ((mainBeta + 1) ^ 2 * mainOp v ^ 2 +
            mainBeta * mainM0 H * mainOm v ^ 2)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hθ,
            Real.sq_sqrt (by
              apply add_nonneg
              · positivity
              · exact mul_nonneg (mul_nonneg hβ (by
                  unfold mainM0
                  positivity)) (sq_nonneg _))]

private theorem mainVarianceRoot_theta_le_Fq {theta v q : ℝ}
    (hθ : 0 ≤ theta) (hθ1 : theta ≤ 1) (hv : 0 ≤ v) (hq : 0 ≤ q) :
    Real.sqrt (theta * v + (theta * v) * q / 2) ≤
      Real.sqrt theta * Real.sqrt (v + v * q / 2) := by
  have hqterm : theta * (v * q / 2) ≤ v * q / 2 :=
    by
      have hbase : 0 ≤ v * q / 2 := by positivity
      have h := mul_le_mul_of_nonneg_right hθ1 hbase
      simpa only [one_mul] using h
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · calc
      theta * v + (theta * v) * q / 2 =
          theta * (v + (v * q / 2)) := by ring
      _ ≤ theta * (v + v * q / 2) := by
          exact mul_le_mul_of_nonneg_left
            (le_of_eq rfl) hθ
      _ = (Real.sqrt theta * Real.sqrt (v + v * q / 2)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hθ,
            Real.sq_sqrt (by positivity)]

private theorem mainLinearError_theta_le_Fq {theta v H xi q : ℝ}
    (hθ : 0 ≤ theta) (hθ1 : theta ≤ 1) (hv : 0 ≤ v)
    (hH : 0 ≤ H) (hq : 0 ≤ q) :
    mainLinearError (theta * v) (theta * H) (theta * xi) q ≤
      theta * mainLinearError v H xi q := by
  have hsθ := sqrt_theta_le_one_Fq hθ1
  have hthetaSqrt : theta * Real.sqrt theta ≤ theta := by
    calc
      theta * Real.sqrt theta ≤ theta * 1 :=
        mul_le_mul_of_nonneg_left hsθ hθ
      _ = theta := by ring
  have hTm := mainTm_theta_le_Fq hθ hθ1 hH
  have hC := mainC_theta_le_Fq hθ1 hH
  have hvar := mainVarianceRoot_theta_le_Fq hθ hθ1 hv hq
  have hrootv : Real.sqrt (theta * v) = Real.sqrt theta * Real.sqrt v :=
    Real.sqrt_mul hθ v
  have hOp := mainOp_theta_scale_Fq (theta := theta) (v := v) hθ
  have hOm := mainOm_theta_scale_Fq (theta := theta) (v := v) hθ
  have hT0 := mainT0_theta_scale_Fq (theta := theta) (xi := xi) hθ
  have hT0nonneg : 0 ≤ mainT0 xi := by unfold mainT0; positivity
  have hTmnonneg : 0 ≤ mainTm H := by unfold mainTm mainM0; positivity
  have hCnonneg : 0 ≤ mainC H := by unfold mainC mainBm mainM0; positivity
  have hOpnonneg : 0 ≤ mainOp v := mainOp_nonneg_Fq' v
  have hOmnonneg : 0 ≤ mainOm v := mainOm_nonneg_Fq' v
  have hM0 : 0 ≤ mainM0 H := by unfold mainM0; positivity
  have hterm₁ :
      Real.sqrt 2 * mainT0 (theta * xi) *
          Real.sqrt (theta * v + (theta * v) * q / 2) *
          mainOp (theta * v) ≤
        theta * (Real.sqrt 2 * mainT0 xi *
          Real.sqrt (v + v * q / 2) * mainOp v) := by
    rw [hT0, hOp]
    have hcoeff : 0 ≤ Real.sqrt 2 * (Real.sqrt theta * mainT0 xi) :=
      mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) hT0nonneg)
    have hprod := mul_le_mul_of_nonneg_left hvar hcoeff
    calc
      Real.sqrt 2 * (Real.sqrt theta * mainT0 xi) *
          Real.sqrt (theta * v + (theta * v) * q / 2) *
          (Real.sqrt theta * mainOp v) ≤
        Real.sqrt 2 * (Real.sqrt theta * mainT0 xi) *
          (Real.sqrt theta * Real.sqrt (v + v * q / 2)) *
          (Real.sqrt theta * mainOp v) := by
            exact mul_le_mul_of_nonneg_right hprod
              (mul_nonneg (Real.sqrt_nonneg _) hOpnonneg)
      _ ≤ theta * (Real.sqrt 2 * mainT0 xi *
          Real.sqrt (v + v * q / 2) * mainOp v) := by
            calc
              _ = (Real.sqrt theta * Real.sqrt theta) * Real.sqrt theta *
                  (Real.sqrt 2 * mainT0 xi *
                    Real.sqrt (v + v * q / 2) * mainOp v) := by ring
              _ = theta * Real.sqrt theta *
                  (Real.sqrt 2 * mainT0 xi *
                    Real.sqrt (v + v * q / 2) * mainOp v) := by
                    rw [main_sqrtTheta_sq_Fq hθ]
              _ ≤ theta * (Real.sqrt 2 * mainT0 xi *
                    Real.sqrt (v + v * q / 2) * mainOp v) := by
                    exact mul_le_mul_of_nonneg_right hthetaSqrt (by positivity)
  have hterm₂ :
      2 * Real.sqrt 2 * mainTm (theta * H) * Real.sqrt (theta * v) *
          mainOm (theta * v) ≤
        theta * (2 * Real.sqrt 2 * mainTm H * Real.sqrt v * mainOm v) := by
    rw [hrootv, hOm]
    have hpower : theta * Real.sqrt theta ≤ theta := by
      calc
        theta * Real.sqrt theta ≤ theta * 1 :=
          mul_le_mul_of_nonneg_left hsθ hθ
        _ = theta := by ring
    have hTm' : mainTm (theta * H) * Real.sqrt theta ≤
        theta * mainTm H := by
      calc
        mainTm (theta * H) * Real.sqrt theta ≤
            (Real.sqrt theta * mainTm H) * Real.sqrt theta :=
          mul_le_mul_of_nonneg_right hTm (Real.sqrt_nonneg _)
        _ = theta * mainTm H := by
          calc
            _ = (Real.sqrt theta * Real.sqrt theta) * mainTm H := by ring
            _ = theta * mainTm H := by rw [main_sqrtTheta_sq_Fq hθ]
    have hcoeff : 0 ≤ 2 * Real.sqrt 2 * Real.sqrt v * mainOm v := by positivity
    calc
      _ = (mainTm (theta * H) * Real.sqrt theta) *
          (Real.sqrt theta * (2 * Real.sqrt 2 * Real.sqrt v * mainOm v)) := by ring
      _ ≤ (theta * mainTm H) *
          (Real.sqrt theta * (2 * Real.sqrt 2 * Real.sqrt v * mainOm v)) :=
            mul_le_mul_of_nonneg_right hTm'
              (mul_nonneg (Real.sqrt_nonneg _) hcoeff)
      _ = (theta * Real.sqrt theta) *
          (2 * Real.sqrt 2 * mainTm H * Real.sqrt v * mainOm v) := by ring
      _ ≤ theta * (2 * Real.sqrt 2 * mainTm H * Real.sqrt v * mainOm v) :=
        mul_le_mul_of_nonneg_right hpower
          (by positivity)
  have hterm₃ : mainBeta * mainOp (theta * v) ^ 2 =
      theta * (mainBeta * mainOp v ^ 2) := by
    rw [hOp, mul_pow, Real.sq_sqrt hθ]
    ring
  have hterm₄ : mainM0 (theta * H) * mainOm (theta * v) ^ 2 ≤
      theta * (mainM0 H * mainOm v ^ 2) := by
    rw [hOm, mul_pow, Real.sq_sqrt hθ]
    calc
      _ = theta * (mainM0 (theta * H) * mainOm v ^ 2) := by ring
      _ ≤ theta * (mainM0 H * mainOm v ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mainM0_theta_le_Fq hθ1 hH)
            (sq_nonneg (mainOm v))) hθ
  have hbaseC₁ : 0 ≤ mainT0 xi * Real.sqrt v := by positivity
  have hbaseC₂ : 0 ≤ Real.sqrt 2 * mainC H * mainOm v := by positivity
  have hterm₅ :
      2 * mainKd (theta * v) *
          (mainT0 (theta * xi) * Real.sqrt (theta * v) +
            Real.sqrt 2 * mainC (theta * H) * mainOm (theta * v)) ≤
        theta * (2 * mainKd v *
          (mainT0 xi * Real.sqrt v + Real.sqrt 2 * mainC H * mainOm v)) := by
    rw [mainKd_theta_scale_Fq hθ, hT0, hrootv, hOm]
    have hpower : theta * Real.sqrt theta ≤ theta := by
      calc
        theta * Real.sqrt theta ≤ theta * 1 :=
          mul_le_mul_of_nonneg_left hsθ hθ
        _ = theta := by ring
    have hfirst :
        2 * (Real.sqrt theta * mainKd v) *
          ((Real.sqrt theta * mainT0 xi) *
            (Real.sqrt theta * Real.sqrt v)) ≤
        theta * (2 * mainKd v * (mainT0 xi * Real.sqrt v)) := by
      calc
        _ = (theta * Real.sqrt theta) *
            (2 * mainKd v * (mainT0 xi * Real.sqrt v)) := by
              calc
                _ = (Real.sqrt theta * Real.sqrt theta) * Real.sqrt theta *
                    (2 * mainKd v * (mainT0 xi * Real.sqrt v)) := by ring
                _ = (theta * Real.sqrt theta) *
                    (2 * mainKd v * (mainT0 xi * Real.sqrt v)) := by
                      rw [main_sqrtTheta_sq_Fq hθ]
        _ ≤ theta * (2 * mainKd v * (mainT0 xi * Real.sqrt v)) :=
          mul_le_mul_of_nonneg_right hpower
            (mul_nonneg (mul_nonneg (by norm_num) (mainKd_nonneg v)) hbaseC₁)
    have hsecond :
        2 * (Real.sqrt theta * mainKd v) * Real.sqrt 2 *
          mainC (theta * H) * (Real.sqrt theta * mainOm v) ≤
        theta * (2 * mainKd v * (Real.sqrt 2 * mainC H * mainOm v)) := by
      calc
        _ = (2 * (Real.sqrt theta * mainKd v) * Real.sqrt 2 *
            mainC (theta * H)) * (Real.sqrt theta * mainOm v) := by ring
        _ ≤ (2 * (Real.sqrt theta * mainKd v) * Real.sqrt 2 *
            mainC H) * (Real.sqrt theta * mainOm v) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hC
                  (mul_nonneg
                    (mul_nonneg (by norm_num)
                      (mul_nonneg (Real.sqrt_nonneg _) (mainKd_nonneg v)))
                    (Real.sqrt_nonneg _)))
                (mul_nonneg (Real.sqrt_nonneg _) hOmnonneg)
        _ = theta * (2 * mainKd v *
            (Real.sqrt 2 * mainC H * mainOm v)) := by
              calc
                _ = (Real.sqrt theta * Real.sqrt theta) *
                    (2 * mainKd v *
                      (Real.sqrt 2 * mainC H * mainOm v)) := by ring
                _ = theta * (2 * mainKd v *
                    (Real.sqrt 2 * mainC H * mainOm v)) := by
                      rw [main_sqrtTheta_sq_Fq hθ]
    calc
      _ =
          2 * (Real.sqrt theta * mainKd v) *
            ((Real.sqrt theta * mainT0 xi) *
              (Real.sqrt theta * Real.sqrt v)) +
          2 * (Real.sqrt theta * mainKd v) * Real.sqrt 2 *
            mainC (theta * H) * (Real.sqrt theta * mainOm v) := by ring
      _ ≤ theta * (2 * mainKd v * (mainT0 xi * Real.sqrt v)) +
          theta * (2 * mainKd v * (Real.sqrt 2 * mainC H * mainOm v)) :=
        add_le_add hfirst hsecond
      _ = theta * (2 * mainKd v *
          (mainT0 xi * Real.sqrt v + Real.sqrt 2 * mainC H * mainOm v)) := by ring
  unfold mainLinearError
  calc
    _ =
        (Real.sqrt 2 * mainT0 (theta * xi) *
            Real.sqrt (theta * v + (theta * v) * q / 2) *
            mainOp (theta * v)) +
          (2 * Real.sqrt 2 * mainTm (theta * H) *
            Real.sqrt (theta * v) * mainOm (theta * v)) +
          mainBeta * mainOp (theta * v) ^ 2 +
          mainM0 (theta * H) * mainOm (theta * v) ^ 2 +
          2 * mainKd (theta * v) *
            (mainT0 (theta * xi) * Real.sqrt (theta * v) +
              Real.sqrt 2 * mainC (theta * H) * mainOm (theta * v)) := rfl
    _ ≤ theta * (Real.sqrt 2 * mainT0 xi *
          Real.sqrt (v + v * q / 2) * mainOp v) +
        theta * (2 * Real.sqrt 2 * mainTm H * Real.sqrt v * mainOm v) +
        theta * (mainBeta * mainOp v ^ 2) +
        theta * (mainM0 H * mainOm v ^ 2) +
        theta * (2 * mainKd v *
          (mainT0 xi * Real.sqrt v + Real.sqrt 2 * mainC H * mainOm v)) := by
            apply add_le_add
            · apply add_le_add
              · apply add_le_add
                · apply add_le_add
                  · exact hterm₁
                  · exact hterm₂
                · exact le_of_eq hterm₃
              · exact hterm₄
            · exact hterm₅
    _ = theta * mainLinearError v H xi q := by
      unfold mainLinearError
      ring

private theorem mainFourLoadAG_theta_le_Fq {theta v H xi q : ℝ}
    (hθ : 0 ≤ theta) (hθ1 : theta ≤ 1) (hv : 0 ≤ v)
    (hH : 0 ≤ H) (hq : 0 ≤ q) :
    mainFourLoadAG (theta * v) (theta * H) (theta * xi) q ≤
      theta * mainFourLoadAG v H xi q := by
  have hsθ := sqrt_theta_le_one_Fq hθ1
  have hthetaSqrt : theta * Real.sqrt theta ≤ theta := by
    calc
      theta * Real.sqrt theta ≤ theta * 1 :=
        mul_le_mul_of_nonneg_left hsθ hθ
      _ = theta := by ring
  have hbe : mainBe (theta * v) q ≤ theta * mainBe v q :=
    mainBe_theta_le_Fq (theta := theta) (v := v) (q := q) hθ hθ1 hv
  have hkd := mainKd_theta_scale_Fq (theta := theta) (v := v) hθ
  have hT0 := mainT0_theta_scale_Fq (theta := theta) (xi := xi) hθ
  have hrootv : Real.sqrt (theta * v) = Real.sqrt theta * Real.sqrt v :=
    Real.sqrt_mul hθ v
  have hvar := mainVarianceRoot_theta_le_Fq hθ hθ1 hv hq
  have hOp := mainOp_theta_scale_Fq (theta := theta) (v := v) hθ
  have hOm := mainOm_theta_scale_Fq (theta := theta) (v := v) hθ
  have hC := mainC_theta_le_Fq hθ1 hH
  have hbeNonneg : 0 ≤ mainBe v q := mainBe_nonneg hv q
  have hKdNonneg : 0 ≤ mainKd v := mainKd_nonneg v
  have hT0Nonneg : 0 ≤ mainT0 xi := by unfold mainT0; positivity
  have hRootNonneg : 0 ≤ Real.sqrt (v + v * q / 2) := Real.sqrt_nonneg _
  have hVNonneg : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
  have hOpNonneg : 0 ≤ mainOp v := mainOp_nonneg_Fq' v
  have hOmNonneg : 0 ≤ mainOm v := mainOm_nonneg_Fq' v
  have hCNonneg : 0 ≤ mainC H := by unfold mainC mainBm mainM0; positivity
  have hsum :
      Real.sqrt (theta * v + (theta * v) * q / 2) +
          Real.sqrt (theta * v) ≤
        Real.sqrt theta * (Real.sqrt (v + v * q / 2) + Real.sqrt v) := by
    calc
      _ ≤ Real.sqrt theta * Real.sqrt (v + v * q / 2) +
          Real.sqrt theta * Real.sqrt v :=
        add_le_add hvar (by rw [hrootv])
      _ = _ := by ring
  have hfirstInside :
      mainT0 (theta * xi) *
          (Real.sqrt (theta * v + (theta * v) * q / 2) +
            Real.sqrt (theta * v)) / Real.sqrt 2 ≤
        theta * (mainT0 xi *
          (Real.sqrt (v + v * q / 2) + Real.sqrt v) / Real.sqrt 2) := by
    rw [hT0]
    have hcoef : 0 ≤ Real.sqrt theta * mainT0 xi :=
      mul_nonneg (Real.sqrt_nonneg _) hT0Nonneg
    have hmul := mul_le_mul_of_nonneg_left hsum hcoef
    have hdenom : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    calc
      _ ≤ (Real.sqrt theta * mainT0 xi) *
          (Real.sqrt theta *
            (Real.sqrt (v + v * q / 2) + Real.sqrt v)) / Real.sqrt 2 :=
          div_le_div_of_nonneg_right hmul hdenom
      _ = theta * (mainT0 xi *
          (Real.sqrt (v + v * q / 2) + Real.sqrt v) / Real.sqrt 2) := by
            calc
              _ = (Real.sqrt theta * Real.sqrt theta) *
                  (mainT0 xi *
                    (Real.sqrt (v + v * q / 2) + Real.sqrt v) / Real.sqrt 2) := by ring
              _ = theta * (mainT0 xi *
                  (Real.sqrt (v + v * q / 2) + Real.sqrt v) / Real.sqrt 2) := by
                    rw [main_sqrtTheta_sq_Fq hθ]
  have hfirst :
      2 * mainKd (theta * v) *
          (mainT0 (theta * xi) *
            (Real.sqrt (theta * v + (theta * v) * q / 2) +
              Real.sqrt (theta * v)) / Real.sqrt 2) ≤
        theta * (2 * mainKd v *
          (mainT0 xi * (Real.sqrt (v + v * q / 2) + Real.sqrt v) /
            Real.sqrt 2)) := by
    rw [hkd]
    calc
      _ ≤ 2 * (Real.sqrt theta * mainKd v) *
          (theta * (mainT0 xi *
            (Real.sqrt (v + v * q / 2) + Real.sqrt v) / Real.sqrt 2)) :=
          mul_le_mul_of_nonneg_left hfirstInside (by positivity)
      _ = (theta * Real.sqrt theta) *
          (2 * mainKd v *
            (mainT0 xi * (Real.sqrt (v + v * q / 2) + Real.sqrt v) /
              Real.sqrt 2)) := by ring
      _ ≤ theta * (2 * mainKd v *
          (mainT0 xi * (Real.sqrt (v + v * q / 2) + Real.sqrt v) /
            Real.sqrt 2)) :=
          mul_le_mul_of_nonneg_right hthetaSqrt (by positivity)
  have hsecond :
      2 * mainKd (theta * v) *
          ((63 / 50 : ℝ) * mainBeta * mainOp (theta * v)) =
        theta * (2 * mainKd v *
          ((63 / 50 : ℝ) * mainBeta * mainOp v)) := by
    rw [hkd, hOp]
    calc
      _ = (Real.sqrt theta * Real.sqrt theta) *
          (2 * mainKd v * ((63 / 50 : ℝ) * mainBeta * mainOp v)) := by ring
      _ = theta * (2 * mainKd v *
          ((63 / 50 : ℝ) * mainBeta * mainOp v)) := by
        rw [main_sqrtTheta_sq_Fq hθ]
  have hthird :
      2 * mainKd (theta * v) *
          (mainC (theta * H) * mainOm (theta * v)) ≤
        theta * (2 * mainKd v * (mainC H * mainOm v)) := by
    rw [hkd, hOm]
    calc
      _ ≤ 2 * (Real.sqrt theta * mainKd v) *
          (mainC H * (Real.sqrt theta * mainOm v)) := by
            have hfactor : 0 ≤ 2 * (Real.sqrt theta * mainKd v) :=
              mul_nonneg (by norm_num)
                (mul_nonneg (Real.sqrt_nonneg _) hKdNonneg)
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hC
                (mul_nonneg (Real.sqrt_nonneg _) hOmNonneg)) hfactor
      _ = theta * (2 * mainKd v * (mainC H * mainOm v)) := by
            calc
              _ = (Real.sqrt theta * Real.sqrt theta) *
                  (2 * mainKd v * (mainC H * mainOm v)) := by ring
              _ = theta * (2 * mainKd v * (mainC H * mainOm v)) := by
                rw [main_sqrtTheta_sq_Fq hθ]
  unfold mainFourLoadAG
  calc
    _ = 2 * mainBe (theta * v) q +
        2 * mainKd (theta * v) *
          (mainT0 (theta * xi) *
              (Real.sqrt (theta * v + (theta * v) * q / 2) +
                Real.sqrt (theta * v)) / Real.sqrt 2 +
            (63 / 50 : ℝ) * mainBeta * mainOp (theta * v) +
            mainC (theta * H) * mainOm (theta * v)) := rfl
    _ ≤ theta * (2 * mainBe v q) +
        theta * (2 * mainKd v *
          (mainT0 xi * (Real.sqrt (v + v * q / 2) + Real.sqrt v) /
              Real.sqrt 2 +
            (63 / 50 : ℝ) * mainBeta * mainOp v + mainC H * mainOm v)) := by
          apply add_le_add
          · exact (mul_le_mul_of_nonneg_left hbe
              (show 0 ≤ (2 : ℝ) by norm_num)).trans_eq (by ring)
          · calc
              _ = 2 * mainKd (theta * v) *
                  (mainT0 (theta * xi) *
                      (Real.sqrt (theta * v + (theta * v) * q / 2) +
                        Real.sqrt (theta * v)) / Real.sqrt 2) +
                  2 * mainKd (theta * v) *
                    ((63 / 50 : ℝ) * mainBeta * mainOp (theta * v)) +
                  2 * mainKd (theta * v) *
                    (mainC (theta * H) * mainOm (theta * v)) := by ring
              _ ≤ theta * (2 * mainKd v *
                  (mainT0 xi * (Real.sqrt (v + v * q / 2) + Real.sqrt v) /
                      Real.sqrt 2)) +
                theta * (2 * mainKd v *
                  ((63 / 50 : ℝ) * mainBeta * mainOp v)) +
                theta * (2 * mainKd v * (mainC H * mainOm v)) := by
                    exact add_le_add
                      (add_le_add hfirst (le_of_eq hsecond)) hthird
              _ = theta * (2 * mainKd v *
                  (mainT0 xi * (Real.sqrt (v + v * q / 2) + Real.sqrt v) /
                      Real.sqrt 2 +
                    (63 / 50 : ℝ) * mainBeta * mainOp v + mainC H * mainOm v)) := by ring
    _ = theta * mainFourLoadAG v H xi q := by
      unfold mainFourLoadAG
      ring

/-- The complete literal seven-row source error is sublinear under the
proportional variance clock.  This is the scalar-profile input to the theta
continuation; every coefficient here is the defining source expression. -/
theorem mainSourceError_theta_scale_le_Fq' {theta v a f H xi q : ℝ}
    (hθ : 0 ≤ theta) (hθ1 : theta ≤ 1) (hv : 0 ≤ v)
    (hH : 0 ≤ H) (hq : 0 ≤ q) :
    mainSourceError (theta * v) (theta * a) (theta * f) (theta * H)
        (theta * xi) q ≤
      theta * mainSourceError v a f H xi q := by
  have hsθ := sqrt_theta_le_one_Fq hθ1
  have hthetaSqrt : theta * Real.sqrt theta ≤ theta := by
    calc
      theta * Real.sqrt theta ≤ theta * 1 :=
        mul_le_mul_of_nonneg_left hsθ hθ
      _ = theta := by ring
  have hthetaSq : theta ^ 2 ≤ theta := by
    have h := mul_le_mul_of_nonneg_right hθ1 hθ
    nlinarith only [h]
  have hsquare : Real.sqrt theta * Real.sqrt theta = theta :=
    main_sqrtTheta_sq_Fq hθ
  have hL : mainLinearError (theta * v) (theta * H) (theta * xi) q ≤
      theta * mainLinearError v H xi q :=
    mainLinearError_theta_le_Fq (theta := theta) (v := v) (H := H)
      (xi := xi) (q := q) hθ hθ1 hv hH hq
  have hEcov := mainEcov_theta_le_Fq hθ hθ1 hv hq
  have hAG :
      mainFourLoadAG (theta * v) (theta * H) (theta * xi) q ≤
        theta * mainFourLoadAG v H xi q :=
    mainFourLoadAG_theta_le_Fq (theta := theta) (v := v) (H := H)
      (xi := xi) (q := q) hθ hθ1 hv hH hq
  have hbe : mainBe (theta * v) q ≤ theta * mainBe v q :=
    mainBe_theta_le_Fq (theta := theta) (v := v) (q := q) hθ hθ1 hv
  have hkd := mainKd_theta_scale_Fq (theta := theta) (v := v) hθ
  have hkrem := mainKrem_theta_scale_Fq (theta := theta) (v := v) hθ
  have hOp := mainOp_theta_scale_Fq (theta := theta) (v := v) hθ
  have hOm := mainOm_theta_scale_Fq (theta := theta) (v := v) hθ
  have hT0 := mainT0_theta_scale_Fq (theta := theta) (xi := xi) hθ
  have hR1 := mainR1_theta_scale_Fq (theta := theta) (a := a) (f := f) (H := H) hθ
  have hR2 := mainR2_theta_scale_Fq (theta := theta) (a := a) (f := f) (H := H) hθ
  have hV := mainV_theta_scale_Fq (theta := theta) (xi := xi) (f := f) hθ
  have hG := mainG_theta_scale_Fq (theta := theta) (xi := xi) hθ
  have hRec := mainRec_theta_scale_Fq (theta := theta) (xi := xi) hθ
  have hSource := mainErrorSourceRoot_theta_scale_Fq
    (theta := theta) (H := H) (xi := xi) hθ
  have hD := mainLoadD_theta_scale_Fq (theta := theta) (v := v) (a := a)
    (f := f) (H := H) (xi := xi) hθ
  have hZ := mainLoadZ_theta_scale_Fq (theta := theta) (v := v) (a := a)
    (f := f) (H := H) (xi := xi) hθ
  have hQ := mainLoadQ_theta_le_Fq (theta := theta) (v := v) (H := H) hθ hθ1 hH
  have hKdNonneg : 0 ≤ mainKd v := mainKd_nonneg v
  have hKremNonneg : 0 ≤ mainKrem v := mainKrem_nonneg v
  have hBetaNonneg : 0 ≤ mainBeta := by norm_num [mainBeta]
  have hBeNonneg : 0 ≤ mainBe v q := mainBe_nonneg hv q
  have hKaNonneg : 0 ≤ mainKa v := by unfold mainKa mainA2 mainA4; positivity
  have hR1Nonneg : 0 ≤ mainR1 a f H := Real.sqrt_nonneg _
  have hR2Nonneg : 0 ≤ mainR2 a f H := Real.sqrt_nonneg _
  have hT0Nonneg : 0 ≤ mainT0 xi := Real.sqrt_nonneg _
  have hVNonneg : 0 ≤ mainV xi f := Real.sqrt_nonneg _
  have hQNonneg : 0 ≤ mainLoadQ H (mainOp v) (mainOm v) := Real.sqrt_nonneg _
  have hDNonneg : 0 ≤ mainLoadD v a f H xi (mainKd v) := by
    unfold mainLoadD
    exact add_nonneg (mul_nonneg hKaNonneg hR1Nonneg)
      (mul_nonneg hKdNonneg hT0Nonneg)
  have hZNonneg : 0 ≤ mainLoadZ v a f H xi (mainKd v) := by
    unfold mainLoadZ
    exact add_nonneg (mul_nonneg hKaNonneg hR2Nonneg)
      (mul_nonneg hKdNonneg (Real.sqrt_nonneg _))
  have hFourNonneg : 0 ≤ mainFourLoadAG v H xi q := by
    unfold mainFourLoadAG
    have hC : 0 ≤ mainC H := by unfold mainC mainBm mainM0; positivity
    have hOp : 0 ≤ mainOp v := mainOp_nonneg_Fq' v
    have hOm : 0 ≤ mainOm v := mainOm_nonneg_Fq' v
    have hrad : 0 ≤ Real.sqrt (v + v * q / 2) + Real.sqrt v := by positivity
    have hfirst : 0 ≤
        mainT0 xi * (Real.sqrt (v + v * q / 2) + Real.sqrt v) / Real.sqrt 2 :=
      div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hrad) (Real.sqrt_nonneg _)
    have hsecond : 0 ≤ (63 / 50 : ℝ) * mainBeta * mainOp v := by positivity
    have hthird : 0 ≤ mainC H * mainOm v := mul_nonneg hC hOm
    exact add_nonneg (mul_nonneg (by norm_num) (mainBe_nonneg hv q))
      (mul_nonneg (mul_nonneg (by norm_num) hKdNonneg)
        (add_nonneg (add_nonneg hfirst hsecond) hthird))
  have hDfbNonneg : 0 ≤
      Real.sqrt 2 * mainBeta * mainLoadD v a f H xi (mainKd v) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hBetaNonneg) hDNonneg
  have hZrecNonneg : 0 ≤
      mainLoadZ v a f H xi (mainKd v) * mainRec xi := by
    exact mul_nonneg hZNonneg (Real.sqrt_nonneg _)
  have hfeedback :
      Real.sqrt 2 * mainBeta *
          mainLoadD (theta * v) (theta * a) (theta * f) (theta * H)
            (theta * xi) (mainKd (theta * v)) +
        mainLoadZ (theta * v) (theta * a) (theta * f) (theta * H)
          (theta * xi) (mainKd (theta * v)) * mainRec (theta * xi) ≤
      theta * (Real.sqrt 2 * mainBeta *
          mainLoadD v a f H xi (mainKd v) +
        mainLoadZ v a f H xi (mainKd v) * mainRec xi) := by
    rw [hD, hZ, hRec]
    have hfirst :
        Real.sqrt 2 * mainBeta *
            (theta * mainLoadD v a f H xi (mainKd v)) =
          theta * (Real.sqrt 2 * mainBeta *
            mainLoadD v a f H xi (mainKd v)) := by ring
    have hsecond :
        theta * mainLoadZ v a f H xi (mainKd v) *
            (Real.sqrt theta * mainRec xi) ≤
          theta * (mainLoadZ v a f H xi (mainKd v) * mainRec xi) := by
      calc
        _ = (theta * Real.sqrt theta) *
            (mainLoadZ v a f H xi (mainKd v) * mainRec xi) := by ring
        _ ≤ theta * (mainLoadZ v a f H xi (mainKd v) * mainRec xi) :=
          mul_le_mul_of_nonneg_right hthetaSqrt hZrecNonneg
    rw [hfirst]
    calc
      _ ≤ theta * (Real.sqrt 2 * mainBeta *
            mainLoadD v a f H xi (mainKd v)) +
          theta * (mainLoadZ v a f H xi (mainKd v) * mainRec xi) :=
        add_le_add le_rfl hsecond
      _ = theta * (Real.sqrt 2 * mainBeta *
            mainLoadD v a f H xi (mainKd v) +
          mainLoadZ v a f H xi (mainKd v) * mainRec xi) := by ring
  have htermZ :
      mainLoadZ (theta * v) (theta * a) (theta * f) (theta * H)
          (theta * xi) (mainKd (theta * v)) ^ 2 ≤
        theta * (mainLoadZ v a f H xi (mainKd v)) ^ 2 := by
    rw [hZ]
    calc
      _ = theta ^ 2 * (mainLoadZ v a f H xi (mainKd v)) ^ 2 := by ring
      _ ≤ theta * (mainLoadZ v a f H xi (mainKd v)) ^ 2 :=
        mul_le_mul_of_nonneg_right hthetaSq (sq_nonneg _)
  have htermR1 :
      theta * v / 2 * mainR1 (theta * a) (theta * f) (theta * H) ^ 2 ≤
        theta * (v / 2 * mainR1 a f H ^ 2) := by
    rw [hR1, mul_pow, Real.sq_sqrt hθ]
    calc
      _ = theta ^ 2 * (v / 2 * mainR1 a f H ^ 2) := by ring
      _ ≤ theta * (v / 2 * mainR1 a f H ^ 2) :=
        mul_le_mul_of_nonneg_right hthetaSq
          (mul_nonneg (div_nonneg hv (by norm_num)) (sq_nonneg _))
  have hmidInner :
      mainKrem (theta * v) * mainR1 (theta * a) (theta * f) (theta * H) +
        mainKd (theta * v) * mainT0 (theta * xi) =
      theta * (mainKrem v * mainR1 a f H + mainKd v * mainT0 xi) := by
    rw [hkrem, hR1, hkd, hT0]
    calc
      _ = (Real.sqrt theta * Real.sqrt theta) *
            (mainKrem v * mainR1 a f H) +
          (Real.sqrt theta * Real.sqrt theta) *
            (mainKd v * mainT0 xi) := by ring
      _ = theta * (mainKrem v * mainR1 a f H + mainKd v * mainT0 xi) := by
        rw [hsquare]
        ring
  have hmidInnerNonneg : 0 ≤
      mainKrem v * mainR1 a f H + mainKd v * mainT0 xi :=
    add_nonneg (mul_nonneg hKremNonneg hR1Nonneg)
      (mul_nonneg hKdNonneg hT0Nonneg)
  have hmidBaseNonneg : 0 ≤
      2 * (mainKrem v * mainR1 a f H + mainKd v * mainT0 xi) *
        mainT0 xi * Real.sqrt v := by positivity
  have htermMid :
      2 * (mainKrem (theta * v) *
            mainR1 (theta * a) (theta * f) (theta * H) +
          mainKd (theta * v) * mainT0 (theta * xi)) *
          mainT0 (theta * xi) * Real.sqrt (theta * v) ≤
        theta * (2 * (mainKrem v * mainR1 a f H + mainKd v * mainT0 xi) *
          mainT0 xi * Real.sqrt v) := by
    rw [hmidInner, hT0, Real.sqrt_mul hθ v]
    calc
      _ = (theta * (Real.sqrt theta * Real.sqrt theta)) *
          (2 * (mainKrem v * mainR1 a f H + mainKd v * mainT0 xi) *
            mainT0 xi * Real.sqrt v) := by
              ring
      _ = theta ^ 2 *
          (2 * (mainKrem v * mainR1 a f H + mainKd v * mainT0 xi) *
            mainT0 xi * Real.sqrt v) := by
              rw [hsquare]
              ring
      _ ≤ theta *
          (2 * (mainKrem v * mainR1 a f H + mainKd v * mainT0 xi) *
            mainT0 xi * Real.sqrt v) := by
              exact mul_le_mul_of_nonneg_right hthetaSq hmidBaseNonneg
  have hCovBaseNonneg : 0 ≤
      Real.sqrt 2 * mainT0 xi * mainR1 a f H * mainEcov v q := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hT0Nonneg) hR1Nonneg)
      (mainEcov_nonneg v q)
  have htermCov :
      Real.sqrt 2 * mainT0 (theta * xi) *
          mainR1 (theta * a) (theta * f) (theta * H) *
          mainEcov (theta * v) q ≤
        theta * (Real.sqrt 2 * mainT0 xi * mainR1 a f H * mainEcov v q) := by
    rw [hT0, hR1]
    calc
      _ ≤ Real.sqrt 2 * (Real.sqrt theta * mainT0 xi) *
          (Real.sqrt theta * mainR1 a f H) * (theta * mainEcov v q) := by
            apply mul_le_mul_of_nonneg_left hEcov
            positivity
      _ = theta ^ 2 *
          (Real.sqrt 2 * mainT0 xi * mainR1 a f H * mainEcov v q) := by
            calc
              _ = (theta * (Real.sqrt theta * Real.sqrt theta)) *
                  (Real.sqrt 2 * mainT0 xi * mainR1 a f H * mainEcov v q) := by ring
              _ = theta ^ 2 *
                  (Real.sqrt 2 * mainT0 xi * mainR1 a f H * mainEcov v q) := by
                    rw [hsquare]
                    ring
      _ ≤ theta *
          (Real.sqrt 2 * mainT0 xi * mainR1 a f H * mainEcov v q) := by
            exact mul_le_mul_of_nonneg_right hthetaSq hCovBaseNonneg
  have htermDQ :
      2 * mainLoadD (theta * v) (theta * a) (theta * f) (theta * H)
          (theta * xi) (mainKd (theta * v)) *
          mainLoadQ (theta * H) (mainOp (theta * v)) (mainOm (theta * v)) ≤
        theta * (2 * mainLoadD v a f H xi (mainKd v) *
          mainLoadQ H (mainOp v) (mainOm v)) := by
    rw [hD]
    calc
      _ ≤ 2 * (theta * mainLoadD v a f H xi (mainKd v)) *
          (Real.sqrt theta * mainLoadQ H (mainOp v) (mainOm v)) :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
      _ = (theta * Real.sqrt theta) *
          (2 * mainLoadD v a f H xi (mainKd v) *
            mainLoadQ H (mainOp v) (mainOm v)) := by ring
      _ ≤ theta * (2 * mainLoadD v a f H xi (mainKd v) *
          mainLoadQ H (mainOp v) (mainOm v)) :=
        mul_le_mul_of_nonneg_right hthetaSqrt
          (mul_nonneg (mul_nonneg (by norm_num) hDNonneg) hQNonneg)
  have htermBeV :
      2 * mainBe (theta * v) q * mainV (theta * xi) (theta * f) ≤
        theta * (2 * mainBe v q * mainV xi f) := by
    rw [hV]
    calc
      _ ≤ 2 * (theta * mainBe v q) *
          (Real.sqrt theta * mainV xi f) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbe (by norm_num))
          (mul_nonneg (Real.sqrt_nonneg _) hVNonneg)
      _ = (theta * Real.sqrt theta) * (2 * mainBe v q * mainV xi f) := by ring
      _ ≤ theta * (2 * mainBe v q * mainV xi f) :=
        mul_le_mul_of_nonneg_right hthetaSqrt
          (mul_nonneg (mul_nonneg (by norm_num) hBeNonneg) hVNonneg)
  have htermAG :
      mainFourLoadAG (theta * v) (theta * H) (theta * xi) q *
          mainG (theta * xi) ≤
        theta * (mainFourLoadAG v H xi q * mainG xi) := by
    rw [hG]
    calc
      _ ≤ (theta * mainFourLoadAG v H xi q) *
          (Real.sqrt theta * mainG xi) :=
        mul_le_mul_of_nonneg_right hAG
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = (theta * Real.sqrt theta) *
          (mainFourLoadAG v H xi q * mainG xi) := by ring
      _ ≤ theta * (mainFourLoadAG v H xi q * mainG xi) :=
        mul_le_mul_of_nonneg_right hthetaSqrt
          (mul_nonneg hFourNonneg (Real.sqrt_nonneg _))
  have hfeedbackBaseNonneg : 0 ≤
      2 * mainKd v * (63 / 50) *
        (Real.sqrt 2 * mainBeta * mainLoadD v a f H xi (mainKd v) +
          mainLoadZ v a f H xi (mainKd v) * mainRec xi) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hKdNonneg)
        (by norm_num : 0 ≤ (63 / 50 : ℝ)))
      (add_nonneg hDfbNonneg hZrecNonneg)
  have hKdThetaNonneg : 0 ≤ mainKd (theta * v) := by
    rw [hkd]
    positivity
  have hfeedbackCoeffThetaNonneg :
      0 ≤ 2 * mainKd (theta * v) * (63 / 50) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hKdThetaNonneg)
      (by norm_num : 0 ≤ (63 / 50 : ℝ))
  have htermFeedback :
      2 * mainKd (theta * v) * (63 / 50) *
          (Real.sqrt 2 * mainBeta *
              mainLoadD (theta * v) (theta * a) (theta * f) (theta * H)
                (theta * xi) (mainKd (theta * v)) +
            mainLoadZ (theta * v) (theta * a) (theta * f) (theta * H)
              (theta * xi) (mainKd (theta * v)) * mainRec (theta * xi)) ≤
        theta * (2 * mainKd v * (63 / 50) *
          (Real.sqrt 2 * mainBeta * mainLoadD v a f H xi (mainKd v) +
            mainLoadZ v a f H xi (mainKd v) * mainRec xi)) := by
    calc
      _ ≤ 2 * mainKd (theta * v) * (63 / 50) *
          (theta * (Real.sqrt 2 * mainBeta * mainLoadD v a f H xi (mainKd v) +
            mainLoadZ v a f H xi (mainKd v) * mainRec xi)) :=
        mul_le_mul_of_nonneg_left hfeedback hfeedbackCoeffThetaNonneg
      _ = (theta * Real.sqrt theta) *
          (2 * mainKd v * (63 / 50) *
          (Real.sqrt 2 * mainBeta * mainLoadD v a f H xi (mainKd v) +
            mainLoadZ v a f H xi (mainKd v) * mainRec xi)) := by
              rw [hkd]
              ring
      _ ≤ theta * (2 * mainKd v * (63 / 50) *
          (Real.sqrt 2 * mainBeta * mainLoadD v a f H xi (mainKd v) +
            mainLoadZ v a f H xi (mainKd v) * mainRec xi)) :=
        mul_le_mul_of_nonneg_right hthetaSqrt hfeedbackBaseNonneg
  unfold mainSourceError mainError
  calc
    _ = mainLinearError (theta * v) (theta * H) (theta * xi) q +
        mainLoadZ (theta * v) (theta * a) (theta * f) (theta * H)
          (theta * xi) (mainKd (theta * v)) ^ 2 +
        (theta * v / 2 * mainR1 (theta * a) (theta * f) (theta * H) ^ 2 +
          2 * (mainKrem (theta * v) *
              mainR1 (theta * a) (theta * f) (theta * H) +
            mainKd (theta * v) * mainT0 (theta * xi)) *
            mainT0 (theta * xi) * Real.sqrt (theta * v) +
          Real.sqrt 2 * mainT0 (theta * xi) *
            mainR1 (theta * a) (theta * f) (theta * H) *
            mainEcov (theta * v) q) +
        2 * mainLoadD (theta * v) (theta * a) (theta * f) (theta * H)
          (theta * xi) (mainKd (theta * v)) *
          mainLoadQ (theta * H) (mainOp (theta * v)) (mainOm (theta * v)) +
        2 * mainBe (theta * v) q *
          mainV (theta * xi) (theta * f) +
        mainFourLoadAG (theta * v) (theta * H) (theta * xi) q *
          mainG (theta * xi) +
        2 * mainKd (theta * v) * (63 / 50) *
          (Real.sqrt 2 * mainBeta *
              mainLoadD (theta * v) (theta * a) (theta * f) (theta * H)
                (theta * xi) (mainKd (theta * v)) +
            mainLoadZ (theta * v) (theta * a) (theta * f) (theta * H)
              (theta * xi) (mainKd (theta * v)) * mainRec (theta * xi)) := rfl
    _ ≤ theta * mainLinearError v H xi q +
        theta * (mainLoadZ v a f H xi (mainKd v)) ^ 2 +
        (theta * (v / 2 * mainR1 a f H ^ 2) +
          theta * (2 * (mainKrem v * mainR1 a f H + mainKd v * mainT0 xi) *
            mainT0 xi * Real.sqrt v) +
          theta * (Real.sqrt 2 * mainT0 xi * mainR1 a f H * mainEcov v q)) +
        theta * (2 * mainLoadD v a f H xi (mainKd v) *
          mainLoadQ H (mainOp v) (mainOm v)) +
        theta * (2 * mainBe v q * mainV xi f) +
        theta * (mainFourLoadAG v H xi q * mainG xi) +
        theta * (2 * mainKd v * (63 / 50) *
          (Real.sqrt 2 * mainBeta * mainLoadD v a f H xi (mainKd v) +
            mainLoadZ v a f H xi (mainKd v) * mainRec xi)) := by
              apply add_le_add
              · apply add_le_add
                · apply add_le_add
                  · apply add_le_add
                    · apply add_le_add
                      · apply add_le_add
                        · exact hL
                        · exact htermZ
                      · exact add_le_add (add_le_add htermR1 htermMid) htermCov
                    · exact htermDQ
                  · exact htermBeV
                · exact htermAG
              · exact htermFeedback
    _ = theta * mainSourceError v a f H xi q := by
      unfold mainSourceError mainError
      ring

end ASDExplicitGamma.Main

end

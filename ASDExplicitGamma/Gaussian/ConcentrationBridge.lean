/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.ConcentrationMGF
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating the Gaussian bridge

The bridge derivative splits into the heat-smoothed directional derivative and the averaged
Laplacian. This is the pointwise identity used to differentiate the log moment.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open Filter
open Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

private theorem bridge_norm_add_smul_bound {n : ℕ}
    (x ξ : Fin n → ℝ) (c : ℝ) :
    1 + ‖x + c • ξ‖ ≤ (1 + ‖x‖) * (1 + |c|) * (1 + ‖ξ‖) := by
  have htri : ‖x + c • ξ‖ ≤ ‖x‖ + |c| * ‖ξ‖ := by
    calc
      ‖x + c • ξ‖ ≤ ‖x‖ + ‖c • ξ‖ := norm_add_le _ _
      _ = ‖x‖ + |c| * ‖ξ‖ := by simp [norm_smul]
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have hc : 0 ≤ |c| := abs_nonneg _
  have hξ : 0 ≤ ‖ξ‖ := norm_nonneg _
  nlinarith [mul_nonneg hx hc, mul_nonneg hx hξ, mul_nonneg hc hξ]

private theorem bridge_integrable_pi_norm_power (n d : ℕ) :
    Integrable (fun ξ : Fin n → ℝ => (1 + ‖ξ‖) ^ d) (standardGaussianPi n) := by
  apply integrable_of_pi_polynomial_bound (by fun_prop) (C := 1) (by norm_num) (d := d)
  intro ξ
  rw [abs_of_nonneg (by positivity : 0 ≤ (1 + ‖ξ‖) ^ d)]
  simp

private theorem coordinate_bound_of_HPoly {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : HasPolynomiallyBoundedCoordinateDerivatives F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ,
      ∀ i x, |coordinateDerivative F i x| ≤ C * (1 + ‖x‖) ^ d := by
  rcases hF.2 with ⟨C, hC, d, hzero, hcoord⟩
  exact ⟨C, hC, d, fun i x =>
    (le_add_of_nonneg_left (abs_nonneg (F x))).trans (hcoord i x)⟩

private theorem integrable_fderiv_shift_constant {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F)
    (x : Fin n → ℝ) (c : ℝ) (v : Fin n → ℝ) :
    Integrable (fun η => fderiv ℝ F (x + c • η) v) (standardGaussianPi n) := by
  obtain ⟨C, hC, d, hcoordinate⟩ := coordinate_bound_of_HPoly hF
  let B : ℝ := (1 + ‖x‖) * (1 + |c|)
  let K : ℝ := (Fintype.card (Fin n) : ℝ) * C * B ^ d * ‖v‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoly := bridge_integrable_pi_norm_power n d
  have hmeas : Measurable (fun η => fderiv ℝ F (x + c • η) v) := by
    have hfd : Continuous (fun z : Fin n → ℝ => fderiv ℝ F z) :=
      hF.1.continuous_fderiv (by norm_num)
    exact (hfd.comp (continuous_const.add (continuous_id.const_smul c))).clm_apply continuous_const
      |>.measurable
  have hbound : ∀ η, |fderiv ℝ F (x + c • η) v| ≤ K * (1 + ‖η‖) ^ d := by
    intro η
    have hnorm : 1 + ‖x + c • η‖ ≤ B * (1 + ‖η‖) :=
      bridge_norm_add_smul_bound x η c
    have hcoord : ∀ i, |coordinateDerivative F i (x + c • η)| ≤
        C * B ^ d * (1 + ‖η‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (x + c • η)| ≤ C * (1 + ‖x + c • η‖) ^ d :=
          hcoordinate i _
        _ ≤ C * (B * (1 + ‖η‖)) ^ d := by gcongr
        _ = C * B ^ d * (1 + ‖η‖) ^ d := by rw [mul_pow]; ring
    have hfd := concentration_abs_fderiv_apply_le (x + c • η) v
      (by positivity : 0 ≤ C * B ^ d * (1 + ‖η‖) ^ d) hcoord
    calc
      |fderiv ℝ F (x + c • η) v| ≤
          (Fintype.card (Fin n) : ℝ) * ‖v‖ *
            (C * B ^ d * (1 + ‖η‖) ^ d) := hfd
      _ = K * (1 + ‖η‖) ^ d := by dsimp [K]; ring
  apply integrable_of_pi_polynomial_bound hmeas (C := K) hK (d := d)
  intro η
  simpa [Real.norm_eq_abs] using hbound η

private theorem integrable_fderiv_shift_id {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F)
    (x : Fin n → ℝ) (c : ℝ) :
    Integrable (fun η => fderiv ℝ F (x + c • η) η) (standardGaussianPi n) := by
  obtain ⟨C, hC, d, hcoordinate⟩ := coordinate_bound_of_HPoly hF
  let B : ℝ := (1 + ‖x‖) * (1 + |c|)
  let K : ℝ := (Fintype.card (Fin n) : ℝ) * C * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoly := bridge_integrable_pi_norm_power n (d + 1)
  have hmeas : Measurable (fun η => fderiv ℝ F (x + c • η) η) := by
    have hfd : Continuous (fun z : Fin n → ℝ => fderiv ℝ F z) :=
      hF.1.continuous_fderiv (by norm_num)
    exact (hfd.comp (continuous_const.add (continuous_id.const_smul c))).clm_apply
      continuous_id |>.measurable
  have hbound : ∀ η, |fderiv ℝ F (x + c • η) η| ≤ K * (1 + ‖η‖) ^ (d + 1) := by
    intro η
    have hnorm : 1 + ‖x + c • η‖ ≤ B * (1 + ‖η‖) :=
      bridge_norm_add_smul_bound x η c
    have hcoord : ∀ i, |coordinateDerivative F i (x + c • η)| ≤
        C * B ^ d * (1 + ‖η‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (x + c • η)| ≤ C * (1 + ‖x + c • η‖) ^ d :=
          hcoordinate i _
        _ ≤ C * (B * (1 + ‖η‖)) ^ d := by gcongr
        _ = C * B ^ d * (1 + ‖η‖) ^ d := by rw [mul_pow]; ring
    have hfd := concentration_abs_fderiv_apply_le (x + c • η) η
      (by positivity : 0 ≤ C * B ^ d * (1 + ‖η‖) ^ d) hcoord
    have hη : ‖η‖ ≤ 1 + ‖η‖ := by linarith [norm_nonneg η]
    calc
      |fderiv ℝ F (x + c • η) η| ≤
          (Fintype.card (Fin n) : ℝ) * ‖η‖ *
            (C * B ^ d * (1 + ‖η‖) ^ d) := hfd
      _ ≤ K * (1 + ‖η‖) ^ (d + 1) := by
        dsimp [K]
        rw [pow_succ]
        have hnonneg : 0 ≤ (Fintype.card (Fin n) : ℝ) * C * B ^ d := by positivity
        calc
          (Fintype.card (Fin n) : ℝ) * ‖η‖ *
              (C * B ^ d * (1 + ‖η‖) ^ d) ≤
              (Fintype.card (Fin n) : ℝ) * C * B ^ d *
                (1 + ‖η‖) ^ d * (1 + ‖η‖) := by
                  have hA : 0 ≤ (Fintype.card (Fin n) : ℝ) * C * B ^ d *
                      (1 + ‖η‖) ^ d := by positivity
                  calc
                    (Fintype.card (Fin n) : ℝ) * ‖η‖ *
                        (C * B ^ d * (1 + ‖η‖) ^ d) =
                        ((Fintype.card (Fin n) : ℝ) * C * B ^ d *
                          (1 + ‖η‖) ^ d) * ‖η‖ := by ring
                    _ ≤ ((Fintype.card (Fin n) : ℝ) * C * B ^ d *
                          (1 + ‖η‖) ^ d) * (1 + ‖η‖) :=
                        mul_le_mul_of_nonneg_left hη hA
                    _ = (Fintype.card (Fin n) : ℝ) * C * B ^ d *
                          (1 + ‖η‖) ^ d * (1 + ‖η‖) := by ring
          _ = (Fintype.card (Fin n) : ℝ) * C * B ^ d *
                ((1 + ‖η‖) ^ d * (1 + ‖η‖)) := by ring
  apply integrable_of_pi_polynomial_bound hmeas (C := K) hK (d := d + 1)
  intro η
  simpa [Real.norm_eq_abs] using hbound η

private theorem hasPolynomiallyBoundedSecond_of_third_bridge {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedThirdCoordinateDerivatives F) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives F := by
  rcases hF with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  exact ⟨hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3),
    ⟨C, hC, d, hzero, hone, htwo⟩⟩

private theorem hasPolynomiallyBoundedCoordinateDerivatives_of_second_bridge {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) :
    HasPolynomiallyBoundedCoordinateDerivatives F := by
  rcases hF.2 with ⟨C, hC, d, hzero, hone, htwo⟩
  refine ⟨hF.1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2), 2 * C, by positivity, d,
    ?_, ?_⟩
  · intro x
    calc
      |F x| ≤ C * (1 + ‖x‖) ^ d := hzero x
      _ ≤ 2 * C * (1 + ‖x‖) ^ d := by
        have hn : 0 ≤ C * (1 + ‖x‖) ^ d := by positivity
        nlinarith
  · intro i x
    calc
      |F x| + |coordinateDerivative F i x| ≤
          C * (1 + ‖x‖) ^ d + C * (1 + ‖x‖) ^ d := add_le_add (hzero x) (hone i x)
      _ = 2 * C * (1 + ‖x‖) ^ d := by ring

/-- Along the Gaussian bridge, differentiating the heat average gives its directional derivative
minus one half of its averaged Laplacian. -/
theorem hasDerivAt_gaussian_heatBridge {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    (ξ : Fin n → ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun r => heatAverage F (Real.sqrt r • ξ) (1 - r))
      (fderiv ℝ (fun x => heatAverage F x (1 - t)) (Real.sqrt t • ξ) ξ /
          (2 * Real.sqrt t) -
        (1 / 2 : ℝ) * heatLaplacianAverage F (Real.sqrt t • ξ) (1 - t)) t := by
  have hF₂ := hasPolynomiallyBoundedSecond_of_third_bridge hF₃
  have hF₁ := hasPolynomiallyBoundedCoordinateDerivatives_of_second_bridge hF₂
  let x : Fin n → ℝ := Real.sqrt t • ξ
  let c : ℝ := Real.sqrt (1 - t)
  have hc : 0 < c := Real.sqrt_pos.2 (by linarith)
  have hbridge := (hasDerivAt_gaussian_bridge_integral hF₁ ξ ht ht1).2
  have hpath : HasDerivAt (fun r => heatAverage F (Real.sqrt r • ξ) (1 - r))
      (∫ η, fderiv ℝ F (x + c • η)
        ((1 / (2 * Real.sqrt t)) • ξ - (1 / (2 * Real.sqrt (1 - t))) • η)
        ∂(standardGaussianPi n)) t := by
    convert hbridge using 1
    simp [heatAverage, shiftAverage]
  have hcenter := hasFDerivAt_shiftAverage_center hF₁ x c
  have hfirstInt : Integrable (fun η => fderiv ℝ F (x + c • η) ξ)
      (standardGaussianPi n) :=
    integrable_fderiv_shift_constant hF₁ x c ξ
  have hsecondInt : Integrable (fun η => fderiv ℝ F (x + c • η) η)
      (standardGaussianPi n) :=
    integrable_fderiv_shift_id hF₁ x c
  have hfirst : (∫ η, fderiv ℝ F (x + c • η) ξ ∂(standardGaussianPi n)) =
      fderiv ℝ (fun y => heatAverage F y (1 - t)) x ξ := by
    have hderiv := hcenter.2.1
    have hEq : fderiv ℝ (fun y => heatAverage F y (1 - t)) x =
        ∫ η, fderiv ℝ F (x + c • η) ∂(standardGaussianPi n) := by
      simpa [c, heatAverage, shiftAverage] using hderiv.fderiv
    calc
      _ = (∫ η, fderiv ℝ F (x + c • η) ∂(standardGaussianPi n)) ξ :=
        (ContinuousLinearMap.integral_apply hcenter.1 ξ).symm
      _ = _ := by rw [hEq]
  have hsecond := integral_fderiv_shift_scaled_eq_sqrt_mul_laplacian
    hF₁ hF₂ x (by nlinarith : 0 < 1 - t)
  have hsecond' :
      ∫ η, fderiv ℝ F (x + c • η) η ∂(standardGaussianPi n) =
        c * heatLaplacianAverage F x (1 - t) := by
    simpa [c, heatLaplacianAverage, shiftAverage] using hsecond
  have hcombine :
      ∫ η, fderiv ℝ F (x + c • η)
        ((1 / (2 * Real.sqrt t)) • ξ - (1 / (2 * Real.sqrt (1 - t))) • η)
        ∂(standardGaussianPi n) =
      (1 / (2 * Real.sqrt t)) *
          fderiv ℝ (fun y => heatAverage F y (1 - t)) x ξ -
        (1 / 2 : ℝ) * heatLaplacianAverage F x (1 - t) := by
    have hsum :
        (fun η => fderiv ℝ F (x + c • η)
          ((1 / (2 * Real.sqrt t)) • ξ - (1 / (2 * Real.sqrt (1 - t))) • η)) =
        fun η => (1 / (2 * Real.sqrt t)) * fderiv ℝ F (x + c • η) ξ -
          (1 / (2 * Real.sqrt (1 - t))) * fderiv ℝ F (x + c • η) η := by
      funext η
      simp [map_sub, map_smul, smul_eq_mul, mul_comm]
    calc
      ∫ η, fderiv ℝ F (x + c • η)
          ((1 / (2 * Real.sqrt t)) • ξ - (1 / (2 * Real.sqrt (1 - t))) • η)
          ∂(standardGaussianPi n) =
        ∫ η, (1 / (2 * Real.sqrt t)) * fderiv ℝ F (x + c • η) ξ -
          (1 / (2 * Real.sqrt (1 - t))) * fderiv ℝ F (x + c • η) η
          ∂(standardGaussianPi n) := by rw [← hsum]
      _ = (1 / (2 * Real.sqrt t)) *
            ∫ η, fderiv ℝ F (x + c • η) ξ ∂(standardGaussianPi n) -
          (1 / (2 * Real.sqrt (1 - t))) *
            ∫ η, fderiv ℝ F (x + c • η) η ∂(standardGaussianPi n) := by
          rw [integral_sub (hfirstInt.const_mul _) (hsecondInt.const_mul _),
            integral_const_mul, integral_const_mul]
      _ = (1 / (2 * Real.sqrt t)) *
            fderiv ℝ (fun y => heatAverage F y (1 - t)) x ξ -
          (1 / (2 * Real.sqrt (1 - t))) *
            (c * heatLaplacianAverage F x (1 - t)) := by rw [hfirst, hsecond']
      _ = (1 / (2 * Real.sqrt t)) *
            fderiv ℝ (fun y => heatAverage F y (1 - t)) x ξ -
          (1 / 2 : ℝ) * heatLaplacianAverage F x (1 - t) := by
          have hs : Real.sqrt (1 - t) ≠ 0 := ne_of_gt hc
          have hcoeff :
              (1 / (2 * Real.sqrt (1 - t))) *
                  (Real.sqrt (1 - t) * heatLaplacianAverage F x (1 - t)) =
                (1 / 2 : ℝ) * heatLaplacianAverage F x (1 - t) := by
            field_simp [hs]
          exact congrArg
            (fun z : ℝ => (1 / (2 * Real.sqrt t)) *
              fderiv ℝ (fun y => heatAverage F y (1 - t)) x ξ - z) hcoeff
  convert hpath using 1
  simpa [x, div_eq_mul_inv, mul_comm] using hcombine.symm

end ASDExplicitGamma.Gaussian

/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.ConcentrationSemigroup
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Growth bounds for Gaussian heat smoothing

Polynomial growth of the first two derivatives is preserved by the finite-dimensional Gaussian
heat average. These estimates provide the polynomial-growth hypotheses needed for Gaussian IBP
after exponentiating a bounded heat average.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open scoped Topology

namespace ASDExplicitGamma.Gaussian

private lemma concentration_norm_add_smul_bound {n : ℕ}
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

theorem integrable_pi_norm_power (n d : ℕ) :
    Integrable (fun ξ : Fin n → ℝ => (1 + ‖ξ‖) ^ d) (standardGaussianPi n) := by
  apply integrable_of_pi_polynomial_bound (by fun_prop) (C := 1) (by norm_num) (d := d)
  intro ξ
  rw [abs_of_nonneg (by positivity : 0 ≤ (1 + ‖ξ‖) ^ d)]
  simp

theorem abs_shiftAverage_le_of_polynomial_bound {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : 0 ≤ C) {d : ℕ}
    (hg : ∀ z, |f z| ≤ C * (1 + ‖z‖) ^ d)
    (x : Fin n → ℝ) (c : ℝ) :
    |shiftAverage f x c| ≤
      (C * (1 + |c|) ^ d * (∫ ξ, (1 + ‖ξ‖) ^ d ∂(standardGaussianPi n))) *
        (1 + ‖x‖) ^ d := by
  let M : ℝ := ∫ ξ, (1 + ‖ξ‖) ^ d ∂(standardGaussianPi n)
  let K : ℝ := C * (1 + |c|) ^ d * (1 + ‖x‖) ^ d
  have hMomentInt := integrable_pi_norm_power n d
  have hMomentNonneg : 0 ≤ M := by
    apply integral_nonneg
    intro ξ
    positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmeas : Measurable (fun ξ : Fin n → ℝ => f (x + c • ξ)) :=
    (hf.comp (continuous_const.add (continuous_id.const_smul c))).measurable
  have hFint : Integrable (fun ξ : Fin n → ℝ => f (x + c • ξ))
      (standardGaussianPi n) := by
    apply integrable_of_pi_polynomial_bound hmeas
      (C := C * ((1 + ‖x‖) * (1 + |c|)) ^ d) (by positivity) (d := d)
    intro ξ
    calc
      |f (x + c • ξ)| ≤ C * (1 + ‖x + c • ξ‖) ^ d := hg _
      _ ≤ C * ((1 + ‖x‖) * (1 + |c|) * (1 + ‖ξ‖)) ^ d := by
        gcongr
        exact concentration_norm_add_smul_bound x ξ c
      _ = C * ((1 + ‖x‖) * (1 + |c|)) ^ d * (1 + ‖ξ‖) ^ d := by
        rw [mul_pow, mul_pow]
        ring
  have hmajorInt : Integrable (fun ξ : Fin n → ℝ => K * (1 + ‖ξ‖) ^ d)
      (standardGaussianPi n) := by
    simpa using hMomentInt.const_mul K
  have hmajor (ξ : Fin n → ℝ) :
      |f (x + c • ξ)| ≤ K * (1 + ‖ξ‖) ^ d := by
    calc
      |f (x + c • ξ)| ≤ C * (1 + ‖x + c • ξ‖) ^ d := hg _
      _ ≤ C * ((1 + ‖x‖) * (1 + |c|) * (1 + ‖ξ‖)) ^ d := by
        gcongr
        exact concentration_norm_add_smul_bound x ξ c
      _ = K * (1 + ‖ξ‖) ^ d := by
        dsimp [K]
        rw [mul_pow, mul_pow]
        ring
  have hIntegral :
      ‖∫ ξ, f (x + c • ξ) ∂(standardGaussianPi n)‖ ≤
        ∫ ξ, ‖f (x + c • ξ)‖ ∂(standardGaussianPi n) :=
    norm_integral_le_integral_norm (μ := standardGaussianPi n)
      (fun ξ : Fin n → ℝ => f (x + c • ξ))
  calc
    |shiftAverage f x c| =
        ‖∫ ξ, f (x + c • ξ) ∂(standardGaussianPi n)‖ := by
          rw [Real.norm_eq_abs]
          rfl
    _ ≤ ∫ ξ, ‖f (x + c • ξ)‖ ∂(standardGaussianPi n) := hIntegral
    _ ≤ ∫ ξ, K * (1 + ‖ξ‖) ^ d ∂(standardGaussianPi n) := by
          exact integral_mono_ae (μ := standardGaussianPi n) hFint.norm hmajorInt
            (ae_of_all (μ := standardGaussianPi n) fun ξ =>
              by simpa [Real.norm_eq_abs] using hmajor ξ)
    _ = K * M := by rw [integral_const_mul]
    _ = (C * (1 + |c|) ^ d * M) * (1 + ‖x‖) ^ d := by
          dsimp [K, M]
          ring_nf

private theorem contDiff_coordinateDerivative_c2 {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ 3 F) (i : Fin n) :
    ContDiff ℝ 2 (coordinateDerivative F i) := by
  have h := hF.contDiff_fderiv_apply (m := 2)
    (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hpair : ContDiff ℝ 2
      (fun x : Fin n → ℝ => (x, (Pi.single i (1 : ℝ) : Fin n → ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hcomp := h.comp hpair
  convert hcomp using 1
  · ext x
    rfl

private theorem contDiff_coordinateDerivative_c1 {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) (i : Fin n) :
    ContDiff ℝ 1 (coordinateDerivative F i) := by
  have h := hF.contDiff_fderiv_apply (m := 1)
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hpair : ContDiff ℝ 1
      (fun x : Fin n → ℝ => (x, (Pi.single i (1 : ℝ) : Fin n → ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hcomp := h.comp hpair
  convert hcomp using 1
  · ext x
    rfl

private theorem hasPolynomiallyBoundedSecond_of_third_local {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedThirdCoordinateDerivatives F) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives F := by
  rcases hF with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  exact ⟨hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3),
    ⟨C, hC, d, hzero, hone, htwo⟩⟩

private theorem hasPolynomiallyBoundedCoordinateDerivatives_of_second_local {n : ℕ}
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
        have hnonneg : 0 ≤ C * (1 + ‖x‖) ^ d := by positivity
        nlinarith
  · intro i x
    calc
      |F x| + |coordinateDerivative F i x| ≤
          C * (1 + ‖x‖) ^ d + C * (1 + ‖x‖) ^ d := add_le_add (hzero x) (hone i x)
      _ = 2 * C * (1 + ‖x‖) ^ d := by ring

private theorem hasPolynomiallyBoundedSecond_coordinateDerivative {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedThirdCoordinateDerivatives F) (i : Fin n) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives (coordinateDerivative F i) := by
  rcases hF with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  refine ⟨contDiff_coordinateDerivative_c2 hcont i, C, hC, d, ?_, ?_, ?_⟩
  · intro x
    exact hone i x
  · intro j x
    exact htwo i j x
  · intro j k x
    exact hthree i j k x

/-- Coordinate differentiation commutes with Gaussian heat averaging. -/
theorem coordinateDerivative_heatAverage {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    (t : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (fun y : Fin n → ℝ => heatAverage F y t) i x =
      heatAverage (coordinateDerivative F i) x t := by
  let c : ℝ := Real.sqrt t
  have hF₁ : HasPolynomiallyBoundedCoordinateDerivatives F :=
    hasPolynomiallyBoundedCoordinateDerivatives_of_second_local hF
  have hcenter := hasFDerivAt_shiftAverage_center hF₁ x c
  let e : Fin n → ℝ := Pi.single i 1
  calc
    coordinateDerivative (fun y : Fin n → ℝ => heatAverage F y t) i x =
        fderiv ℝ (fun y => heatAverage F y t) x e := by
          simp [coordinateDerivative, e]
    _ = (∫ ξ, fderiv ℝ F (x + c • ξ) ∂(standardGaussianPi n)) e := by
          simpa [heatAverage, c] using
            congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L e)
              hcenter.2.1.fderiv
    _ = ∫ ξ, fderiv ℝ F (x + c • ξ) e ∂(standardGaussianPi n) :=
          ContinuousLinearMap.integral_apply hcenter.1 e
    _ = ∫ ξ, coordinateDerivative F i (x + c • ξ) ∂(standardGaussianPi n) := by
          apply integral_congr_ae
          exact ae_of_all _ fun ξ => by simp [coordinateDerivative, e]
    _ = heatAverage (coordinateDerivative F i) x t := rfl

/-- Gaussian heat averaging preserves polynomial growth of the function and its first two
coordinate derivatives. -/
theorem hasPolynomiallyBoundedSecond_heatAverage_of_third {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F) (t : ℝ) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives
      (fun x : Fin n → ℝ => heatAverage F x t) := by
  rcases hF₃ with ⟨hFcont, C, hC, d, hzero, hone, htwo, hthree⟩
  let U : (Fin n → ℝ) → ℝ := fun x => heatAverage F x t
  let c : ℝ := Real.sqrt t
  let M : ℝ := ∫ ξ, (1 + ‖ξ‖) ^ d ∂(standardGaussianPi n)
  let C' : ℝ := C * (1 + |c|) ^ d * M
  have hC' : 0 ≤ C' := by
    have hM : 0 ≤ M := by
      apply integral_nonneg
      intro ξ
      positivity
    dsimp [C']
    positivity
  have hF₂ := hasPolynomiallyBoundedSecond_of_third_local
    ⟨hFcont, C, hC, d, hzero, hone, htwo, hthree⟩
  have hF₁ := hasPolynomiallyBoundedCoordinateDerivatives_of_second_local hF₂
  have hUcont : ContDiff ℝ 2 U := by
    simpa only [U] using contDiff_two_heatAverage_of_third
      ⟨hFcont, C, hC, d, hzero, hone, htwo, hthree⟩ t
  have hcenterF (x : Fin n → ℝ) := hasFDerivAt_shiftAverage_center hF₁ x c
  have hUfirst (i : Fin n) (x : Fin n → ℝ) :
      coordinateDerivative U i x = heatAverage (coordinateDerivative F i) x t := by
    let e : Fin n → ℝ := Pi.single i 1
    have hderiv := (hcenterF x).2.1
    calc
      coordinateDerivative U i x = fderiv ℝ U x e := by
        simp [coordinateDerivative, e]
      _ = (∫ ξ, fderiv ℝ F (x + c • ξ) ∂(standardGaussianPi n)) e := by
        simpa [U, heatAverage, c] using
          congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L e) hderiv.fderiv
      _ = ∫ ξ, fderiv ℝ F (x + c • ξ) e ∂(standardGaussianPi n) :=
        ContinuousLinearMap.integral_apply (hcenterF x).1 e
      _ = ∫ ξ, coordinateDerivative F i (x + c • ξ) ∂(standardGaussianPi n) := by
        apply integral_congr_ae
        exact ae_of_all _ fun ξ => by simp [coordinateDerivative, e]
      _ = heatAverage (coordinateDerivative F i) x t := rfl
  have hUsecond (i j : Fin n) (x : Fin n → ℝ) :
      coordinateDerivative (coordinateDerivative U i) j x =
        heatAverage (coordinateDerivative (coordinateDerivative F i) j) x t := by
    let Gi : (Fin n → ℝ) → ℝ := coordinateDerivative F i
    have hG₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives Gi :=
      hasPolynomiallyBoundedSecond_coordinateDerivative
        ⟨hFcont, C, hC, d, hzero, hone, htwo, hthree⟩ i
    have hG₁ := hasPolynomiallyBoundedCoordinateDerivatives_of_second_local hG₂
    have hcenterG (y : Fin n → ℝ) := hasFDerivAt_shiftAverage_center hG₁ y c
    have heq : coordinateDerivative U i = fun y => heatAverage Gi y t := by
      funext y
      exact hUfirst i y
    let e : Fin n → ℝ := Pi.single j 1
    rw [heq]
    calc
      coordinateDerivative (fun y => heatAverage Gi y t) j x =
          fderiv ℝ (fun y => heatAverage Gi y t) x e := by
            simp [coordinateDerivative, e]
      _ = (∫ ξ, fderiv ℝ Gi (x + c • ξ) ∂(standardGaussianPi n)) e := by
            simpa [heatAverage, c] using
              congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L e)
                (hcenterG x).2.1.fderiv
      _ = ∫ ξ, fderiv ℝ Gi (x + c • ξ) e ∂(standardGaussianPi n) :=
            ContinuousLinearMap.integral_apply (hcenterG x).1 e
      _ = ∫ ξ, coordinateDerivative Gi j (x + c • ξ) ∂(standardGaussianPi n) := by
            apply integral_congr_ae
            exact ae_of_all _ fun ξ => by simp [coordinateDerivative, e]
      _ = heatAverage (coordinateDerivative Gi j) x t := rfl
  refine ⟨hUcont, C', hC', d, ?_, ?_, ?_⟩
  · intro x
    simpa [U, heatAverage, c, M, C'] using abs_shiftAverage_le_of_polynomial_bound
      hFcont.continuous hC hzero x c
  · intro i x
    rw [hUfirst]
    simpa [heatAverage, c, M, C'] using abs_shiftAverage_le_of_polynomial_bound
      (contDiff_coordinateDerivative_c2 hFcont i).continuous hC (hone i) x c
  · intro i j x
    rw [hUsecond]
    have hGi : ContDiff ℝ 2 (coordinateDerivative F i) :=
      contDiff_coordinateDerivative_c2 hFcont i
    have hGij : ContDiff ℝ 1 (coordinateDerivative (coordinateDerivative F i) j) :=
      contDiff_coordinateDerivative_c1 hGi j
    simpa [heatAverage, c, M, C'] using abs_shiftAverage_le_of_polynomial_bound
      hGij.continuous hC (htwo i j) x c

end ASDExplicitGamma.Gaussian

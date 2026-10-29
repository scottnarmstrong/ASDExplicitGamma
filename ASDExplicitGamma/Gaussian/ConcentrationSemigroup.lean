/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.FiniteHeat
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Gaussian concentration through the heat semigroup

The initial lemmas make the heat identity available as a scaled Gaussian integration-by-parts
formula. The sharp concentration estimate is developed from this identity below.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open Filter
open Set
open scoped Topology
open scoped ENNReal NNReal

namespace ASDExplicitGamma.Gaussian

private lemma concentration_norm_add_smul_le {n : ℕ} (x ξ : Fin n → ℝ) (u : ℝ) :
    1 + ‖x + u • ξ‖ ≤ (1 + ‖x‖) * (1 + |u|) * (1 + ‖ξ‖) := by
  have htri : ‖x + u • ξ‖ ≤ ‖x‖ + |u| * ‖ξ‖ := by
    calc
      ‖x + u • ξ‖ ≤ ‖x‖ + ‖u • ξ‖ := norm_add_le _ _
      _ = ‖x‖ + |u| * ‖ξ‖ := by simp [norm_smul]
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have hu : 0 ≤ |u| := abs_nonneg _
  have hξ : 0 ≤ ‖ξ‖ := norm_nonneg _
  nlinarith [mul_nonneg hx hu, mul_nonneg hx hξ, mul_nonneg hu hξ]

theorem concentration_fderiv_apply_eq_sum {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (z v : Fin n → ℝ) :
    fderiv ℝ F z v = ∑ i, v i * coordinateDerivative F i z := by
  have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hv, map_sum]
  simp [coordinateDerivative, smul_eq_mul, Pi.single_apply]

theorem concentration_abs_fderiv_apply_le {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (z v : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i, |coordinateDerivative F i z| ≤ B) :
    |fderiv ℝ F z v| ≤ (Fintype.card (Fin n) : ℝ) * ‖v‖ * B := by
  rw [concentration_fderiv_apply_eq_sum]
  calc
    |∑ i, v i * coordinateDerivative F i z| ≤
        ∑ i, |v i * coordinateDerivative F i z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖v‖ * B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hv : |v i| ≤ ‖v‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
      calc
        |v i| * |coordinateDerivative F i z| ≤ |v i| * B :=
          mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
        _ ≤ ‖v‖ * B := mul_le_mul_of_nonneg_right hv hB
    _ = (Fintype.card (Fin n) : ℝ) * ‖v‖ * B := by
      simp [Finset.sum_const, mul_assoc]

/-- Differentiating a polynomially bounded `C¹` Gaussian shift with respect to its scale.
The proof is included here because this derivative is paired with the heat identity in the
scaled Gaussian IBP formula below. -/
private theorem hasDerivAt_shiftAverage_zero {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) (u : ℝ) :
    HasDerivAt (shiftAverage F 0)
      (∫ ξ, fderiv ℝ F (u • ξ) ξ ∂(standardGaussianPi n)) u := by
  rcases hF.2 with ⟨C, hC, d, hfunctionBound, hcoordinateBound⟩
  let Φ : ℝ → (Fin n → ℝ) → ℝ := fun s ξ => F (s • ξ)
  let Φ' : ℝ → (Fin n → ℝ) → ℝ := fun s ξ => fderiv ℝ F (s • ξ) ξ
  let B : ℝ := 2 + |u|
  let K : ℝ := (Fintype.card (Fin n) : ℝ) * (|u| + 1) * C * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hshiftCont (s : ℝ) : Continuous (fun ξ : Fin n → ℝ => s • ξ) :=
    continuous_id.const_smul s
  have hFmeas : ∀ᶠ s in nhds u, AEStronglyMeasurable (Φ s) (standardGaussianPi n) := by
    filter_upwards with s
    exact ((hF.1.continuous.comp (hshiftCont s)).measurable).aestronglyMeasurable
  have hFint : Integrable (Φ u) (standardGaussianPi n) := by
    let C' : ℝ := C * (1 + |u|) ^ d
    have hC' : 0 ≤ C' := by dsimp [C']; positivity
    apply integrable_of_pi_polynomial_bound
      ((hF.1.continuous.comp (continuous_id.const_smul u)).measurable)
      hC' (d := d)
    intro ξ
    have hnorm : 1 + ‖u • ξ‖ ≤ (1 + |u|) * (1 + ‖ξ‖) := by
      calc
        1 + ‖u • ξ‖ ≤ (1 + ‖(0 : Fin n → ℝ)‖) * (1 + |u|) * (1 + ‖ξ‖) :=
          by simpa using concentration_norm_add_smul_le (0 : Fin n → ℝ) ξ u
        _ = (1 + |u|) * (1 + ‖ξ‖) := by simp
    calc
      |F (u • ξ)| ≤ C * (1 + ‖u • ξ‖) ^ d := hfunctionBound _
      _ ≤ C * ((1 + |u|) * (1 + ‖ξ‖)) ^ d := by gcongr
      _ = C' * (1 + ‖ξ‖) ^ d := by
        dsimp [C']
        rw [mul_pow]
        ring
  have hderivCont : Continuous (fun ξ : Fin n → ℝ => fderiv ℝ F (u • ξ) ξ) := by
    have hfd : Continuous (fun z : Fin n → ℝ => fderiv ℝ F z) :=
      hF.1.continuous_fderiv (by norm_num)
    exact (hfd.comp (hshiftCont u)).clm_apply continuous_id
  have hF'meas : AEStronglyMeasurable (Φ' u) (standardGaussianPi n) :=
    hderivCont.measurable.aestronglyMeasurable
  have hpoly : Integrable (fun ξ : Fin n → ℝ => (1 + ‖ξ‖) ^ (d + 1))
      (standardGaussianPi n) := by
    apply integrable_of_pi_polynomial_bound (by fun_prop) (C := 1) (by norm_num)
      (d := d + 1)
    intro ξ
    rw [abs_of_nonneg (by positivity : 0 ≤ (1 + ‖ξ‖) ^ (d + 1))]
    simp
  have hboundInt : Integrable (fun ξ : Fin n → ℝ => K * (1 + ‖ξ‖) ^ (d + 1))
      (standardGaussianPi n) := by
    simpa using hpoly.const_mul K
  have hbound : ∀ᵐ ξ ∂(standardGaussianPi n), ∀ s ∈ Metric.ball u 1,
      ‖Φ' s ξ‖ ≤ K * (1 + ‖ξ‖) ^ (d + 1) := by
    apply ae_of_all
    intro ξ s hs
    have hsabs : |s| ≤ |u| + 1 := by
      have hdist : |s - u| < 1 := by simpa [Real.dist_eq] using Metric.mem_ball.mp hs
      calc
        |s| = |(s - u) + u| := by congr 1; ring
        _ ≤ |s - u| + |u| := abs_add_le _ _
        _ ≤ 1 + |u| := by linarith
        _ = |u| + 1 := by ring
    have hcoord : ∀ i, |coordinateDerivative F i (s • ξ)| ≤
        C * (1 + ‖s • ξ‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (s • ξ)| ≤
            |F (s • ξ)| + |coordinateDerivative F i (s • ξ)| :=
              le_add_of_nonneg_left (abs_nonneg _)
        _ ≤ C * (1 + ‖s • ξ‖) ^ d := hcoordinateBound i (s • ξ)
    have hnorm : 1 + ‖s • ξ‖ ≤ B * (1 + ‖ξ‖) := by
      calc
        1 + ‖s • ξ‖ ≤ (1 + |s|) * (1 + ‖ξ‖) := by
          simpa using concentration_norm_add_smul_le (0 : Fin n → ℝ) ξ s
        _ ≤ B * (1 + ‖ξ‖) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [B]
          linarith [hsabs]
    have hcoord' : ∀ i, |coordinateDerivative F i (s • ξ)| ≤
        C * B ^ d * (1 + ‖ξ‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (s • ξ)| ≤ C * (1 + ‖s • ξ‖) ^ d := hcoord i
        _ ≤ C * (B * (1 + ‖ξ‖)) ^ d := by gcongr
        _ = C * B ^ d * (1 + ‖ξ‖) ^ d := by rw [mul_pow]; ring
    have hfd := concentration_abs_fderiv_apply_le (s • ξ) ξ
      (by positivity : 0 ≤ C * B ^ d * (1 + ‖ξ‖) ^ d) hcoord'
    have hξnorm : ‖ξ‖ ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
    calc
      ‖Φ' s ξ‖ = |fderiv ℝ F (s • ξ) ξ| := Real.norm_eq_abs _
      _ ≤ (Fintype.card (Fin n) : ℝ) * ‖ξ‖ *
          (C * B ^ d * (1 + ‖ξ‖) ^ d) := hfd
      _ ≤ K * (1 + ‖ξ‖) ^ (d + 1) := by
        dsimp [K]
        have hfactor : 0 ≤ (Fintype.card (Fin n) : ℝ) * C * B ^ d := by positivity
        have hpow : 0 ≤ (1 + ‖ξ‖) ^ d := by positivity
        rw [pow_succ]
        calc
          (Fintype.card (Fin n) : ℝ) * ‖ξ‖ * (C * B ^ d * (1 + ‖ξ‖) ^ d) ≤
              (Fintype.card (Fin n) : ℝ) * (1 + ‖ξ‖) *
                (C * B ^ d * (1 + ‖ξ‖) ^ d) := by
                  gcongr
          _ ≤ (Fintype.card (Fin n) : ℝ) * (|u| + 1) *
                (1 + ‖ξ‖) * (C * B ^ d * (1 + ‖ξ‖) ^ d) := by
                  have hscale : 1 + ‖ξ‖ ≤ (|u| + 1) * (1 + ‖ξ‖) := by
                    have hnonneg : 0 ≤ |u| * (1 + ‖ξ‖) := by positivity
                    nlinarith
                  have hfactorGrow :
                      (Fintype.card (Fin n) : ℝ) * (1 + ‖ξ‖) ≤
                        (Fintype.card (Fin n) : ℝ) * (|u| + 1) * (1 + ‖ξ‖) := by
                    calc
                      (Fintype.card (Fin n) : ℝ) * (1 + ‖ξ‖) ≤
                          (Fintype.card (Fin n) : ℝ) * ((|u| + 1) * (1 + ‖ξ‖)) :=
                        mul_le_mul_of_nonneg_left hscale (by positivity)
                      _ = (Fintype.card (Fin n) : ℝ) * (|u| + 1) *
                          (1 + ‖ξ‖) := by ring
                  exact mul_le_mul_of_nonneg_right hfactorGrow (by positivity)
          _ = (Fintype.card (Fin n) : ℝ) * (|u| + 1) * C * B ^ d *
                ((1 + ‖ξ‖) ^ d * (1 + ‖ξ‖)) := by ring
  have hdiff : ∀ᵐ ξ ∂(standardGaussianPi n), ∀ s ∈ Metric.ball u 1,
      HasDerivAt (Φ · ξ) (Φ' s ξ) s := by
    apply ae_of_all
    intro ξ s hs
    have harg : HasDerivAt (fun r : ℝ => r • ξ) ξ s := by
      simpa using (hasDerivAt_id s).smul_const ξ
    have houter := (hF.1.differentiable_one (s • ξ)).hasFDerivAt
    have hcomp := houter.comp_hasDerivAt s harg
    simpa [Φ, Φ', Function.comp_def] using hcomp
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := Φ) (x₀ := u) (s := Metric.ball u 1) (F' := Φ')
    (bound := fun ξ => K * (1 + ‖ξ‖) ^ (d + 1))
    (Metric.ball_mem_nhds _ zero_lt_one) hFmeas hFint hF'meas hbound hboundInt hdiff
  change HasDerivAt (fun s => ∫ ξ, F (0 + s • ξ) ∂(standardGaussianPi n))
    (∫ ξ, fderiv ℝ F (u • ξ) ξ ∂(standardGaussianPi n)) u
  simpa only [zero_add] using hderiv.2

/-- Differentiating a polynomially bounded Gaussian shift in its centre. -/
theorem hasFDerivAt_shiftAverage_center {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F)
    (x : Fin n → ℝ) (c : ℝ) :
    Integrable (fun ξ => fderiv ℝ F (x + c • ξ)) (standardGaussianPi n) ∧
    HasFDerivAt (fun y => shiftAverage F y c)
      (∫ ξ, fderiv ℝ F (x + c • ξ) ∂(standardGaussianPi n)) x ∧
    ContinuousAt (fun y => ∫ ξ, fderiv ℝ F (y + c • ξ)
      ∂(standardGaussianPi n)) x := by
  rcases hF.2 with ⟨C, hC, d, hfunctionBound, hcoordinateBound⟩
  let Ψ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun y ξ => F (y + c • ξ)
  let Ψ' : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ :=
    fun y ξ => fderiv ℝ F (y + c • ξ)
  let B : ℝ := (2 + ‖x‖) * (1 + |c|)
  let K : ℝ := (Fintype.card (Fin n) : ℝ) * C * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcontArg (y : Fin n → ℝ) : Continuous (fun ξ : Fin n → ℝ => y + c • ξ) := by
    exact continuous_const.add (continuous_id.const_smul c)
  have hFmeas : ∀ᶠ y in nhds x, AEStronglyMeasurable (Ψ y) (standardGaussianPi n) := by
    filter_upwards with y
    exact ((hF.1.continuous.comp (hcontArg y)).measurable).aestronglyMeasurable
  have hFint : Integrable (Ψ x) (standardGaussianPi n) := by
    let C' : ℝ := C * ((1 + ‖x‖) * (1 + |c|)) ^ d
    have hC' : 0 ≤ C' := by dsimp [C']; positivity
    apply integrable_of_pi_polynomial_bound
      ((hF.1.continuous.comp (hcontArg x)).measurable) hC' (d := d)
    intro ξ
    have hnorm : 1 + ‖x + c • ξ‖ ≤ (1 + ‖x‖) * (1 + |c|) * (1 + ‖ξ‖) :=
      concentration_norm_add_smul_le x ξ c
    calc
      |F (x + c • ξ)| ≤ C * (1 + ‖x + c • ξ‖) ^ d := hfunctionBound _
      _ ≤ C * ((1 + ‖x‖) * (1 + |c|) * (1 + ‖ξ‖)) ^ d := by gcongr
      _ = C' * (1 + ‖ξ‖) ^ d := by dsimp [C']; rw [mul_pow]; ring
  have hF'meas : AEStronglyMeasurable (Ψ' x) (standardGaussianPi n) := by
    have hfd : Continuous (fun z : Fin n → ℝ => fderiv ℝ F z) :=
      hF.1.continuous_fderiv (by norm_num)
    exact ((hfd.comp (hcontArg x)).measurable).aestronglyMeasurable
  have hpoly : Integrable (fun ξ : Fin n → ℝ => (1 + ‖ξ‖) ^ d)
      (standardGaussianPi n) := by
    apply integrable_of_pi_polynomial_bound (by fun_prop) (C := 1) (by norm_num) (d := d)
    intro ξ
    rw [abs_of_nonneg (by positivity : 0 ≤ (1 + ‖ξ‖) ^ d)]
    simp
  have hboundInt : Integrable (fun ξ : Fin n → ℝ => K * (1 + ‖ξ‖) ^ d)
      (standardGaussianPi n) := by simpa using hpoly.const_mul K
  have hbound : ∀ᵐ ξ ∂(standardGaussianPi n), ∀ y ∈ Metric.ball x 1,
      ‖Ψ' y ξ‖ ≤ K * (1 + ‖ξ‖) ^ d := by
    apply ae_of_all
    intro ξ y hy
    have hyx : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hy
    have hyNorm : ‖y‖ ≤ ‖x‖ + 1 := by
      calc
        ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
          calc
            ‖y‖ = ‖x + (y - x)‖ := by congr 1; abel
            _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + 1 := by linarith
    have hargNorm : 1 + ‖y + c • ξ‖ ≤ B * (1 + ‖ξ‖) := by
      calc
        1 + ‖y + c • ξ‖ ≤ (1 + ‖y‖) * (1 + |c|) * (1 + ‖ξ‖) :=
          concentration_norm_add_smul_le y ξ c
        _ ≤ B * (1 + ‖ξ‖) := by
          calc
            (1 + ‖y‖) * (1 + |c|) * (1 + ‖ξ‖) ≤
                (2 + ‖x‖) * (1 + |c|) * (1 + ‖ξ‖) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  linarith [hyNorm]
            _ = B * (1 + ‖ξ‖) := rfl
    have hcoord : ∀ i, |coordinateDerivative F i (y + c • ξ)| ≤
        C * (1 + ‖y + c • ξ‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (y + c • ξ)| ≤
            |F (y + c • ξ)| + |coordinateDerivative F i (y + c • ξ)| :=
              le_add_of_nonneg_left (abs_nonneg _)
        _ ≤ C * (1 + ‖y + c • ξ‖) ^ d := hcoordinateBound i _
    have hcoord' : ∀ i, |coordinateDerivative F i (y + c • ξ)| ≤
        C * B ^ d * (1 + ‖ξ‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (y + c • ξ)| ≤
            C * (1 + ‖y + c • ξ‖) ^ d := hcoord i
        _ ≤ C * (B * (1 + ‖ξ‖)) ^ d := by gcongr
        _ = C * B ^ d * (1 + ‖ξ‖) ^ d := by rw [mul_pow]; ring
    have hop : ‖fderiv ℝ F (y + c • ξ)‖ ≤ K * (1 + ‖ξ‖) ^ d := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      have hv := concentration_abs_fderiv_apply_le (y + c • ξ) v
        (by positivity : 0 ≤ C * B ^ d * (1 + ‖ξ‖) ^ d) hcoord'
      calc
        ‖fderiv ℝ F (y + c • ξ) v‖ = |fderiv ℝ F (y + c • ξ) v| := Real.norm_eq_abs _
        _ ≤ (Fintype.card (Fin n) : ℝ) * ‖v‖ *
            (C * B ^ d * (1 + ‖ξ‖) ^ d) := hv
        _ = (K * (1 + ‖ξ‖) ^ d) * ‖v‖ := by dsimp [K]; ring
    exact hop
  have hdiff : ∀ᵐ ξ ∂(standardGaussianPi n), ∀ y ∈ Metric.ball x 1,
      HasFDerivAt (Ψ · ξ) (Ψ' y ξ) y := by
    apply ae_of_all
    intro ξ y hy
    have harg : HasFDerivAt (fun z : Fin n → ℝ => z + c • ξ)
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) y := by
      have hbase : HasFDerivAt (fun z : Fin n → ℝ => z)
          (ContinuousLinearMap.id ℝ (Fin n → ℝ)) y := hasFDerivAt_id y
      exact (hasFDerivAt_add_const_iff (c := c • ξ)).2 hbase
    exact (hF.1.differentiable_one (y + c • ξ)).hasFDerivAt.comp y harg
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := Ψ) (x₀ := x) (s := Metric.ball x 1) (F' := Ψ')
    (bound := fun ξ => K * (1 + ‖ξ‖) ^ d)
    (Metric.ball_mem_nhds _ zero_lt_one) hFmeas hFint hF'meas hbound hboundInt hdiff
  have hderiv' : HasFDerivAt (fun y => ∫ ξ, F (y + c • ξ) ∂(standardGaussianPi n))
      (∫ ξ, fderiv ℝ F (x + c • ξ) ∂(standardGaussianPi n)) x := by
    simpa [Ψ, Ψ'] using hderiv
  have hF'derivInt : Integrable (Ψ' x) (standardGaussianPi n) := by
    have hboundAt : ∀ᵐ ξ ∂(standardGaussianPi n),
        ‖Ψ' x ξ‖ ≤ K * (1 + ‖ξ‖) ^ d :=
      hbound.mono fun ξ hξ => hξ x (Metric.mem_ball_self zero_lt_one)
    exact Integrable.mono' hboundInt hF'meas hboundAt
  have hF'measNhd : ∀ᶠ y in nhds x,
      AEStronglyMeasurable (Ψ' y) (standardGaussianPi n) := by
    filter_upwards with y
    exact (((hF.1.continuous_fderiv (by norm_num)).comp (hcontArg y)).measurable).aestronglyMeasurable
  have hF'boundNhd : ∀ᶠ y in nhds x, ∀ᵐ ξ ∂(standardGaussianPi n),
      ‖Ψ' y ξ‖ ≤ K * (1 + ‖ξ‖) ^ d := by
    filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
    exact hbound.mono fun ξ hξ => hξ y hy
  have hF'cont : ∀ᵐ ξ ∂(standardGaussianPi n), ContinuousAt (Ψ' · ξ) x := by
    apply ae_of_all
    intro ξ
    have hfd : Continuous (fun z : Fin n → ℝ => fderiv ℝ F z) :=
      hF.1.continuous_fderiv (by norm_num)
    exact (hfd.comp (continuous_id.add
      (continuous_const : Continuous fun _ : Fin n → ℝ => c • ξ))).continuousAt
  have hF'continuousAt := continuousAt_of_dominated (F := Ψ') (x₀ := x)
    (bound := fun ξ => K * (1 + ‖ξ‖) ^ d)
    hF'measNhd hF'boundNhd hboundInt hF'cont
  constructor
  · constructor
    · exact hF'derivInt.aestronglyMeasurable
    · exact hF'derivInt.hasFiniteIntegral
  · constructor
    · simpa only [shiftAverage] using hderiv'
    · simpa [Ψ'] using hF'continuousAt

/-- A `C³` function whose coordinate derivatives through order three have polynomial growth. -/
def HasPolynomiallyBoundedThirdCoordinateDerivatives {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 3 F ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ,
    (∀ x, |F x| ≤ C * (1 + ‖x‖) ^ d) ∧
    (∀ i x, |coordinateDerivative F i x| ≤ C * (1 + ‖x‖) ^ d) ∧
    (∀ i j x, |coordinateDerivative (coordinateDerivative F i) j x| ≤
      C * (1 + ‖x‖) ^ d) ∧
    ∀ i j k x,
      |coordinateDerivative (coordinateDerivative (coordinateDerivative F i) j) k x| ≤
        C * (1 + ‖x‖) ^ d

private theorem hasPolynomiallyBoundedSecond_of_third {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedThirdCoordinateDerivatives F) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives F := by
  rcases hF with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  exact ⟨hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3),
    ⟨C, hC, d, hzero, hone, htwo⟩⟩

private theorem contDiff_coordinateDerivative_of_three {n : ℕ}
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

private theorem contDiff_coordinateDerivative_of_two {n : ℕ}
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

private theorem hasPolynomiallyBoundedCoordinateDerivatives_of_second {n : ℕ}
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

private theorem fderiv_translate {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiff ℝ 1 F) (x z : Fin n → ℝ) :
    fderiv ℝ (fun y => F (x + y)) z = fderiv ℝ F (x + z) := by
  have hinner : HasFDerivAt (fun y : Fin n → ℝ => x + y)
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)) z := by
    exact (hasFDerivAt_const_add_iff x).2 (hasFDerivAt_id z)
  have hcomp := (hF.differentiable_one (x + z)).hasFDerivAt.comp z hinner
  simpa [Function.comp_def] using hcomp.fderiv

private theorem coordinateDerivative_translate {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiff ℝ 1 F) (x z : Fin n → ℝ) (i : Fin n) :
    coordinateDerivative (fun y => F (x + y)) i z =
      coordinateDerivative F i (x + z) := by
  rw [coordinateDerivative, fderiv_translate hF x z, coordinateDerivative]

private theorem hasPolynomiallyBoundedSecond_of_translate {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    (x : Fin n → ℝ) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives (fun z => F (x + z)) := by
  rcases hF.2 with ⟨C, hC, d, hzero, hone, htwo⟩
  let B : ℝ := 1 + ‖x‖
  let C' : ℝ := C * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  have hnorm (z : Fin n → ℝ) : 1 + ‖x + z‖ ≤ B * (1 + ‖z‖) := by
    have htriangle := norm_add_le x z
    have hprod : 1 + ‖x‖ + ‖z‖ ≤ (1 + ‖x‖) * (1 + ‖z‖) := by
      nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg z)]
    dsimp [B]
    linarith
  have hcont : ContDiff ℝ 2 (fun z : Fin n → ℝ => F (x + z)) := by
    exact hF.1.comp (contDiff_const.add contDiff_id)
  have hfirst (i : Fin n) (z : Fin n → ℝ) :
      coordinateDerivative (fun y => F (x + y)) i z =
        coordinateDerivative F i (x + z) :=
    coordinateDerivative_translate (hF.1.of_le (by norm_num)) x z i
  have hsecond (i j : Fin n) (z : Fin n → ℝ) :
      coordinateDerivative (coordinateDerivative (fun y => F (x + y)) i) j z =
        coordinateDerivative (coordinateDerivative F i) j (x + z) := by
    have heq : coordinateDerivative (fun y => F (x + y)) i =
        fun y => coordinateDerivative F i (x + y) := by
      funext y
      exact hfirst i y
    rw [heq]
    exact coordinateDerivative_translate
      (contDiff_coordinateDerivative_of_two hF.1 i) x z j
  refine ⟨hcont, C', hC', d, ?_, ?_, ?_⟩
  · intro z
    calc
      |F (x + z)| ≤ C * (1 + ‖x + z‖) ^ d := hzero _
      _ ≤ C * (B * (1 + ‖z‖)) ^ d := by gcongr; exact hnorm z
      _ = C' * (1 + ‖z‖) ^ d := by dsimp [C']; rw [mul_pow]; ring
  · intro i z
    rw [hfirst]
    calc
      |coordinateDerivative F i (x + z)| ≤ C * (1 + ‖x + z‖) ^ d := hone i _
      _ ≤ C * (B * (1 + ‖z‖)) ^ d := by gcongr; exact hnorm z
      _ = C' * (1 + ‖z‖) ^ d := by dsimp [C']; rw [mul_pow]; ring
  · intro i j z
    rw [hsecond]
    calc
      |coordinateDerivative (coordinateDerivative F i) j (x + z)| ≤
          C * (1 + ‖x + z‖) ^ d := htwo i j _
      _ ≤ C * (B * (1 + ‖z‖)) ^ d := by gcongr; exact hnorm z
      _ = C' * (1 + ‖z‖) ^ d := by dsimp [C']; rw [mul_pow]; ring

theorem continuousAt_shiftAverage_center_of_polynomial_bound {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : 0 ≤ C) {d : ℕ}
    (hg : ∀ z, |f z| ≤ C * (1 + ‖z‖) ^ d)
    (x : Fin n → ℝ) (c : ℝ) :
    ContinuousAt (fun y => shiftAverage f y c) x := by
  let Ψ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun y ξ => f (y + c • ξ)
  let B : ℝ := (2 + ‖x‖) * (1 + |c|)
  let K : ℝ := C * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoly : Integrable (fun ξ : Fin n → ℝ => (1 + ‖ξ‖) ^ d)
      (standardGaussianPi n) := by
    apply integrable_of_pi_polynomial_bound (by fun_prop) (C := 1) (by norm_num) (d := d)
    intro ξ
    rw [abs_of_nonneg (by positivity : 0 ≤ (1 + ‖ξ‖) ^ d)]
    simp
  have hboundInt : Integrable (fun ξ : Fin n → ℝ => K * (1 + ‖ξ‖) ^ d)
      (standardGaussianPi n) := by simpa using hpoly.const_mul K
  have hFmeas : ∀ᶠ y in nhds x, AEStronglyMeasurable (Ψ y) (standardGaussianPi n) := by
    filter_upwards with y
    exact ((hf.comp (continuous_const.add (continuous_id.const_smul c))).measurable).aestronglyMeasurable
  have hbound : ∀ᶠ y in nhds x, ∀ᵐ ξ ∂(standardGaussianPi n),
      ‖Ψ y ξ‖ ≤ K * (1 + ‖ξ‖) ^ d := by
    filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
    have hyx : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hy
    have hyNorm : ‖y‖ ≤ ‖x‖ + 1 := by
      calc
        ‖y‖ = ‖x + (y - x)‖ := by congr 1; abel
        _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + 1 := by linarith
    have hpoint (ξ : Fin n → ℝ) : 1 + ‖y + c • ξ‖ ≤ B * (1 + ‖ξ‖) := by
      calc
        1 + ‖y + c • ξ‖ ≤ (1 + ‖y‖) * (1 + |c|) * (1 + ‖ξ‖) :=
          concentration_norm_add_smul_le y ξ c
        _ ≤ B * (1 + ‖ξ‖) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [hyNorm]
    apply ae_of_all
    intro ξ
    have hpolyBound : C * (1 + ‖y + c • ξ‖) ^ d ≤ K * (1 + ‖ξ‖) ^ d := by
      calc
        C * (1 + ‖y + c • ξ‖) ^ d ≤ C * (B * (1 + ‖ξ‖)) ^ d := by
          gcongr
          exact hpoint ξ
        _ = K * (1 + ‖ξ‖) ^ d := by dsimp [K]; rw [mul_pow]; ring
    calc
      ‖Ψ y ξ‖ = |f (y + c • ξ)| := Real.norm_eq_abs _
      _ ≤ C * (1 + ‖y + c • ξ‖) ^ d := hg _
      _ ≤ K * (1 + ‖ξ‖) ^ d := hpolyBound
  have hcont : ∀ᵐ ξ ∂(standardGaussianPi n), ContinuousAt (Ψ · ξ) x := by
    apply ae_of_all
    intro ξ
    exact (hf.comp (continuous_id.add
      (continuous_const : Continuous fun _ : Fin n → ℝ => c • ξ))).continuousAt
  have hresult := continuousAt_of_dominated (F := Ψ) (x₀ := x)
    (bound := fun ξ => K * (1 + ‖ξ‖) ^ d) hFmeas hbound hboundInt hcont
  simpa only [shiftAverage] using hresult

private theorem contDiff_one_heatAverage_of_second {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives F) (t : ℝ) :
    ContDiff ℝ 1 (fun x : Fin n → ℝ => heatAverage F x t) := by
  let c : ℝ := Real.sqrt t
  let U : (Fin n → ℝ) → ℝ := fun x => heatAverage F x t
  let D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ := fun x =>
    ∫ ξ, fderiv ℝ F (x + c • ξ) ∂(standardGaussianPi n)
  have hF₁ : HasPolynomiallyBoundedCoordinateDerivatives F :=
    hasPolynomiallyBoundedCoordinateDerivatives_of_second hF₂
  have hcenter (x : Fin n → ℝ) := hasFDerivAt_shiftAverage_center hF₁ x c
  have hDderiv (x : Fin n → ℝ) : HasFDerivAt U (D x) x := by
    have h := hcenter x
    simpa [U, D, heatAverage, c] using h.2.1
  have hDcont : Continuous D :=
    continuous_iff_continuousAt.mpr fun x => (hcenter x).2.2
  rw [contDiff_one_iff_hasFDerivAt]
  exact ⟨D, hDcont, hDderiv⟩

theorem hasPolynomiallyBoundedSecond_of_directionalDerivative {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    (v : Fin n → ℝ) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives (fun x => fderiv ℝ F x v) := by
  rcases hF with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  let D : (Fin n → ℝ) → ℝ := fun x => fderiv ℝ F x v
  let C' : ℝ := (Fintype.card (Fin n) : ℝ) * ‖v‖ * C
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  have hDcont : ContDiff ℝ 2 D := by
    have h := hcont.contDiff_fderiv_apply (m := 2)
      (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
    have hpair : ContDiff ℝ 2 (fun x : Fin n → ℝ => (x, v)) :=
      contDiff_id.prodMk contDiff_const
    convert h.comp hpair using 1
    · ext x
      rfl
  have hDrepr : D = fun x => ∑ i, v i * coordinateDerivative F i x := by
    funext x
    exact concentration_fderiv_apply_eq_sum x v
  have hfirst (j : Fin n) (x : Fin n → ℝ) :
      coordinateDerivative D j x =
        ∑ i, v i * coordinateDerivative (coordinateDerivative F i) j x := by
    rw [coordinateDerivative, hDrepr]
    rw [fderiv_fun_sum]
    · simp only [sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      have hdiffi : DifferentiableAt ℝ (coordinateDerivative F i) x :=
        (contDiff_coordinateDerivative_of_two
          (hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) i).differentiable_one x
      have h := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j (1 : ℝ)))
        (fderiv_const_mul hdiffi (v i))
      simpa [coordinateDerivative, smul_eq_mul] using h
    · intro i hi
      exact ((contDiff_coordinateDerivative_of_three hcont i).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one x |>.const_mul (v i)
  have hsecond (j k : Fin n) (x : Fin n → ℝ) :
      coordinateDerivative (coordinateDerivative D j) k x =
        ∑ i, v i *
          coordinateDerivative (coordinateDerivative (coordinateDerivative F i) j) k x := by
    have hfun : coordinateDerivative D j = fun y =>
        ∑ i, v i * coordinateDerivative (coordinateDerivative F i) j y := by
      funext y
      exact hfirst j y
    rw [hfun, coordinateDerivative, fderiv_fun_sum]
    · simp only [sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      have hdiffi : DifferentiableAt ℝ
          (coordinateDerivative (coordinateDerivative F i) j) x :=
        (contDiff_coordinateDerivative_of_two
          (contDiff_coordinateDerivative_of_three hcont i) j).differentiable_one x
      have h := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single k (1 : ℝ)))
        (fderiv_const_mul hdiffi (v i))
      simpa [coordinateDerivative, smul_eq_mul] using h
    · intro i hi
      exact ((contDiff_coordinateDerivative_of_two
        (contDiff_coordinateDerivative_of_three hcont i) j).differentiable_one x).const_mul
          (v i)
  have habsSum (x : Fin n → ℝ) {A : Fin n → ℝ}
      (hA : ∀ i, |A i| ≤ C * (1 + ‖x‖) ^ d) :
      |∑ i, v i * A i| ≤ C' * (1 + ‖x‖) ^ d := by
    calc
      |∑ i, v i * A i| ≤ ∑ i, |v i * A i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ‖v‖ * (C * (1 + ‖x‖) ^ d) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        have hvi : |v i| ≤ ‖v‖ := by
          simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
        calc
          |v i| * |A i| ≤ |v i| * (C * (1 + ‖x‖) ^ d) :=
            mul_le_mul_of_nonneg_left (hA i) (abs_nonneg _)
          _ ≤ ‖v‖ * (C * (1 + ‖x‖) ^ d) := by gcongr
      _ = C' * (1 + ‖x‖) ^ d := by
        simp [C', Finset.sum_const, mul_assoc]
  refine ⟨hDcont, ?_⟩
  refine ⟨C', hC', d, ?_, ?_, ?_⟩
  · intro x
    change |D x| ≤ C' * (1 + ‖x‖) ^ d
    rw [hDrepr]
    apply habsSum x
    intro i
    exact hone i x
  · intro i x
    rw [hfirst]
    apply habsSum x
    intro j
    exact htwo j i x
  · intro i j x
    rw [hsecond]
    apply habsSum x
    intro k
    exact hthree k i j x

theorem contDiff_two_heatAverage_of_third {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F) (t : ℝ) :
    ContDiff ℝ 2 (fun x : Fin n → ℝ => heatAverage F x t) := by
  have hF₂ := hasPolynomiallyBoundedSecond_of_third hF₃
  have hF₁ := hasPolynomiallyBoundedCoordinateDerivatives_of_second hF₂
  let c : ℝ := Real.sqrt t
  let U : (Fin n → ℝ) → ℝ := fun x => heatAverage F x t
  have hcenter (x : Fin n → ℝ) := hasFDerivAt_shiftAverage_center hF₁ x c
  have hUderiv (x : Fin n → ℝ) :
      HasFDerivAt U (∫ ξ, fderiv ℝ F (x + c • ξ) ∂(standardGaussianPi n)) x := by
    simpa [U, heatAverage, c] using (hcenter x).2.1
  have hUdifferentiable : Differentiable ℝ U := fun x => (hUderiv x).differentiableAt
  have hEval (x v : Fin n → ℝ) :
      fderiv ℝ U x v = shiftAverage (fun z => fderiv ℝ F z v) x c := by
    calc
      fderiv ℝ U x v = (∫ ξ, fderiv ℝ F (x + c • ξ)
          ∂(standardGaussianPi n)) v := by rw [(hUderiv x).fderiv]
      _ = ∫ ξ, fderiv ℝ F (x + c • ξ) v ∂(standardGaussianPi n) :=
        ContinuousLinearMap.integral_apply (hcenter x).1 v
      _ = shiftAverage (fun z => fderiv ℝ F z v) x c := by rfl
  rw [show (2 : WithTop ℕ∞) = (1 : WithTop ℕ∞) + 1 by norm_num,
    contDiff_succ_iff_fderiv_apply]
  refine ⟨hUdifferentiable, ?_, ?_⟩
  · intro hn
    norm_num at hn
  · intro v
    let G : (Fin n → ℝ) → ℝ := fun z => fderiv ℝ F z v
    have hG₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives G :=
      hasPolynomiallyBoundedSecond_of_directionalDerivative hF₃ v
    have hGcont : ContDiff ℝ 1 (fun x : Fin n → ℝ => heatAverage G x t) :=
      contDiff_one_heatAverage_of_second hG₂ t
    have hEq : (fun x => fderiv ℝ U x v) = fun x => heatAverage G x t := by
      funext x
      calc
        fderiv ℝ U x v = shiftAverage G x c := hEval x v
        _ = heatAverage G x t := by rfl
    rw [hEq]
    exact hGcont

private theorem hasDerivAt_gaussian_bridge_argument {n : ℕ}
    (ξ η : Fin n → ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun r : ℝ => Real.sqrt r • ξ + Real.sqrt (1 - r) • η)
      ((1 / (2 * Real.sqrt t)) • ξ - (1 / (2 * Real.sqrt (1 - t))) • η) t := by
  have hleft : HasDerivAt (fun r : ℝ => Real.sqrt r • ξ)
      ((1 / (2 * Real.sqrt t)) • ξ) t := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt ht)).smul_const ξ using 1
  have hsub : HasDerivAt (fun r : ℝ => 1 - r) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have hroot : HasDerivAt (fun r : ℝ => Real.sqrt (1 - r))
      (-(1 / (2 * Real.sqrt (1 - t)))) t := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt (by linarith : 0 < 1 - t))).comp t hsub using 1
    · ext r
      rfl
    · ring_nf
  have hright := hroot.smul_const η
  convert hleft.add hright using 1
  · rw [sub_eq_add_neg, ← neg_smul]

theorem hasDerivAt_gaussian_bridge_integral {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F)
    (ξ : Fin n → ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Integrable (fun η => fderiv ℝ F (Real.sqrt t • ξ + Real.sqrt (1 - t) • η)
        ((1 / (2 * Real.sqrt t)) • ξ - (1 / (2 * Real.sqrt (1 - t))) • η))
        (standardGaussianPi n) ∧
    HasDerivAt
      (fun r => ∫ η, F (Real.sqrt r • ξ + Real.sqrt (1 - r) • η)
        ∂(standardGaussianPi n))
      (∫ η, fderiv ℝ F (Real.sqrt t • ξ + Real.sqrt (1 - t) • η)
        ((1 / (2 * Real.sqrt t)) • ξ - (1 / (2 * Real.sqrt (1 - t))) • η)
        ∂(standardGaussianPi n)) t := by
  rcases hF.2 with ⟨C, hC, d, hvalue, hcoordinate⟩
  let A : ℝ → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun r η => Real.sqrt r • ξ + Real.sqrt (1 - r) • η
  let A' : ℝ → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun r η => (1 / (2 * Real.sqrt r)) • ξ - (1 / (2 * Real.sqrt (1 - r))) • η
  let Bξ : ℝ := 1 + ‖ξ‖
  let Vξ : ℝ := ‖ξ‖ / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2))
  let K : ℝ := (Fintype.card (Fin n) : ℝ) * C * Bξ ^ d * Vξ
  let δ : ℝ := min (t / 2) ((1 - t) / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hBξ : 0 ≤ Bξ := by dsimp [Bξ]; positivity
  have hVξ : 0 ≤ Vξ := by dsimp [Vξ]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hAcont (r : ℝ) : Continuous (A r) := by
    dsimp [A]
    fun_prop
  have hFmeas : ∀ᶠ r in nhds t,
      AEStronglyMeasurable (fun η => F (A r η)) (standardGaussianPi n) := by
    filter_upwards with r
    exact ((hF.1.continuous.comp (hAcont r)).measurable).aestronglyMeasurable
  have hFint : Integrable (fun η => F (A t η)) (standardGaussianPi n) := by
    have hpoint (η : Fin n → ℝ) :
        1 + ‖A t η‖ ≤ Bξ * (1 + ‖η‖) := by
      have hsqt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
      have hsqt1 : Real.sqrt t ≤ 1 := by
        rw [Real.sqrt_le_one]
        linarith
      have hsq1t : 0 ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
      have hsq1t1 : Real.sqrt (1 - t) ≤ 1 := by
        rw [Real.sqrt_le_one]
        linarith
      have hsum : ‖A t η‖ ≤ ‖ξ‖ + ‖η‖ := by
        dsimp [A]
        calc
          ‖Real.sqrt t • ξ + Real.sqrt (1 - t) • η‖ ≤
              ‖Real.sqrt t • ξ‖ + ‖Real.sqrt (1 - t) • η‖ := norm_add_le _ _
          _ = Real.sqrt t * ‖ξ‖ + Real.sqrt (1 - t) * ‖η‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqt,
              norm_smul, Real.norm_eq_abs, abs_of_nonneg hsq1t]
          _ ≤ ‖ξ‖ + ‖η‖ := by
            simpa only [one_mul] using add_le_add
              (mul_le_mul_of_nonneg_right hsqt1 (norm_nonneg ξ))
              (mul_le_mul_of_nonneg_right hsq1t1 (norm_nonneg η))
      dsimp [Bξ]
      nlinarith [norm_nonneg η, norm_nonneg ξ]
    have hmeas := (hF.1.continuous.comp (hAcont t)).measurable
    apply integrable_of_pi_polynomial_bound hmeas (C := C * Bξ ^ d)
      (by positivity) (d := d)
    intro η
    calc
      |F (A t η)| ≤ C * (1 + ‖A t η‖) ^ d := hvalue _
      _ ≤ C * (Bξ * (1 + ‖η‖)) ^ d := by gcongr; exact hpoint η
      _ = C * Bξ ^ d * (1 + ‖η‖) ^ d := by rw [mul_pow]; ring
  have hderivCont : Continuous (fun η =>
      fderiv ℝ F (A t η) (A' t η)) := by
    have hfd : Continuous (fun z : Fin n → ℝ => fderiv ℝ F z) :=
      hF.1.continuous_fderiv (by norm_num)
    exact (hfd.comp (hAcont t)).clm_apply (by fun_prop)
  have hF'meas : AEStronglyMeasurable (fun η =>
      fderiv ℝ F (A t η) (A' t η)) (standardGaussianPi n) :=
    hderivCont.measurable.aestronglyMeasurable
  have hpoly : Integrable (fun η : Fin n → ℝ => (1 + ‖η‖) ^ (d + 1))
      (standardGaussianPi n) := by
    apply integrable_of_pi_polynomial_bound (by fun_prop) (C := 1) (by norm_num)
      (d := d + 1)
    intro η
    rw [abs_of_nonneg (by positivity : 0 ≤ (1 + ‖η‖) ^ (d + 1))]
    simp
  have hboundInt : Integrable (fun η : Fin n → ℝ => K * (1 + ‖η‖) ^ (d + 1))
      (standardGaussianPi n) := by simpa using hpoly.const_mul K
  have hbound : ∀ᵐ η ∂(standardGaussianPi n), ∀ r ∈ Metric.ball t δ,
      ‖fderiv ℝ F (A r η) (A' r η)‖ ≤ K * (1 + ‖η‖) ^ (d + 1) := by
    apply ae_of_all
    intro η r hr
    have hdist : |r - t| < δ := by simpa [Real.dist_eq] using Metric.mem_ball.mp hr
    have hlow : t / 2 < r := by
      dsimp [δ] at hdist
      rw [abs_lt] at hdist
      have hsmall : δ ≤ t / 2 := min_le_left _ _
      linarith
    have hupp : r < (1 + t) / 2 := by
      dsimp [δ] at hdist
      rw [abs_lt] at hdist
      have hsmall : δ ≤ (1 - t) / 2 := min_le_right _ _
      linarith
    have hlow1 : (1 - t) / 2 < 1 - r := by linarith
    have hrootr : Real.sqrt (t / 2) ≤ Real.sqrt r := Real.sqrt_le_sqrt hlow.le
    have hroot1r : Real.sqrt ((1 - t) / 2) ≤ Real.sqrt (1 - r) :=
      Real.sqrt_le_sqrt hlow1.le
    have hroot0 : 0 < Real.sqrt (t / 2) := Real.sqrt_pos.2 (by linarith)
    have hroot10 : 0 < Real.sqrt ((1 - t) / 2) := Real.sqrt_pos.2 (by linarith)
    have hcoeff : ‖A' r η‖ ≤ Vξ * (1 + ‖η‖) := by
      have hnorm : ‖A' r η‖ ≤ ‖ξ‖ / (2 * Real.sqrt r) +
          ‖η‖ / (2 * Real.sqrt (1 - r)) := by
        dsimp [A']
        calc
          ‖(1 / (2 * Real.sqrt r)) • ξ -
              (1 / (2 * Real.sqrt (1 - r))) • η‖ ≤
              ‖(1 / (2 * Real.sqrt r)) • ξ‖ +
                ‖(1 / (2 * Real.sqrt (1 - r))) • η‖ := norm_sub_le _ _
          _ = ‖ξ‖ / (2 * Real.sqrt r) + ‖η‖ / (2 * Real.sqrt (1 - r)) := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
              Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            ring
      have hfirst : ‖ξ‖ / (2 * Real.sqrt r) ≤ ‖ξ‖ / (2 * Real.sqrt (t / 2)) := by
        have hden : 2 * Real.sqrt (t / 2) ≤ 2 * Real.sqrt r := by nlinarith
        have hrecip : 1 / (2 * Real.sqrt r) ≤ 1 / (2 * Real.sqrt (t / 2)) :=
          one_div_le_one_div_of_le (by positivity) hden
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hrecip)
          (norm_nonneg _)
      have hsecond : ‖η‖ / (2 * Real.sqrt (1 - r)) ≤
          ‖η‖ / (2 * Real.sqrt ((1 - t) / 2)) := by
        have hden : 2 * Real.sqrt ((1 - t) / 2) ≤ 2 * Real.sqrt (1 - r) := by nlinarith
        have hrecip : 1 / (2 * Real.sqrt (1 - r)) ≤
            1 / (2 * Real.sqrt ((1 - t) / 2)) :=
          one_div_le_one_div_of_le (by positivity) hden
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hrecip)
          (norm_nonneg _)
      dsimp [Vξ]
      calc
        ‖A' r η‖ ≤ ‖ξ‖ / (2 * Real.sqrt r) +
            ‖η‖ / (2 * Real.sqrt (1 - r)) := hnorm
        _ ≤ ‖ξ‖ / (2 * Real.sqrt (t / 2)) +
            ‖η‖ / (2 * Real.sqrt ((1 - t) / 2)) := add_le_add hfirst hsecond
        _ ≤ ‖ξ‖ / (2 * Real.sqrt (t / 2)) * (1 + ‖η‖) +
            1 / (2 * Real.sqrt ((1 - t) / 2)) * (1 + ‖η‖) := by
          have hnonneg₁ : 0 ≤ ‖ξ‖ / (2 * Real.sqrt (t / 2)) := by positivity
          have hnonneg₂ : 0 ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by positivity
          have hη : 0 ≤ ‖η‖ := norm_nonneg _
          have h₁ : ‖ξ‖ / (2 * Real.sqrt (t / 2)) ≤
              ‖ξ‖ / (2 * Real.sqrt (t / 2)) * (1 + ‖η‖) := by
            calc
              _ = (‖ξ‖ / (2 * Real.sqrt (t / 2))) * 1 := by ring
              _ ≤ (‖ξ‖ / (2 * Real.sqrt (t / 2))) * (1 + ‖η‖) :=
                mul_le_mul_of_nonneg_left (by linarith) hnonneg₁
          have h₂ : ‖η‖ / (2 * Real.sqrt ((1 - t) / 2)) ≤
              1 / (2 * Real.sqrt ((1 - t) / 2)) * (1 + ‖η‖) := by
            calc
              _ = (1 / (2 * Real.sqrt ((1 - t) / 2))) * ‖η‖ := by ring
              _ ≤ (1 / (2 * Real.sqrt ((1 - t) / 2))) * (1 + ‖η‖) :=
                mul_le_mul_of_nonneg_left (by linarith) hnonneg₂
          exact add_le_add h₁ h₂
        _ = Vξ * (1 + ‖η‖) := by dsimp [Vξ]; ring
    have hpoint : 1 + ‖A r η‖ ≤ Bξ * (1 + ‖η‖) := by
      have hsqr : 0 ≤ r := by linarith
      have hsq1 : 0 ≤ 1 - r := by linarith
      have hsqr1 : Real.sqrt r ≤ 1 := by rw [Real.sqrt_le_one]; linarith
      have hsq11 : Real.sqrt (1 - r) ≤ 1 := by rw [Real.sqrt_le_one]; linarith
      have hsum : ‖A r η‖ ≤ ‖ξ‖ + ‖η‖ := by
        dsimp [A]
        calc
          ‖Real.sqrt r • ξ + Real.sqrt (1 - r) • η‖ ≤
              ‖Real.sqrt r • ξ‖ + ‖Real.sqrt (1 - r) • η‖ := norm_add_le _ _
          _ = Real.sqrt r * ‖ξ‖ + Real.sqrt (1 - r) * ‖η‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
              norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          _ ≤ ‖ξ‖ + ‖η‖ := by
            simpa only [one_mul] using add_le_add
              (mul_le_mul_of_nonneg_right hsqr1 (norm_nonneg ξ))
              (mul_le_mul_of_nonneg_right hsq11 (norm_nonneg η))
      dsimp [Bξ]
      nlinarith [norm_nonneg η, norm_nonneg ξ]
    have hcoord : ∀ i, |coordinateDerivative F i (A r η)| ≤
        C * (1 + ‖A r η‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (A r η)| ≤
            |F (A r η)| + |coordinateDerivative F i (A r η)| :=
              le_add_of_nonneg_left (abs_nonneg _)
        _ ≤ C * (1 + ‖A r η‖) ^ d := hcoordinate i _
    have hcoord' : ∀ i, |coordinateDerivative F i (A r η)| ≤
        C * Bξ ^ d * (1 + ‖η‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (A r η)| ≤ C * (1 + ‖A r η‖) ^ d := hcoord i
        _ ≤ C * (Bξ * (1 + ‖η‖)) ^ d := by gcongr
        _ = C * Bξ ^ d * (1 + ‖η‖) ^ d := by rw [mul_pow]; ring
    have hfd := concentration_abs_fderiv_apply_le (A r η) (A' r η)
      (by positivity : 0 ≤ C * Bξ ^ d * (1 + ‖η‖) ^ d) hcoord'
    have hη : ‖η‖ ≤ 1 + ‖η‖ := by linarith [norm_nonneg η]
    calc
      ‖fderiv ℝ F (A r η) (A' r η)‖ ≤
          (Fintype.card (Fin n) : ℝ) * ‖A' r η‖ *
            (C * Bξ ^ d * (1 + ‖η‖) ^ d) := hfd
      _ ≤ (Fintype.card (Fin n) : ℝ) * (Vξ * (1 + ‖η‖)) *
            (C * Bξ ^ d * (1 + ‖η‖) ^ d) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcoeff (by positivity)) (by positivity)
      _ = K * (1 + ‖η‖) ^ (d + 1) := by
        dsimp [K]
        rw [pow_succ]
        ring
  have hdiff : ∀ᵐ η ∂(standardGaussianPi n), ∀ r ∈ Metric.ball t δ,
      HasDerivAt (fun q => F (A q η)) (fderiv ℝ F (A r η) (A' r η)) r := by
    apply ae_of_all
    intro η r hr
    have hdist : |r - t| < δ := by simpa [Real.dist_eq] using Metric.mem_ball.mp hr
    have hlt : 0 < r := by
      dsimp [δ] at hdist
      rw [abs_lt] at hdist
      have hh := min_le_left (t / 2) ((1 - t) / 2)
      linarith
    have hlt1 : r < 1 := by
      dsimp [δ] at hdist
      rw [abs_lt] at hdist
      have hh := min_le_right (t / 2) ((1 - t) / 2)
      linarith
    have hA := hasDerivAt_gaussian_bridge_argument ξ η hlt hlt1
    have houter := (hF.1.differentiable_one (A r η)).hasFDerivAt
    have hcomp := houter.comp_hasDerivAt r hA
    simpa [A, A', Function.comp_def] using hcomp
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r η => F (A r η)) (x₀ := t) (s := Metric.ball t δ)
    (F' := fun r η => fderiv ℝ F (A r η) (A' r η))
    (bound := fun η => K * (1 + ‖η‖) ^ (d + 1))
    (Metric.ball_mem_nhds _ hδ) hFmeas hFint hF'meas hbound hboundInt hdiff
  simpa only [A, A'] using hderiv

/-- The heat identity gives the scaled Gaussian integration-by-parts identity. -/
theorem integral_fderiv_scaled_eq_sqrt_mul_laplacian {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₁ : HasPolynomiallyBoundedCoordinateDerivatives F)
    (hF₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    {t : ℝ} (ht : 0 < t) :
    ∫ ξ, fderiv ℝ F (Real.sqrt t • ξ) ξ ∂(standardGaussianPi n) =
      Real.sqrt t * ∫ ξ, ∑ i, coordinateDerivative (coordinateDerivative F i) i
        (Real.sqrt t • ξ) ∂(standardGaussianPi n) := by
  let s : ℝ := Real.sqrt t
  have hs : 0 < s := Real.sqrt_pos.2 ht
  have hsderiv : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t :=
    Real.hasDerivAt_sqrt (ne_of_gt ht)
  have hscale := hasDerivAt_shiftAverage_zero hF₁ s
  have hpath := hscale.comp t hsderiv
  have hheat := hasDerivAt_heatAverage hF₂ (0 : Fin n → ℝ) ht
  have hpath' : HasDerivAt (heatAverage F 0)
      ((1 / (2 * s)) * ∫ ξ, fderiv ℝ F (s • ξ) ξ ∂(standardGaussianPi n)) t := by
    convert hpath using 1
    · rfl
    · dsimp [s]
      rw [mul_comm]
  have hheat' : HasDerivAt (heatAverage F 0)
      ((1 / 2 : ℝ) * ∫ ξ, ∑ i,
        coordinateDerivative (coordinateDerivative F i) i (s • ξ)
        ∂(standardGaussianPi n)) t := by
    simpa [heatLaplacianAverage, s] using hheat
  have hEq := hpath'.unique hheat'
  have htwo : (1 / (2 * s)) *
      ∫ ξ, fderiv ℝ F (s • ξ) ξ ∂(standardGaussianPi n) =
      (1 / 2 : ℝ) * ∫ ξ, ∑ i,
        coordinateDerivative (coordinateDerivative F i) i (s • ξ)
        ∂(standardGaussianPi n) := hEq
  have hsne : s ≠ 0 := ne_of_gt hs
  calc
    ∫ ξ, fderiv ℝ F (s • ξ) ξ ∂(standardGaussianPi n) =
        (2 * s) * ((1 / (2 * s)) *
          ∫ ξ, fderiv ℝ F (s • ξ) ξ ∂(standardGaussianPi n)) := by
            field_simp [hsne]
    _ = (2 * s) * ((1 / 2 : ℝ) *
          ∫ ξ, ∑ i, coordinateDerivative (coordinateDerivative F i) i
            (s • ξ) ∂(standardGaussianPi n)) := congrArg (fun z : ℝ => (2 * s) * z) htwo
    _ = s * ∫ ξ, ∑ i, coordinateDerivative (coordinateDerivative F i) i
          (s • ξ) ∂(standardGaussianPi n) := by ring

/-- The scaled Gaussian derivative/Laplacian identity also holds for a Gaussian shift centered
at an arbitrary point. -/
theorem integral_fderiv_shift_scaled_eq_sqrt_mul_laplacian {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₁ : HasPolynomiallyBoundedCoordinateDerivatives F)
    (hF₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    (x : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ ξ, fderiv ℝ F (x + Real.sqrt t • ξ) ξ ∂(standardGaussianPi n) =
      Real.sqrt t * ∫ ξ, ∑ i,
        coordinateDerivative (coordinateDerivative F i) i (x + Real.sqrt t • ξ)
        ∂(standardGaussianPi n) := by
  let T : (Fin n → ℝ) → ℝ := fun z => F (x + z)
  have hT₂ := hasPolynomiallyBoundedSecond_of_translate hF₂ x
  have hT₁ : HasPolynomiallyBoundedCoordinateDerivatives T :=
    hasPolynomiallyBoundedCoordinateDerivatives_of_second hT₂
  have hzero := integral_fderiv_scaled_eq_sqrt_mul_laplacian hT₁ hT₂ ht
  have hFderiv (z : Fin n → ℝ) : fderiv ℝ T z = fderiv ℝ F (x + z) :=
    fderiv_translate hF₁.1 x z
  have hcoord (i j : Fin n) (z : Fin n → ℝ) :
      coordinateDerivative (coordinateDerivative T i) j z =
        coordinateDerivative (coordinateDerivative F i) j (x + z) := by
    have heq : coordinateDerivative T i = fun y => coordinateDerivative F i (x + y) := by
      funext y
      exact coordinateDerivative_translate hF₁.1 x y i
    rw [heq]
    exact coordinateDerivative_translate
      (contDiff_coordinateDerivative_of_two hF₂.1 i) x z j
  calc
    ∫ ξ, fderiv ℝ F (x + Real.sqrt t • ξ) ξ ∂(standardGaussianPi n) =
        ∫ ξ, fderiv ℝ T (Real.sqrt t • ξ) ξ ∂(standardGaussianPi n) := by
          apply integral_congr_ae
          exact ae_of_all _ fun ξ =>
            congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L ξ)
              (hFderiv (Real.sqrt t • ξ)).symm
    _ = Real.sqrt t * ∫ ξ, ∑ i,
          coordinateDerivative (coordinateDerivative T i) i (Real.sqrt t • ξ)
          ∂(standardGaussianPi n) := hzero
    _ = Real.sqrt t * ∫ ξ, ∑ i,
          coordinateDerivative (coordinateDerivative F i) i (x + Real.sqrt t • ξ)
          ∂(standardGaussianPi n) := by
            congr 1
            apply integral_congr_ae
            apply ae_of_all
            intro ξ
            apply Finset.sum_congr rfl
            intro i hi
            exact hcoord i i (Real.sqrt t • ξ)

end ASDExplicitGamma.Gaussian

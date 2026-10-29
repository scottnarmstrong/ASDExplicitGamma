/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.ConcentrationTruncation
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Moments.SubGaussian

/-!
# Gaussian concentration for polynomial-growth inputs

The bounded-input semigroup estimate extends to polynomial-growth functions by smooth bounded
truncation and Fatou's lemma.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open Filter
open scoped Topology

namespace ASDExplicitGamma.Gaussian

private theorem tendsto_gaussianConcentrationTruncation_nat (s : ℝ) :
    Tendsto (fun N : ℕ => gaussianConcentrationTruncation ((N : ℝ) + 1) s)
      atTop (𝓝 s) := by
  let R : ℕ → ℝ := fun N => (N : ℝ) + 1
  have hR : Tendsto R atTop atTop := by
    apply tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ)) (g := R)
    · intro N
      exact le_add_of_nonneg_right (by norm_num)
    · exact tendsto_natCast_atTop_atTop
  have hR2 : Tendsto (fun N => R N ^ 2) atTop atTop := by
    simpa only [pow_two] using hR.atTop_mul_atTop₀ hR
  have herr : Tendsto (fun N : ℕ => (|s| ^ 3 / 6) / R N ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hR2
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero (fun _ => dist_nonneg) ?_ herr
  intro N
  rw [Real.dist_eq]
  have h := abs_gaussianConcentrationTruncation_sub_le (R := R N) (s := s)
    (show 0 < R N by dsimp [R]; positivity)
  calc
    |gaussianConcentrationTruncation ((N : ℝ) + 1) s - s| ≤
        |s| ^ 3 / (6 * R N ^ 2) := by simpa [R] using h
    _ = (|s| ^ 3 / 6) / R N ^ 2 := by
      field_simp [ne_of_gt (show 0 < R N by dsimp [R]; positivity)]

/-- Sharp Gaussian concentration for `C³` functions on a finite product Gaussian space whose
coordinate derivatives through order three have polynomial growth. The gradient uses the
Euclidean `ℓ²` norm even though the product carrier has its `ℓ∞` norm. -/
theorem integral_exp_centered_le_of_polynomial_growth {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    {L lam : ℝ} (hL : 0 ≤ L)
    (hgrad : ∀ x, ‖coordinateGradientEuclidean F x‖ ≤ L) :
    Integrable F (standardGaussianPi n) ∧
      Integrable (fun x => Real.exp (lam * F x)) (standardGaussianPi n) ∧
      Integrable (fun x => Real.exp (lam * (F x -
        ∫ y, F y ∂(standardGaussianPi n)))) (standardGaussianPi n) ∧
      (∫ x, Real.exp (lam * (F x -
        ∫ y, F y ∂(standardGaussianPi n))) ∂(standardGaussianPi n)) ≤
        Real.exp (lam ^ 2 * L ^ 2 / 2) := by
  rcases hF₃.2 with ⟨C, hC, d, hFbound, hFderiv, hFderiv₂, hFderiv₃⟩
  have hFmeas : Measurable F := hF₃.1.continuous.measurable
  have hFInt : Integrable F (standardGaussianPi n) :=
    integrable_of_pi_polynomial_bound hFmeas hC hFbound
  let G : ℕ → (Fin n → ℝ) → ℝ := fun N x =>
    gaussianConcentrationTruncation ((N : ℝ) + 1) (F x)
  let m : ℕ → ℝ := fun N => ∫ x, G N x ∂(standardGaussianPi n)
  have hGpoint (x : Fin n → ℝ) : Tendsto (fun N => G N x) atTop (𝓝 (F x)) := by
    simpa [G] using tendsto_gaussianConcentrationTruncation_nat (F x)
  have hGmeas (N : ℕ) : Measurable (G N) := by
    exact (contDiff_gaussianConcentrationTruncation (R := (N : ℝ) + 1)).continuous.measurable.comp
      hFmeas
  have hGbound (N : ℕ) (x : Fin n → ℝ) : |G N x| ≤ |F x| := by
    exact abs_gaussianConcentrationTruncation_le
      (R := (N : ℝ) + 1) (s := F x) (by positivity)
  have hm_tendsto : Tendsto m atTop (𝓝 (∫ x, F x ∂(standardGaussianPi n))) := by
    have hpoint : ∀ᵐ x ∂(standardGaussianPi n),
        Tendsto (fun N => G N x) atTop (𝓝 (F x)) := ae_of_all _ hGpoint
    have hmeas : ∀ᶠ N in atTop,
        AEStronglyMeasurable (G N) (standardGaussianPi n) :=
      Eventually.of_forall fun N => (hGmeas N).aestronglyMeasurable
    have hbound : ∀ᶠ N in atTop, ∀ᵐ x ∂(standardGaussianPi n),
        ‖G N x‖ ≤ |F x| := by
      filter_upwards with N
      exact ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hGbound N x
    have h := tendsto_integral_filter_of_dominated_convergence
      (F := G) (f := F) (bound := fun x => |F x|)
      hmeas hbound hFInt.norm hpoint
    simpa [m] using h
  have hG₃ (N : ℕ) : HasPolynomiallyBoundedThirdCoordinateDerivatives (G N) := by
    have hscale : 1 ≤ (N : ℝ) + 1 := by
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    simpa [G] using hasPolynomiallyBoundedThirdCoordinateDerivatives_truncation_comp
      hF₃ (R := (N : ℝ) + 1) hscale
  have hgradG (N : ℕ) (x : Fin n → ℝ) :
      ‖coordinateGradientEuclidean (G N) x‖ ≤ L := by
    have hcoord : ∀ i,
        coordinateDerivative (G N) i x =
          deriv (gaussianConcentrationTruncation ((N : ℝ) + 1)) (F x) *
            coordinateDerivative F i x := by
      intro i
      change coordinateDerivative
          (fun y => gaussianConcentrationTruncation ((N : ℝ) + 1) (F y)) i x = _
      exact coordinateDerivative_comp_truncation_local
        (hF₃.1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3))
        ((contDiff_gaussianConcentrationTruncation
          (R := (N : ℝ) + 1)).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)) i x
    have hvec : coordinateGradientEuclidean (G N) x =
        deriv (gaussianConcentrationTruncation ((N : ℝ) + 1)) (F x) •
          coordinateGradientEuclidean F x := by
      ext i
      simp only [coordinateGradientEuclidean]
      exact hcoord i
    rw [hvec, norm_smul]
    calc
      ‖deriv (gaussianConcentrationTruncation ((N : ℝ) + 1)) (F x)‖ *
          ‖coordinateGradientEuclidean F x‖ ≤ 1 * L :=
        mul_le_mul (abs_deriv_gaussianConcentrationTruncation_le
          (R := (N : ℝ) + 1) (s := F x) (by positivity))
          (hgrad x) (norm_nonneg _) (by norm_num)
      _ = L := by ring
  have hbounded (N : ℕ) := integral_exp_centered_le_of_bounded
    (hG₃ N) (B := (N : ℝ) + 1) (L := L) (lam := lam)
    (by positivity) hL
    (fun x => by
      change |gaussianConcentrationTruncation ((N : ℝ) + 1) (F x)| ≤ (N : ℝ) + 1
      exact abs_gaussianConcentrationTruncation_le_R
        (R := (N : ℝ) + 1) (s := F x) (by positivity))
    (hgradG N)
  let φ : (Fin n → ℝ) → ℝ := fun x => Real.exp (lam *
    (F x - ∫ y, F y ∂(standardGaussianPi n)))
  let φN : ℕ → (Fin n → ℝ) → ℝ := fun N x => Real.exp (lam * (G N x - m N))
  let eN : ℕ → (Fin n → ℝ) → ENNReal := fun N x => ENNReal.ofReal (φN N x)
  have hφmeas : Measurable φ := by
    fun_prop
  have heNmeas (N : ℕ) : Measurable (eN N) := by
    fun_prop
  have hpointφ (x : Fin n → ℝ) : Tendsto (fun N => φN N x) atTop (𝓝 (φ x)) := by
    have harg : Tendsto (fun N => lam * (G N x - m N)) atTop
        (𝓝 (lam * (F x - ∫ y, F y ∂(standardGaussianPi n)))) := by
      exact tendsto_const_nhds.mul ((hGpoint x).sub hm_tendsto)
    change Tendsto (Real.exp ∘ (fun N => lam * (G N x - m N))) atTop
      (𝓝 (Real.exp (lam * (F x - ∫ y, F y ∂(standardGaussianPi n)))))
    exact Real.continuous_exp.continuousAt.tendsto.comp harg
  have hpointENN (x : Fin n → ℝ) :
      Tendsto (fun N => eN N x) atTop (𝓝 (ENNReal.ofReal (φ x))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hpointφ x)
  have hφNnonneg (N : ℕ) : 0 ≤ᵐ[standardGaussianPi n] φN N :=
    ae_of_all _ fun x => (Real.exp_pos _).le
  have heNbound (N : ℕ) :
      (∫⁻ x, eN N x ∂(standardGaussianPi n)) ≤ ENNReal.ofReal
        (Real.exp (lam ^ 2 * L ^ 2 / 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hbounded N).2.2.1 (hφNnonneg N)]
    exact ENNReal.ofReal_le_ofReal (hbounded N).2.2.2
  have hfatou := lintegral_liminf_le (μ := standardGaussianPi n)
    (f := eN) (u := atTop) heNmeas
  have hliminf : Filter.liminf (fun N => ∫⁻ x, eN N x ∂(standardGaussianPi n)) atTop ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * L ^ 2 / 2)) := by
    apply Filter.liminf_le_of_frequently_le
    · exact Filter.Frequently.of_forall heNbound
    · refine ⟨0, ?_⟩
      filter_upwards with N
      exact bot_le
  have hfatouBound :
      (∫⁻ x, ENNReal.ofReal (φ x) ∂(standardGaussianPi n)) ≤
        ENNReal.ofReal (Real.exp (lam ^ 2 * L ^ 2 / 2)) := by
    calc
      _ = ∫⁻ x, liminf (fun N => eN N x) atTop ∂(standardGaussianPi n) := by
        apply lintegral_congr_ae
        filter_upwards with x
        exact (hpointENN x).liminf_eq.symm
      _ ≤ Filter.liminf (fun N => ∫⁻ x, eN N x ∂(standardGaussianPi n)) atTop := hfatou
      _ ≤ _ := hliminf
  have hφfinite :
      (∫⁻ x, ENNReal.ofReal (φ x) ∂(standardGaussianPi n)) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hfatouBound ENNReal.ofReal_lt_top
  have hφInt : Integrable φ (standardGaussianPi n) := by
    have h := integrable_toReal_of_lintegral_ne_top
      (hφmeas.ennreal_ofReal.aemeasurable) hφfinite
    convert h using 1
    · ext x
      simp [φ, ENNReal.toReal_ofReal, Real.exp_nonneg]
  have hφboundENN : ENNReal.ofReal (∫ x, φ x ∂(standardGaussianPi n)) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * L ^ 2 / 2)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hφInt
      (ae_of_all _ fun x => (Real.exp_pos _).le)]
    exact hfatouBound
  have hφbound : (∫ x, φ x ∂(standardGaussianPi n)) ≤
      Real.exp (lam ^ 2 * L ^ 2 / 2) :=
    (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).1 hφboundENN
  have hrawInt : Integrable (fun x => Real.exp (lam * F x))
      (standardGaussianPi n) := by
    have hEq : (fun x => Real.exp (lam * F x)) = fun x =>
        Real.exp (lam * ∫ y, F y ∂(standardGaussianPi n)) * φ x := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hEq]
    exact hφInt.const_mul _
  exact ⟨hFInt, hrawInt, hφInt, by simpa [φ] using hφbound⟩

end ASDExplicitGamma.Gaussian

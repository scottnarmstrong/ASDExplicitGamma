/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.ConcentrationMoment

/-!
# Bounded Gaussian heat moments

This module handles endpoint continuity and the differential inequality for bounded inputs.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open Filter
open scoped Topology

namespace ASDExplicitGamma.Gaussian

private theorem tendsto_heatAverage_bridge_at {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    {B : ℝ} (hFbound : ∀ x, |F x| ≤ B)
    (ξ : Fin n → ℝ) (t₀ : ℝ) :
    Tendsto (fun r => heatAverage F (Real.sqrt r • ξ) (1 - r)) (𝓝 t₀)
      (𝓝 <| ∫ η, F (Real.sqrt t₀ • ξ + Real.sqrt (1 - t₀) • η)
        ∂(standardGaussianPi n)) := by
  let Φ : ℝ → (Fin n → ℝ) → ℝ := fun r η =>
    F (Real.sqrt r • ξ + Real.sqrt (1 - r) • η)
  let Φ₀ : (Fin n → ℝ) → ℝ := fun η =>
    F (Real.sqrt t₀ • ξ + Real.sqrt (1 - t₀) • η)
  have hmeas : ∀ᶠ r in 𝓝 t₀,
      AEStronglyMeasurable (Φ r) (standardGaussianPi n) := by
    filter_upwards with r
    have harg : Continuous (fun η : Fin n → ℝ =>
        Real.sqrt r • ξ + Real.sqrt (1 - r) • η) := by
      exact continuous_const.add (continuous_id.const_smul (Real.sqrt (1 - r)))
    exact ((hF₃.1.continuous.comp harg).measurable).aestronglyMeasurable
  have hbound : ∀ᶠ r in 𝓝 t₀, ∀ᵐ η ∂(standardGaussianPi n),
      ‖Φ r η‖ ≤ B := by
    filter_upwards with r
    exact ae_of_all _ fun η => by
      simpa [Φ, Real.norm_eq_abs] using hFbound _
  have hpoint : ∀ᵐ η ∂(standardGaussianPi n),
      Tendsto (fun r => Φ r η) (𝓝 t₀) (𝓝 (Φ₀ η)) := by
    apply ae_of_all
    intro η
    have hsqrt₁ : Continuous (fun r : ℝ => Real.sqrt r) := Real.continuous_sqrt
    have hsqrt₂ : Continuous (fun r : ℝ => Real.sqrt (1 - r)) :=
      Real.continuous_sqrt.comp (continuous_const.sub continuous_id)
    have harg : Continuous (fun r : ℝ =>
        Real.sqrt r • ξ + Real.sqrt (1 - r) • η) := by
      exact (hsqrt₁.smul continuous_const).add (hsqrt₂.smul continuous_const)
    change Tendsto (fun r => F (Real.sqrt r • ξ + Real.sqrt (1 - r) • η))
      (𝓝 t₀) (𝓝 (F (Real.sqrt t₀ • ξ + Real.sqrt (1 - t₀) • η)))
    exact (hF₃.1.continuous.comp harg).continuousAt.tendsto
  have h := tendsto_integral_filter_of_dominated_convergence
    (F := Φ) (f := Φ₀) (bound := fun _ : Fin n → ℝ => B)
    hmeas hbound (integrable_const B) hpoint
  simpa [Φ, Φ₀, heatAverage, shiftAverage] using h

/-- The bounded heat moment is continuous in its interpolation parameter, including both
endpoints. -/
theorem continuous_gaussianHeatMoment_of_bounded {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    {B : ℝ} (hB : 0 ≤ B) (hFbound : ∀ x, |F x| ≤ B)
    (lam : ℝ) : Continuous (gaussianHeatMoment F lam) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  let Φ : ℝ → (Fin n → ℝ) → ℝ := fun r ξ =>
    Real.exp (lam * heatAverage F (Real.sqrt r • ξ) (1 - r))
  let Φ₀ : (Fin n → ℝ) → ℝ := fun ξ =>
    Real.exp (lam * ∫ η, F (Real.sqrt t₀ • ξ + Real.sqrt (1 - t₀) • η)
      ∂(standardGaussianPi n))
  let Q : ℝ := Real.exp (|lam| * B)
  have hmeas : ∀ᶠ r in 𝓝 t₀,
      AEStronglyMeasurable (Φ r) (standardGaussianPi n) := by
    filter_upwards with r
    have hU := contDiff_two_heatAverage_of_third hF₃ (1 - r)
    have hcenter : Continuous (fun ξ : Fin n → ℝ => Real.sqrt r • ξ) := by fun_prop
    have harg : Continuous (fun ξ : Fin n → ℝ =>
        lam * heatAverage F (Real.sqrt r • ξ) (1 - r)) :=
      continuous_const.mul (hU.continuous.comp hcenter)
    exact (Real.continuous_exp.comp harg).measurable.aestronglyMeasurable
  have hbound : ∀ᶠ r in 𝓝 t₀, ∀ᵐ ξ ∂(standardGaussianPi n),
      ‖Φ r ξ‖ ≤ Q := by
    filter_upwards with r
    exact ae_of_all _ fun ξ => by
      simpa [Φ, Q, Real.norm_eq_abs] using
        abs_exp_heatAverage_le_of_bounded hF₃ hB hFbound lam (1 - r)
          (Real.sqrt r • ξ)
  have hpoint : ∀ᵐ ξ ∂(standardGaussianPi n),
      Tendsto (fun r => Φ r ξ) (𝓝 t₀) (𝓝 (Φ₀ ξ)) := by
    apply ae_of_all
    intro ξ
    have hbridge := tendsto_heatAverage_bridge_at hF₃ hFbound ξ t₀
    have hscaled : Tendsto (fun r => lam * heatAverage F (Real.sqrt r • ξ) (1 - r))
        (𝓝 t₀) (𝓝 (lam * ∫ η,
          F (Real.sqrt t₀ • ξ + Real.sqrt (1 - t₀) • η)
            ∂(standardGaussianPi n))) :=
      tendsto_const_nhds.mul hbridge
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp hscaled
    simpa [Φ, Φ₀, Function.comp_def] using hexp
  have h := tendsto_integral_filter_of_dominated_convergence
    (F := Φ) (f := Φ₀) (bound := fun _ : Fin n → ℝ => Q)
    hmeas hbound (integrable_const Q) hpoint
  change Tendsto (fun r => gaussianHeatMoment F lam r) (𝓝 t₀)
    (𝓝 (gaussianHeatMoment F lam t₀))
  simpa [Φ, Φ₀, Q, gaussianHeatMoment, heatAverage, shiftAverage] using h

/-- The sharp centered moment bound for bounded `C³` functions with polynomially bounded
derivatives. -/
theorem integral_exp_centered_le_of_bounded {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    {B L lam : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hFbound : ∀ x, |F x| ≤ B)
    (hgrad : ∀ x, ‖coordinateGradientEuclidean F x‖ ≤ L) :
    Integrable F (standardGaussianPi n) ∧
      Integrable (fun x => Real.exp (lam * F x)) (standardGaussianPi n) ∧
      Integrable (fun x => Real.exp (lam * (F x -
        ∫ y, F y ∂(standardGaussianPi n)))) (standardGaussianPi n) ∧
      (∫ x, Real.exp (lam * (F x -
        ∫ y, F y ∂(standardGaussianPi n))) ∂(standardGaussianPi n)) ≤
        Real.exp (lam ^ 2 * L ^ 2 / 2) := by
  let Q : ℝ := Real.exp (|lam| * B)
  have hFmeas : AEStronglyMeasurable F (standardGaussianPi n) :=
    hF₃.1.continuous.measurable.aestronglyMeasurable
  have hFInt : Integrable F (standardGaussianPi n) := by
    refine Integrable.mono' (integrable_const B) hFmeas ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hFbound x
  have hExpmeas : AEStronglyMeasurable (fun x => Real.exp (lam * F x))
      (standardGaussianPi n) := by
    have hcont : Continuous (fun x : Fin n → ℝ => Real.exp (lam * F x)) :=
      Real.continuous_exp.comp (continuous_const.mul hF₃.1.continuous)
    exact hcont.measurable.aestronglyMeasurable
  have hExpbound (x : Fin n → ℝ) :
      |Real.exp (lam * F x)| ≤ Q := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      lam * F x ≤ |lam * F x| := le_abs_self _
      _ = |lam| * |F x| := abs_mul _ _
      _ ≤ |lam| * B := mul_le_mul_of_nonneg_left (hFbound x) (abs_nonneg _)
  have hExpInt : Integrable (fun x => Real.exp (lam * F x))
      (standardGaussianPi n) := by
    refine Integrable.mono' (integrable_const Q) hExpmeas ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hExpbound x
  let M : ℝ → ℝ := gaussianHeatMoment F lam
  let c : ℝ := lam ^ 2 * L ^ 2 / 2
  let D : ℝ → ℝ := fun t => (lam ^ 2 / 2) * ∫ ξ,
    Real.exp (lam * heatAverage F (Real.sqrt t • ξ) (1 - t)) *
      ∑ i : Fin n,
        (coordinateDerivative (fun x => heatAverage F x (1 - t)) i
          (Real.sqrt t • ξ)) ^ 2 ∂(standardGaussianPi n)
  have hMcont : Continuous M := by
    simpa [M] using continuous_gaussianHeatMoment_of_bounded hF₃ hB hFbound lam
  have hMderiv {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
      HasDerivAt M (D t) t := by
    simpa [D, M] using hasDerivAt_gaussianHeatMoment hF₃ hB hL hFbound hgrad ht ht1
  have hderivBound {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : D t ≤ c * M t := by
    let U : (Fin n → ℝ) → ℝ := fun x => heatAverage F x (1 - t)
    let A : (Fin n → ℝ) → ℝ := fun x => Real.exp (lam * U x)
    let R : (Fin n → ℝ) → ℝ := fun x => A x *
      ∑ i : Fin n, (coordinateDerivative U i x) ^ 2
    have hU₂ := hasPolynomiallyBoundedSecond_heatAverage_of_third hF₃ (1 - t)
    have hgradU (x : Fin n → ℝ) :
        ‖coordinateGradientEuclidean U x‖ ≤ L := by
      exact norm_coordinateGradient_heatAverage_le hF₃ hgrad x (1 - t)
    have hsumBound (x : Fin n → ℝ) :
        (∑ i : Fin n, (coordinateDerivative U i x) ^ 2) ≤ L ^ 2 := by
      rw [sum_sq_coordinateGradient_eq_norm_sq]
      exact (sq_le_sq₀ (norm_nonneg _) hL).2 (hgradU x)
    have hAcont : Continuous A :=
      Real.continuous_exp.comp (continuous_const.mul hU₂.1.continuous)
    have hcoordCont (i : Fin n) : Continuous (coordinateDerivative U i) := by
      have hfd : Continuous (fun x : Fin n → ℝ => fderiv ℝ U x) :=
        hU₂.1.continuous_fderiv (by norm_num)
      unfold coordinateDerivative
      exact hfd.clm_apply continuous_const
    have hsumCont : Continuous (fun x : Fin n → ℝ =>
        ∑ i : Fin n, (coordinateDerivative U i x) ^ 2) := by
      apply continuous_finsetSum
      intro i hi
      exact (hcoordCont i).pow 2
    have hRcont : Continuous R := hAcont.mul hsumCont
    have hAInt : Integrable (fun ξ : Fin n → ℝ => A (Real.sqrt t • ξ))
        (standardGaussianPi n) := by
      have hcenter : Continuous (fun ξ : Fin n → ℝ => Real.sqrt t • ξ) := by fun_prop
      refine Integrable.mono' (integrable_const Q)
        (hAcont.comp hcenter
          |>.measurable.aestronglyMeasurable) ?_
      filter_upwards with ξ
      simpa [A, U, Q, Real.norm_eq_abs] using
        abs_exp_heatAverage_le_of_bounded hF₃ hB hFbound lam (1 - t)
          (Real.sqrt t • ξ)
    have hRInt : Integrable (fun ξ : Fin n → ℝ => R (Real.sqrt t • ξ))
        (standardGaussianPi n) := by
      have hcenter : Continuous (fun ξ : Fin n → ℝ => Real.sqrt t • ξ) := by fun_prop
      have hRbound (x : Fin n → ℝ) :
          ‖R x‖ ≤ Q * L ^ 2
      := by
        have hsumNonneg : 0 ≤ ∑ i : Fin n, (coordinateDerivative U i x) ^ 2 :=
          Finset.sum_nonneg fun i hi => sq_nonneg _
        have hAnonneg : 0 ≤ A x := le_of_lt (Real.exp_pos _)
        have hpoint : 0 ≤ R x := mul_nonneg hAnonneg hsumNonneg
        rw [Real.norm_eq_abs, abs_of_nonneg hpoint]
        change A x * (∑ i : Fin n, (coordinateDerivative U i x) ^ 2) ≤ _
        have hAupper : A x ≤ Q := by
          simpa [A, U, Q, abs_of_pos (Real.exp_pos _)] using
            abs_exp_heatAverage_le_of_bounded hF₃ hB hFbound lam (1 - t) x
        exact mul_le_mul hAupper (hsumBound x) hsumNonneg
          (le_of_lt (Real.exp_pos _))
      refine Integrable.mono' (integrable_const (Q * L ^ 2))
        (hRcont.comp hcenter
          |>.measurable.aestronglyMeasurable) ?_
      filter_upwards with ξ
      simpa [Real.norm_eq_abs] using hRbound (Real.sqrt t • ξ)
    have hpoint (ξ : Fin n → ℝ) :
        R (Real.sqrt t • ξ) ≤ L ^ 2 * A (Real.sqrt t • ξ) := by
      have hsumNonneg : 0 ≤ ∑ i : Fin n, (coordinateDerivative U i
          (Real.sqrt t • ξ)) ^ 2 := Finset.sum_nonneg fun i hi => sq_nonneg _
      have hApos : 0 ≤ A (Real.sqrt t • ξ) := le_of_lt (Real.exp_pos _)
      change A (Real.sqrt t • ξ) *
          ∑ i : Fin n, (coordinateDerivative U i (Real.sqrt t • ξ)) ^ 2 ≤ _
      exact (mul_le_mul_of_nonneg_left (hsumBound _) hApos).trans_eq (by ring)
    have hIntegralBound :
        (∫ ξ, R (Real.sqrt t • ξ) ∂(standardGaussianPi n)) ≤
          L ^ 2 * ∫ ξ, A (Real.sqrt t • ξ) ∂(standardGaussianPi n) := by
      refine (integral_mono_ae hRInt (hAInt.const_mul (L ^ 2))
        (ae_of_all _ hpoint)).trans_eq ?_
      rw [integral_const_mul]
    have hCoeff : 0 ≤ lam ^ 2 / 2 := by positivity
    have hmainEq :
        (∫ ξ, Real.exp (lam * heatAverage F (Real.sqrt t • ξ) (1 - t)) *
            ∑ i : Fin n,
              (coordinateDerivative (fun x => heatAverage F x (1 - t)) i
                (Real.sqrt t • ξ)) ^ 2 ∂(standardGaussianPi n)) =
          ∫ ξ, R (Real.sqrt t • ξ) ∂(standardGaussianPi n) := by
      apply integral_congr_ae
      exact ae_of_all _ fun ξ => by simp [R, A, U]
    have hM_eq : ∫ ξ, A (Real.sqrt t • ξ) ∂(standardGaussianPi n) = M t := by
      simp [M, gaussianHeatMoment, A, U]
    have hboundFinal : D t ≤ c * M t := by
      change (lam ^ 2 / 2) *
          (∫ ξ, Real.exp (lam * heatAverage F (Real.sqrt t • ξ) (1 - t)) *
            ∑ i : Fin n,
              (coordinateDerivative (fun x => heatAverage F x (1 - t)) i
                (Real.sqrt t • ξ)) ^ 2 ∂(standardGaussianPi n)) ≤ c * M t
      rw [hmainEq]
      have hstep :
          (lam ^ 2 / 2) * ∫ ξ, R (Real.sqrt t • ξ) ∂(standardGaussianPi n) ≤
            (lam ^ 2 / 2) *
              (L ^ 2 * ∫ ξ, A (Real.sqrt t • ξ) ∂(standardGaussianPi n)) :=
        mul_le_mul_of_nonneg_left hIntegralBound hCoeff
      have hend :
          (lam ^ 2 / 2) *
              (L ^ 2 * ∫ ξ, A (Real.sqrt t • ξ) ∂(standardGaussianPi n)) ≤ c * M t := by
        rw [hM_eq]
        exact le_of_eq (by dsimp [c]; ring)
      exact hstep.trans hend
    simpa [D, c] using hboundFinal
  have hHcont : Continuous (fun r => Real.exp (-c * r) * M r) := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hMcont
  have hHderiv {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
      HasDerivAt (fun r => Real.exp (-c * r) * M r)
        (Real.exp (-c * t) * (deriv M t - c * M t)) t := by
    have hlin : HasDerivAt (fun r : ℝ => -c * r) (-c) t := by
      simpa using (hasDerivAt_id t).const_mul (-c)
    have hexp := (Real.hasDerivAt_exp (-c * t)).comp t hlin
    convert hexp.mul (hMderiv ht ht1) using 1
    · ext r
      congr 1
    · rw [(hMderiv ht ht1).deriv]
      simp only [Function.comp_apply, neg_mul]
      ring
  have hanti : AntitoneOn (fun r => Real.exp (-c * r) * M r) (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hHcont.continuousOn
    · intro t ht
      have ht' : t ∈ Set.Ioo 0 1 := by simpa [interior_Icc] using ht
      exact (hHderiv ht'.1 ht'.2).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo 0 1 := by simpa [interior_Icc] using ht
      rw [(hHderiv ht'.1 ht'.2).deriv]
      have hbound := hderivBound ht'.1 ht'.2
      have hbound' : deriv M t ≤ c * M t := by
        rw [(hMderiv ht'.1 ht'.2).deriv]
        exact hbound
      have hnonpos : deriv M t - c * M t ≤ 0 := by
        linarith only [hbound']
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hnonpos
  have hmean : heatAverage F 0 1 = ∫ x, F x ∂(standardGaussianPi n) := by
    simp [heatAverage, shiftAverage, standardGaussianPi]
  have hzero : M 0 = Real.exp (lam * ∫ x, F x ∂(standardGaussianPi n)) := by
    simp [M, gaussianHeatMoment, Real.sqrt_zero, hmean, standardGaussianPi]
  have hone : M 1 = ∫ x, Real.exp (lam * F x) ∂(standardGaussianPi n) := by
    simp [M, gaussianHeatMoment, heatAverage, shiftAverage, Real.sqrt_one,
      standardGaussianPi]
  have hendpoint := hanti (Set.left_mem_Icc.mpr (by norm_num))
    (Set.right_mem_Icc.mpr (by norm_num)) (by norm_num)
  simp only [M, mul_zero, mul_one, Real.exp_zero, hzero, hone, one_mul] at hendpoint
  let m : ℝ := ∫ x, F x ∂(standardGaussianPi n)
  have hraw :
      (∫ x, Real.exp (lam * F x) ∂(standardGaussianPi n)) ≤
        Real.exp (c + lam * m) := by
    calc
      (∫ x, Real.exp (lam * F x) ∂(standardGaussianPi n)) =
          (Real.exp c * Real.exp (-c)) *
            (∫ x, Real.exp (lam * F x) ∂(standardGaussianPi n)) := by
              rw [← Real.exp_add]
              simp
      _ = Real.exp c * (Real.exp (-c) *
            ∫ x, Real.exp (lam * F x) ∂(standardGaussianPi n)) := by ring
      _ ≤ Real.exp c * Real.exp (lam * m) :=
            mul_le_mul_of_nonneg_left hendpoint (Real.exp_nonneg c)
      _ = Real.exp (c + lam * m) := by rw [← Real.exp_add]
  have hmeanBound : |m| ≤ B := by
    dsimp [m]
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ x, F x ∂(standardGaussianPi n)‖ ≤
          ∫ x, ‖F x‖ ∂(standardGaussianPi n) := norm_integral_le_integral_norm _
      _ ≤ ∫ _x, B ∂(standardGaussianPi n) := by
          apply integral_mono_ae hFInt.norm (integrable_const B)
          exact ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hFbound x
      _ = B := by simp [standardGaussianPi]
  have hcenterInt : Integrable (fun x =>
      Real.exp (lam * (F x - ∫ y, F y ∂(standardGaussianPi n))))
      (standardGaussianPi n) := by
    let Qc : ℝ := Real.exp (|lam| * (2 * B))
    have hcont : Continuous (fun x : Fin n → ℝ =>
        Real.exp (lam * (F x - ∫ y, F y ∂(standardGaussianPi n)))) :=
      Real.continuous_exp.comp
        (continuous_const.mul (hF₃.1.continuous.sub continuous_const))
    refine Integrable.mono' (integrable_const Qc)
      (hcont.measurable.aestronglyMeasurable) ?_
    filter_upwards with x
    have hval : |F x - ∫ y, F y ∂(standardGaussianPi n)| ≤ 2 * B := by
      calc
        |F x - ∫ y, F y ∂(standardGaussianPi n)| ≤
            |F x| + |∫ y, F y ∂(standardGaussianPi n)| := abs_sub _ _
        _ ≤ B + B := add_le_add (hFbound x) hmeanBound
        _ = 2 * B := by ring
    have hbound : |Real.exp (lam * (F x - ∫ y, F y ∂(standardGaussianPi n)))| ≤ Qc := by
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        lam * (F x - ∫ y, F y ∂(standardGaussianPi n)) ≤
            |lam * (F x - ∫ y, F y ∂(standardGaussianPi n))| := le_abs_self _
        _ = |lam| * |F x - ∫ y, F y ∂(standardGaussianPi n)| := abs_mul _ _
        _ ≤ |lam| * (2 * B) := mul_le_mul_of_nonneg_left hval (abs_nonneg _)
    simpa [Qc, Real.norm_eq_abs] using hbound
  have hcenterEq :
      (∫ x, Real.exp (lam * (F x - m)) ∂(standardGaussianPi n)) =
        Real.exp (-lam * m) *
          ∫ x, Real.exp (lam * F x) ∂(standardGaussianPi n) := by
    calc
      _ = ∫ x, Real.exp (-lam * m) * Real.exp (lam * F x)
            ∂(standardGaussianPi n) := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by
            change Real.exp (lam * (F x - m)) =
              Real.exp (-lam * m) * Real.exp (lam * F x)
            rw [← Real.exp_add]
            congr 1
            ring
      _ = _ := integral_const_mul _ _
  refine ⟨hFInt, hExpInt, hcenterInt, ?_⟩
  rw [hcenterEq]
  calc
    Real.exp (-lam * m) *
        (∫ x, Real.exp (lam * F x) ∂(standardGaussianPi n)) ≤
        Real.exp (-lam * m) * Real.exp (c + lam * m) :=
      mul_le_mul_of_nonneg_left hraw (Real.exp_nonneg _)
    _ = Real.exp (lam ^ 2 * L ^ 2 / 2) := by
      rw [← Real.exp_add]
      dsimp [c]
      congr 1
      ring

end ASDExplicitGamma.Gaussian

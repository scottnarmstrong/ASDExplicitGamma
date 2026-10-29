module

public import ASDExplicitGamma.Gaussian.H3Kernel1D
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Group.Bounded

/-! # L², continuity and derivative facts for the q3 convolution kernels -/

@[expose] public section

open MeasureTheory Set Filter ASDExplicitGamma.Model
open scoped Topology NNReal ENNReal

namespace ASDExplicitGamma.Gaussian

private def positiveSquare (x : ℝ) : ℝ := (max x 0) ^ 2

private theorem positiveSquare_hasDerivAt (x : ℝ) :
    HasDerivAt positiveSquare (2 * max x 0) x := by
  by_cases hx0 : x < 0
  · have heq : positiveSquare =ᶠ[nhds x] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hx0] with y hy
      simp [positiveSquare, max_eq_right (le_of_lt hy)]
    have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x (0 : ℝ)
    have hzero : 2 * max x 0 = 0 := by simp [max_eq_right hx0.le]
    simpa [hzero] using hconst.congr_of_eventuallyEq heq
  · by_cases hxpos : 0 < x
    · have heq : positiveSquare =ᶠ[nhds x] fun y : ℝ => y ^ 2 := by
        filter_upwards [eventually_gt_nhds hxpos] with y hy
        simp [positiveSquare, max_eq_left hy.le]
      have hpoly : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        convert (hasDerivAt_pow 2 x) using 1; ring
      have hres := hpoly.congr_of_eventuallyEq heq
      convert hres using 1; simp [max_eq_left hxpos.le]
    · have hx : x = 0 := le_antisymm (le_of_not_gt hxpos) (le_of_not_gt hx0)
      subst x
      rw [hasDerivAt_iff_tendsto_slope]
      have heq : (fun y : ℝ => slope positiveSquare 0 y) =ᶠ[nhdsWithin 0 ({0}ᶜ)]
          fun y => max y 0 := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy0 : y ≠ 0 := hy
        by_cases h : 0 ≤ y
        · simp [slope, positiveSquare, max_eq_left h]; field_simp [hy0]
        · simp [slope, positiveSquare, max_eq_right (le_of_not_ge h)]
      have hcont : ContinuousAt (fun y : ℝ => max y 0) 0 :=
        (continuous_id.max continuous_const).continuousAt
      simpa using (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

private theorem q3Argument_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - 4 * y ^ 2) (-8 * x) x := by
  convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_pow 2 x).const_mul 4) using 1
  ring

theorem gauss_q3KernelD1_hasDerivAt (x : ℝ) :
    HasDerivAt q3KernelD1 (q3KernelD2 x) x := by
  have ht := q3Argument_hasDerivAt x
  have hp := (positiveSquare_hasDerivAt (1 - 4 * x ^ 2)).comp x ht
  have hl : HasDerivAt (fun y : ℝ => -8 * y) (-8) x := by
    have hfun : (fun y : ℝ => -8 * y) = fun y => (-8 : ℝ) * id y := by
      funext y
      simp [id]
    rw [hfun]
    simpa using HasDerivAt.const_mul (-8 : ℝ) (hasDerivAt_id x)
  have hmul := hp.mul hl
  have hscaled := HasDerivAt.const_mul (Real.sqrt (3003 / 1024) * 3 : ℝ) hmul
  have hfun : q3KernelD1 = fun y =>
      (Real.sqrt (3003 / 1024) * 3) *
        (positiveSquare (1 - 4 * y ^ 2) * (-8 * y)) := by
    funext y
    simp [q3KernelD1, positiveSquare, mul_comm, mul_left_comm, mul_assoc]
  rw [hfun]
  convert hscaled using 1
  · funext y
    simp [Function.comp_def, positiveSquare, mul_comm, mul_left_comm, mul_assoc]
  · simp [q3KernelD2, positiveSquare, mul_comm, mul_left_comm, mul_assoc]
    ring

theorem q3_deriv_eq : deriv q3Kernel = q3KernelD1 :=
  funext fun x => (q3Kernel_hasDerivAt x).deriv

theorem q3_second_deriv_eq : deriv q3KernelD1 = q3KernelD2 :=
  funext fun x => (gauss_q3KernelD1_hasDerivAt x).deriv

theorem q3KernelD1_contDiff : ContDiff ℝ 1 q3KernelD1 := by
  rw [← q3_deriv_eq]
  simpa using q3Kernel_contDiff_two.deriv'

theorem gauss_q3KernelD2_continuous : Continuous q3KernelD2 := by
  rw [← q3_second_deriv_eq]
  exact q3KernelD1_contDiff.continuous_deriv (by norm_num)

theorem q3KernelD1_hasCompactSupport : HasCompactSupport q3KernelD1 := by
  rw [← q3_deriv_eq]
  exact q3Kernel_hasCompactSupport.deriv

theorem q3KernelD2_hasCompactSupport : HasCompactSupport q3KernelD2 := by
  rw [← q3_second_deriv_eq]
  exact q3KernelD1_hasCompactSupport.deriv

private theorem lipschitz_of_compact_derivative {f g : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) (hs : HasCompactSupport g) :
    ∃ C : ℝ≥0, LipschitzWith C f := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hs
  refine ⟨⟨max B 0, le_max_right _ _⟩,
    lipschitzWith_of_nnnorm_deriv_le (fun x => (hf x).differentiableAt) ?_⟩
  intro x
  change ‖deriv f x‖ ≤ max B 0
  rw [(hf x).deriv]
  exact (hB x).trans (le_max_left _ _)

/-- The first two kernel levels have global Lipschitz bounds from their compact derivatives. -/
theorem q3Kernel_first_lipschitz :
    (∃ C : ℝ≥0, LipschitzWith C q3Kernel) ∧ (∃ C : ℝ≥0, LipschitzWith C q3KernelD1) :=
  ⟨lipschitz_of_compact_derivative q3Kernel_hasDerivAt q3KernelD1_contDiff.continuous
      q3KernelD1_hasCompactSupport,
    lipschitz_of_compact_derivative gauss_q3KernelD1_hasDerivAt gauss_q3KernelD2_continuous
      q3KernelD2_hasCompactSupport⟩

/-- The original and first derivative kernels satisfy genuine weak IBP, with no cutoff
boundary measure. Together with `q3_second_weak_derivative` this gives all three orders. -/
theorem q3_first_weak_derivatives {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∫ x, q3Kernel x * deriv φ x) = -(∫ x, q3KernelD1 x * φ x) ∧
    (∫ x, q3KernelD1 x * deriv φ x) = -(∫ x, q3KernelD2 x * φ x) := by
  have hcφ := hφ.continuous
  have hcdφ := hφ.continuous_deriv (by norm_num)
  constructor
  · exact integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => q3Kernel_hasDerivAt x) (fun x _ => (hφ.differentiable_one x).hasDerivAt)
      ((q3Kernel_continuous.mul hcdφ).integrable_of_hasCompactSupport q3Kernel_hasCompactSupport.mul_right)
      ((q3KernelD1_contDiff.continuous.mul hcφ).integrable_of_hasCompactSupport q3KernelD1_hasCompactSupport.mul_right)
      ((q3Kernel_continuous.mul hcφ).integrable_of_hasCompactSupport q3Kernel_hasCompactSupport.mul_right)
  · exact integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => gauss_q3KernelD1_hasDerivAt x) (fun x _ => (hφ.differentiable_one x).hasDerivAt)
      ((q3KernelD1_contDiff.continuous.mul hcdφ).integrable_of_hasCompactSupport q3KernelD1_hasCompactSupport.mul_right)
      ((gauss_q3KernelD2_continuous.mul hcφ).integrable_of_hasCompactSupport q3KernelD2_hasCompactSupport.mul_right)
      ((q3KernelD1_contDiff.continuous.mul hcφ).integrable_of_hasCompactSupport q3KernelD1_hasCompactSupport.mul_right)

/-- The four actual one-dimensional weak derivative kernels. -/
noncomputable def q3Derivative (r : Fin 4) : ℝ → ℝ :=
  ![q3Kernel, q3KernelD1, q3KernelD2, q3KernelD3] r

/-- Their exact ordinary squared L² norms from the q3 kernel computation. -/
noncomputable def q3DerivativeMoment (r : Fin 4) : ℝ := ![1, 78 / 5, 3432 / 5, 61776] r

theorem q3DerivativeMoment_pos (r : Fin 4) : 0 < q3DerivativeMoment r := by
  fin_cases r <;> norm_num [q3DerivativeMoment]

theorem q3Derivative_measurable (r : Fin 4) : Measurable (q3Derivative r) := by
  fin_cases r
  · exact q3Kernel_continuous.measurable
  · exact q3KernelD1_contDiff.continuous.measurable
  · exact gauss_q3KernelD2_continuous.measurable
  · change Measurable q3KernelD3
    rw [q3Third_eq_indicator]
    exact (show Continuous q3ThirdPolynomial by unfold q3ThirdPolynomial; fun_prop).measurable.indicator measurableSet_Ioo

theorem q3Derivative_integral_sq (r : Fin 4) :
    (∫ x, q3Derivative r x ^ 2) = q3DerivativeMoment r := by
  fin_cases r
  · exact q3Kernel_sq_integral
  · exact q3KernelD1_sq_integral_exact
  · exact q3KernelD2_sq_integral_exact
  · exact q3KernelD3_sq_integral_exact

end ASDExplicitGamma.Gaussian

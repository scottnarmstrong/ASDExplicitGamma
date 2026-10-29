/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Model.Q3Kernel
public import ASDExplicitGamma.Model.Q3Cov
public import ASDExplicitGamma.Gaussian.Q3RealizationLaw
public import ASDExplicitGamma.Gaussian.Q3RealizationFactorization
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Basic.Denumerable
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Fourier coefficients for the periodized q3 feature
-/

@[expose] public section

open MeasureTheory Filter Set
open ProbabilityTheory
open scoped Topology ComplexConjugate

namespace ASDExplicitGamma.Gaussian

open ASDExplicitGamma.Model
open Algsuperdiff.Section3
open scoped Convolution

private theorem q3FourierKernel_even (x : ℝ) : q3Kernel (-x) = q3Kernel x := by
  rw [q3Kernel, q3Kernel]
  simp [abs_neg]

private theorem q3FourierCov_eq_complexConvolution (u : ℝ) :
    (ASDExplicitGamma.q3Cov u : ℂ) =
      MeasureTheory.convolution (fun x : ℝ => (q3Kernel x : ℂ))
        (fun x : ℝ => (q3Kernel x : ℂ)) (ContinuousLinearMap.mul ℂ ℂ) volume u := by
  rw [ASDExplicitGamma.q3Cov, MeasureTheory.convolution_def]
  rw [← integral_complex_ofReal]
  have hchange := Measure.integral_comp_mul_left
    (fun x : ℝ => (q3Kernel x : ℂ) * (q3Kernel (u - x) : ℂ)) (-1)
  simpa [q3FourierKernel_even, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hchange

private theorem q3FourierCov_eq_realConvolution (u : ℝ) :
    ASDExplicitGamma.q3Cov u =
      MeasureTheory.convolution q3Kernel q3Kernel (ContinuousLinearMap.mul ℝ ℝ) volume u := by
  rw [ASDExplicitGamma.q3Cov, MeasureTheory.convolution_def]
  have hchange := Measure.integral_comp_mul_left
    (fun x : ℝ => q3Kernel x * q3Kernel (u - x)) (-1)
  simpa [q3FourierKernel_even, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hchange

private theorem q3FourierCov_continuous : Continuous ASDExplicitGamma.q3Cov := by
  have hconv : Continuous (MeasureTheory.convolution q3Kernel q3Kernel
      (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    q3Kernel_hasCompactSupport.continuous_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) q3Kernel_integrable.locallyIntegrable q3Kernel_continuous
  have hEq : ASDExplicitGamma.q3Cov =
      MeasureTheory.convolution q3Kernel q3Kernel (ContinuousLinearMap.mul ℝ ℝ) volume :=
    funext q3FourierCov_eq_realConvolution
  rw [hEq]
  exact hconv

private theorem q3FourierCov_transform (ξ : ℝ) :
    FourierTransform.fourier (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)) ξ =
      FourierTransform.fourier (fun x : ℝ => (q3Kernel x : ℂ)) ξ ^ 2 := by
  have hq : Integrable (fun x : ℝ => (q3Kernel x : ℂ)) := q3Kernel_integrable.ofReal
  have hconv : (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)) =
      MeasureTheory.convolution (fun x : ℝ => (q3Kernel x : ℂ))
        (fun x : ℝ => (q3Kernel x : ℂ)) (ContinuousLinearMap.mul ℂ ℂ) volume :=
    funext q3FourierCov_eq_complexConvolution
  rw [hconv]
  simpa [pow_two] using Real.fourier_mul_convolution_eq hq hq ξ

private theorem q3FourierCoeffOn_eq_scaled_transform {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] {f : ℝ → ℝ}
    (hsupp : Function.support (fun x : ℝ => (f x : ℂ)) ⊆ Set.Ioc (-L / 2) (L / 2))
    (n : ℤ) :
    fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (f x : ℂ)) n =
      (1 / (L : ℂ)) *
        FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) ((n : ℝ) / L) := by
  have hlenR : L / 2 - (-L / 2) = L := by ring
  have hexp (x : ℝ) :
      fourier (-n) (x : AddCircle L) =
        Complex.exp (((-2 * Real.pi * x * ((n : ℝ) / L) : ℝ) : ℂ) * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [fourierCoeffOn_eq_integral]
  rw [hlenR]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  calc
    _ = (1 / (L : ℂ)) *
        ∫ x in (-L / 2)..(L / 2),
          Complex.exp (((-2 * Real.pi * x * ((n : ℝ) / L) : ℝ) : ℂ) * Complex.I) *
            (f x : ℂ) := by
          congr 2
          funext x
          simp only [smul_eq_mul]
          exact congrArg (fun z : ℂ => z * (f x : ℂ)) (hexp x)
    _ = (1 / (L : ℂ)) *
        FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) ((n : ℝ) / L) := by
          have hsupp' : Function.support (fun x : ℝ =>
              Complex.exp (((-2 * Real.pi * x * ((n : ℝ) / L) : ℝ) : ℂ) * Complex.I) *
                (f x : ℂ)) ⊆ Set.Ioc (-L / 2) (L / 2) :=
            (Function.support_mul_subset_right _ _).trans hsupp
          rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp']
          rw [Real.fourier_real_eq_integral_exp_smul]
          simp only [smul_eq_mul]

private theorem q3FourierKernelCoeffOn_support {L : ℝ} (hL : 2 < L) :
    Function.support (fun x : ℝ => (q3Kernel x : ℂ)) ⊆ Set.Ioc (-L / 2) (L / 2) := by
  apply Function.support_subset_iff'.2
  intro x hx
  have hx' : x ≤ -L / 2 ∨ L / 2 < x := by
    simp only [Set.mem_Ioc] at hx
    rcases not_and_or.mp hx with h | h
    · exact Or.inl (le_of_not_gt h)
    · exact Or.inr (lt_of_not_ge h)
  have hcut : 1 / 2 ≤ |x| := by
    rcases hx' with hx' | hx'
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  simp [q3Kernel_eq_zero_of_abs_ge hcut]

private theorem q3FourierCovCoeffOn_support {L : ℝ} (hL : 2 < L) :
    Function.support (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)) ⊆
      Set.Ioc (-L / 2) (L / 2) := by
  apply Function.support_subset_iff'.2
  intro x hx
  have hx' : x ≤ -L / 2 ∨ L / 2 < x := by
    simp only [Set.mem_Ioc] at hx
    rcases not_and_or.mp hx with h | h
    · exact Or.inl (le_of_not_gt h)
    · exact Or.inr (lt_of_not_ge h)
  have hcut : 1 ≤ |x| := by
    rcases hx' with hx' | hx'
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  simp [ASDExplicitGamma.Model.q3Cov_zero_of_abs_ge_one hcut]

private theorem q3FourierCoeffOn_cov_eq_L_mul_kernel_sq {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] (n : ℤ) :
    fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)) n =
      (L : ℂ) *
        (fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
          (fun x : ℝ => (q3Kernel x : ℂ)) n) ^ 2 := by
  rw [q3FourierCoeffOn_eq_scaled_transform hL (q3FourierCovCoeffOn_support hL) n,
    q3FourierCoeffOn_eq_scaled_transform hL (q3FourierKernelCoeffOn_support hL) n,
    q3FourierCov_transform]
  have hLne : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans (by norm_num) hL))
  field_simp [hLne]

private theorem q3FourierKernel_transform_real (ξ : ℝ) :
    star (FourierTransform.fourier (fun x : ℝ => (q3Kernel x : ℂ)) ξ) =
      FourierTransform.fourier (fun x : ℝ => (q3Kernel x : ℂ)) ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  let g : ℝ → ℂ := fun x =>
    Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) * (q3Kernel x : ℂ)
  change star (∫ x, g x) = ∫ x, g x
  calc
    star (∫ x, g x) = ∫ x, star (g x) := (integral_conj).symm
    _ = ∫ x, g (-x) := by
      congr 1
      funext x
      simp only [g, star_mul]
      have hExp :
          star (Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)) =
            Complex.exp (((-2 * Real.pi * (-x) * ξ : ℝ) : ℂ) * Complex.I) := by
        calc
          _ = Complex.exp
              (star (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)) :=
                (Complex.exp_conj _).symm
          _ = _ := by
            congr 1
            calc
              star (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) =
                  star Complex.I * star ((-2 * Real.pi * x * ξ : ℝ) : ℂ) := star_mul _ _
              _ = (-Complex.I) * ((-2 * Real.pi * x * ξ : ℝ) : ℂ) :=
                congrArg₂ (fun a b : ℂ => a * b) Complex.conj_I (Complex.conj_ofReal _)
              _ = ((-2 * Real.pi * (-x) * ξ : ℝ) : ℂ) * Complex.I := by
                push_cast
                ring
      rw [hExp, q3FourierKernel_even]
      have hreal : star (q3Kernel x : ℂ) = (q3Kernel x : ℂ) :=
        Complex.conj_ofReal _
      calc
        _ = (q3Kernel x : ℂ) *
            Complex.exp (↑(-2 * Real.pi * -x * ξ) * Complex.I) := by rw [hreal]
        _ = _ := by ring
    _ = ∫ x, g x := by
      simpa [g] using Measure.integral_comp_mul_left g (-1)

private lemma q3KernelD1_zero_of_abs_ge {x : ℝ} (hx : 1 / 2 ≤ |x|) :
    q3KernelD1 x = 0 := by
  have hp : 1 - 4 * x ^ 2 ≤ 0 := by nlinarith [sq_abs x]
  simp [q3KernelD1, max_eq_right hp]

private theorem q3FourierD1_eq_deriv : deriv q3Kernel = q3KernelD1 := by
  funext x
  exact (q3Kernel_hasDerivAt x).deriv

private theorem q3FourierD1_hasDeriv (x : ℝ) :
    HasDerivAt (deriv q3Kernel) (deriv (deriv q3Kernel) x) x := by
  exact (q3Kernel_contDiff_two.differentiable_deriv_two x).hasDerivAt

private theorem q3FourierD1_endpoint_zero {L : ℝ} (hL : 2 < L) :
    deriv q3Kernel (-L / 2) = 0 ∧ deriv q3Kernel (L / 2) = 0 := by
  rw [q3FourierD1_eq_deriv]
  constructor
  · apply q3KernelD1_zero_of_abs_ge
    rw [abs_of_nonpos (by linarith : -L / 2 ≤ 0)]
    linarith
  · apply q3KernelD1_zero_of_abs_ge
    rw [abs_of_nonneg (by linarith : 0 ≤ L / 2)]
    linarith

private noncomputable def q3FourierSecondDerivative (x : ℝ) : ℝ :=
  deriv (deriv q3Kernel) x

private theorem q3FourierSecondDerivative_continuous :
    Continuous q3FourierSecondDerivative := by
  unfold q3FourierSecondDerivative
  have hq1 : ContDiff ℝ 1 (deriv q3Kernel) := by
    simpa using q3Kernel_contDiff_two.deriv'
  exact hq1.continuous_deriv (by norm_num)

private theorem q3FourierSecondCoeff_norm_le {L B : ℝ} (hL : 2 < L)
    [Fact (0 < L)]
    (hB : ∀ x ∈ Set.Icc (-L / 2) (L / 2),
      ‖q3FourierSecondDerivative x‖ ≤ B) (n : ℤ) :
    ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
      (fun x : ℝ => ((q3FourierSecondDerivative x : ℝ) : ℂ)) n‖ ≤ B := by
  have hlen : L / 2 - (-L / 2) = L := by ring
  have hpos : 0 < L := lt_trans (by norm_num) hL
  rw [fourierCoeffOn_eq_integral, hlen, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have hmono : ∫ x in (-L / 2)..(L / 2),
      ‖q3FourierSecondDerivative x‖ ≤ L * B := by
    have hcont := q3FourierSecondDerivative_continuous.norm
    have h :=
      intervalIntegral.integral_mono_on (by linarith : -L / 2 ≤ L / 2)
        (hcont.intervalIntegrable (μ := volume) _ _) intervalIntegrable_const fun x hx => hB x hx
    simpa [hlen, intervalIntegral.integral_const] using h
  calc
    (1 / L) * ‖∫ x in -L / 2..L / 2,
        fourier (-n) (x : AddCircle L) •
          ((q3FourierSecondDerivative x : ℝ) : ℂ)‖ ≤
        (1 / L) * ∫ x in -L / 2..L / 2,
          ‖fourier (-n) (x : AddCircle L) •
            ((q3FourierSecondDerivative x : ℝ) : ℂ)‖ :=
      mul_le_mul_of_nonneg_left
        (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (by positivity)
    _ = (1 / L) * ∫ x in -L / 2..L / 2, ‖q3FourierSecondDerivative x‖ := by
      congr 2
      funext x
      have hunit : ‖fourier (-n) (x : AddCircle L)‖ = 1 := by
        rw [fourier_coe_apply]
        have harg : 2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) * (x : ℂ) / (L : ℂ) =
            ((-2 * Real.pi * (n : ℝ) * x / L : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [harg, Complex.norm_exp_ofReal_mul_I]
      calc
        _ = ‖fourier (-n) (x : AddCircle L)‖ *
            ‖((q3FourierSecondDerivative x : ℝ) : ℂ)‖ := norm_smul _ _
        _ = ‖q3FourierSecondDerivative x‖ := by
          rw [hunit]
          simp [Complex.norm_real]
    _ ≤ (1 / L) * (L * B) := mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = B := by field_simp [ne_of_gt hpos]

private theorem q3FourierCoeffOn_first_derivative {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n =
      (L / (2 * Real.pi * Complex.I * n)) *
        fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
          (fun x : ℝ => ((q3KernelD1 x : ℝ) : ℂ)) n := by
  let a : ℝ := -L / 2
  let b : ℝ := L / 2
  have hab : a < b := by dsimp [a, b]; linarith
  have hlen : (b : ℂ) - a = L := by dsimp [a, b]; push_cast; ring
  have hqa : q3Kernel a = 0 := by
    apply q3Kernel_eq_zero_of_abs_ge
    dsimp [a]
    rw [abs_of_nonpos (by linarith : -L / 2 ≤ 0)]
    linarith
  have hqb : q3Kernel b = 0 := by
    apply q3Kernel_eq_zero_of_abs_ge
    dsimp [b]
    rw [abs_of_nonneg (by linarith : 0 ≤ L / 2)]
    linarith
  have hcont : ContinuousOn (fun x : ℝ => (q3Kernel x : ℂ)) (uIcc a b) :=
    (Complex.continuous_ofReal.comp q3Kernel_continuous).continuousOn
  have hq1 : Continuous (deriv q3Kernel) :=
    q3Kernel_contDiff_two.continuous_deriv (by norm_num)
  have hq1D1 : Continuous q3KernelD1 := by
    simpa only [← q3FourierD1_eq_deriv] using hq1
  have hq1Int : IntervalIntegrable (fun x : ℝ => ((q3KernelD1 x : ℝ) : ℂ))
      volume a b := by
    exact (Complex.continuous_ofReal.comp hq1D1).intervalIntegrable a b
  have hformula := fourierCoeffOn_of_hasDeriv_right hab hn hcont
    (fun x _ => (q3Kernel_hasDerivAt x).ofReal_comp.hasDerivWithinAt) hq1Int
  have hformula' :
      fourierCoeffOn hab (fun x : ℝ => (q3Kernel x : ℂ)) n =
        1 / (-2 * Real.pi * Complex.I * n) *
          (-(L : ℂ) * fourierCoeffOn hab
            (fun x : ℝ => ((q3KernelD1 x : ℝ) : ℂ)) n) := by
    rw [hformula, hqa, hqb, hlen]
    simp only [sub_self, mul_zero, zero_sub]
    field_simp [hn, Complex.I_ne_zero, Real.pi_ne_zero]
  calc
    _ = 1 / (-2 * Real.pi * Complex.I * n) *
        (-(L : ℂ) * fourierCoeffOn hab
          (fun x : ℝ => ((q3KernelD1 x : ℝ) : ℂ)) n) := hformula'
    _ = (L / (2 * Real.pi * Complex.I * n)) *
        fourierCoeffOn hab (fun x : ℝ => ((q3KernelD1 x : ℝ) : ℂ)) n := by
          field_simp [hn, Complex.I_ne_zero, Real.pi_ne_zero]

private theorem q3FourierCoeffOn_second_derivative {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => ((q3KernelD1 x : ℝ) : ℂ)) n =
      (L / (2 * Real.pi * Complex.I * n)) *
        fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
          (fun x : ℝ => ((q3FourierSecondDerivative x : ℝ) : ℂ)) n := by
  let a : ℝ := -L / 2
  let b : ℝ := L / 2
  have hab : a < b := by dsimp [a, b]; linarith
  have hlen : (b : ℂ) - a = L := by dsimp [a, b]; push_cast; ring
  have hbound := q3FourierD1_endpoint_zero hL
  have hq1D1 : Continuous q3KernelD1 := by
    simpa only [← q3FourierD1_eq_deriv] using
      q3Kernel_contDiff_two.continuous_deriv (by norm_num)
  have hcont : ContinuousOn (fun x : ℝ => ((q3KernelD1 x : ℝ) : ℂ)) (uIcc a b) :=
    (Complex.continuous_ofReal.comp hq1D1).continuousOn
  have hq2Int : IntervalIntegrable
      (fun x : ℝ => ((q3FourierSecondDerivative x : ℝ) : ℂ)) volume a b := by
    exact (Complex.continuous_ofReal.comp q3FourierSecondDerivative_continuous).intervalIntegrable a b
  have hD1deriv (x : ℝ) :
      HasDerivAt (fun y : ℝ => (q3KernelD1 y : ℂ))
        (q3FourierSecondDerivative x : ℂ) x := by
    have hbase := (q3FourierD1_hasDeriv x).ofReal_comp
    convert hbase using 1
    · funext y
      simp only [q3FourierD1_eq_deriv]
    · simp [q3FourierSecondDerivative]
  have hformula := fourierCoeffOn_of_hasDeriv_right hab hn hcont
    (fun x _ => (hD1deriv x).hasDerivWithinAt) hq2Int
  have hformula' :
      fourierCoeffOn hab (fun x : ℝ => ((q3KernelD1 x : ℝ) : ℂ)) n =
        1 / (-2 * Real.pi * Complex.I * n) *
          (-(L : ℂ) * fourierCoeffOn hab
            (fun x : ℝ => ((q3FourierSecondDerivative x : ℝ) : ℂ)) n) := by
    rw [hformula]
    have hboundD1 : q3KernelD1 a = 0 ∧ q3KernelD1 b = 0 := by
      simpa only [q3FourierD1_eq_deriv] using hbound
    simp only [hboundD1.1, hboundD1.2, hlen]
    simp only [sub_self, mul_zero, zero_sub]
    field_simp [hn, Complex.I_ne_zero, Real.pi_ne_zero]
  calc
    _ = 1 / (-2 * Real.pi * Complex.I * n) *
        (-(L : ℂ) * fourierCoeffOn hab
          (fun x : ℝ => ((q3FourierSecondDerivative x : ℝ) : ℂ)) n) := hformula'
    _ = (L / (2 * Real.pi * Complex.I * n)) *
        fourierCoeffOn hab (fun x : ℝ => ((q3FourierSecondDerivative x : ℝ) : ℂ)) n := by
      field_simp [hn, Complex.I_ne_zero, Real.pi_ne_zero]

private theorem q3FourierSecondDerivative_bounded {L : ℝ} :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Set.Icc (-L / 2) (L / 2),
      ‖q3FourierSecondDerivative x‖ ≤ B := by
  have hcompact : IsCompact (Set.Icc (-L / 2) (L / 2)) := isCompact_Icc
  have hcont : ContinuousOn (fun x : ℝ => ‖q3FourierSecondDerivative x‖)
      (Set.Icc (-L / 2) (L / 2)) :=
    q3FourierSecondDerivative_continuous.norm.continuousOn
  have hbdd := hcompact.bddAbove_image hcont
  obtain ⟨B, hB0, hB⟩ := hbdd.exists_ge 0
  refine ⟨B, hB0, ?_⟩
  intro x hx
  exact hB _ ⟨x, hx, rfl⟩

private theorem q3FourierKernelCoeffOn_norm_le_inv_sq {L B : ℝ} (hL : 2 < L)
    [Fact (0 < L)]
    (hB : ∀ x ∈ Set.Icc (-L / 2) (L / 2),
      ‖q3FourierSecondDerivative x‖ ≤ B)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
      (fun x : ℝ => (q3Kernel x : ℂ)) n‖ ≤
        (B * (L / (2 * Real.pi)) ^ 2) / (n : ℝ) ^ 2 := by
  have hpos : 0 < L := lt_trans (by norm_num) hL
  have hcoef := q3FourierSecondCoeff_norm_le hL hB n
  have hfactor :
      ‖(L : ℂ) / (2 * Real.pi * Complex.I * n)‖ =
        L / (2 * Real.pi * |(n : ℝ)|) := by
    simp [Complex.norm_I, Real.norm_eq_abs,
      abs_of_pos hpos]
  rw [q3FourierCoeffOn_first_derivative hL hn,
    q3FourierCoeffOn_second_derivative hL hn]
  calc
    _ = ‖(L : ℂ) / (2 * Real.pi * Complex.I * n)‖ ^ 2 *
        ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
          (fun x : ℝ => ((q3FourierSecondDerivative x : ℝ) : ℂ)) n‖ := by
      rw [norm_mul, norm_mul]
      ring
    _ ≤ (L / (2 * Real.pi * |(n : ℝ)|)) ^ 2 * B := by
      rw [hfactor]
      exact mul_le_mul_of_nonneg_left hcoef (sq_nonneg _)
    _ = (B * (L / (2 * Real.pi)) ^ 2) / (n : ℝ) ^ 2 := by
      have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
      have hnAbs : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr hnR
      field_simp [hnR, hnAbs, Real.pi_ne_zero]
      rw [sq_abs]
      ring

private theorem q3Int_shifted_abs_le {n : ℤ} (hn : n ≠ 0) :
    |(n : ℝ) + 1 / 2| ≤ (3 / 2 : ℝ) * |(n : ℝ)| := by
  have hnabs : 1 ≤ |(n : ℝ)| := by
    have hsign : (n : ℤ) ≤ -1 ∨ 1 ≤ n := by omega
    rcases hsign with hnneg | hnpos
    · have hnreal : (n : ℝ) ≤ -1 := by exact_mod_cast hnneg
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      rw [abs_of_nonneg (by linarith)]
      linarith
  calc
    |(n : ℝ) + 1 / 2| ≤ |(n : ℝ)| + |(1 / 2 : ℝ)| := abs_add_le _ _
    _ = |(n : ℝ)| + 1 / 2 := by norm_num
    _ ≤ |(n : ℝ)| + (1 / 2) * |(n : ℝ)| := by nlinarith
    _ = (3 / 2 : ℝ) * |(n : ℝ)| := by ring

private theorem q3Int_inv_sq_le_shifted {C : ℝ} (hC : 0 ≤ C) {n : ℤ}
    (hn : n ≠ 0) :
    C / (n : ℝ) ^ 2 ≤ (9 / 4 * C) / |(n : ℝ) + 1 / 2| ^ 2 := by
  have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hnabs : 0 < |(n : ℝ)| := abs_pos.mpr hnR
  have hshiftpos : 0 < |(n : ℝ) + 1 / 2| := by
    have hhalf : (1 / 2 : ℝ) ≤ |(n : ℝ) + 1 / 2| := by
      have hnabsInt : (1 : ℝ) ≤ |(n : ℝ)| := by
        have hsign : (n : ℤ) ≤ -1 ∨ 1 ≤ n := by omega
        rcases hsign with hnneg | hnpos
        · have hnreal : (n : ℝ) ≤ -1 := by exact_mod_cast hnneg
          rw [abs_of_nonpos (by linarith)]
          linarith
        · have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
          rw [abs_of_nonneg (by linarith)]
          linarith
      calc
        (1 / 2 : ℝ) ≤ |(n : ℝ)| - 1 / 2 := by linarith
        _ ≤ |(n : ℝ) + 1 / 2| := by
          have htri := abs_add_le ((n : ℝ) + 1 / 2) (-(1 / 2 : ℝ))
          have heq : (n : ℝ) = ((n : ℝ) + 1 / 2) + (-(1 / 2 : ℝ)) := by ring
          rw [heq] at htri
          norm_num at htri ⊢
          linarith
    linarith
  rw [div_le_div_iff₀ (sq_pos_of_ne_zero hnR)
    (sq_pos_of_ne_zero (ne_of_gt hshiftpos))]
  have hsquare : |(n : ℝ) + 1 / 2| ^ 2 ≤
      ((3 / 2 : ℝ) * |(n : ℝ)|) ^ 2 := by
    exact pow_le_pow_left₀ (abs_nonneg _) (q3Int_shifted_abs_le hn) 2
  calc
    C * |(n : ℝ) + 1 / 2| ^ 2 ≤ C * ((3 / 2 : ℝ) * |(n : ℝ)|) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hC
    _ = (9 / 4 * C) * (n : ℝ) ^ 2 := by
      rw [mul_pow, sq_abs]
      ring

private theorem q3FourierKernelCoeffOn_norm_le_shifted {L B : ℝ} (hL : 2 < L)
    [Fact (0 < L)]
    (hB : ∀ x ∈ Set.Icc (-L / 2) (L / 2),
      ‖q3FourierSecondDerivative x‖ ≤ B)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
      (fun x : ℝ => (q3Kernel x : ℂ)) n‖ ≤
        (9 / 4 * (B * (L / (2 * Real.pi)) ^ 2)) / |(n : ℝ) + 1 / 2| ^ 2 := by
  calc
    _ ≤ (B * (L / (2 * Real.pi)) ^ 2) / (n : ℝ) ^ 2 :=
      q3FourierKernelCoeffOn_norm_le_inv_sq hL hB hn
    _ ≤ (9 / 4 * (B * (L / (2 * Real.pi)) ^ 2)) /
        |(n : ℝ) + 1 / 2| ^ 2 := by
      apply q3Int_inv_sq_le_shifted
      have hB0 : 0 ≤ B := by
        have hx : (0 : ℝ) ∈ Set.Icc (-L / 2) (L / 2) := by
          constructor <;> linarith
        exact le_trans (norm_nonneg _) (hB 0 hx)
      exact mul_nonneg hB0 (sq_nonneg _)
      exact hn

private theorem intShifted_invSq_summable (D : ℝ) :
    Summable (fun n : ℤ => D / |(n : ℝ) + 1 / 2| ^ 2) := by
  have hpowerR : Summable (fun n : ℤ =>
      1 / |(n : ℝ) + 1 / 2| ^ (2 : ℝ)) :=
    (Real.summable_one_div_int_add_rpow (1 / 2) (2 : ℝ)).2 (by norm_num)
  have hpower : Summable (fun n : ℤ => 1 / |(n : ℝ) + 1 / 2| ^ 2) := by
    simpa only [Real.rpow_ofNat] using hpowerR
  convert hpower.mul_left D using 1
  funext n
  simp [div_eq_mul_inv]

private theorem q3FourierKernelCoeffOn_summable_of_major {L D : ℝ} (hL : 2 < L)
    [Fact (0 < L)]
    (hmajor : Summable (fun n : ℤ => D / |(n : ℝ) + 1 / 2| ^ 2))
    (hbound : ∀ n : ℤ,
      ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n‖ ≤ D / |(n : ℝ) + 1 / 2| ^ 2) :
    Summable (fun n : ℤ =>
      ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n‖) := by
  apply Summable.of_norm_bounded hmajor
  intro n
  simpa only [norm_norm] using hbound n

private theorem q3FourierKernelCoeffOn_norm_le_shifted_of_D {L B D : ℝ}
    (hL : 2 < L) [Fact (0 < L)]
    (hB : ∀ x ∈ Set.Icc (-L / 2) (L / 2),
      ‖q3FourierSecondDerivative x‖ ≤ B)
    (hD : 9 / 4 * (B * (L / (2 * Real.pi)) ^ 2) ≤ D)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
      (fun x : ℝ => (q3Kernel x : ℂ)) n‖ ≤ D / |(n : ℝ) + 1 / 2| ^ 2 := by
  calc
    _ ≤ (9 / 4 * (B * (L / (2 * Real.pi)) ^ 2)) /
        |(n : ℝ) + 1 / 2| ^ 2 := q3FourierKernelCoeffOn_norm_le_shifted hL hB hn
    _ ≤ D / |(n : ℝ) + 1 / 2| ^ 2 :=
      div_le_div_of_nonneg_right hD (sq_nonneg _)

private theorem q3FourierKernelCoeffOn_summable {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] :
    Summable (fun n : ℤ =>
      ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n‖) := by
  obtain ⟨B, hB0, hB⟩ := q3FourierSecondDerivative_bounded (L := L)
  let C : ℝ := B * (L / (2 * Real.pi)) ^ 2
  let b : ℤ → ℂ := fun n =>
    fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
      (fun x : ℝ => (q3Kernel x : ℂ)) n
  let D : ℝ := max (9 / 4 * C) (‖b 0‖ / 4)
  have hD0 : ‖b 0‖ / 4 ≤ D := le_max_right _ _
  have hD1 : 9 / 4 * C ≤ D := le_max_left _ _
  have hmajor := intShifted_invSq_summable D
  apply q3FourierKernelCoeffOn_summable_of_major hL hmajor
  intro n
  by_cases hn : n = 0
  · subst n
    have hb0 : ‖b 0‖ ≤ 4 * D := by nlinarith
    calc
      ‖b 0‖ ≤ 4 * D := hb0
      _ = D / |(0 : ℝ) + 1 / 2| ^ 2 := by
        norm_num [div_eq_mul_inv]; ring
      _ ≤ D / |((0 : ℤ) : ℝ) + (1 / 2 : ℝ)| ^ 2 := by norm_num
  · have hD : 9 / 4 * (B * (L / (2 * Real.pi)) ^ 2) ≤ D := by
      simpa [C] using hD1
    simpa [b] using q3FourierKernelCoeffOn_norm_le_shifted_of_D hL hB hD hn

private theorem q3Kernel_norm_le_two (x : ℝ) : ‖q3Kernel x‖ ≤ 2 := by
  rw [q3Kernel_eq_positive_part, Real.norm_eq_abs]
  have hconst : Real.sqrt (3003 / 1024 : ℝ) ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> norm_num
  have hm0 : 0 ≤ max (1 - 4 * x ^ 2) 0 := le_max_right _ _
  have hm1 : max (1 - 4 * x ^ 2) 0 ≤ 1 := by
    apply max_le
    · nlinarith [sq_nonneg x]
    · norm_num
  have hm3 : max (1 - 4 * x ^ 2) 0 ^ 3 ≤ 1 := by
    calc
      _ ≤ 1 ^ 3 := pow_le_pow_left₀ hm0 hm1 3
      _ = 1 := by norm_num
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hm0 _))]
  exact (mul_le_mul hconst hm3 (by positivity) (by norm_num)).trans_eq (by norm_num)

private theorem q3FourierKernelCoeffOn_norm_le_two {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] (n : ℤ) :
    ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
      (fun x : ℝ => (q3Kernel x : ℂ)) n‖ ≤ 2 := by
  have hpos : 0 < L := lt_trans (by norm_num) hL
  have hlen : L / 2 - (-L / 2) = L := by ring
  rw [fourierCoeffOn_eq_integral, hlen, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have hmono : ∫ x in (-L / 2)..(L / 2), ‖q3Kernel x‖ ≤ L * 2 := by
    have hcont := q3Kernel_continuous.norm
    have h := intervalIntegral.integral_mono_on (by linarith : -L / 2 ≤ L / 2)
      (hcont.intervalIntegrable (μ := volume) _ _) intervalIntegrable_const
      fun x hx => q3Kernel_norm_le_two x
    simpa [hlen, intervalIntegral.integral_const] using h
  calc
    (1 / L) * ‖∫ x in -L / 2..L / 2,
        fourier (-n) (x : AddCircle L) • (q3Kernel x : ℂ)‖ ≤
        (1 / L) * ∫ x in -L / 2..L / 2,
          ‖fourier (-n) (x : AddCircle L) • (q3Kernel x : ℂ)‖ :=
      mul_le_mul_of_nonneg_left
        (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (by positivity)
    _ = (1 / L) * ∫ x in -L / 2..L / 2, ‖q3Kernel x‖ := by
      congr 2
      funext x
      rw [norm_smul]
      have hunit : ‖fourier (-n) (x : AddCircle L)‖ = 1 := by
        rw [fourier_coe_apply]
        have harg : 2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) * (x : ℂ) / (L : ℂ) =
            ((-2 * Real.pi * (n : ℝ) * x / L : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [harg, Complex.norm_exp_ofReal_mul_I]
      rw [hunit]
      simp [Complex.norm_real]
    _ ≤ (1 / L) * (L * 2) := mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = 2 := by field_simp [ne_of_gt hpos]

private noncomputable def q3CovPeriodization (L : ℝ) (hL : 2 < L)
    [Fact (0 < L)] : C(AddCircle L, ℂ) := by
  let a : ℝ := -L / 2
  have ha : 1 ≤ |a| := by
    dsimp [a]
    rw [abs_of_nonpos (by linarith : -L / 2 ≤ 0)]
    linarith
  have hb : 1 ≤ |a + L| := by
    dsimp [a]
    rw [show -L / 2 + L = L / 2 by ring,
      abs_of_nonneg (by linarith : 0 ≤ L / 2)]
    linarith
  have hend : (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)) a =
      (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)) (a + L) := by
    change (ASDExplicitGamma.q3Cov a : ℂ) = (ASDExplicitGamma.q3Cov (a + L) : ℂ)
    rw [ASDExplicitGamma.Model.q3Cov_zero_of_abs_ge_one ha,
      ASDExplicitGamma.Model.q3Cov_zero_of_abs_ge_one hb]
  have hcont : ContinuousOn (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ))
      (Icc a (a + L)) :=
    (Complex.continuous_ofReal.comp q3FourierCov_continuous).continuousOn
  exact ⟨AddCircle.liftIco L a (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)),
    AddCircle.liftIco_continuous hend hcont⟩

private noncomputable def q3CovFourierCoefficientReal (L : ℝ) [Fact (0 < L)]
    (n : ℤ) : ℝ :=
  L * ‖fourierCoeffOn (a := -L / 2) (b := L / 2)
    (by have hpos : 0 < L := Fact.out; linarith)
    (fun x : ℝ => (q3Kernel x : ℂ)) n‖ ^ 2

private theorem q3FourierKernelCoeffOn_star_eq {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] (n : ℤ) :
    star (fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
      (fun x : ℝ => (q3Kernel x : ℂ)) n) =
      fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n := by
  rw [q3FourierCoeffOn_eq_scaled_transform hL (q3FourierKernelCoeffOn_support hL) n]
  simp [q3FourierKernel_transform_real]

private theorem q3CovPeriodization_coeff_eq_centered {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] (n : ℤ) :
    fourierCoeff (q3CovPeriodization L hL) n =
      fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)) n := by
  change fourierCoeff
      (AddCircle.liftIco L (-L / 2)
        (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ))) n = _
  rw [fourierCoeff_eq_intervalIntegral _ n (-L / 2)]
  rw [fourierCoeffOn_eq_integral _ n (by linarith)]
  rw [show -L / 2 + L = L / 2 by ring,
    show L / 2 - (-L / 2) = L by ring]
  have hInt :
      ∫ x in (-L / 2)..(L / 2),
        fourier (-n) (x : AddCircle L) • AddCircle.liftIco L (-L / 2)
          (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)) (x : AddCircle L) =
      ∫ x in (-L / 2)..(L / 2),
        fourier (-n) (x : AddCircle L) • (ASDExplicitGamma.q3Cov x : ℂ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
    intro x hx
    change fourier (-n) (x : AddCircle L) • AddCircle.liftIco L (-L / 2)
        (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)) (x : AddCircle L) =
      fourier (-n) (x : AddCircle L) • (ASDExplicitGamma.q3Cov x : ℂ)
    have hx' : x ∈ Ioo (-L / 2) (-L / 2 + L) := by
      simpa only [show -L / 2 + L = L / 2 by ring] using hx
    rw [AddCircle.liftIco_coe_apply (Ioo_subset_Ico_self hx')]
  rw [hInt]

private theorem q3FourierCoeff_covPeriodization_eq_real {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] (n : ℤ) :
    fourierCoeff (q3CovPeriodization L hL) n =
      (q3CovFourierCoefficientReal L n : ℂ) := by
  calc
    fourierCoeff (q3CovPeriodization L hL) n =
        fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
          (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)) n :=
      q3CovPeriodization_coeff_eq_centered hL n
    _ = (L : ℂ) *
        (fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
          (fun x : ℝ => (q3Kernel x : ℂ)) n) ^ 2 :=
      q3FourierCoeffOn_cov_eq_L_mul_kernel_sq hL n
  have hreal := Complex.conj_eq_iff_re.mp
    (q3FourierKernelCoeffOn_star_eq hL n)
  have hαsq :
      (fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n) ^ 2 =
      (‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n‖ ^ 2 : ℂ) := by
    rw [← hreal]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast (sq_abs
      (fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n).re).symm
  rw [q3CovFourierCoefficientReal]
  rw [hαsq]
  push_cast
  ring

private theorem q3CovPeriodization_fourierCoeff_summable {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] : Summable (fourierCoeff (q3CovPeriodization L hL)) := by
  have hα := q3FourierKernelCoeffOn_summable hL
  have hmajor : Summable (fun n : ℤ => (2 * L) *
      ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n‖) := hα.mul_left (2 * L)
  apply Summable.of_norm_bounded hmajor
  intro n
  rw [q3FourierCoeff_covPeriodization_eq_real hL n]
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hLpos : 0 < L := lt_trans (by norm_num) hL
  have hr : ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
      (fun x : ℝ => (q3Kernel x : ℂ)) n‖ ≤ 2 := q3FourierKernelCoeffOn_norm_le_two hL n
  have hr0 : 0 ≤ ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
      (fun x : ℝ => (q3Kernel x : ℂ)) n‖ := norm_nonneg _
  change |q3CovFourierCoefficientReal L n| ≤ (2 * L) *
    ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
      (fun x : ℝ => (q3Kernel x : ℂ)) n‖
  rw [q3CovFourierCoefficientReal,
    abs_of_nonneg (mul_nonneg hLpos.le (sq_nonneg _))]
  have hrsq : ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
      (fun x : ℝ => (q3Kernel x : ℂ)) n‖ ^ 2 ≤
      2 * ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n‖ := by
    have hr2 : 0 ≤ 2 - ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n‖ := by linarith
    nlinarith [mul_nonneg hr0 hr2]
  calc
    L * ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n‖ ^ 2 ≤
      L * (2 * ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n‖) := by
          exact mul_le_mul_of_nonneg_left hrsq hLpos.le
    _ = (2 * L) * ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n‖ := by ring

private theorem q3CovFourierCoefficientReal_nonneg {L : ℝ} [Fact (0 < L)] (_hL : 2 < L)
    (n : ℤ) : 0 ≤ q3CovFourierCoefficientReal L n := by
  have hLpos : 0 < L := Fact.out
  exact mul_nonneg hLpos.le (sq_nonneg _)

private theorem q3CovFourierCoefficientReal_summable {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] : Summable (q3CovFourierCoefficientReal L) := by
  have hcoeff := q3CovPeriodization_fourierCoeff_summable hL
  have hnorm (n : ℤ) :
      ‖fourierCoeff (q3CovPeriodization L hL) n‖ = q3CovFourierCoefficientReal L n := by
    rw [q3FourierCoeff_covPeriodization_eq_real hL n,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (q3CovFourierCoefficientReal_nonneg hL n)]
  exact hcoeff.norm.congr hnorm

private theorem q3CovFourierSqrtCoefficient_summable {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] : Summable (fun n : ℤ => Real.sqrt (q3CovFourierCoefficientReal L n)) := by
  have hLpos : 0 < L := Fact.out
  have hα := q3FourierKernelCoeffOn_summable hL
  have hsqrt (n : ℤ) : Real.sqrt (q3CovFourierCoefficientReal L n) =
      Real.sqrt L * ‖fourierCoeffOn (a := -L / 2) (b := L / 2) (by linarith)
        (fun x : ℝ => (q3Kernel x : ℂ)) n‖ := by
    rw [q3CovFourierCoefficientReal, Real.sqrt_mul hLpos.le,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hscaled := hα.mul_left (Real.sqrt L)
  exact hscaled.congr fun n => (hsqrt n).symm

private theorem summable_finite_fiber {α σ : Type*} [Fintype σ]
    {f : α → ℝ} (hf0 : ∀ a, 0 ≤ f a) (hf : Summable f) :
    Summable (fun p : α × σ => f p.1) := by
  apply (summable_prod_of_nonneg (fun p : α × σ => hf0 p.1)).2
  constructor
  · intro a
    exact Summable.of_finite
  · have hscaled : Summable (fun a : α => (Fintype.card σ : ℝ) * f a) :=
      hf.mul_left (Fintype.card σ : ℝ)
    convert hscaled using 1
    funext a
    simp

private noncomputable def q3CircleMode {L : ℝ} (n : ℤ) (s : Fin 2)
    (t : AddCircle L) : ℝ :=
  if s = 0 then (fourier n t).re else (fourier n t).im

private theorem q3CircleMode_continuous {L : ℝ} (n : ℤ) (s : Fin 2) :
    Continuous (q3CircleMode (L := L) n s) := by
  unfold q3CircleMode
  split_ifs
  ·
    exact Complex.continuous_re.comp (fourier n).continuous
  ·
    exact Complex.continuous_im.comp (fourier n).continuous

private theorem q3CircleMode_abs_le_one {L : ℝ} [Fact (0 < L)]
    (n : ℤ) (s : Fin 2) (t : AddCircle L) :
    |q3CircleMode n s t| ≤ 1 := by
  have hnorm : ‖fourier n t‖ = 1 := by
    simp [fourier_apply]
  by_cases hs : s = 0
  · simp [q3CircleMode, hs]
    exact (Complex.abs_re_le_norm _).trans_eq hnorm
  · simp [q3CircleMode, hs]
    exact (Complex.abs_im_le_norm _).trans_eq hnorm

private theorem q3CovPeriodization_real_fourier {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] (t : AddCircle L) :
    (q3CovPeriodization L hL t).re =
      ∑' n : ℤ, q3CovFourierCoefficientReal L n * (fourier n t).re := by
  have hcoeff := q3CovPeriodization_fourierCoeff_summable hL
  have hpoint : HasSum
      (fun n : ℤ => fourierCoeff (q3CovPeriodization L hL) n * fourier n t)
      (q3CovPeriodization L hL t) := by
    simpa only [smul_eq_mul] using
      (has_pointwise_sum_fourier_series_of_summable hcoeff t)
  have hreal : HasSum
      (fun n : ℤ => q3CovFourierCoefficientReal L n * (fourier n t).re)
      (q3CovPeriodization L hL t).re := by
    convert Complex.hasSum_re hpoint using 1
    · funext n
      rw [q3FourierCoeff_covPeriodization_eq_real hL n]
      simp [Complex.mul_re]
  exact hreal.tsum_eq.symm

private noncomputable def q3CircleFeature {L : ℝ} [Fact (0 < L)]
    (p : ℤ × Fin 2) (t : AddCircle L) : ℝ :=
  Real.sqrt (q3CovFourierCoefficientReal L p.1) * q3CircleMode p.1 p.2 t

private theorem q3CircleFeature_product_summable {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] (t u : AddCircle L) :
    Summable (fun p : ℤ × Fin 2 => q3CircleFeature p t * q3CircleFeature p u) := by
  have hcoeff := q3CovFourierCoefficientReal_summable hL
  have hmajor : Summable (fun p : ℤ × Fin 2 => q3CovFourierCoefficientReal L p.1) :=
    summable_finite_fiber (fun n => q3CovFourierCoefficientReal_nonneg hL n) hcoeff
  apply Summable.of_norm_bounded hmajor
  intro p
  rw [Real.norm_eq_abs]
  let a := q3CovFourierCoefficientReal L p.1
  have ha : 0 ≤ a := q3CovFourierCoefficientReal_nonneg hL p.1
  have hst : Real.sqrt a * Real.sqrt a = a := by
    rw [← sq, Real.sq_sqrt ha]
  have hprod : q3CircleFeature p t * q3CircleFeature p u =
      a * q3CircleMode p.1 p.2 t * q3CircleMode p.1 p.2 u := by
    dsimp [q3CircleFeature, a]
    calc
      _ = (Real.sqrt (q3CovFourierCoefficientReal L p.1) *
          Real.sqrt (q3CovFourierCoefficientReal L p.1)) *
          q3CircleMode p.1 p.2 t * q3CircleMode p.1 p.2 u := by ring
      _ = _ := by rw [hst]
  rw [hprod, abs_mul, abs_mul, abs_of_nonneg ha]
  calc
    (q3CovFourierCoefficientReal L p.1 *
        |q3CircleMode p.1 p.2 t|) * |q3CircleMode p.1 p.2 u| ≤
      (q3CovFourierCoefficientReal L p.1 * 1) * 1 := by
        gcongr
        · exact q3CircleMode_abs_le_one _ _ _
        · exact q3CircleMode_abs_le_one _ _ _
    _ = q3CovFourierCoefficientReal L p.1 := by ring

private theorem q3CircleMode_product_sum {L : ℝ} (n : ℤ) (t u : AddCircle L) :
    ∑ s : Fin 2, q3CircleMode n s t * q3CircleMode n s u =
      (fourier n t * star (fourier n u)).re := by
  simp [Fin.sum_univ_two, q3CircleMode, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]

private theorem q3Circle_fourier_kernel {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] (t u : AddCircle L) :
    ∑' p : ℤ × Fin 2, q3CircleFeature p t * q3CircleFeature p u =
      (q3CovPeriodization L hL (t - u)).re := by
  have hsum := q3CircleFeature_product_summable hL t u
  have hfiber (n : ℤ) : Summable
      (fun s : Fin 2 => q3CircleFeature (n, s) t * q3CircleFeature (n, s) u) :=
    Summable.of_finite
  have hinner (n : ℤ) :
      ∑' s : Fin 2, q3CircleFeature (n, s) t * q3CircleFeature (n, s) u =
        q3CovFourierCoefficientReal L n * (fourier n (t - u)).re := by
    have hchar : fourier n (t - u) = fourier n t * fourier (-n) u := by
      rw [fourier_apply, fourier_apply, fourier_apply]
      rw [zsmul_sub, neg_zsmul, sub_eq_add_neg,
        AddCircle.toCircle_add, AddCircle.toCircle_neg]
      simp
    have hneg : star (fourier n u) = fourier (-n) u := by
      exact (fourier_neg (n := n) (x := u)).symm
    rw [tsum_fintype]
    have hterms (s : Fin 2) :
        q3CircleFeature (n, s) t * q3CircleFeature (n, s) u =
          q3CovFourierCoefficientReal L n *
            (q3CircleMode n s t * q3CircleMode n s u) := by
      simp only [q3CircleFeature]
      have hroot : Real.sqrt (q3CovFourierCoefficientReal L n) *
          Real.sqrt (q3CovFourierCoefficientReal L n) =
            q3CovFourierCoefficientReal L n := by
        rw [← sq, Real.sq_sqrt (q3CovFourierCoefficientReal_nonneg hL n)]
      calc
        _ = (Real.sqrt (q3CovFourierCoefficientReal L n) *
            Real.sqrt (q3CovFourierCoefficientReal L n)) *
            q3CircleMode n s t * q3CircleMode n s u := by ring
        _ = _ := by rw [hroot]; ring
    calc
      ∑ s : Fin 2, q3CircleFeature (n, s) t * q3CircleFeature (n, s) u =
          q3CovFourierCoefficientReal L n *
            ∑ s : Fin 2, q3CircleMode n s t * q3CircleMode n s u := by
              simp_rw [hterms]
              rw [← Finset.mul_sum]
      _ = q3CovFourierCoefficientReal L n *
          (fourier n t * star (fourier n u)).re := by rw [q3CircleMode_product_sum]
      _ = q3CovFourierCoefficientReal L n * (fourier n (t - u)).re := by
        rw [hneg, ← hchar]
  have hsum' :
      ∑' n : ℤ, ∑' s : Fin 2,
          q3CircleFeature (n, s) t * q3CircleFeature (n, s) u =
        ∑' n : ℤ, q3CovFourierCoefficientReal L n * (fourier n (t - u)).re := by
    apply tsum_congr
    exact hinner
  calc
    _ = ∑' n : ℤ, ∑' s : Fin 2,
        q3CircleFeature (n, s) t * q3CircleFeature (n, s) u :=
          hsum.tsum_prod' hfiber
    _ = ∑' n : ℤ, q3CovFourierCoefficientReal L n *
        (fourier n (t - u)).re := by
          apply tsum_congr
          exact hinner
    _ = (q3CovPeriodization L hL (t - u)).re :=
          (q3CovPeriodization_real_fourier hL (t - u)).symm

/-- Indices for the real cosine/sine products in the two coordinates. -/
private abbrev Q3FourierFeatureIndex := (ℤ × Fin 2) × (ℤ × Fin 2)

/-- The two-dimensional real feature associated with the Fourier modes of the periodized q3
covariance. -/
private noncomputable def q3FourierFeature {K : Set (Homogenization.Vec 2)} [CompactSpace (↥K)]
    (L h : ℝ) [Fact (0 < L)] (p : Q3FourierFeatureIndex) : C(↥K, ℝ) := by
  let c : ℝ := h * (Real.sqrt (q3CovFourierCoefficientReal L p.1.1) *
    Real.sqrt (q3CovFourierCoefficientReal L p.2.1))
  let coord (k : Fin 2) : C(↥K, AddCircle L) := {
    toFun := fun x => (((x : Homogenization.Vec 2) k : ℝ) : AddCircle L)
    continuous_toFun := (AddCircle.continuous_mk' (𝕜 := ℝ) (p := L)).comp
      ((continuous_apply k).comp continuous_subtype_val)
  }
  let mode0 : ↥K → ℝ := fun x => q3CircleMode p.1.1 p.1.2 (coord 0 x)
  let mode1 : ↥K → ℝ := fun x => q3CircleMode p.2.1 p.2.2 (coord 1 x)
  have hmode0 : Continuous mode0 :=
    (q3CircleMode_continuous p.1.1 p.1.2).comp (coord 0).continuous
  have hmode1 : Continuous mode1 :=
    (q3CircleMode_continuous p.2.1 p.2.2).comp (coord 1).continuous
  exact ⟨fun x => c * (mode0 x * mode1 x), continuous_const.mul (hmode0.mul hmode1)⟩

private theorem q3FourierFeature_apply {K : Set (Homogenization.Vec 2)}
    [CompactSpace (↥K)] {L h : ℝ} [Fact (0 < L)]
    (p : Q3FourierFeatureIndex) (x : ↥K) :
    q3FourierFeature (K := K) L h p x =
      h * (Real.sqrt (q3CovFourierCoefficientReal L p.1.1) *
        Real.sqrt (q3CovFourierCoefficientReal L p.2.1)) *
        (q3CircleMode p.1.1 p.1.2
            (((x : Homogenization.Vec 2) 0 : ℝ) : AddCircle L) *
          q3CircleMode p.2.1 p.2.2
            (((x : Homogenization.Vec 2) 1 : ℝ) : AddCircle L)) := by
  rfl

private theorem q3FourierSqrtMode_summable {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] :
    Summable (fun p : ℤ × Fin 2 => Real.sqrt (q3CovFourierCoefficientReal L p.1)) := by
  exact summable_finite_fiber (fun n => Real.sqrt_nonneg _)
    (q3CovFourierSqrtCoefficient_summable hL)

private theorem q3FourierSqrtProductIndex_summable {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] :
    Summable (fun p : Q3FourierFeatureIndex =>
      Real.sqrt (q3CovFourierCoefficientReal L p.1.1) *
        Real.sqrt (q3CovFourierCoefficientReal L p.2.1)) := by
  let f : ℤ × Fin 2 → ℝ := fun p => Real.sqrt (q3CovFourierCoefficientReal L p.1)
  have hf := q3FourierSqrtMode_summable hL
  have hp : Summable (fun p : Q3FourierFeatureIndex => f p.1 * f p.2) := by
    apply (summable_prod_of_nonneg (fun p : Q3FourierFeatureIndex =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
    constructor
    · intro p
      exact hf.mul_left (f p)
    · have houter : Summable (fun p : ℤ × Fin 2 => f p * ∑' q : ℤ × Fin 2, f q) :=
        hf.mul_right (∑' q : ℤ × Fin 2, f q)
      convert houter using 1
      funext p
      exact hf.tsum_mul_left (f p)
  exact hp.congr fun p => by rfl

private theorem q3FourierFeature_norm_le {K : Set (Homogenization.Vec 2)}
    [CompactSpace (↥K)] {L h : ℝ} [Fact (0 < L)] (hh : 0 ≤ h)
    (p : Q3FourierFeatureIndex) :
    ‖q3FourierFeature (K := K) L h p‖ ≤
      h * (Real.sqrt (q3CovFourierCoefficientReal L p.1.1) *
        Real.sqrt (q3CovFourierCoefficientReal L p.2.1)) := by
  let c := h * (Real.sqrt (q3CovFourierCoefficientReal L p.1.1) *
    Real.sqrt (q3CovFourierCoefficientReal L p.2.1))
  have hc : 0 ≤ c := mul_nonneg hh (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [ContinuousMap.norm_le (q3FourierFeature (K := K) L h p) hc]
  intro x
  rw [Real.norm_eq_abs]
  change |c * (q3CircleMode p.1.1 p.1.2
      (((x : Homogenization.Vec 2) 0 : ℝ) : AddCircle L) *
    q3CircleMode p.2.1 p.2.2
      (((x : Homogenization.Vec 2) 1 : ℝ) : AddCircle L))| ≤ c
  have hm0 := q3CircleMode_abs_le_one p.1.1 p.1.2
    (((x : Homogenization.Vec 2) 0 : ℝ) : AddCircle L)
  have hm1 := q3CircleMode_abs_le_one p.2.1 p.2.2
    (((x : Homogenization.Vec 2) 1 : ℝ) : AddCircle L)
  calc
    _ = c * (|q3CircleMode p.1.1 p.1.2
          (((x : Homogenization.Vec 2) 0 : ℝ) : AddCircle L)| *
        |q3CircleMode p.2.1 p.2.2
          (((x : Homogenization.Vec 2) 1 : ℝ) : AddCircle L)|) := by
            rw [abs_mul, abs_of_nonneg hc, abs_mul]
    _ ≤ c * (1 * 1) := by gcongr
    _ = c := by ring

private theorem q3FourierFeature_norm_summable {K : Set (Homogenization.Vec 2)}
    [CompactSpace (↥K)] {L h : ℝ} (hL : 2 < L) [Fact (0 < L)] (hh : 0 ≤ h) :
    Summable (fun p : Q3FourierFeatureIndex =>
      ‖q3FourierFeature (K := K) L h p‖) := by
  have hbase := q3FourierSqrtProductIndex_summable (L := L) hL
  have hmajor := hbase.mul_left h
  apply Summable.of_norm_bounded hmajor
  intro p
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    (q3FourierFeature_norm_le (K := K) (L := L) (h := h) hh p)

private theorem summable_prod_of_summable_abs {α β : Type*}
    {f : α → ℝ} {g : β → ℝ}
    (hf : Summable (fun a => |f a|)) (hg : Summable (fun b => |g b|)) :
    Summable (fun p : α × β => f p.1 * g p.2) := by
  have hmajor : Summable (fun p : α × β => |f p.1| * |g p.2|) := by
    apply (summable_prod_of_nonneg (fun p : α × β =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _))).2
    constructor
    · intro a
      exact hg.mul_left (|f a|)
    · have houter : Summable (fun a : α => |f a| * ∑' b : β, |g b|) :=
        hf.mul_right (∑' b : β, |g b|)
      convert houter using 1
      funext a
      exact hg.tsum_mul_left (|f a|)
  apply Summable.of_norm_bounded hmajor
  intro p
  simp [Real.norm_eq_abs]

private theorem q3CovPeriodization_coe_eq {L : ℝ} (hL : 2 < L)
    [Fact (0 < L)] {u : ℝ} (hu : u ∈ Ico (-L / 2) (L / 2)) :
    q3CovPeriodization L hL (u : AddCircle L) = (ASDExplicitGamma.q3Cov u : ℂ) := by
  change AddCircle.liftIco L (-L / 2)
      (fun x : ℝ => (ASDExplicitGamma.q3Cov x : ℂ)) (u : AddCircle L) = _
  have hu' : u ∈ Ico (-L / 2) (-L / 2 + L) := by
    simpa only [show -L / 2 + L = L / 2 by ring] using hu
  rw [AddCircle.liftIco_coe_apply hu']

private theorem q3Coordinate_difference_abs_le_diam
    {K : Set (Homogenization.Vec 2)} [CompactSpace (↥K)]
    (x y : ↥K) (k : Fin 2) :
    |((x : Homogenization.Vec 2) k) - ((y : Homogenization.Vec 2) k)| ≤
      Metric.diam (Set.univ : Set (↥K)) := by
  have hd := Metric.dist_le_diam_of_mem isCompact_univ.isBounded
    (Set.mem_univ x) (Set.mem_univ y)
  calc
    |((x : Homogenization.Vec 2) k) - ((y : Homogenization.Vec 2) k)| =
        ‖((x : Homogenization.Vec 2) - (y : Homogenization.Vec 2)) k‖ := by
          rw [Real.norm_eq_abs, Pi.sub_apply]
    _ ≤ ‖(x : Homogenization.Vec 2) - (y : Homogenization.Vec 2)‖ :=
      norm_le_pi_norm _ _
    _ = dist x y := by
      change ‖(x : Homogenization.Vec 2) - (y : Homogenization.Vec 2)‖ =
        dist (x : Homogenization.Vec 2) (y : Homogenization.Vec 2)
      rw [dist_eq_norm]
    _ ≤ Metric.diam (Set.univ : Set (↥K)) := hd

private theorem exists_q3_covariance_factorization_aux
    {K : Set (Homogenization.Vec 2)} [CompactSpace (↥K)] (h : ℝ) (hh : 0 < h)
    (L : ℝ) (hL : 2 < L)
    (hL_eq : L = 2 * Metric.diam (Set.univ : Set (↥K)) + 4)
    [Fact (0 < L)] [Infinite Q3FourierFeatureIndex] [Denumerable Q3FourierFeatureIndex] :
    ∃ (T : GaussianFactorL2 ℕ →L[ℝ] C(↥K, ℝ))
      (v : ℕ → GaussianFactorL2 ℕ),
      Summable (fun j => ‖v j‖ ^ 2) ∧
        ∀ x y : ↥K,
          (∑' j, T (v j) x * T (v j) y) =
            q3CovarianceKernel h (x : Homogenization.Vec 2) (y : Homogenization.Vec 2) := by
  classical
  let D : ℝ := Metric.diam (Set.univ : Set (↥K))
  have hD : 0 ≤ D := Metric.diam_nonneg
  let e : Q3FourierFeatureIndex ≃ ℕ := Denumerable.eqv Q3FourierFeatureIndex
  let H : Q3FourierFeatureIndex → C(↥K, ℝ) :=
    fun j => q3FourierFeature (K := K) L h j
  let Hn : ℕ → C(↥K, ℝ) := fun n => H (e.symm n)
  have hHJ : Summable (fun j => ‖H j‖) := by
    simpa only [H] using q3FourierFeature_norm_summable (K := K) (L := L) (h := h)
      hL hh.le
  have hH : Summable (fun n => ‖Hn n‖) := by
    change Summable ((fun j => ‖H j‖) ∘ e.symm)
    exact hHJ.comp_injective e.symm.injective
  obtain ⟨T, v, hA, hTv⟩ :=
    exists_l2_factorization_of_summable_norm Hn hH
  refine ⟨T, v, hA, ?_⟩
  intro x y
  let A : ℤ × Fin 2 → ℝ := fun p =>
    q3CircleFeature p (((x : Homogenization.Vec 2) 0 : ℝ) : AddCircle L) *
      q3CircleFeature p (((y : Homogenization.Vec 2) 0 : ℝ) : AddCircle L)
  let B : ℤ × Fin 2 → ℝ := fun p =>
    q3CircleFeature p (((x : Homogenization.Vec 2) 1 : ℝ) : AddCircle L) *
      q3CircleFeature p (((y : Homogenization.Vec 2) 1 : ℝ) : AddCircle L)
  have hA' : Summable A := by
    exact (q3CircleFeature_product_summable hL _ _).congr fun p => rfl
  have hB' : Summable B := by
    exact (q3CircleFeature_product_summable hL _ _).congr fun p => rfl
  have hAB : Summable (fun p : Q3FourierFeatureIndex => A p.1 * B p.2) :=
    summable_prod_of_summable_abs hA'.norm hB'.norm
  have hpoint (p : Q3FourierFeatureIndex) :
      H p x * H p y = h ^ 2 * (A p.1 * B p.2) := by
    change q3FourierFeature (K := K) L h p x *
      q3FourierFeature (K := K) L h p y = _
    rw [q3FourierFeature_apply, q3FourierFeature_apply]
    dsimp [A, B, q3CircleFeature]
    ring
  have hsum :
      (∑' p : Q3FourierFeatureIndex, H p x * H p y) =
        h ^ 2 * ((∑' p : ℤ × Fin 2, A p) * (∑' p : ℤ × Fin 2, B p)) := by
    calc
      _ = ∑' p : Q3FourierFeatureIndex, h ^ 2 * (A p.1 * B p.2) := by
        apply tsum_congr
        exact hpoint
      _ = h ^ 2 * ∑' p : Q3FourierFeatureIndex, A p.1 * B p.2 :=
        hAB.tsum_mul_left (h ^ 2)
      _ = h ^ 2 * ((∑' p : ℤ × Fin 2, A p) *
          (∑' p : ℤ × Fin 2, B p)) := by
        rw [(hA'.tsum_mul_tsum hB' hAB).symm]
  have hperiod0 :
      (∑' p : ℤ × Fin 2, A p) =
        (q3CovPeriodization L hL
          ((((x : Homogenization.Vec 2) 0 : ℝ) : AddCircle L) -
            (((y : Homogenization.Vec 2) 0 : ℝ) : AddCircle L))).re := by
    exact q3Circle_fourier_kernel hL _ _
  have hperiod1 :
      (∑' p : ℤ × Fin 2, B p) =
        (q3CovPeriodization L hL
          ((((x : Homogenization.Vec 2) 1 : ℝ) : AddCircle L) -
            (((y : Homogenization.Vec 2) 1 : ℝ) : AddCircle L))).re := by
    exact q3Circle_fourier_kernel hL _ _
  have hcov0 :
      q3CovPeriodization L hL
          ((((x : Homogenization.Vec 2) 0 : ℝ) : AddCircle L) -
            (((y : Homogenization.Vec 2) 0 : ℝ) : AddCircle L)) =
        (q3Cov (((x : Homogenization.Vec 2) - (y : Homogenization.Vec 2)) 0) : ℂ) := by
    rw [← AddCircle.coe_sub]
    apply q3CovPeriodization_coe_eq hL
    have hd := q3Coordinate_difference_abs_le_diam x y 0
    have hbound : |((x : Homogenization.Vec 2) 0) - ((y : Homogenization.Vec 2) 0)| < L / 2 := by
      calc
        |((x : Homogenization.Vec 2) 0) - ((y : Homogenization.Vec 2) 0)| ≤ D := by
          simpa only [D] using hd
        _ < D + 2 := by linarith [hD]
        _ = L / 2 := by rw [hL_eq]; ring
    rcases abs_lt.mp hbound with ⟨hl, hr⟩
    exact ⟨by linarith, hr⟩
  have hcov1 :
      q3CovPeriodization L hL
          ((((x : Homogenization.Vec 2) 1 : ℝ) : AddCircle L) -
            (((y : Homogenization.Vec 2) 1 : ℝ) : AddCircle L)) =
        (q3Cov (((x : Homogenization.Vec 2) - (y : Homogenization.Vec 2)) 1) : ℂ) := by
    rw [← AddCircle.coe_sub]
    apply q3CovPeriodization_coe_eq hL
    have hd := q3Coordinate_difference_abs_le_diam x y 1
    have hbound : |((x : Homogenization.Vec 2) 1) - ((y : Homogenization.Vec 2) 1)| < L / 2 := by
      calc
        |((x : Homogenization.Vec 2) 1) - ((y : Homogenization.Vec 2) 1)| ≤ D := by
          simpa only [D] using hd
        _ < D + 2 := by linarith [hD]
        _ = L / 2 := by rw [hL_eq]; ring
    rcases abs_lt.mp hbound with ⟨hl, hr⟩
    exact ⟨by linarith, hr⟩
  calc
    (∑' j : ℕ, T (v j) x * T (v j) y) =
        ∑' j : ℕ, Hn j x * Hn j y := by
      apply tsum_congr
      intro j
      rw [hTv j]
    _ = ∑' p : Q3FourierFeatureIndex, H p x * H p y := by
      exact (e.symm).tsum_eq (fun p : Q3FourierFeatureIndex => H p x * H p y)
    _ = h ^ 2 * ((∑' p : ℤ × Fin 2, A p) * (∑' p : ℤ × Fin 2, B p)) := hsum
    _ = q3CovarianceKernel h (x : Homogenization.Vec 2) (y : Homogenization.Vec 2) := by
      rw [hperiod0, hperiod1, hcov0, hcov1]
      simp only [Complex.ofReal_re]
      simp [q3CovarianceKernel]
      ring

/-- A compact-set q3 covariance has a real, absolutely summable Fourier feature family. Applying
the generic `ℓ²` factorization turns this family into the Hilbert operator and vectors required by
the Gaussian-series realization theorem. -/
theorem exists_q3_covariance_factorization
    {K : Set (Homogenization.Vec 2)} [CompactSpace (↥K)] (h : ℝ) (hh : 0 < h) :
    ∃ (T : GaussianFactorL2 ℕ →L[ℝ] C(↥K, ℝ))
      (v : ℕ → GaussianFactorL2 ℕ),
      Summable (fun j => ‖v j‖ ^ 2) ∧
        ∀ x y : ↥K,
          (∑' j, T (v j) x * T (v j) y) =
            q3CovarianceKernel h (x : Homogenization.Vec 2) (y : Homogenization.Vec 2) := by
  classical
  let D : ℝ := Metric.diam (Set.univ : Set (↥K))
  let L : ℝ := 2 * D + 4
  have hD : 0 ≤ D := Metric.diam_nonneg
  have hL : 2 < L := by dsimp [L]; linarith
  have hFact : Fact (0 < L) := ⟨by linarith⟩
  have hInfinite : Infinite Q3FourierFeatureIndex := Infinite.of_injective
    (fun n : ℤ => ((n, (0 : Fin 2)), (0, (0 : Fin 2))))
    (by intro a b hab; exact congrArg (fun p : Q3FourierFeatureIndex => p.1.1) hab)
  have hDenumerable : Denumerable Q3FourierFeatureIndex :=
    Classical.choice (@nonempty_denumerable Q3FourierFeatureIndex _ hInfinite)
  exact @exists_q3_covariance_factorization_aux K ‹CompactSpace (↥K)› h hh L hL rfl
    hFact hInfinite hDenumerable

/-- The frozen planar q3 shell law on a compact set is the law of a Hilbert-factorized Gaussian
series in the continuous-function space. Its only source hypothesis is the frozen
`PlanarQ3Gaussian` declaration. -/
theorem zeroShellLaw_map_shellFieldScalarRestriction_eq_gaussianSeries
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {K : Set (Homogenization.Vec 2)} [CompactSpace (↥K)] :
    ∃ (T : GaussianFactorL2 ℕ →L[ℝ] C(↥K, ℝ))
      (v : ℕ → GaussianFactorL2 ℕ)
      (hA : Summable (fun j => ‖v j‖ ^ 2)),
      ((Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw M.P).toMeasure).map
          (shellFieldScalarRestriction K) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) := by
  classical
  obtain ⟨T, v, hA, hKernel⟩ := exists_q3_covariance_factorization (K := K) h hM.1
  let μ : Measure (Algsuperdiff.Frozen.Assumptions.ShellField 2) :=
    (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw M.P).toMeasure
  let C : ↥K → ↥K → ℝ := fun x y =>
    q3CovarianceKernel h (x : Homogenization.Vec 2) (y : Homogenization.Vec 2)
  have hShell : ∀ {ι : Type} [Fintype ι] (x : ι → ↥K) (t : ι → ℝ),
      μ.map (fun j => ∑ i, t i * j (x i) 1 0) =
        gaussianReal 0 (Real.toNNReal (∑ i, ∑ k, t i * t k * C (x i) (x k))) := by
    intro ι _ x t
    exact zeroShellLaw_map_finite_q3_observation M h hM x t
  have hKernel' : ∀ x y : ↥K, (∑' j, T (v j) x * T (v j) y) = C x y := by
    intro x y
    exact hKernel x y
  refine ⟨T, v, hA, ?_⟩
  exact shellFieldScalarRestriction_law_eq_gaussianSeries
    μ C hA T hShell hKernel'

end ASDExplicitGamma.Gaussian

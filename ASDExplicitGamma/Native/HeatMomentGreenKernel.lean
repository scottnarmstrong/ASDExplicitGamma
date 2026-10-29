module

public import ASDExplicitGamma.Native.HeatAffineGreen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! The degree-specific positive Green weights used in each heat redistribution. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory Set
noncomputable section

/-- The exponential increment lies below its chord on the unit interval. -/
theorem heat_exp_increment_chord (c r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.exp (c*r)-1 ≤ r*(Real.exp c-1) := by
  have hh := convexOn_exp.2 (mem_univ (0:ℝ)) (mem_univ c)
    (sub_nonneg.mpr hr1) hr0 (show (1-r)+r=1 by ring)
  simp only [smul_eq_mul,mul_zero,zero_add,Real.exp_zero,mul_one] at hh
  rw [mul_comm r c] at hh
  linarith

/-- Exact positive affine moment kernel, before integration of the forcing. -/
def heatMomentGreenKernel (c : ℝ) (j d : ℕ) (r : ℝ) : ℝ :=
  (Real.exp (c*r))^j*(4*(Real.exp (c*r)-1))^d

theorem heat_moment_green_kernel_bound (c : ℝ) (hc : 0 ≤ c) (j d : ℕ)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    heatMomentGreenKernel c j d r ≤ (Real.exp c)^j*(4*(Real.exp c-1))^d*r^d := by
  have hcr : c*r ≤ c := by nlinarith
  have hinc : 0 ≤ Real.exp (c*r)-1 := sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hc hr0))
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 4*(Real.exp (c*r)-1))
    (mul_le_mul_of_nonneg_left (heat_exp_increment_chord c r hr0 hr1) (by norm_num : (0:ℝ)≤4)) d
  unfold heatMomentGreenKernel
  calc
    _ ≤ (Real.exp c)^j*(4*(r*(Real.exp c-1)))^d :=
      mul_le_mul (pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr hcr) j)
        hpow (pow_nonneg (by positivity) _) (pow_nonneg (Real.exp_nonneg _) _)
    _ = _ := by rw [show 4*(r*(Real.exp c-1))=(4*(Real.exp c-1))*r by ring,mul_pow]; ring

/-- Integrating retains the source denominator d+1, rather than replacing the
entire Green kernel by its endpoint maximum. -/
theorem heat_moment_green_kernel_integral (c : ℝ) (hc : 0 ≤ c) (j d : ℕ) :
    (∫ r in (0:ℝ)..1,heatMomentGreenKernel c j d r) ≤
      (Real.exp c)^j*(4*(Real.exp c-1))^d/(d+1:ℕ) := by
  have hcont : Continuous (heatMomentGreenKernel c j d) := by
    unfold heatMomentGreenKernel
    fun_prop
  have hmajor : Continuous (fun r : ℝ => (Real.exp c)^j*(4*(Real.exp c-1))^d*r^d) := by fun_prop
  have hh := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ)≤1)
    (hcont.intervalIntegrable 0 1) (hmajor.intervalIntegrable 0 1)
    (fun r hr => heat_moment_green_kernel_bound c hc j d r hr.1 hr.2)
  apply hh.trans_eq
  rw [intervalIntegral.integral_const_mul,integral_pow]
  simp only [one_pow,zero_pow (Nat.succ_ne_zero d),sub_zero,Nat.cast_add,Nat.cast_one]
  ring

/-- The same forcing bound holds uniformly at every heat time, so the next
finite redistribution may reuse its output as a pathwise-in-time cap. -/
theorem heat_moment_green_kernel_uniform (c : ℝ) (hc : 0 ≤ c) (j d : ℕ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ s in (0:ℝ)..t,heatMomentGreenKernel c j d (t-s)) ≤
      (Real.exp c)^j*(4*(Real.exp c-1))^d/(d+1:ℕ) := by
  have hcont : Continuous (heatMomentGreenKernel c j d) := by
    unfold heatMomentGreenKernel
    fun_prop
  have hpos : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) 1)] heatMomentGreenKernel c j d := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hinc : 0 ≤ Real.exp (c*r)-1 := sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hc hr.1.le))
    unfold heatMomentGreenKernel
    positivity
  calc
    _ = ∫ r in (0:ℝ)..t,heatMomentGreenKernel c j d r := by
      rw [intervalIntegral.integral_comp_sub_left (f := heatMomentGreenKernel c j d) t]
      simp
    _ ≤ ∫ r in (0:ℝ)..1,heatMomentGreenKernel c j d r :=
      intervalIntegral.integral_mono_interval le_rfl ht0 ht1 hpos (hcont.intervalIntegrable 0 1)
    _ ≤ _ := heat_moment_green_kernel_integral c hc j d

/-- Degree-k source Green coefficient, including its exact binomial weight. -/
theorem heat_moment_green_degree_bound (c : ℝ) (hc : 0 ≤ c) (k j : ℕ)
    (E t : ℝ) (hE : 0 ≤ E) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ s in (0:ℝ)..t,(Nat.choose k j:ℝ)*E*heatMomentGreenKernel c j (k-j) (t-s)) ≤
      (Nat.choose k j:ℝ)*(Real.exp c)^j*(4*(Real.exp c-1))^(k-j)*E/(k-j+1:ℕ) := by
  rw [intervalIntegral.integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left (heat_moment_green_kernel_uniform c hc j (k-j) t ht0 ht1)
    (mul_nonneg (Nat.cast_nonneg (Nat.choose k j)) hE)
  convert hh using 1 <;> ring

end
end ASDExplicitGamma.Native

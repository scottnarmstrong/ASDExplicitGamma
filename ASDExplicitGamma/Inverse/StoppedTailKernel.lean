module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Exact exponential kernels for the real-order diameter moments. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory Set

/-- The positive exponential derivative integrates to its exact primitive. -/
theorem exp_kernel_interval (t : ℝ) :
    (∫ s in (0:ℝ)..t, (1/8:ℝ)*Real.exp (s/8)) = Real.exp (t/8)-1 := by
  have hd (x : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (s/8)) ((1/8:ℝ)*Real.exp (x/8)) x := by
    simpa only [id_eq,mul_comm] using! ((hasDerivAt_id x).div_const 8).exp
  have hc : Continuous (fun s : ℝ => (1/8:ℝ)*Real.exp (s/8)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const 8))
  simpa only [zero_div,Real.exp_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable 0 t)

/-- The source tail and the moment kernel leave an exactly integrable exponential. -/
theorem exp_kernel_product (t : ℝ) :
    Real.exp (-t/4)*((1/8:ℝ)*Real.exp (t/8)) = (1/8:ℝ)*Real.exp ((-1/8:ℝ)*t) := by
  calc
    _ = (1/8:ℝ)*(Real.exp (-t/4)*Real.exp (t/8)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

theorem exp_tail_kernel_integrable :
    IntegrableOn (fun t : ℝ => (1/8:ℝ)*Real.exp ((-1/8:ℝ)*t)) (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (by norm_num : (-1/8:ℝ) < 0) 0).const_mul (1/8:ℝ)

/-- Exact total mass of the tail kernel. -/
theorem exp_tail_kernel_integral :
    (∫ t : ℝ in Ioi 0, (1/8:ℝ)*Real.exp ((-1/8:ℝ)*t)) = 1 := by
  rw [integral_const_mul,integral_exp_mul_Ioi (by norm_num : (-1/8:ℝ) < 0) 0]
  norm_num

end ASDExplicitGamma.Inverse

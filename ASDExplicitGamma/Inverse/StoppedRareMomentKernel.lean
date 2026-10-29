module

public import ASDExplicitGamma.Inverse.StoppedRareMomentPrimitive

/-! Exact finite and infinite kernels in the source rare-moment layer cake. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem power_layer_kernel_interval (n : ℕ) (t : ℝ) :
    (∫ x in (0:ℝ)..t, (n+1:ℝ)*x^n) = t^(n+1) := by
  rw [intervalIntegral.integral_const_mul,integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero n),sub_zero]
  have hn : (n+1:ℝ) ≠ 0 := by positivity
  field_simp

theorem power_layer_kernel_integrable (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun x : ℝ => (n+1:ℝ)*x^n) (Ioc 0 t) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp
    ((continuous_const.mul (continuous_id.pow n)).intervalIntegrable 0 t)

theorem power_layer_kernel_lintegral (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ x in Ioc 0 t, ENNReal.ofReal ((n+1:ℝ)*x^n)) = ENNReal.ofReal (t^(n+1)) := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioc 0 t)] (fun x : ℝ => (n+1:ℝ)*x^n) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (by positivity) (pow_nonneg hx.1.le n)
  rw [← ofReal_integral_eq_lintegral_ofReal (power_layer_kernel_integrable n t ht) hn,
    ← intervalIntegral.integral_of_le ht,power_layer_kernel_interval]

theorem rare_moment_tail_integrable (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun x : ℝ => x^n*Real.exp (-x/4)) (Ioi t) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun x (_ : x ∈ Ici t) => rare_moment_primitive_deriv n x)
    (fun _x hx => mul_nonneg (pow_nonneg (ht.trans hx.le) n) (Real.exp_pos _).le)
    (rare_moment_primitive_tendsto n)

theorem rare_moment_tail_lintegral (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ x in Ioi t, ENNReal.ofReal ((n+1:ℝ)*x^n*Real.exp (-x/4))) =
      ENNReal.ofReal ((n+1:ℝ)*4*rareMomentPolynomial n t*Real.exp (-t/4)) := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi t)] (fun x : ℝ => (n+1:ℝ)*(x^n*Real.exp (-x/4))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg (ht.trans hx.le) n) (Real.exp_pos _).le)
  simp_rw [mul_assoc]
  rw [← ofReal_integral_eq_lintegral_ofReal ((rare_moment_tail_integrable n t ht).const_mul _) hn,
    integral_const_mul,rare_moment_tail_integral n t ht]
  simp only [mul_assoc]

end
end ASDExplicitGamma.Inverse

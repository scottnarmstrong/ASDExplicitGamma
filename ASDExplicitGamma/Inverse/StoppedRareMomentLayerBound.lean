module

public import ASDExplicitGamma.Inverse.StoppedRareMomentKernel

/-! The full two-piece layer-cake bound, retaining every endpoint term. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem rare_moment_polynomial_nonneg (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ rareMomentPolynomial n t := by
  induction n with
  | zero => norm_num [rareMomentPolynomial]
  | succ n ih =>
    simp only [rareMomentPolynomial]
    positivity

/-- Splitting at t0 keeps the complete polynomial rare-moment bound; all
infinite integrals are bounded before any finite-energy assertion is used. -/
theorem tail_moment_lintegral_bound (F : ℝ → ℝ≥0∞) (n : ℕ)
    (a B T : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hrare : ∀ u > 0, F u ≤ ENNReal.ofReal a)
    (hexp : ∀ u > 0, F u ≤ ENNReal.ofReal (B*Real.exp (-u/4))) :
    (∫⁻ u in Ioi 0, F u*ENNReal.ofReal ((n+1:ℝ)*u^n)) ≤
      ENNReal.ofReal (a*T^(n+1)+B*((n+1:ℝ)*4*rareMomentPolynomial n T*Real.exp (-T/4))) := by
  have hs : (∫⁻ u in Ioc 0 T, F u*ENNReal.ofReal ((n+1:ℝ)*u^n)) ≤
      ENNReal.ofReal (a*T^(n+1)) := by
    calc
      _ ≤ ∫⁻ u in Ioc 0 T, ENNReal.ofReal a*ENNReal.ofReal ((n+1:ℝ)*u^n) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        exact mul_le_mul_of_nonneg_right (hrare u hu.1) (zero_le : (0:ℝ≥0∞) ≤ _)
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,power_layer_kernel_lintegral n T hT,
          ← ENNReal.ofReal_mul ha]
  have hl : (∫⁻ u in Ioi T, F u*ENNReal.ofReal ((n+1:ℝ)*u^n)) ≤
      ENNReal.ofReal (B*((n+1:ℝ)*4*rareMomentPolynomial n T*Real.exp (-T/4))) := by
    calc
      _ ≤ ∫⁻ u in Ioi T, ENNReal.ofReal B*ENNReal.ofReal ((n+1:ℝ)*u^n*Real.exp (-u/4)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := lt_of_le_of_lt hT hu
        have hk : 0 ≤ (n+1:ℝ)*u^n := by positivity
        apply (mul_le_mul_of_nonneg_right (hexp u hu0) (zero_le : (0:ℝ≥0∞) ≤ _)).trans_eq
        rw [ENNReal.ofReal_mul hB,ENNReal.ofReal_mul hk]
        ac_rfl
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,rare_moment_tail_lintegral n T hT,
          ← ENNReal.ofReal_mul hB]
  rw [← Ioc_union_Ioi_eq_Ioi hT,lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  apply (add_le_add hs hl).trans_eq
  rw [ENNReal.ofReal_add (mul_nonneg ha (pow_nonneg hT _))]
  have hP := rare_moment_polynomial_nonneg n T hT
  positivity

end
end ASDExplicitGamma.Inverse

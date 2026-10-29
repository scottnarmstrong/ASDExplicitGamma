module

public import ASDExplicitGamma.Inverse.StoppedTailKernel

/-! Exponential moments from the actual diameter tail, without assuming integrability. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- A nonnegative variable with tail exp(-t/4) has exponential moment at
1/8 at most two. Integrability is a conclusion of the layer-cake argument. -/
theorem exp_moment_of_unit_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω)
    (htail : ∀ t > 0, μ.real {ω | t < X ω} ≤ Real.exp (-t/4)) :
    Integrable (fun ω => Real.exp (X ω/8)) μ ∧
      (∫ ω, Real.exp (X ω/8) ∂μ) ≤ 2 := by
  let G := fun ω => Real.exp (X ω/8)-1
  have hG0 (ω : Ω) : 0 ≤ G ω := by
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg (hX0 ω) (by norm_num)))
  have hc : Continuous (fun t : ℝ => (1/8:ℝ)*Real.exp (t/8)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const 8))
  have hcake := lintegral_comp_eq_lintegral_meas_lt_mul μ (Filter.Eventually.of_forall hX0)
    hX.aemeasurable (fun t _ => hc.intervalIntegrable 0 t)
    (Filter.Eventually.of_forall (fun t => by positivity : ∀ t : ℝ, 0 ≤ (1/8:ℝ)*Real.exp (t/8)))
  simp_rw [exp_kernel_interval] at hcake
  have hb : (∫⁻ ω, ENNReal.ofReal (G ω) ∂μ) ≤ 1 := by
    rw [hcake]
    calc
      _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-t/4))*ENNReal.ofReal ((1/8:ℝ)*Real.exp (t/8)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        apply mul_le_mul_of_nonneg_right _ (zero_le : (0:ℝ≥0∞) ≤ _)
        exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (Real.exp_pos _).le).mpr (htail t ht)
      _ = ∫⁻ t in Ioi 0, ENNReal.ofReal ((1/8:ℝ)*Real.exp ((-1/8:ℝ)*t)) := by
        apply lintegral_congr
        intro t
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,exp_kernel_product]
      _ = 1 := by
        have hk0 : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
            (fun t : ℝ => (1/8:ℝ)*Real.exp ((-1/8:ℝ)*t)) :=
          Filter.Eventually.of_forall (fun t => by positivity)
        rw [← ofReal_integral_eq_lintegral_ofReal exp_tail_kernel_integrable hk0,
          exp_tail_kernel_integral]
        norm_num

  have hiG : Integrable G μ := by
    refine ⟨((hX.div_const 8).exp.sub_const 1).aestronglyMeasurable,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG0)).mpr (hb.trans_lt (by finiteness))
  have hi : Integrable (fun ω => Real.exp (X ω/8)) μ := by
    convert hiG.add (integrable_const (1:ℝ)) using 1
    funext ω
    dsimp only [G,Pi.add_apply]
    ring
  have hr := ENNReal.toReal_mono (by finiteness : (1:ℝ≥0∞) ≠ ∞) hb
  rw [← ofReal_integral_eq_lintegral_ofReal hiG (Filter.Eventually.of_forall hG0),
    ENNReal.toReal_ofReal (integral_nonneg hG0),ENNReal.toReal_one] at hr
  refine ⟨hi,?_⟩
  have he : (fun ω => Real.exp (X ω/8)) = fun ω => G ω+1 := by
    funext ω
    dsimp only [G,Pi.add_apply]
    ring
  rw [he,integral_add hiG (integrable_const (1:ℝ))]
  simp only [integral_const,probReal_univ,one_smul]
  linarith only [hr]

end
end ASDExplicitGamma.Inverse

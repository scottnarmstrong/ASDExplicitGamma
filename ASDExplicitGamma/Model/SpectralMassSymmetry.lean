module

public import ASDExplicitGamma.Model.SpectralCovariance
public import ASDExplicitGamma.Model.SpectralModel

@[expose] public section

open MeasureTheory Complex

namespace ASDExplicitGamma.Model

/-- Exchange the two frequency coordinates. -/
def q3FrequencySwap (ξ : Q3FrequencyPlane) : Q3FrequencyPlane :=
  WithLp.toLp 2 (ξ.snd, ξ.fst)

/-- The product spectral measure is invariant under exchange of coordinates. -/
theorem q3SpectralMeasure_integral_swap (h : ℝ) (f : Q3FrequencyPlane → ℝ) :
    (∫ ξ, f (q3FrequencySwap ξ) ∂q3SpectralMeasure h) =
      ∫ ξ, f ξ ∂q3SpectralMeasure h := by
  rw [q3SpectralMeasure, ← MeasurableEquiv.coe_toLp, integral_map_equiv, integral_map_equiv]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (q3SpectralDensity2_continuous h).measurable.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul₀
    (q3SpectralDensity2_continuous h).measurable.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (q3SpectralDensity2_nonneg h _), smul_eq_mul]
  have heq (ξ : ℝ × ℝ) : q3SpectralDensity2 h ξ *
      f (q3FrequencySwap ((MeasurableEquiv.toLp 2 (ℝ × ℝ)) ξ)) =
      (fun z : ℝ × ℝ => q3SpectralDensity2 h z * f ((MeasurableEquiv.toLp 2 (ℝ × ℝ)) z))
        (Prod.swap ξ) := by
    simp only [q3FrequencySwap, MeasurableEquiv.toLp_apply, WithLp.toLp_fst, WithLp.toLp_snd,
      Prod.swap, q3SpectralDensity2]
    ring
  simp_rw [heq]
  exact integral_prod_swap
    (fun ξ : ℝ × ℝ => q3SpectralDensity2 h ξ * f ((MeasurableEquiv.toLp 2 (ℝ × ℝ)) ξ))
    (μ := volume) (ν := volume)

/-- Total spectral mass, with the normalization of the frozen q3 kernel. -/
theorem q3SpectralMeasure_real_mass (h : ℝ) : (q3SpectralMeasure h).real Set.univ = h ^ 2 := by
  have hm := q3SpectralMeasure_exponential_integral h 0 0
  simp only [mul_zero, add_zero, ofReal_zero, zero_mul, exp_zero,
    q3Cov_zero_eq_one, mul_one] at hm
  have hr := congrArg Complex.re hm
  simpa only [integral_const, Complex.real_smul, mul_one, Complex.ofReal_re] using hr

theorem q3SpectralMeasure_singleton_zero (h : ℝ) : q3SpectralMeasure h {0} = 0 := by
  rw [q3SpectralMeasure, ← MeasurableEquiv.coe_toLp, MeasurableEquiv.map_apply]
  have heq : (MeasurableEquiv.toLp 2 (ℝ × ℝ)) ⁻¹' ({0} : Set Q3FrequencyPlane) =
      ({(0, 0)} : Set (ℝ × ℝ)) := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.toLp_apply]
    constructor
    · intro hξ
      have hv := congrArg WithLp.ofLp hξ
      exact hv
    · rintro rfl
      rfl
  rw [heq]
  exact measure_singleton _

private theorem square_ratio_bounds (x y : ℝ) :
    0 ≤ x ^ 2 / (x ^ 2 + y ^ 2) ∧ x ^ 2 / (x ^ 2 + y ^ 2) ≤ 1 := by
  by_cases hr : x ^ 2 + y ^ 2 = 0
  · simp only [hr, div_zero, le_refl, zero_le_one, and_self]
  have hp : 0 < x ^ 2 + y ^ 2 :=
    lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hr)
  exact ⟨div_nonneg (sq_nonneg _) hp.le,
    (div_le_one hp).mpr (le_add_of_nonneg_right (sq_nonneg _))⟩

private theorem diagonal_ratio_integrable (h : ℝ) :
    Integrable (fun ξ : Q3FrequencyPlane => ξ.fst ^ 2 / (ξ.fst ^ 2 + ξ.snd ^ 2))
      (q3SpectralMeasure h) := by
  apply (integrable_const (1 : ℝ)).mono'
    (show Measurable (fun ξ : Q3FrequencyPlane => ξ.fst ^ 2 / (ξ.fst ^ 2 + ξ.snd ^ 2))
      from by fun_prop).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (square_ratio_bounds ξ.fst ξ.snd).1]
    exact (square_ratio_bounds ξ.fst ξ.snd).2

/-- Each diagonal Helmholtz weight carries one half of the total spectral mass. -/
theorem q3SpectralMeasure_diagonal_energy (h : ℝ) :
    (∫ ξ : Q3FrequencyPlane, ξ.snd ^ 2 / (ξ.fst ^ 2 + ξ.snd ^ 2)
      ∂q3SpectralMeasure h) = h ^ 2 / 2 := by
  have hi0 := diagonal_ratio_integrable h
  have hswap := q3SpectralMeasure_integral_swap h
    (fun ξ : Q3FrequencyPlane => ξ.fst ^ 2 / (ξ.fst ^ 2 + ξ.snd ^ 2))
  simp only [q3FrequencySwap, WithLp.toLp_fst, WithLp.toLp_snd, add_comm] at hswap
  have hi1 : Integrable (fun ξ : Q3FrequencyPlane => ξ.snd ^ 2 / (ξ.fst ^ 2 + ξ.snd ^ 2))
      (q3SpectralMeasure h) := by
    apply (integrable_const (1 : ℝ)).mono'
      (show Measurable (fun ξ : Q3FrequencyPlane => ξ.snd ^ 2 / (ξ.fst ^ 2 + ξ.snd ^ 2))
        from by fun_prop).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
      simpa only [add_comm] using (square_ratio_bounds ξ.snd ξ.fst).2
  have hne : ∀ᵐ ξ ∂q3SpectralMeasure h, ξ ≠ 0 := by
    rw [ae_iff]
    simpa only [Set.compl_ofPred, Classical.not_not, Set.ofPred_eq_eq_singleton] using
      q3SpectralMeasure_singleton_zero h
  have hsum : (∫ ξ : Q3FrequencyPlane,
      ξ.fst ^ 2 / (ξ.fst ^ 2 + ξ.snd ^ 2) + ξ.snd ^ 2 / (ξ.fst ^ 2 + ξ.snd ^ 2)
        ∂q3SpectralMeasure h) = h ^ 2 := by
    calc
      _ = ∫ _ : Q3FrequencyPlane, (1 : ℝ) ∂q3SpectralMeasure h := by
        apply integral_congr_ae
        filter_upwards [hne] with ξ hξ
        have hn : ξ.fst ^ 2 + ξ.snd ^ 2 ≠ 0 := by
          have he : ‖ξ‖ ^ 2 = ξ.fst ^ 2 + ξ.snd ^ 2 := by
            rw [WithLp.prod_norm_sq_eq_of_L2]
            simp only [Real.norm_eq_abs, sq_abs]
          rw [← he]
          exact pow_ne_zero _ (norm_ne_zero_iff.mpr hξ)
        rw [← add_div, div_self hn]
      _ = h ^ 2 := by rw [integral_const, smul_eq_mul, mul_one, q3SpectralMeasure_real_mass]
  rw [integral_add hi0 hi1] at hsum
  linarith only [hswap, hsum]

end ASDExplicitGamma.Model

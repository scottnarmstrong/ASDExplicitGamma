module

public import ASDExplicitGamma.Native.HeatRemainderControlJointLaw
public import Mathlib.MeasureTheory.Measure.Prod

/-! Sharp Lp augmentation by an independent auxiliary shear. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Tensorization is used only between the physical medium and the auxiliary
Gaussian variable, never between the physical inverse weight and trace. -/
theorem nativeHeat_independent_product_Lp
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (g : Ξ → ℝ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g ν) (p : ℝ) (hp : 0 < p) :
    eLpNorm (fun z : Ω × Ξ => f z.1 * g z.2) (ENNReal.ofReal p) (μ.prod ν) =
      eLpNorm f (ENNReal.ofReal p) μ * eLpNorm g (ENNReal.ofReal p) ν := by
  have hfm : AEStronglyMeasurable (fun z : Ω × Ξ => f z.1) (μ.prod ν) := hf.comp_measurePreserving measurePreserving_fst
  have hgm : AEStronglyMeasurable (fun z : Ω × Ξ => g z.2) (μ.prod ν) := hg.comp_measurePreserving measurePreserving_snd
  have hmul : AEStronglyMeasurable (fun z : Ω × Ξ => f z.1 * g z.2) (μ.prod ν) := hfm.mul hgm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hmul]
  simp only [ENNReal.toReal_ofReal hp.le, enorm_mul]
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_prod_mul (hf.enorm.pow_const p) (hg.enorm.pow_const p),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hg]
  simp only [ENNReal.toReal_ofReal hp.le]

/-- Taking a square root halves the physical moment order exactly. -/
theorem nativeHeat_sqrt_Lp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (hf0 : ∀ ω, 0 ≤ f ω)
    (p : ℝ) (hp : 0 < p) :
    eLpNorm (fun ω => Real.sqrt (f ω)) (ENNReal.ofReal (2 * p)) μ =
      eLpNorm f (ENNReal.ofReal p) μ ^ (1 / 2 : ℝ) := by
  have he := eLpNorm_norm_rpow (p := ENNReal.ofReal (2*p)) f hf
    (by norm_num : (0 : ℝ) < 1/2)
  have hexp : ENNReal.ofReal (2*p) * ENNReal.ofReal (1/2 : ℝ) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hexp] at he
  simpa only [Real.norm_of_nonneg (hf0 _), Real.sqrt_eq_rpow, Real.rpow_eq_pow] using he

/-- Squaring a nonnegative test doubles its Lp order exactly. -/
theorem nativeHeat_square_Lp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (hf0 : ∀ ω, 0 ≤ f ω)
    (p : ℝ) (hp : 0 < p) :
    eLpNorm (fun ω => f ω ^ (2 : ℕ)) (ENNReal.ofReal p) μ =
      eLpNorm f (ENNReal.ofReal (2*p)) μ ^ (2 : ℕ) := by
  have he := eLpNorm_norm_rpow (p := ENNReal.ofReal p) f hf (by norm_num : (0 : ℝ) < 2)
  have hexp : ENNReal.ofReal p * ENNReal.ofReal (2 : ℝ) = ENNReal.ofReal (2*p) := by
    rw [← ENNReal.ofReal_mul hp.le]
    congr 1
    ring
  rw [hexp] at he
  simpa only [Real.norm_of_nonneg (hf0 _), Real.rpow_ofNat, ENNReal.rpow_ofNat] using he

/-- Minkowski after the exact shear square-root inequality gives the sharp
heat augmentation envelope. The inverse factor may be arbitrarily correlated
with the physical trace; only the auxiliary variable is tensorized. -/
theorem nativeHeat_shear_envelope_Lp
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f d : Ω → ℝ) (g : Ξ → ℝ) (S : Ω × Ξ → ℝ)
    (hf : AEStronglyMeasurable f μ) (hd : AEStronglyMeasurable d μ)
    (hg : AEStronglyMeasurable g ν) (hS : AEStronglyMeasurable S (μ.prod ν))
    (hf0 : ∀ ω, 0 ≤ f ω) (hd0 : ∀ ω, 0 ≤ d ω) (hS0 : ∀ z, 0 ≤ S z)
    (hpoint : ∀ᵐ z ∂μ.prod ν, S z ≤ (Real.sqrt (f z.1) + Real.sqrt (d z.1) * |g z.2|)^2)
    (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm S (ENNReal.ofReal p) (μ.prod ν) ≤
      (eLpNorm f (ENNReal.ofReal p) μ ^ (1/2 : ℝ) +
        eLpNorm d (ENNReal.ofReal p) μ ^ (1/2 : ℝ) * eLpNorm g (ENNReal.ofReal (2*p)) ν)^2 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp
  let F : Ω × Ξ → ℝ := fun z => Real.sqrt (f z.1)
  let D : Ω × Ξ → ℝ := fun z => Real.sqrt (d z.1) * |g z.2|
  have hfroot : AEStronglyMeasurable (fun ω => Real.sqrt (f ω)) μ := Real.continuous_sqrt.comp_aestronglyMeasurable hf
  have hdroot : AEStronglyMeasurable (fun ω => Real.sqrt (d ω)) μ := Real.continuous_sqrt.comp_aestronglyMeasurable hd
  have hF : AEStronglyMeasurable F (μ.prod ν) := hfroot.comp_measurePreserving measurePreserving_fst
  have hgabs : AEStronglyMeasurable (fun ξ => |g ξ|) ν := by simpa only [Real.norm_eq_abs] using hg.norm
  have hD : AEStronglyMeasurable D (μ.prod ν) :=
    (hdroot.comp_measurePreserving measurePreserving_fst).mul
      (hgabs.comp_measurePreserving measurePreserving_snd)
  have hFD0 (z : Ω × Ξ) : 0 ≤ (F+D) z :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
  have hmono : eLpNorm S (ENNReal.ofReal p) (μ.prod ν) ≤
      eLpNorm (fun z => ((F+D) z)^2) (ENNReal.ofReal p) (μ.prod ν) := by
    apply eLpNorm_mono_ae hS
    filter_upwards [hpoint] with z hz
    rw [Real.norm_of_nonneg (hS0 z), Real.norm_of_nonneg (sq_nonneg _)]
    exact hz
  rw [nativeHeat_square_Lp (μ.prod ν) (F+D) (hF.add hD) hFD0 p hp0] at hmono
  have hadd := eLpNorm_add_le (f := F) (g := D) (μ := μ.prod ν)
    (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2*p) by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 2*p by linarith)))
  have hFnorm : eLpNorm F (ENNReal.ofReal (2*p)) (μ.prod ν) =
      eLpNorm f (ENNReal.ofReal p) μ ^ (1/2 : ℝ) := by
    rw [show F = (fun ω => Real.sqrt (f ω)) ∘ Prod.fst from rfl,
      eLpNorm_comp_measurePreserving hfroot measurePreserving_fst, nativeHeat_sqrt_Lp μ f hf hf0 p hp0]
  have hDnorm : eLpNorm D (ENNReal.ofReal (2*p)) (μ.prod ν) =
      eLpNorm d (ENNReal.ofReal p) μ ^ (1/2 : ℝ) * eLpNorm g (ENNReal.ofReal (2*p)) ν := by
    rw [show D = (fun z : Ω × Ξ => Real.sqrt (d z.1) * |g z.2|) from rfl,
      nativeHeat_independent_product_Lp μ ν (fun ω => Real.sqrt (d ω)) (fun ξ => |g ξ|)
        hdroot hgabs (2*p) (by positivity), nativeHeat_sqrt_Lp μ d hd hd0 p hp0]
    congr 1
    simpa only [Real.norm_eq_abs] using eLpNorm_norm g hg
  rw [hFnorm, hDnorm] at hadd
  exact hmono.trans (pow_le_pow_left' hadd 2)

end
end ASDExplicitGamma.Native

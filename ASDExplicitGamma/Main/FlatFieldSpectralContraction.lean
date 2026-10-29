module

public import ASDExplicitGamma.Model.SpectralMassSymmetry
public import ASDExplicitGamma.Model.SpectralHelmholtzProjection
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Fourier.FourierTransform

/-! The q3 spectral Helmholtz multiplier has isotropic matrix mean. -/

@[expose] public section

open MeasureTheory
open FourierTransform

namespace ASDExplicitGamma.Main

open ASDExplicitGamma.Model

private theorem main_q3FourierKernel_even (x : ℝ) :
    q3FourierKernel (-x) = q3FourierKernel x := by
  let f : ℝ → ℂ := fun y => (q3Kernel y : ℂ)
  have heven : f ∘ LinearIsometryEquiv.neg ℝ = f := by
    funext y
    simp [f, q3Kernel, abs_neg]
  have h := Real.fourier_comp_linearIsometry
    (LinearIsometryEquiv.neg ℝ) f x
  rw [heven] at h
  simpa only [q3FourierKernel, f, LinearIsometryEquiv.coe_neg] using h.symm

private theorem main_q3SpectralDensity1_even (x : ℝ) :
    q3SpectralDensity1 (-x) = q3SpectralDensity1 x := by
  simp [q3SpectralDensity1, main_q3FourierKernel_even]

private def mainQ3ReflectFirst (p : ℝ × ℝ) : ℝ × ℝ := (-p.1, p.2)

private def mainQ3ReflectFirstEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun := mainQ3ReflectFirst
  invFun := mainQ3ReflectFirst
  left_inv := by intro p; cases p; simp [mainQ3ReflectFirst]
  right_inv := by intro p; cases p; simp [mainQ3ReflectFirst]
  measurable_toFun := by
    change Measurable mainQ3ReflectFirst
    fun_prop [mainQ3ReflectFirst]
  measurable_invFun := by
    change Measurable mainQ3ReflectFirst
    fun_prop [mainQ3ReflectFirst]

private theorem mainQ3ReflectFirst_measurePreserving :
    MeasurePreserving mainQ3ReflectFirst (volume.prod volume) (volume.prod volume) := by
  change MeasurePreserving
    (fun p : ℝ × ℝ => ((fun x : ℝ => -x) p.1, (fun x : ℝ => x) p.2))
    (volume.prod volume) (volume.prod volume)
  exact MeasurePreserving.prod (Measure.measurePreserving_neg volume)
    (MeasurePreserving.id volume)

private theorem mainQ3ReflectFirstEquiv_measurePreserving :
    MeasurePreserving mainQ3ReflectFirstEquiv (volume.prod volume) (volume.prod volume) := by
  simpa [mainQ3ReflectFirstEquiv] using mainQ3ReflectFirst_measurePreserving

private theorem main_q3HelmholtzCrossWeight_abs_le_one (x y : ℝ) :
    |x * y / (x ^ 2 + y ^ 2)| ≤ 1 := by
  by_cases hzero : x ^ 2 + y ^ 2 = 0
  · simp [hzero]
  · have hden : 0 < x ^ 2 + y ^ 2 :=
      lt_of_le_of_ne (add_nonneg (sq_nonneg x) (sq_nonneg y)) (Ne.symm hzero)
    rw [abs_div, abs_mul, abs_of_pos hden]
    have hxy : |x| * |y| ≤ x ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
    exact (div_le_one hden).2 hxy

/-- The off-diagonal entry of the whole-space q3 Helmholtz covariance vanishes. -/
theorem main_q3SpectralHelmholtz_cross_zero (h : ℝ) :
    (∫ ξ : Q3FrequencyPlane,
      ξ.fst * ξ.snd / (ξ.fst ^ 2 + ξ.snd ^ 2) ∂q3SpectralMeasure h) = 0 := by
  rw [q3SpectralMeasure, ← MeasurableEquiv.coe_toLp, integral_map_equiv]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (q3SpectralDensity2_continuous h).measurable.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (q3SpectralDensity2_nonneg h _), smul_eq_mul,
    MeasurableEquiv.toLp_apply, WithLp.toLp_fst, WithLp.toLp_snd]
  let w : ℝ × ℝ → ℝ := fun p => p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)
  let g : ℝ × ℝ → ℝ := fun p => q3SpectralDensity2 h p * w p
  have hgmeas : AEStronglyMeasurable g (volume.prod volume) := by
    apply ((q3SpectralDensity2_continuous h).measurable.mul ?_).aestronglyMeasurable
    dsimp [w]
    fun_prop
  have hgint : Integrable g (volume.prod volume) := by
    have hd := q3SpectralDensity2_integrable h
    apply hd.mono' hgmeas
    filter_upwards [] with p
    have hw := main_q3HelmholtzCrossWeight_abs_le_one p.1 p.2
    change ‖q3SpectralDensity2 h p * w p‖ ≤ q3SpectralDensity2 h p
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (q3SpectralDensity2_nonneg h p)]
    calc
      q3SpectralDensity2 h p * |w p| ≤ q3SpectralDensity2 h p * 1 :=
        mul_le_mul_of_nonneg_left hw (q3SpectralDensity2_nonneg h p)
      _ = q3SpectralDensity2 h p := mul_one _
  have hreflect (p : ℝ × ℝ) : g (mainQ3ReflectFirst p) = -g p := by
    simp [g, w, mainQ3ReflectFirst, q3SpectralDensity2,
      main_q3SpectralDensity1_even]
    ring
  have hcomp := mainQ3ReflectFirstEquiv_measurePreserving.integral_comp' g
  have hzero : (∫ p, g p ∂(volume.prod volume)) = 0 := by
    have hneg : (∫ p, g p ∂(volume.prod volume)) =
        -(∫ p, g p ∂(volume.prod volume)) := by
      calc
        _ = ∫ p, g (mainQ3ReflectFirst p) ∂(volume.prod volume) := hcomp.symm
        _ = _ := by simp_rw [hreflect, integral_neg]
    linarith
  simpa [g, w] using hzero

/-- Together with `q3SpectralMeasure_diagonal_energy`, the spectral matrix
average of `ξ ξᵀ / |ξ|²` is `(h²/2) I`. -/
theorem main_q3SpectralHelmholtz_matrix_mean (h : ℝ) :
    (∫ ξ : Q3FrequencyPlane,
      (ξ.fst ^ 2 / (ξ.fst ^ 2 + ξ.snd ^ 2) : ℝ) ∂q3SpectralMeasure h) = h ^ 2 / 2 ∧
    (∫ ξ : Q3FrequencyPlane,
      (ξ.fst * ξ.snd / (ξ.fst ^ 2 + ξ.snd ^ 2) : ℝ) ∂q3SpectralMeasure h) = 0 ∧
    (∫ ξ : Q3FrequencyPlane,
      (ξ.snd ^ 2 / (ξ.fst ^ 2 + ξ.snd ^ 2) : ℝ) ∂q3SpectralMeasure h) = h ^ 2 / 2 := by
  have hdiag := q3SpectralMeasure_diagonal_energy h
  have hcross := main_q3SpectralHelmholtz_cross_zero h
  have hswap := q3SpectralMeasure_integral_swap h
    (fun ξ : Q3FrequencyPlane => ξ.fst ^ 2 / (ξ.fst ^ 2 + ξ.snd ^ 2))
  simp only [q3FrequencySwap, WithLp.toLp_fst, WithLp.toLp_snd, add_comm] at hswap
  exact ⟨hswap.symm.trans hdiag, hcross, hdiag⟩

end ASDExplicitGamma.Main

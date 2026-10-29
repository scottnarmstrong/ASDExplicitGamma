module

public import ASDExplicitGamma.Model.Q3Kernel
public import ASDExplicitGamma.Model.SpectralDensity
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

open MeasureTheory FourierTransform Complex

namespace ASDExplicitGamma.Model

private theorem fourier_norm_bound (f : ℝ → ℂ) (x : ℝ) :
    ‖𝓕 f x‖ ≤ ∫ y, ‖f y‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) f x

private theorem weighted_square_bound {x y A : ℝ} (hy : 0 ≤ y)
    (h : (1 + x ^ 2) * y ≤ A) :
    (1 + x ^ 2) * y ^ 2 ≤ A ^ 2 * (1 + x ^ 2)⁻¹ := by
  have hw : 0 < 1 + x ^ 2 := by positivity
  have hA : 0 ≤ A := (mul_nonneg hw.le hy).trans h
  apply (mul_le_mul_iff_left₀ hw).mp
  rw [mul_assoc (A ^ 2), inv_mul_cancel₀ hw.ne', mul_one]
  have hs := mul_le_mul h h (mul_nonneg hw.le hy) hA
  nlinarith only [hs]

/-- A compactly supported `C²` function has a finite quadratic Fourier moment. -/
theorem integrable_weighted_fourier_sq_of_contDiff_two
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Integrable (fun x : ℝ => (1 + x ^ 2) * ‖𝓕 f x‖ ^ 2) := by
  have hf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have hi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hs
  have hi1 : Integrable (deriv f) := hf1.continuous.integrable_of_hasCompactSupport hs.deriv
  have hi2 : Integrable (deriv (deriv f)) :=
    (hf1.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport hs.deriv.deriv
  have hd1 := Real.fourier_deriv hi (hf.differentiable (by norm_num)) hi1
  have hd2 := Real.fourier_deriv hi1 (hf1.differentiable (by norm_num)) hi2
  let B : ℝ := ∫ y, ‖deriv (deriv f) y‖
  let C : ℝ := (∫ y, ‖f y‖) + B / (2 * Real.pi) ^ 2
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hbound (x : ℝ) : (1 + x ^ 2) * ‖𝓕 f x‖ ≤ C := by
    have h2 := fourier_norm_bound (deriv (deriv f)) x
    rw [hd2, hd1] at h2
    simp only [smul_eq_mul, norm_mul, norm_ofNat, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one] at h2
    have hxx : |x| * |x| = x ^ 2 := sq_abs x ▸ (pow_two |x|).symm
    have hsecond : x ^ 2 * ‖𝓕 f x‖ ≤ B / (2 * Real.pi) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hpi)).mpr
      calc
        x ^ 2 * ‖𝓕 f x‖ * (2 * Real.pi) ^ 2 =
            (2 * Real.pi * |x|) * ((2 * Real.pi * |x|) * ‖𝓕 f x‖) := by
          rw [← hxx]
          ring
        _ ≤ B := h2
    have hbase := fourier_norm_bound f x
    dsimp [C]
    nlinarith only [hbase, hsecond]
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi
  apply (integrable_inv_one_add_sq.const_mul (C ^ 2)).mono' 
  · exact ((continuous_const.add (continuous_id.pow 2)).mul (hcont.norm.pow 2)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (sq_nonneg _))]
      exact weighted_square_bound (norm_nonneg _) (hbound x)

/-- The Fourier transform of the q3 smoothing kernel. -/
noncomputable def q3FourierKernel (ξ : ℝ) : ℂ :=
  𝓕 (fun x : ℝ => (q3Kernel x : ℂ)) ξ

/-- The one-dimensional nonnegative spectral density. -/
noncomputable def q3SpectralDensity1 (ξ : ℝ) : ℝ := ‖q3FourierKernel ξ‖ ^ 2

theorem q3FourierKernel_continuous : Continuous q3FourierKernel :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ q3Kernel_integrable.ofReal

theorem q3SpectralDensity1_continuous : Continuous q3SpectralDensity1 :=
  q3FourierKernel_continuous.norm.pow 2

/-- The q3 spectral density has an integrable quadratic moment. -/
theorem q3SpectralDensity1_weighted_integrable :
    Integrable (fun ξ : ℝ => (1 + ξ ^ 2) * q3SpectralDensity1 ξ) := by
  apply integrable_weighted_fourier_sq_of_contDiff_two
  · exact Complex.ofRealCLM.contDiff.comp q3Kernel_contDiff_two
  · exact q3Kernel_hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)

/-- The q3 spectral density is integrable. -/
theorem q3SpectralDensity1_integrable : Integrable q3SpectralDensity1 := by
  have hc : Continuous q3SpectralDensity1 := by
    apply Continuous.pow _ 2
    apply Continuous.norm
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ q3Kernel_integrable.ofReal
  apply q3SpectralDensity1_weighted_integrable.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (show 0 ≤ q3SpectralDensity1 ξ from sq_nonneg _)]
    exact le_mul_of_one_le_left (sq_nonneg _) (by nlinarith only [sq_nonneg ξ])

/-- The second Fourier moment is integrable. -/
theorem q3SpectralDensity1_second_integrable :
    Integrable (fun ξ : ℝ => ξ ^ 2 * q3SpectralDensity1 ξ) := by
  have h := q3SpectralDensity1_weighted_integrable.sub q3SpectralDensity1_integrable
  convert h using 1
  funext ξ
  dsimp only [Pi.sub_apply]
  ring

/-- The product spectral density on two real coordinates, including amplitude. -/
noncomputable def q3SpectralDensity2 (h : ℝ) (ξ : ℝ × ℝ) : ℝ :=
  h ^ 2 * q3SpectralDensity1 ξ.1 * q3SpectralDensity1 ξ.2

/-- Finiteness of the quadratic graph-weight density in two dimensions. -/
theorem q3SpectralDensity2_weighted_integrable (h : ℝ) :
    Integrable (fun ξ : ℝ × ℝ =>
      (1 + ξ.1 ^ 2 + ξ.2 ^ 2) * q3SpectralDensity2 h ξ) (volume.prod volume) := by
  have h0 := q3SpectralDensity1_integrable.mul_prod q3SpectralDensity1_integrable
  have h1 := q3SpectralDensity1_second_integrable.mul_prod q3SpectralDensity1_integrable
  have h2 := q3SpectralDensity1_integrable.mul_prod q3SpectralDensity1_second_integrable
  convert ((h0.add h1).add h2).const_mul (h ^ 2) using 1
  funext ξ
  dsimp [q3SpectralDensity2]
  ring

/-- The frequency plane with its Euclidean inner product. -/
abbrev Q3FrequencyPlane := WithLp 2 (ℝ × ℝ)

theorem q3SpectralDensity2_continuous (h : ℝ) : Continuous (q3SpectralDensity2 h) :=
  (continuous_const.mul (q3SpectralDensity1_continuous.comp continuous_fst)).mul
    (q3SpectralDensity1_continuous.comp continuous_snd)

theorem q3SpectralDensity2_nonneg (h : ℝ) (ξ : ℝ × ℝ) :
    0 ≤ q3SpectralDensity2 h ξ :=
  mul_nonneg (mul_nonneg (sq_nonneg h) (sq_nonneg _)) (sq_nonneg _)

theorem q3SpectralDensity2_integrable (h : ℝ) :
    Integrable (q3SpectralDensity2 h) (volume.prod volume) := by
  apply (q3SpectralDensity2_weighted_integrable h).mono'
    (q3SpectralDensity2_continuous h).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (q3SpectralDensity2_nonneg h ξ)]
    exact le_mul_of_one_le_left (q3SpectralDensity2_nonneg h ξ)
      (by nlinarith only [sq_nonneg ξ.1, sq_nonneg ξ.2])

/-- The q3 spectral measure `h² |q̂(ξ₁)|² |q̂(ξ₂)|² dξ`. -/
noncomputable def q3SpectralMeasure (h : ℝ) : Measure Q3FrequencyPlane :=
  ((volume.prod volume).withDensity
    (fun ξ => ENNReal.ofReal (q3SpectralDensity2 h ξ))).map (WithLp.toLp 2)

instance q3SpectralMeasure_finite (h : ℝ) : IsFiniteMeasure (q3SpectralMeasure h) := by
  let instRawFinite : IsFiniteMeasure ((volume.prod volume).withDensity
      (fun ξ => ENNReal.ofReal (q3SpectralDensity2 h ξ))) :=
    isFiniteMeasure_withDensity
      ((hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall (q3SpectralDensity2_nonneg h))).mp
          (q3SpectralDensity2_integrable h).hasFiniteIntegral).ne
  exact Measure.isFiniteMeasure_map _ _

/-- The graph weight is integrable for the actual planar q3 spectral measure. -/
theorem q3SpectralMeasure_graphWeight_integrable (h : ℝ) :
    Integrable (fun ξ : Q3FrequencyPlane => 1 + ‖ξ‖ ^ 2) (q3SpectralMeasure h) := by
  rw [q3SpectralMeasure, ← MeasurableEquiv.coe_toLp,
    (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding.integrable_map_iff]
  apply (integrable_withDensity_iff_integrable_smul₀'
    (q3SpectralDensity2_continuous h).measurable.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  convert q3SpectralDensity2_weighted_integrable h using 1
  funext ξ
  rw [ENNReal.toReal_ofReal (q3SpectralDensity2_nonneg h ξ)]
  simp only [Function.comp_apply, smul_eq_mul, WithLp.prod_norm_sq_eq_of_L2,
    MeasurableEquiv.toLp_apply, WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs]
  ring

/-- The graph-weight spectral measure is finite. -/
noncomputable def q3SpectralGraphMeasure (h : ℝ) : Measure Q3FrequencyPlane :=
  (q3SpectralMeasure h).withDensity (fun ξ => ENNReal.ofReal (1 + ‖ξ‖ ^ 2))

instance q3SpectralGraphMeasure_finite (h : ℝ) :
    IsFiniteMeasure (q3SpectralGraphMeasure h) :=
  isFiniteMeasure_withDensity
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => by positivity)).mp
      (q3SpectralMeasure_graphWeight_integrable h).hasFiniteIntegral).ne

end ASDExplicitGamma.Model

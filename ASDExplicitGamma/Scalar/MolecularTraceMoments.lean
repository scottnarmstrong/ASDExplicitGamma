module

public import ASDExplicitGamma.Scalar.MolecularStreamMoments

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Variational
open scoped ENNReal

private theorem variance_nonneg (M : ABKModel 2) (h : ℝ) (m : ℤ) :
    0 ≤ shellVarianceSum h M.gamma m :=
  ge_of_tendsto (cutoffPartialStream_variance_tendsto M h m)
    (Filter.Eventually.of_forall fun N => (cutoffPartialVariance M h m N).coe_nonneg)

/-- The true-frame competitor reduces to the dimensionless molecular
variance ratio plus the actual spatial square average. -/
theorem cutoffTraceDefect_le_variance_competitor (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) (ω : Cutoff.CutoffSample 2) :
    cutoffTraceDefect M m k ω ≤
      (shellVarianceSum h M.gamma m / M.nu ^ 2) ^ 2 / 2 +
        2 * cutoffStreamSquareAverage m k ω / M.nu ^ 2 := by
  let σ : ℝ := Annealed.sigmaBar M m
  let B := shellVarianceSum h M.gamma m
  let A := cutoffStreamSquareAverage m k ω
  have hB : 0 ≤ B := variance_nonneg M h m
  have hA : 0 ≤ A :=
    mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg fun x => sq_nonneg _)
  have hfloor : M.nu ≤ σ := nu_le_sigmaBar M m
  have hs : 0 < σ := M.nu_pos.trans_le hfloor
  have hupper : σ - M.nu ≤ B / (2 * M.nu) := by
    have hu := sigmaBar_le_molecular_upper M h hM m
    change σ ≤ M.nu + B / (2 * M.nu) at hu
    linarith only [hu]
  have hdelta : 0 ≤ σ - M.nu := sub_nonneg.mpr hfloor
  have hsq : (σ - M.nu) ^ 2 ≤ (B / (2 * M.nu)) ^ 2 :=
    (sq_le_sq₀ hdelta (div_nonneg hB (mul_nonneg (by norm_num) M.nu_pos.le))).mpr hupper
  have hden : M.nu ^ 2 ≤ M.nu * σ := by nlinarith only [hfloor, M.nu_pos]
  have hp := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * (σ - M.nu) ^ 2)
    (sq_pos_of_pos M.nu_pos) hden
  have hq := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * A)
    (sq_pos_of_pos M.nu_pos) hden
  have hr := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg M.nu)
  have hc := cutoffTraceDefect_le_molecular_competitor M m k ω
  change cutoffTraceDefect M m k ω ≤ 2 * (σ - M.nu) ^ 2 / (M.nu * σ) + 2 * A / (M.nu * σ) at hc
  have halg : 2 * (B / (2 * M.nu)) ^ 2 / M.nu ^ 2 = (B / M.nu ^ 2) ^ 2 / 2 := by
    field_simp [M.nu_pos.ne']
  change cutoffTraceDefect M m k ω ≤ (B / M.nu ^ 2) ^ 2 / 2 + 2 * A / M.nu ^ 2
  linarith only [hc, hp, hq, hr, halg]

/-- Uniform fixed-label L20 trace estimate, with the sharp Gaussian 78 coefficient. -/
theorem cutoffTraceDefect_L20_molecular (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) :
    eLpNorm (cutoffTraceDefect M m k) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((shellVarianceSum h M.gamma m / M.nu ^ 2) ^ 2 / 2 +
        78 * (shellVarianceSum h M.gamma m / M.nu ^ 2)) := by
  let C := (shellVarianceSum h M.gamma m / M.nu ^ 2) ^ 2 / 2
  let c := 2 / M.nu ^ 2
  let A := cutoffStreamSquareAverage m k
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hC : 0 ≤ C := by positivity
  have hc : 0 ≤ c := by positivity
  have hB := variance_nonneg M h m
  have hbound : ∀ᵐ ω ∂μ, ‖cutoffTraceDefect M m k ω‖ ≤ ((fun _ : Cutoff.CutoffSample 2 => C) + c • A) ω := by
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (cutoffTraceDefect_nonneg M m k ω)]
    have hh := cutoffTraceDefect_le_variance_competitor M h hM m k ω
    convert hh using 1; dsimp [C, c, A]; ring
  calc
    _ ≤ eLpNorm ((fun _ : Cutoff.CutoffSample 2 => C) + c • A) 20 μ :=
      eLpNorm_mono_ae_real (cutoffTraceDefect_measurable M m k).aestronglyMeasurable hbound
    _ ≤ eLpNorm (fun _ : Cutoff.CutoffSample 2 => C) 20 μ + eLpNorm (c • A) 20 μ := eLpNorm_add_le (by norm_num)
    _ = ENNReal.ofReal C + ENNReal.ofReal c * eLpNorm A 20 μ := by
      rw [eLpNorm_const' C (by norm_num) (by norm_num), eLpNorm_const_smul,
        Real.enorm_of_nonneg hC, Real.enorm_of_nonneg hc]
      simp only [measure_univ, ENNReal.one_rpow, mul_one]
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal c * ENNReal.ofReal (39 * shellVarianceSum h M.gamma m) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (cutoffStreamSquareAverage_L20 M h hM m k) (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal c))
    _ = _ := by
      rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add hC (mul_nonneg hc (mul_nonneg (by norm_num) hB))]
      congr 1
      dsimp [C, c]
      ring

/-- Integrability of each actual completed-law trace observable follows from
the molecular competitor and the physical stream-square average. -/
theorem integrable_cutoffTraceDefect_molecular (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) :
    Integrable (cutoffTraceDefect M m k) (Cutoff.cutoffSampleLaw M).toMeasure := by
  let C := (shellVarianceSum h M.gamma m / M.nu ^ 2) ^ 2 / 2
  let c := 2 / M.nu ^ 2
  have hg : Integrable (fun ω => C + c * cutoffStreamSquareAverage m k ω)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (integrable_const C).add ((integrable_cutoffStreamSquareAverage M h hM m k).const_mul c)
  apply hg.mono' (cutoffTraceDefect_measurable M m k).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (cutoffTraceDefect_nonneg M m k ω)]
  have hh := cutoffTraceDefect_le_variance_competitor M h hM m k ω
  convert hh using 1; dsimp [C, c]; ring

/-- Uniform fixed-label mean trace estimate; the mean uses the true point
variance B_m, rather than the fortieth-moment constant. -/
theorem cutoffTraceDefect_mean_molecular (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) :
    (∫⁻ ω, ENNReal.ofReal (cutoffTraceDefect M m k ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal ((shellVarianceSum h M.gamma m / M.nu ^ 2) ^ 2 / 2 +
        2 * (shellVarianceSum h M.gamma m / M.nu ^ 2)) := by
  let C := (shellVarianceSum h M.gamma m / M.nu ^ 2) ^ 2 / 2
  let c := 2 / M.nu ^ 2
  have hA := integrable_cutoffStreamSquareAverage M h hM m k
  have hg : Integrable (fun ω => C + c * cutoffStreamSquareAverage m k ω)
      (Cutoff.cutoffSampleLaw M).toMeasure := (integrable_const C).add (hA.const_mul c)
  have hi := integrable_cutoffTraceDefect_molecular M h hM m k
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (cutoffTraceDefect_nonneg M m k))]
  apply ENNReal.ofReal_le_ofReal
  have hb := integral_mono hi hg (fun ω => by
    have hh := cutoffTraceDefect_le_variance_competitor M h hM m k ω
    convert hh using 1; dsimp [C, c]; ring)
  have he : (∫ ω, (C + c * cutoffStreamSquareAverage m k ω)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) = C + c * shellVarianceSum h M.gamma m := by
    rw [integral_add (integrable_const C) (hA.const_mul c), integral_const,
      probReal_univ, one_smul, integral_const_mul, integral_cutoffStreamSquareAverage M h hM m k]
  rw [he] at hb
  convert hb using 1; dsimp [C, c]; ring

end ASDExplicitGamma.Scalar

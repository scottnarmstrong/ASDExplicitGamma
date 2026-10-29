module

public import ASDExplicitGamma.Scalar.MolecularCutoffCompetitor
public import ASDExplicitGamma.Scalar.MolecularMomentNorm
public import ASDExplicitGamma.Model.CutoffGaussian
public import ASDExplicitGamma.Model.CutoffVariance
public import ASDExplicitGamma.Gaussian.MolecularMoments
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal NNReal

/-- Joint measurability of the literal completed scalar stream. -/
theorem measurable_cutoff_stream_joint (m : ℤ) :
    Measurable (fun p : Cutoff.CutoffSample 2 × Vec 2 => Cutoff.cutoffValue m p.1 p.2 1 0) := by
  have hh := measurable_uncurry_of_continuous_of_measurable
    (u := fun x : Vec 2 => fun ω : Cutoff.CutoffSample 2 => Cutoff.cutoffValue m ω x 1 0)
    (fun ω => Cutoff.continuous_cutoffValue_entry m ω 1 0)
    (fun x => Cutoff.measurable_cutoff_apply_entry m x 1 0)
  exact hh.comp measurable_swap

/-- All fortieth moments are integrable and constant across spatial points. -/
theorem cutoff_stream_fortieth_moment (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (x : Vec 2) :
    Integrable (fun ω => Cutoff.cutoffValue m ω x 1 0 ^ 40) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, Cutoff.cutoffValue m ω x 1 0 ^ 40 ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ z : ℝ, z ^ 40 ∂gaussianReal 0 (Real.toNNReal (shellVarianceSum h M.gamma m)) := by
  let v := Real.toNNReal (shellVarianceSum h M.gamma m)
  have hg : Integrable (fun z : ℝ => z ^ 40) (gaussianReal 0 v) := by
    have hh := (memLp_id_gaussianReal' (μ := 0) (v := v) 40 (by norm_num)).integrable_norm_pow
      (by norm_num : (40 : ℕ) ≠ 0)
    apply hh.congr
    exact Filter.Eventually.of_forall fun z => by
      simp only [id_eq, Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 40)]
  have hl := cutoffStream_gaussian M h hM m x
  exact ⟨hl.integrable_fun_comp hg, hl.integral_comp (f := fun z : ℝ => z ^ 40) (by fun_prop)⟩

private theorem cutoff_stream_fortieth_product_integrable (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) :
    Integrable (fun p : Cutoff.CutoffSample 2 × Vec 2 => Cutoff.cutoffValue m p.1 p.2 1 0 ^ 40)
      ((Cutoff.cutoffSampleLaw M).toMeasure.prod (volume.restrict (cubeSet (originCube 2 k)))) := by
  apply (integrable_prod_iff' ((measurable_cutoff_stream_joint m).pow_const 40).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => (cutoff_stream_fortieth_moment M h hM m x).1), ?_⟩
  have he : (fun x : Vec 2 => ∫ ω, ‖Cutoff.cutoffValue m ω x 1 0 ^ 40‖
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) = fun _ =>
      ∫ z : ℝ, z ^ 40 ∂gaussianReal 0 (Real.toNNReal (shellVarianceSum h M.gamma m)) := by
    funext x
    simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Cutoff.cutoffValue m _ x 1 0 ^ 40)]
    exact (cutoff_stream_fortieth_moment M h hM m x).2
  rw [he]
  exact integrable_const _

/-- Jensen's inequality compares the twentieth power of the spatial square
average to the spatial fortieth-moment average, on each actual sample. -/
theorem cutoffStreamSquareAverage_pow_twenty_le (m k : ℤ) (ω : Cutoff.CutoffSample 2) :
    cutoffStreamSquareAverage m k ω ^ 20 ≤
      volumeAverage (cubeSet (originCube 2 k)) (fun x => Cutoff.cutoffValue m ω x 1 0 ^ 40) := by
  let Q := originCube 2 k
  have h40 : IntegrableOn (fun x => Cutoff.cutoffValue m ω x 1 0 ^ 40) (cubeSet Q) := by
    apply ((Cutoff.continuous_cutoffValue_entry m ω 1 0).pow 40).continuousOn.integrableOn_of_subset_isCompact
      (isBounded_cubeSet Q).isCompact_closure (measurableSet_cubeSet Q) subset_closure
    exact (volume_cubeSet_lt_top Q).ne
  have hvol : volume (cubeSet Q) ≠ 0 := by
    intro hz
    have hv := volume_cubeSet_toReal_pos Q
    rw [hz, ENNReal.toReal_zero] at hv
    exact lt_irrefl 0 hv
  have hcomp : IntegrableOn ((fun z : ℝ => z ^ 20) ∘
      (fun x => Cutoff.cutoffValue m ω x 1 0 ^ 2)) (cubeSet Q) := by
    convert h40 using 1
    funext x
    simp only [Function.comp_apply, ← pow_mul]
  have hj := (convexOn_pow (𝕜 := ℝ) 20).map_set_average_le (by fun_prop)
    isClosed_Ici hvol (volume_cubeSet_lt_top Q).ne
    (Filter.Eventually.of_forall (fun x => sq_nonneg (Cutoff.cutoffValue m ω x 1 0)))
    (cutoff_stream_square_integrable m k ω)
    hcomp
  simpa only [MeasureTheory.setAverage_eq, Measure.real, smul_eq_mul,
    cutoffStreamSquareAverage, volumeAverage, ← pow_mul] using hj

/-- Measurability of the spatial stream-square average on the actual carrier. -/
theorem measurable_cutoffStreamSquareAverage (m k : ℤ) : Measurable (cutoffStreamSquareAverage m k) := by
  have hh := ((measurable_cutoff_stream_joint m).pow_const 2).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (cubeSet (originCube 2 k)))
  change Measurable (fun ω : Cutoff.CutoffSample 2 =>
    (volume (cubeSet (originCube 2 k))).toReal⁻¹ *
      ∫ x in cubeSet (originCube 2 k), Cutoff.cutoffValue m ω x 1 0 ^ 2)
  exact hh.measurable.const_mul _

/-- The expected normalized fortieth-moment average is its pointwise Gaussian moment. -/
theorem integral_cutoff_stream_fortieth_average (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) :
    (∫ ω, volumeAverage (cubeSet (originCube 2 k)) (fun x => Cutoff.cutoffValue m ω x 1 0 ^ 40)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ z : ℝ, z ^ 40 ∂gaussianReal 0 (Real.toNNReal (shellVarianceSum h M.gamma m)) := by
  let Q := originCube 2 k
  have hs := integral_integral_swap
    (f := fun ω : Cutoff.CutoffSample 2 => fun x : Vec 2 => Cutoff.cutoffValue m ω x 1 0 ^ 40)
    (cutoff_stream_fortieth_product_integrable M h hM m k)
  have he : (fun x : Vec 2 => ∫ ω, Cutoff.cutoffValue m ω x 1 0 ^ 40
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) = fun _ =>
      ∫ z : ℝ, z ^ 40 ∂gaussianReal 0 (Real.toNNReal (shellVarianceSum h M.gamma m)) := by
    funext x
    exact (cutoff_stream_fortieth_moment M h hM m x).2
  unfold volumeAverage
  rw [integral_const_mul, hs, he]
  exact volumeAverage_const (volume_cubeSet_toReal_pos Q).ne'

/-- Jensen and Fubini give the exact spatial twentieth-moment estimate. -/
theorem cutoffStreamSquareAverage_twentieth_moment (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) :
    Integrable (fun ω => cutoffStreamSquareAverage m k ω ^ 20) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, cutoffStreamSquareAverage m k ω ^ 20 ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (39 * shellVarianceSum h M.gamma m) ^ 20 := by
  let v : ℝ := (volume (cubeSet (originCube 2 k))).toReal
  have hi40 : Integrable (fun ω => volumeAverage (cubeSet (originCube 2 k))
      (fun x => Cutoff.cutoffValue m ω x 1 0 ^ 40)) (Cutoff.cutoffSampleLaw M).toMeasure :=
    (cutoff_stream_fortieth_product_integrable M h hM m k).integral_prod_left.const_mul v⁻¹
  have hi20 : Integrable (fun ω => cutoffStreamSquareAverage m k ω ^ 20)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    apply hi40.mono' ((measurable_cutoffStreamSquareAverage m k).pow_const 20).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ cutoffStreamSquareAverage m k ω ^ 20)]
      exact cutoffStreamSquareAverage_pow_twenty_le m k ω
  refine ⟨hi20, ?_⟩
  have hh := integral_mono hi20 hi40 (cutoffStreamSquareAverage_pow_twenty_le m k)
  rw [integral_cutoff_stream_fortieth_average M h hM m k] at hh
  have hB : 0 ≤ shellVarianceSum h M.gamma m :=
    ge_of_tendsto (cutoffPartialStream_variance_tendsto M h m)
      (Filter.Eventually.of_forall fun N => (cutoffPartialVariance M h m N).coe_nonneg)
  have hg := integral_gaussian_pow_forty_le_variance (Real.toNNReal (shellVarianceSum h M.gamma m))
  rw [Real.coe_toNNReal _ hB] at hg
  exact hh.trans hg

/-- The sharp L20 stream-square bound is uniform in the observation scale. -/
theorem cutoffStreamSquareAverage_L20 (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) :
    eLpNorm (cutoffStreamSquareAverage m k) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (39 * shellVarianceSum h M.gamma m) := by
  have hp (ω : Cutoff.CutoffSample 2) : 0 ≤ cutoffStreamSquareAverage m k ω :=
    mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg fun x => sq_nonneg _)
  have hB : 0 ≤ shellVarianceSum h M.gamma m :=
    ge_of_tendsto (cutoffPartialStream_variance_tendsto M h m)
      (Filter.Eventually.of_forall fun N => (cutoffPartialVariance M h m N).coe_nonneg)
  obtain ⟨hi, hb⟩ := cutoffStreamSquareAverage_twentieth_moment M h hM m k
  exact eLpNorm_twenty_le_of_integral_pow (measurable_cutoffStreamSquareAverage m k).aestronglyMeasurable
    (Filter.Eventually.of_forall hp) hi (mul_nonneg (by norm_num) hB) hb

private theorem cutoff_stream_square_product_integrable (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) :
    Integrable (fun p : Cutoff.CutoffSample 2 × Vec 2 => Cutoff.cutoffValue m p.1 p.2 1 0 ^ 2)
      ((Cutoff.cutoffSampleLaw M).toMeasure.prod (volume.restrict (cubeSet (originCube 2 k)))) := by
  apply (integrable_prod_iff' ((measurable_cutoff_stream_joint m).pow_const 2).aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro x
    have hh := ((cutoffStream_gaussian M h hM m x).memLp
      (memLp_id_gaussianReal' 2 (by norm_num))).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    simpa only [Real.norm_eq_abs, sq_abs] using hh
  · have he : (fun x : Vec 2 => ∫ ω, ‖Cutoff.cutoffValue m ω x 1 0 ^ 2‖
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) = fun _ => shellVarianceSum h M.gamma m := by
      funext x
      have heq (ω : Cutoff.CutoffSample 2) : |Cutoff.cutoffValue m ω x 1 0 ^ 2| =
          Cutoff.cutoffValue m ω x 1 0 ^ 2 := abs_of_nonneg (sq_nonneg _)
      simp only [Real.norm_eq_abs, heq]
      exact q3_cutoff_stream_second_moment M h hM m x
    rw [he]
    exact integrable_const _

/-- Expected stream-square average equals the actual accumulated variance,
uniformly over all observation scales. -/
theorem integral_cutoffStreamSquareAverage (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) :
    (∫ ω, cutoffStreamSquareAverage m k ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      shellVarianceSum h M.gamma m := by
  have hs := integral_integral_swap
    (f := fun ω : Cutoff.CutoffSample 2 => fun x : Vec 2 => Cutoff.cutoffValue m ω x 1 0 ^ 2)
    (cutoff_stream_square_product_integrable M h hM m k)
  have he : (fun x : Vec 2 => ∫ ω, Cutoff.cutoffValue m ω x 1 0 ^ 2
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) = fun _ => shellVarianceSum h M.gamma m := by
    funext x
    exact q3_cutoff_stream_second_moment M h hM m x
  unfold cutoffStreamSquareAverage volumeAverage
  rw [integral_const_mul, hs, he]
  exact volumeAverage_const (volume_cubeSet_toReal_pos (originCube 2 k)).ne'

/-- The actual spatial square average is integrable. -/
theorem integrable_cutoffStreamSquareAverage (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) :
    Integrable (cutoffStreamSquareAverage m k) (Cutoff.cutoffSampleLaw M).toMeasure :=
  (cutoff_stream_square_product_integrable M h hM m k).integral_prod_left.const_mul _

end ASDExplicitGamma.Scalar

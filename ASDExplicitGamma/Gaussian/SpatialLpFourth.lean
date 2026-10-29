module

public import ASDExplicitGamma.Gaussian.SpatialKernelFourth
public import ASDExplicitGamma.Gaussian.Q3ContinuousOperator
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # The physical convolution as an operator into spatial L⁴ -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

/-- Ordinary spatial Lebesgue measure on a compact spatial carrier. -/
noncomputable def spatialVolume (K : Set (Vec 2)) : Measure K :=
  Measure.comap Subtype.val volume

theorem spatialVolume_univ (K : Set (Vec 2)) [CompactSpace K] :
    spatialVolume K Set.univ = volume K := by
  have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  rw [spatialVolume, comap_subtype_coe_apply hK.isClosed.measurableSet]
  simp only [Subtype.range_coe_subtype, Set.image_univ, Set.ofPred_mem_eq]

instance spatialVolume_isFiniteMeasure (K : Set (Vec 2)) [CompactSpace K] :
    IsFiniteMeasure (spatialVolume K) := by
  constructor
  rw [spatialVolume_univ]
  exact (isCompact_iff_compactSpace.mpr inferInstance).measure_lt_top

/-- The scalar spatial L⁴ carrier, with ordinary (unnormalized) Lebesgue measure. -/
noncomputable abbrev SpatialLp4 (K : Set (Vec 2)) := Lp ℝ 4 (spatialVolume K)

instance spatialLp4_fact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

instance spatialLp4_ne_top : Fact ((4 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

noncomputable instance spatialLp4_measurableSpace (K : Set (Vec 2)) :
    MeasurableSpace (SpatialLp4 K) := borel _

instance spatialLp4_borelSpace (K : Set (Vec 2)) : BorelSpace (SpatialLp4 K) := ⟨rfl⟩

/-- The actual physical convolution followed by the canonical spatial L⁴ inclusion. -/
noncomputable def q3SpatialLp4Operator (K : Set (Vec 2)) [CompactSpace K]
    (β : ℝ) (L : {l : ℝ // 0 < l}) : WhiteNoise →L[ℝ] SpatialLp4 K :=
  (ContinuousMap.toLp 4 (spatialVolume K) ℝ).comp
    (q3ContinuousOperator K β L h3Zero)

/-- The fourth power of an L⁴ norm is the ordinary fourth moment. -/
theorem lp4_norm_pow_four {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Lp ℝ 4 μ) : ‖f‖ ^ 4 = ∫ x, f x ^ 4 ∂μ := by
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (integral_nonneg fun x => by positivity)]
  norm_num
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change |f x| ^ (4 : ℕ) = f x ^ (4 : ℕ)
    rw [pow_abs, abs_of_nonneg (by positivity)]

/-- No representative ambiguity remains in the spatial fourth moment of a physical convolution. -/
theorem q3SpatialLp4Operator_norm_pow_four (K : Set (Vec 2)) [CompactSpace K]
    (β : ℝ) (L : {l : ℝ // 0 < l}) (u : WhiteNoise) :
    ‖q3SpatialLp4Operator K β L u‖ ^ 4 =
      ∫ x in K, q3Convolution β L h3Zero u x ^ 4 ∂volume := by
  rw [lp4_norm_pow_four]
  have he := ContinuousMap.coeFn_toLp (p := 4) (spatialVolume K) (𝕜 := ℝ)
    (q3ContinuousOperator K β L h3Zero u)
  change (∫ x : K, (q3SpatialLp4Operator K β L u) x ^ 4 ∂spatialVolume K) = _
  calc
    _ = ∫ x : K, q3Convolution β L h3Zero u x.1 ^ 4 ∂spatialVolume K := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      exact congrArg (fun r : ℝ => r ^ 4) hx
    _ = _ := by
      exact integral_subtype_comap
        (isCompact_iff_compactSpace.mpr inferInstance : IsCompact K).isClosed.measurableSet
        (fun x => q3Convolution β L h3Zero u x ^ 4)

/-- The fine-shell estimate in the squared spatial norm. -/
theorem q3SpatialLp4Operator_norm_sq_le_fine (K : Set (Vec 2)) [CompactSpace K]
    (β : ℝ) (L : {l : ℝ // 0 < l}) (u : WhiteNoise) :
    ‖q3SpatialLp4Operator K β L u‖ ^ 2 ≤ β ^ 2 * L.1 * ‖u‖ ^ 2 := by
  have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  have hfinite : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hh := integral_q3Convolution_pow_four_le_fine β L u (volume.restrict K)
    Measure.restrict_le_self
  rw [← q3SpatialLp4Operator_norm_pow_four K β L u] at hh
  apply (sq_le_sq₀ (sq_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg β) L.2.le) (sq_nonneg ‖u‖))).mp
  convert hh using 1 <;> ring

/-- The coarse-shell estimate in the squared spatial norm. -/
theorem q3SpatialLp4Operator_norm_sq_le_coarse (K : Set (Vec 2)) [CompactSpace K]
    (β : ℝ) (L : {l : ℝ // 0 < l}) (u : WhiteNoise) :
    ‖q3SpatialLp4Operator K β L u‖ ^ 2 ≤ β ^ 2 * Real.sqrt (volume.real K) * ‖u‖ ^ 2 := by
  have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  have hfinite : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hh := integral_q3Convolution_pow_four_le_coarse β L u (volume.restrict K)
  rw [← q3SpatialLp4Operator_norm_pow_four K β L u] at hh
  have hm : (volume.restrict K).real Set.univ = volume.real K := by
    simp only [measureReal_def, Measure.restrict_apply_univ]
  rw [hm] at hh
  apply (sq_le_sq₀ (sq_nonneg _) (by positivity : 0 ≤ β ^ 2 * Real.sqrt (volume.real K) * ‖u‖ ^ 2)).mp
  calc
    _ = ‖q3SpatialLp4Operator K β L u‖ ^ 4 := by ring
    _ ≤ _ := hh
    _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt measureReal_nonneg]; ring

end ASDExplicitGamma.Gaussian

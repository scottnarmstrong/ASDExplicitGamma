module

public import ASDExplicitGamma.Gaussian.WholeRoot
public import ASDExplicitGamma.Gaussian.NormalScaledMoments
public import ASDExplicitGamma.Inverse.ClippedMatrixConditional
public import ASDExplicitGamma.Response.CoefficientFamily
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # All-order moments of the later q3 wave -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

section
variable {n : ℕ} [NeZero n] (a b c d : ℝ) (β w : Fin n → ℝ)
  (L : Fin n → {l : ℝ // 0 < l})

/-- The pointwise even moments of a retained physical band are bounded by its total
attenuated point variance. -/
theorem q3WeightedBandPartialValue_point_moment_le (hab : a < b) (hcd : c < d)
    (x : closedRectangle a b c d) (N : ℕ) {V : ℝ} (hV :
      (∑ i, w i ^ 2 * β i ^ 2) ≤ V) (k : ℕ) (hk : 1 ≤ k) :
    (∫ ω, q3WeightedBandPartialValue a b c d β w L N ω x ^ (2 * k)
      ∂standardGaussianInfinitePi) ≤ (2 * (k : ℝ)) ^ k * V ^ k := by
  let F := q3WeightedBandPartialValue a b c d β w L N
  let s : ℝ := ∑ j ∈ Finset.range N,
    (q3WeightedBandH3Value a b c d β w L
      (q3BandH3Directions a b c d β L j) x) ^ 2
  have hs : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg fun j hj => by positivity
  have hsum : s ≤ ∑ i, w i ^ 2 * β i ^ 2 := by
    dsimp [s]
    exact q3WeightedBandH3Value_partial_variance_le a b c d β w L hab hcd x N
  have hV0 : 0 ≤ V := le_trans (Finset.sum_nonneg fun i hi => by positivity) hV
  have hfield : MemLp F (ENNReal.ofReal (2 * (k : ℝ))) standardGaussianInfinitePi := by
    exact memLp_q3WeightedBandPartialValue a b c d β w L
      (show 2 ≤ 2 * (k : ℝ) by exact_mod_cast (show 2 ≤ 2 * k by omega)) N
  have heval := (ContinuousMap.evalCLM ℝ x).continuous.comp_aestronglyMeasurable
    hfield.aestronglyMeasurable
  have hlaw := q3WeightedBandPartialValue_point_law a b c d β w L x N
  have hmoment : (∫ ω, F ω x ^ (2 * k) ∂standardGaussianInfinitePi) =
      ∫ y : ℝ, y ^ (2 * k) ∂gaussianReal 0 (Real.toNNReal s) := by
    rw [← integral_map (φ := fun ω => F ω x) (f := fun y : ℝ => y ^ (2 * k))
      heval.aemeasurable (by fun_prop), hlaw]
  have hgauss := integral_gaussianReal_pow_even_le (Real.toNNReal s) k
  have hvariance : (Real.toNNReal s : ℝ) ≤ V := by
    rw [Real.coe_toNNReal _ hs]
    exact hsum.trans hV
  rw [hmoment]
  calc
    _ ≤ (2 * (k : ℝ)) ^ k * (Real.toNNReal s : ℝ) ^ k := hgauss
    _ ≤ (2 * (k : ℝ)) ^ k * V ^ k := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (show 0 ≤ (Real.toNNReal s : ℝ) by positivity) hvariance k)
        (by positivity)

/-- On a finite spatial carrier, the L⁴ norm is controlled by every even Lᵖ norm
of order at least four, with the exact finite-volume factor. -/
theorem continuousMap_toLp4_evenMoment_le {K : Type*} [PseudoMetricSpace K]
    [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    (ν : Measure K) [IsFiniteMeasure ν] (f : C(K, ℝ)) (k : ℕ) (hk : 2 ≤ k) :
    ‖ContinuousMap.toLp 4 ν ℝ f‖ ^ (2 * k) ≤
      (∫ x, |f x| ^ (2 * k) ∂ν) * (ν.real Set.univ) ^ ((k : ℝ) / 2 - 1) := by
  have hmem4 : MemLp f (ENNReal.ofReal 4) ν :=
    f.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hmem2k : MemLp f (ENNReal.ofReal (2 * (k : ℝ))) ν :=
    f.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hq : ENNReal.ofReal 4 ≤ ENNReal.ofReal (2 * (k : ℝ)) := by
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast (show 4 ≤ 2 * k by omega))
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq hmem4.aestronglyMeasurable
  have hexp : 1 / (ENNReal.ofReal 4).toReal -
      1 / (ENNReal.ofReal (2 * (k : ℝ))).toReal = (1 / 4 : ℝ) - 1 / (2 * k) := by
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (4 : ℝ)),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (k : ℝ))]
  have hexp0 : 0 ≤ 1 / (ENNReal.ofReal 4).toReal -
      1 / (ENNReal.ofReal (2 * (k : ℝ))).toReal := by
    rw [hexp]
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : 0 < (2 * (k : ℝ)) := by positivity
    have hdiv : 1 / (2 * (k : ℝ)) ≤ (1 / 4 : ℝ) := by
      apply (div_le_div_iff₀ hkpos (by norm_num : (0 : ℝ) < 4)).2
      nlinarith
    linarith
  have htop : (eLpNorm f (ENNReal.ofReal (2 * (k : ℝ))) ν *
      ν Set.univ ^ (1 / (ENNReal.ofReal 4).toReal -
        1 / (ENNReal.ofReal (2 * (k : ℝ))).toReal)) ≠ ∞ := by
    exact ENNReal.mul_ne_top hmem2k.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hexp0 (measure_ne_top ν Set.univ))
  have hcmpR := ENNReal.toReal_mono htop hcmp
  have hL4 : (eLpNorm f (ENNReal.ofReal 4) ν).toReal =
      ‖ContinuousMap.toLp 4 ν ℝ f‖ := by
    rw [Lp.norm_def]
    simpa only [ENNReal.ofReal_ofNat] using congrArg ENNReal.toReal
      (eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (p := 4) ν (𝕜 := ℝ) f).symm)
  have hIeq : (∫ x, |f x| ^ (2 * (k : ℝ)) ∂ν) =
      ∫ x, |f x| ^ (2 * k) ∂ν := by
    apply integral_congr_ae
    filter_upwards with x
    rw [show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by norm_cast,
      Real.rpow_natCast]
  have hL2k : (eLpNorm f (ENNReal.ofReal (2 * (k : ℝ))) ν).toReal =
      (∫ x, |f x| ^ (2 * k) ∂ν) ^ (1 / (2 * (k : ℝ))) := by
    rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top
      hmem2k.aestronglyMeasurable]
    have hqnonneg : 0 ≤ 2 * (k : ℝ) := by positivity
    simp only [ENNReal.toReal_ofReal hqnonneg, Real.norm_eq_abs]
    congr 1
    norm_num [one_div]
  have harea : (ν Set.univ).toReal = ν.real Set.univ := by
    rfl
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, hL4, hL2k, harea, hexp] at hcmpR
  have hI0 : 0 ≤ ∫ x, |f x| ^ (2 * (k : ℝ)) ∂ν :=
    integral_nonneg fun x => by positivity
  have hA0 : 0 ≤ ν.real Set.univ := measureReal_nonneg
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hcmpR (2 * k)
  have hIexp : ((∫ x, |f x| ^ (2 * k) ∂ν) ^ ((1 : ℝ) / (2 * (k : ℝ)))) ^ (2 * k) =
      ∫ x, |f x| ^ (2 * k) ∂ν := by
    let I := ∫ x, |f x| ^ (2 * k) ∂ν
    have he : ((1 : ℝ) / (2 * (k : ℝ))) * ((2 * k : ℕ) : ℝ) = 1 := by
      field_simp
      norm_cast
    have hI0' : 0 ≤ I := integral_nonneg fun x => by positivity
    change (I ^ ((1 : ℝ) / (2 * (k : ℝ)))) ^ (2 * k) = I
    calc
      _ = (I ^ ((1 : ℝ) / (2 * (k : ℝ)))) ^ ((2 * k : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
      _ = I ^ ((1 / (2 * (k : ℝ))) * ((2 * k : ℕ) : ℝ)) :=
        (Real.rpow_mul hI0' _ _).symm
      _ = I := by rw [he, Real.rpow_one]
  have hAexp : ((ν.real Set.univ) ^ ((1 / 4 : ℝ) - 1 / (2 * k))) ^ (2 * k) =
      (ν.real Set.univ) ^ ((k : ℝ) / 2 - 1) := by
    have he : ((1 / 4 : ℝ) - 1 / (2 * (k : ℝ))) * ((2 * k : ℕ) : ℝ) =
        (k : ℝ) / 2 - 1 := by
      field_simp
      push_cast
      ring
    calc
      _ = (ν.real Set.univ ^ ((1 / 4 : ℝ) - 1 / (2 * (k : ℝ)))) ^
          ((2 * k : ℕ) : ℝ) := by rw [Real.rpow_natCast]
      _ = ν.real Set.univ ^ (((1 / 4 : ℝ) - 1 / (2 * (k : ℝ))) * ((2 * k : ℕ) : ℝ)) :=
        (Real.rpow_mul hA0 _ _).symm
      _ = _ := by rw [he]
  rw [mul_pow, hIexp, hAexp] at hpow
  exact hpow

/-- Even moments of the spatial L⁴ norm follow from pointwise Gaussian moments and Fubini. -/
theorem q3WeightedBandPartial_spatial_evenMoment_le {n : ℕ} [NeZero n]
    (a c R : ℝ) (hR : 0 < R) (β w : Fin n → ℝ)
    (L : Fin n → {l : ℝ // 0 < l}) (hab : a < a + R) (hcd : c < c + R)
    (N : ℕ) {V : ℝ} (hV : (∑ i, w i ^ 2 * β i ^ 2) ≤ V) (k : ℕ) (hk : 2 ≤ k) :
    (∫ ω, ‖ContinuousMap.toLp 4 (spatialVolume
      (closedRectangle a (a + R) c (c + R))) ℝ
      (q3WeightedBandPartialValue a (a + R) c (c + R) β w L N ω)‖ ^ (2 * k)
      ∂standardGaussianInfinitePi) ≤ (2 * (k : ℝ)) ^ k * V ^ k * R ^ k := by
  let K := closedRectangle a (a + R) c (c + R)
  let ν := spatialVolume K
  let F := q3WeightedBandPartialValue a (a + R) c (c + R) β w L N
  have hF : MemLp F (ENNReal.ofReal (2 * (k : ℝ))) standardGaussianInfinitePi :=
    memLp_q3WeightedBandPartialValue a (a + R) c (c + R) β w L
      (show 2 ≤ 2 * (k : ℝ) by exact_mod_cast (show 2 ≤ 2 * k by omega)) N
  have hToLp := hF.continuousLinearMap_comp (ContinuousMap.toLp 4 ν ℝ)
  have hToLpMom : Integrable (fun ω => ‖ContinuousMap.toLp 4 ν ℝ (F ω)‖ ^ (2 * k))
      standardGaussianInfinitePi := by
    have hh := hToLp.integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top
    have hexp : (ENNReal.ofReal (2 * (k : ℝ))).toReal = ((2 * k : ℕ) : ℝ) := by
      rw [ENNReal.toReal_ofReal (by positivity)]
      norm_cast
    rw [hexp] at hh
    have heq : (fun ω => ‖ContinuousMap.toLp 4 ν ℝ (F ω)‖ ^ ((2 * k : ℕ) : ℝ)) =
        fun ω => ‖ContinuousMap.toLp 4 ν ℝ (F ω)‖ ^ (2 * k) := by
      funext ω
      exact Real.rpow_natCast _ _
    rw [← heq]
    exact hh
  have hFmom : Integrable (fun ω => ‖F ω‖ ^ (2 * k)) standardGaussianInfinitePi := by
    have hh := hF.integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top
    have hexp : (ENNReal.ofReal (2 * (k : ℝ))).toReal = ((2 * k : ℕ) : ℝ) := by
      rw [ENNReal.toReal_ofReal (by positivity)]
      norm_cast
    rw [hexp] at hh
    have heq : (fun ω => ‖F ω‖ ^ ((2 * k : ℕ) : ℝ)) =
        fun ω => ‖F ω‖ ^ (2 * k) := by
      funext ω
      exact Real.rpow_natCast _ _
    rw [← heq]
    exact hh
  let g : (ℕ → ℝ) × K → ℝ := fun z => F z.1 z.2 ^ (2 * k)
  have hg : AEStronglyMeasurable g (standardGaussianInfinitePi.prod ν) := by
    have hh := continuous_eval.comp_aestronglyMeasurable
      ((hF.aestronglyMeasurable.comp_fst (ν := ν)).prodMk
        (measurable_snd.stronglyMeasurable.aestronglyMeasurable :
          AEStronglyMeasurable (fun z : (ℕ → ℝ) × K => z.2)
            (standardGaussianInfinitePi.prod ν)))
    exact hh.pow _
  have hmajor : Integrable (fun z : (ℕ → ℝ) × K => ‖F z.1‖ ^ (2 * k))
      (standardGaussianInfinitePi.prod ν) := hFmom.comp_fst ν
  have hgint : Integrable g (standardGaussianInfinitePi.prod ν) := by
    refine hmajor.mono' hg ?_
    filter_upwards with z
    dsimp [g]
    rw [← pow_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (ContinuousMap.norm_coe_le_norm (F z.1) z.2) _
  have hinnerInt : Integrable (fun ω => ∫ x, F ω x ^ (2 * k) ∂ν)
      standardGaussianInfinitePi := by
    exact hgint.integral_prod_left
  have houterInt : Integrable (fun x => ∫ ω, F ω x ^ (2 * k)
      ∂standardGaussianInfinitePi) ν := by
    exact hgint.integral_prod_right
  have hswap := integral_integral_swap (f := fun ω x => F ω x ^ (2 * k)) hgint
  have hpoint (x : K) : (∫ ω, F ω x ^ (2 * k)
      ∂standardGaussianInfinitePi) ≤ (2 * (k : ℝ)) ^ k * V ^ k := by
    exact q3WeightedBandPartialValue_point_moment_le a (a + R) c (c + R) β w L
      hab hcd x N hV k (by omega)
  have hpointIntegral : (∫ x, ∫ ω, F ω x ^ (2 * k)
      ∂standardGaussianInfinitePi ∂ν) ≤
      ((2 * (k : ℝ)) ^ k * V ^ k) * ν.real Set.univ := by
    calc
      _ ≤ ∫ x, (2 * (k : ℝ)) ^ k * V ^ k ∂ν :=
        integral_mono houterInt (integrable_const _) hpoint
      _ = _ := by rw [integral_const, smul_eq_mul]; ring
  have harea : ν.real Set.univ = R ^ 2 := by
    dsimp [ν, K]
    exact spatialVolume_square_real (a := a) (c := c) (R := R) hR.le
  have hexp : 0 ≤ (k : ℝ) / 2 - 1 := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hfactor : R ^ 2 * (R ^ 2) ^ ((k : ℝ) / 2 - 1) = R ^ k := by
    have hpow2 : R ^ (2 : ℕ) = R ^ (2 : ℝ) := (Real.rpow_natCast R 2).symm
    have hexpEq : (2 : ℝ) + 2 * ((k : ℝ) / 2 - 1) = (k : ℝ) := by ring
    calc
      _ = R ^ (2 : ℝ) * (R ^ (2 : ℝ)) ^ ((k : ℝ) / 2 - 1) := by rw [hpow2]
      _ = R ^ ((2 : ℝ) + 2 * ((k : ℝ) / 2 - 1)) := by
        rw [(Real.rpow_mul hR.le _ _).symm, ← Real.rpow_add hR]
      _ = R ^ ((k : ℝ)) := by rw [hexpEq]
      _ = R ^ k := Real.rpow_natCast R k
  have harea0 : 0 ≤ ν.real Set.univ := by positivity
  have hEven (ω : ℕ → ℝ) : (∫ x, |F ω x| ^ (2 * k) ∂ν) =
      ∫ x, F ω x ^ (2 * k) ∂ν := by
    apply integral_congr_ae
    filter_upwards with x
    calc
      |F ω x| ^ (2 * k) = (|F ω x| ^ 2) ^ k := by rw [pow_mul]
      _ = (F ω x ^ 2) ^ k := by rw [sq_abs]
      _ = F ω x ^ (2 * k) := by rw [pow_mul]
  have hscaleInt := integral_mono hToLpMom
    (hinnerInt.const_mul ((ν.real Set.univ) ^ ((k : ℝ) / 2 - 1)))
    (fun ω => by
      calc
        ‖ContinuousMap.toLp 4 ν ℝ (F ω)‖ ^ (2 * k) ≤
            (∫ x, |F ω x| ^ (2 * k) ∂ν) * (ν.real Set.univ) ^ ((k : ℝ) / 2 - 1) :=
          continuousMap_toLp4_evenMoment_le ν (F ω) k hk
        _ = (ν.real Set.univ) ^ ((k : ℝ) / 2 - 1) *
            (∫ x, F ω x ^ (2 * k) ∂ν) := by rw [hEven ω]; ring)
  calc
    _ ≤ (∫ ω, (ν.real Set.univ) ^ ((k : ℝ) / 2 - 1) *
        (∫ x, F ω x ^ (2 * k) ∂ν) ∂standardGaussianInfinitePi) := hscaleInt
    _ = (ν.real Set.univ) ^ ((k : ℝ) / 2 - 1) *
        (∫ x, ∫ ω, F ω x ^ (2 * k) ∂standardGaussianInfinitePi ∂ν) := by
      rw [integral_const_mul, hswap]
    _ ≤ ((2 * (k : ℝ)) ^ k * V ^ k * (ν.real Set.univ)) *
        (ν.real Set.univ) ^ ((k : ℝ) / 2 - 1) := by
      convert mul_le_mul_of_nonneg_left hpointIntegral (Real.rpow_nonneg harea0 _) using 1
      ring
    _ = (2 * (k : ℝ)) ^ k * V ^ k * R ^ k := by
      calc
        _ = ((2 * (k : ℝ)) ^ k * V ^ k) *
            (ν.real Set.univ * (ν.real Set.univ) ^ ((k : ℝ) / 2 - 1)) := by ring
        _ = _ := by rw [harea, hfactor]

/-- An even moment of the finite physical band is controlled by the point variance and the
square side after the exact spatial Lp comparison. -/
theorem q3WeightedBandPartial_spatialLp_evenMoment_sq_le {n : ℕ} [NeZero n]
    (a c R : ℝ) (hR : 0 < R) (hab : a < a + R) (hcd : c < c + R)
    (β w : Fin n → ℝ) (L : Fin n → {l : ℝ // 0 < l}) (N : ℕ)
    {V : ℝ} (hV : (∑ i, w i ^ 2 * β i ^ 2) ≤ V) (k : ℕ) (hk : 2 ≤ k) :
    (eLpNorm (fun ω => q3WeightedBandH3Spatial a (a + R) c (c + R) β w L
      (gaussianPartialSum (q3BandH3Directions a (a + R) c (c + R) β L) N ω))
      (ENNReal.ofReal (2 * (k : ℝ))) standardGaussianInfinitePi).toReal ^ 2 ≤
        2 * (k : ℝ) * V * R := by
  let D := q3BandH3Directions a (a + R) c (c + R) β L
  let T := q3WeightedBandH3Spatial a (a + R) c (c + R) β w L
  let F := q3WeightedBandPartialValue a (a + R) c (c + R) β w L N
  have hV0 : 0 ≤ V := le_trans (Finset.sum_nonneg fun i hi => by positivity) hV
  have hfield : MemLp F (ENNReal.ofReal (2 * (k : ℝ))) standardGaussianInfinitePi :=
    memLp_q3WeightedBandPartialValue a (a + R) c (c + R) β w L
      (show 2 ≤ 2 * (k : ℝ) by exact_mod_cast (show 2 ≤ 2 * k by omega)) N
  have himage : MemLp (fun ω => T (gaussianPartialSum D N ω))
      (ENNReal.ofReal (2 * (k : ℝ))) standardGaussianInfinitePi := by
    have heq : (fun ω => T (gaussianPartialSum D N ω)) =
        fun ω => ContinuousMap.toLp 4 (spatialVolume
          (closedRectangle a (a + R) c (c + R))) ℝ (F ω) := by
      funext ω
      rfl
    rw [heq]
    exact hfield.continuousLinearMap_comp
      (ContinuousMap.toLp 4 (spatialVolume
        (closedRectangle a (a + R) c (c + R))) ℝ)
  have hmoment := q3WeightedBandPartial_spatial_evenMoment_le a c R hR β w L
    hab hcd N hV k (by omega)
  have hmoment' : (∫ ω, ‖T (gaussianPartialSum D N ω)‖ ^ (2 * k)
      ∂standardGaussianInfinitePi) ≤ (2 * (k : ℝ)) ^ k * V ^ k * R ^ k := by
    have heq : (fun ω => T (gaussianPartialSum D N ω)) =
        fun ω => ContinuousMap.toLp 4 (spatialVolume
          (closedRectangle a (a + R) c (c + R))) ℝ (F ω) := by
      funext ω
      rfl
    calc
      _ = ∫ ω, ‖ContinuousMap.toLp 4 (spatialVolume
          (closedRectangle a (a + R) c (c + R))) ℝ (F ω)‖ ^ (2 * k)
          ∂standardGaussianInfinitePi := by
        apply integral_congr_ae
        filter_upwards with ω
        exact congrArg (fun f => ‖f‖ ^ (2 * k)) (congrFun heq ω)
      _ ≤ _ := hmoment
  let Z : (ℕ → ℝ) → ℝ := fun ω => ‖T (gaussianPartialSum D N ω)‖
  have hZ : MemLp Z (ENNReal.ofReal (2 * (k : ℝ))) standardGaussianInfinitePi :=
    himage.norm
  have hmomentEq : rioMoment standardGaussianInfinitePi (2 * (k : ℝ)) Z =
      ∫ ω, ‖T (gaussianPartialSum D N ω)‖ ^ (2 * k) ∂standardGaussianInfinitePi := by
    unfold rioMoment Z
    apply integral_congr_ae
    filter_upwards with ω
    rw [abs_of_nonneg (norm_nonneg _),
      show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
  have hroot : (((2 * (k : ℝ)) ^ k * V ^ k * R ^ k) ^ (2 / (2 * (k : ℝ)))) =
      2 * (k : ℝ) * V * R := by
    let B : ℝ := 2 * (k : ℝ) * V * R
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hpow : (2 * (k : ℝ)) ^ k * V ^ k * R ^ k = B ^ k := by
      dsimp [B]
      have hpow₁ : ((2 * (k : ℝ)) * V) ^ k =
          (2 * (k : ℝ)) ^ k * V ^ k := mul_pow _ _ _
      have hpow₂ : (((2 * (k : ℝ)) * V) * R) ^ k =
          ((2 * (k : ℝ)) * V) ^ k * R ^ k := mul_pow _ _ _
      calc
        _ = ((2 * (k : ℝ)) * V) ^ k * R ^ k := by rw [← hpow₁]
        _ = (((2 * (k : ℝ)) * V) * R) ^ k := hpow₂.symm
    have hexp : ((k : ℝ) * (2 / (2 * (k : ℝ)))) = 1 := by field_simp
    rw [hpow]
    rw [← Real.rpow_natCast, (Real.rpow_mul hB _ _).symm, hexp, Real.rpow_one]
  have hLpSq := rio_lpNorm_sq (μ := standardGaussianInfinitePi)
    (p := 2 * (k : ℝ)) (by positivity) hZ
  rw [hmomentEq] at hLpSq
  have hnorm := eLpNorm_norm (p := ENNReal.ofReal (2 * (k : ℝ)))
    (fun ω => T (gaussianPartialSum D N ω)) himage.aestronglyMeasurable
  have hLpSq' : (eLpNorm (fun ω => T (gaussianPartialSum D N ω))
      (ENNReal.ofReal (2 * (k : ℝ))) standardGaussianInfinitePi).toReal ^ 2 =
      (∫ ω, ‖T (gaussianPartialSum D N ω)‖ ^ (2 * k)
        ∂standardGaussianInfinitePi) ^ (2 / (2 * (k : ℝ))) := by
    rw [← hnorm]
    exact hLpSq
  have hmomentNonneg : 0 ≤ ∫ ω, ‖T (gaussianPartialSum D N ω)‖ ^ (2 * k)
      ∂standardGaussianInfinitePi := integral_nonneg fun ω => by positivity
  have hpowLe := Real.rpow_le_rpow hmomentNonneg hmoment' (by positivity : 0 ≤ 2 / (2 * (k : ℝ)))
  rw [hLpSq']
  exact hpowLe.trans_eq hroot

/-- Even spatial moments pass from each finite Gaussian projection to the full physical band
series through the proved H³ Gaussian series limit. -/
theorem q3WeightedBandSeries_spatialLp_evenMoment_sq_le {n : ℕ} [NeZero n]
    (a c R : ℝ) (hR : 0 < R) (hab : a < a + R) (hcd : c < c + R)
    (β w : Fin n → ℝ) (L : Fin n → {l : ℝ // 0 < l})
    {V : ℝ} (hV : (∑ i, w i ^ 2 * β i ^ 2) ≤ V) (k : ℕ) (hk : 2 ≤ k) :
    (eLpNorm (fun ω => q3WeightedBandH3Spatial a (a + R) c (c + R) β w L
      (q3BandSeries a (a + R) c (c + R) β L ω))
      (ENNReal.ofReal (2 * (k : ℝ))) standardGaussianInfinitePi).toReal ^ 2 ≤
        2 * (k : ℝ) * V * R := by
  have hsum : Summable (fun j => ‖q3BandH3Directions a (a + R) c (c + R) β L j‖ ^ 2) :=
    q3BandH3Directions_summable a (a + R) c (c + R) β L
  have hpFact : Fact (2 ≤ 2 * (k : ℝ)) :=
    ⟨by exact_mod_cast (show 2 ≤ 2 * k by omega)⟩
  apply @gaussianSeries_image_lpNorm_sq_le
    (Q3BandH3 a (a + R) c (c + R) β L)
    (SpatialLp4 (closedRectangle a (a + R) c (c + R))) inferInstance
    (instQ3BandH3InnerProductSpace a (a + R) c (c + R) β L)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (q3BandH3Directions a (a + R) c (c + R) β L) hsum
    (q3WeightedBandH3Spatial a (a + R) c (c + R) β w L) (2 * (k : ℝ)) _ hpFact
  intro N
  exact q3WeightedBandPartial_spatialLp_evenMoment_sq_le a c R hR hab hcd β w L N hV k hk

/-- The normalized whole-square statistic has the source all-order bound on the full
ordinary-H³ realization of any finite physical band. -/
theorem q3WeightedBandH3_missingWave_bound {n : ℕ} [NeZero n]
    (a c R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ) (hab : a < a + R) (hcd : c < c + R)
    (β w : Fin n → ℝ) (L : Fin n → {l : ℝ // 0 < l})
    {A p : ℝ} (hA : 0 ≤ A) (hvar : (∑ i, w i ^ 2 * β i ^ 2) ≤ σ ^ 2 * (9 * A))
    (hp : 1 ≤ p) :
    (eLpNorm (fun ω => wholeRootSpatialStatistic σ R
      (q3WeightedBandH3Value a (a + R) c (c + R) β w L
        (q3BandSeries a (a + R) c (c + R) β L ω)))
      (ENNReal.ofReal p) standardGaussianInfinitePi).toReal ≤ 40 * (p + 2) * A := by
  let T := q3WeightedBandH3Spatial a (a + R) c (c + R) β w L
  let V := σ ^ 2 * (9 * A)
  let k := Nat.ceil (max p 2)
  have hk2 : 2 ≤ k := by
    dsimp [k]
    have hle : (2 : ℝ) ≤ max p 2 := le_max_right _ _
    exact_mod_cast (le_trans hle (Nat.le_ceil (max p 2)))
  have hpk : p ≤ (k : ℝ) := by
    dsimp [k]
    exact le_trans (le_max_left _ _) (Nat.le_ceil (max p 2))
  have hklt : (k : ℝ) < p + 2 := by
    dsimp [k]
    have hceil : (Nat.ceil (max p 2) : ℝ) < max p 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hmax : max p 2 ≤ p + 1 := max_le (by linarith) (by linarith)
    linarith
  have hV : (∑ i, w i ^ 2 * β i ^ 2) ≤ V := by simpa [V] using hvar
  have htargetMomentK := q3WeightedBandSeries_spatialLp_evenMoment_sq_le
    a c R hR hab hcd β w L hV k hk2
  have hqmono : ENNReal.ofReal (2 * p) ≤ ENNReal.ofReal (2 * (k : ℝ)) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpk (by norm_num))
  have hseries : MemLp (q3BandSeries a (a + R) c (c + R) β L)
      (ENNReal.ofReal (2 * (k : ℝ))) standardGaussianInfinitePi :=
    memLp_q3BandSeries a (a + R) c (c + R) β L
      (by exact_mod_cast (show 2 ≤ 2 * k by omega))
  have hTmem : MemLp (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω))
      (ENNReal.ofReal (2 * (k : ℝ))) standardGaussianInfinitePi :=
    @MemLp.continuousLinearMap_comp (ℕ → ℝ) ℝ
      (Q3BandH3 a (a + R) c (c + R) β L)
      (SpatialLp4 (closedRectangle a (a + R) c (c + R))) inferInstance
      (ENNReal.ofReal (2 * (k : ℝ))) standardGaussianInfinitePi
      inferInstance inferInstance inferInstance
      (instQ3BandH3NormedSpace a (a + R) c (c + R) β L) inferInstance
      (q3BandSeries a (a + R) c (c + R) β L) hseries T
  have hTmemP : MemLp (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω))
      (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi := hTmem.mono_exponent hqmono
  have hmono := eLpNorm_le_eLpNorm_of_exponent_le
    (f := fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω))
    (μ := standardGaussianInfinitePi) hqmono
  have hmonoR := ENNReal.toReal_mono hTmem.eLpNorm_ne_top hmono
  have hmonoSq := pow_le_pow_left₀ ENNReal.toReal_nonneg hmonoR 2
  have htargetMoment : (eLpNorm (fun ω => T
      (q3BandSeries a (a + R) c (c + R) β L ω))
        (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi).toReal ^ 2 ≤
      2 * (k : ℝ) * V * R := hmonoSq.trans htargetMomentK
  have hconst : 0 ≤ 2 / (R * σ ^ 2) := by positivity
  have hstat : (fun ω => wholeRootSpatialStatistic σ R
      (q3WeightedBandH3Value a (a + R) c (c + R) β w L
        (q3BandSeries a (a + R) c (c + R) β L ω))) =
      (2 / (R * σ ^ 2)) • fun ω => ‖T
        (q3BandSeries a (a + R) c (c + R) β L ω)‖ ^ 2 := by
    funext ω
    rfl
  have hscale : eLpNorm (fun ω => wholeRootSpatialStatistic σ R
      (q3WeightedBandH3Value a (a + R) c (c + R) β w L
        (q3BandSeries a (a + R) c (c + R) β L ω)))
      (ENNReal.ofReal p) standardGaussianInfinitePi =
      ENNReal.ofReal (2 / (R * σ ^ 2)) * eLpNorm (fun ω => ‖T
        (q3BandSeries a (a + R) c (c + R) β L ω)‖ ^ 2)
        (ENNReal.ofReal p) standardGaussianInfinitePi := by
    rw [hstat, eLpNorm_const_smul]
    simp only [Real.enorm_of_nonneg hconst]
  have hpower : eLpNorm (fun ω => ‖T
      (q3BandSeries a (a + R) c (c + R) β L ω)‖ ^ 2)
      (ENNReal.ofReal p) standardGaussianInfinitePi =
      eLpNorm (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω))
        (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi ^ 2 := by
    calc
      _ = eLpNorm (fun ω => ‖T (q3BandSeries a (a + R) c (c + R) β L ω)‖ ^
          ((2 : ℕ) : ℝ)) (ENNReal.ofReal p) standardGaussianInfinitePi := by
        congr 1
        funext ω
        exact (Real.rpow_natCast _ 2).symm
      _ = eLpNorm (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω))
          (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi ^ (2 : ℝ) := by
        have hnorm := eLpNorm_norm_rpow (p := ENNReal.ofReal p)
          (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω))
          hTmemP.aestronglyMeasurable
          (by norm_num : (0 : ℝ) < 2)
        have hexponent : ENNReal.ofReal p * ENNReal.ofReal 2 = ENNReal.ofReal (2 * p) := by
          calc
            _ = ENNReal.ofReal (p * 2) := (ENNReal.ofReal_mul (by linarith : 0 ≤ p)).symm
            _ = _ := by congr 1; ring
        rw [hexponent] at hnorm
        change eLpNorm (fun ω => ‖T (q3BandSeries a (a + R) c (c + R) β L ω)‖ ^ (2 : ℝ))
            (ENNReal.ofReal p) standardGaussianInfinitePi = _ at hnorm
        exact hnorm
      _ = _ := ENNReal.rpow_natCast _ 2
  rw [hscale, hpower, ENNReal.toReal_mul, ENNReal.toReal_ofReal hconst,
    ENNReal.toReal_pow]
  have hfinal : (2 / (R * σ ^ 2)) * (2 * (k : ℝ) * V * R) =
      4 * (k : ℝ) * (9 * A) := by
    dsimp [V]
    field_simp
    ring
  calc
    _ ≤ (2 / (R * σ ^ 2)) * (2 * (k : ℝ) * V * R) :=
      mul_le_mul_of_nonneg_left htargetMoment hconst
    _ = 36 * (k : ℝ) * A := by rw [hfinal]; ring
    _ ≤ 40 * (p + 2) * A := by
      have hkbound : 36 * (k : ℝ) ≤ 40 * (p + 2) := by nlinarith [hp, hklt]
      exact mul_le_mul_of_nonneg_right hkbound hA

/-- The normalized Lebesgue average on a finite spatial carrier, represented as a bounded
linear observation of its continuous fields. -/
noncomputable def q3SpatialAverageCLM {K : Set (Vec 2)} [CompactSpace K]
    (_harea : 0 < (spatialVolume K).real Set.univ) : C(K, ℝ) →L[ℝ] ℝ :=
  ((spatialVolume K).real Set.univ)⁻¹ • spatialIntegralCLM Set.univ

@[simp] theorem q3SpatialAverageCLM_apply {K : Set (Vec 2)} [CompactSpace K]
    (harea : 0 < (spatialVolume K).real Set.univ) (f : C(K, ℝ)) :
    q3SpatialAverageCLM harea f = ((spatialVolume K).real Set.univ)⁻¹ *
      ∫ x, f x ∂spatialVolume K := by
  simp [q3SpatialAverageCLM, spatialIntegralCLM, smul_eq_mul]

/-- Cauchy--Schwarz for integration on a finite carrier, in its squared form. -/
theorem integral_sq_le_measureReal_mul_integral_sq {K : Type*} [MeasurableSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (f : K → ℝ)
    (hfLp : MemLp f (ENNReal.ofReal 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ x, f x ^ 2 ∂μ := by
  have habs : MemLp (fun x => |f x|) (ENNReal.ofReal 2) μ := hfLp.norm
  have hone : MemLp (fun _ : K => (1 : ℝ)) (ENNReal.ofReal 2) μ := memLp_const 1
  have hpq : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun x => abs_nonneg (f x))
    (Filter.Eventually.of_forall fun _ : K => (by norm_num : 0 ≤ (1 : ℝ))) habs hone
  have hI : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hA : 0 ≤ μ.real Set.univ := measureReal_nonneg
  have hIeq : ∫ x, |f x| ^ (2 : ℝ) ∂μ = ∫ x, f x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    simp [Real.rpow_ofNat, sq_abs]
  have hAeq : ∫ x, (1 : ℝ) ^ (2 : ℝ) ∂μ = μ.real Set.univ := by
    simp [Real.rpow_ofNat]
  have hroot : ∫ x, |f x| ∂μ ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (μ.real Set.univ) := by
    calc
      _ = ∫ x, |f x| * 1 ∂μ := by simp
      _ ≤ _ := by simpa only [hIeq, hAeq, Real.sqrt_eq_rpow] using hh
  have hnorm : |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f
  have hle := hnorm.trans hroot
  have hsquare := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hle
  rw [sq_abs, mul_pow, Real.sq_sqrt hI, Real.sq_sqrt hA] at hsquare
  nlinarith [hsquare]

/-- The square of a deterministic spatial average is bounded by the average of the square. -/
theorem q3SpatialAverage_sq_le {K : Set (Vec 2)} [CompactSpace K]
    (harea : 0 < (spatialVolume K).real Set.univ) (f : C(K, ℝ)) :
    (q3SpatialAverageCLM harea f) ^ 2 ≤
      ((spatialVolume K).real Set.univ)⁻¹ * ∫ x, f x ^ 2 ∂spatialVolume K := by
  have hfLp : MemLp f (ENNReal.ofReal 2) (spatialVolume K) :=
    f.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hc := integral_sq_le_measureReal_mul_integral_sq (spatialVolume K) f hfLp
  rw [q3SpatialAverageCLM_apply harea f]
  let A : ℝ := (spatialVolume K).real Set.univ
  let I : ℝ := ∫ x, f x ∂spatialVolume K
  let J : ℝ := ∫ x, f x ^ 2 ∂spatialVolume K
  have hA : 0 < A := harea
  have hc' : I ^ 2 ≤ A * J := by simpa [A, I, J] using hc
  change (A⁻¹ * I) ^ 2 ≤ A⁻¹ * J
  calc
    (A⁻¹ * I) ^ 2 = A⁻¹ ^ 2 * I ^ 2 := by ring
    _ ≤ A⁻¹ ^ 2 * (A * J) := mul_le_mul_of_nonneg_left hc' (sq_nonneg _)
    _ = A⁻¹ * J := by field_simp [ne_of_gt hA]

section
variable {n : ℕ} [NeZero n] (a b c d : ℝ) (β w : Fin n → ℝ)
  (L : Fin n → {l : ℝ // 0 < l})

/-- Every bounded linear observation of a finite retained band is a scalar Gaussian with
variance equal to its finite coefficient square sum. -/
theorem q3WeightedBandPartial_observation_lpNorm_sq_le
    (P : C(closedRectangle a b c d, ℝ) →L[ℝ] ℝ) (N : ℕ) {V p : ℝ}
    (hvar : (∑ j ∈ Finset.range N,
      (P (q3WeightedBandH3Value a b c d β w L
        (q3BandH3Directions a b c d β L j))) ^ 2) ≤ V) (hp : 1 ≤ p) :
    (eLpNorm (fun ω => P (q3WeightedBandPartialValue a b c d β w L N ω))
      (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi).toReal ^ 2 ≤
        (2 * p + 2) * V := by
  let F := q3WeightedBandPartialValue a b c d β w L N
  let coeff : ℕ → ℝ := fun j => P (q3WeightedBandH3Value a b c d β w L
    (q3BandH3Directions a b c d β L j))
  let s : ℝ := ∑ j ∈ Finset.range N, coeff j ^ 2
  have hs : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg fun j hj => sq_nonneg _
  have hV0 : 0 ≤ V := le_trans
    (Finset.sum_nonneg fun j hj => sq_nonneg _) hvar
  have hfield : MemLp F (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi := by
    exact memLp_q3WeightedBandPartialValue a b c d β w L
      (show 2 ≤ 2 * p by linarith) N
  have hPfield : MemLp (fun ω => P (F ω)) (ENNReal.ofReal (2 * p))
      standardGaussianInfinitePi := hfield.continuousLinearMap_comp P
  have heval : AEStronglyMeasurable (fun ω => P (F ω)) standardGaussianInfinitePi :=
    P.continuous.comp_aestronglyMeasurable hfield.aestronglyMeasurable
  have hfun : (fun ω => P (F ω)) = gaussianScalarPartialSum coeff N := by
    funext ω
    simp [F, coeff, q3WeightedBandPartialValue, gaussianPartialSum,
      gaussianScalarPartialSum, map_sum, map_smul]
  have hlaw : standardGaussianInfinitePi.map (fun ω => P (F ω)) =
      gaussianReal 0 (Real.toNNReal s) := by
    rw [hfun, map_gaussianScalarPartialSum]
  have hmap := eLpNorm_map_measure (p := ENNReal.ofReal (2 * p))
    (μ := standardGaussianInfinitePi) (f := fun ω => P (F ω))
    (by fun_prop : AEStronglyMeasurable (id : ℝ → ℝ)
      (standardGaussianInfinitePi.map fun ω => P (F ω))) heval.aemeasurable
  have hnorm : eLpNorm (fun ω => P (F ω)) (ENNReal.ofReal (2 * p))
      standardGaussianInfinitePi =
      eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2 * p)) (gaussianReal 0 (Real.toNNReal s)) := by
    calc
      _ = eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2 * p))
          (standardGaussianInfinitePi.map fun ω => P (F ω)) := hmap.symm
      _ = _ := by rw [hlaw]
  have hscalar := gaussianReal_lpNorm_sq_le (Real.toNNReal s) hp
  have hvariance : (Real.toNNReal s : ℝ) ≤ V := by
    rw [Real.coe_toNNReal _ hs]
    simpa [s, coeff] using hvar
  rw [hnorm]
  exact hscalar.trans (mul_le_mul_of_nonneg_left hvariance (by linarith))

/-- A normalized spatial average of a finite physical band keeps the point variance cap. -/
theorem q3WeightedBandPartial_spatialAverage_lpNorm_sq_le
    (a c R : ℝ) (hR : 0 < R) (hab : a < a + R) (hcd : c < c + R)
    (N : ℕ) {V p : ℝ} (hV : (∑ i, w i ^ 2 * β i ^ 2) ≤ V) (hp : 1 ≤ p) :
    (eLpNorm (fun ω => q3SpatialAverageCLM
      (by rw [spatialVolume_square_real (R := R) hR.le]; positivity)
      (q3WeightedBandPartialValue a (a + R) c (c + R) β w L N ω))
      (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi).toReal ^ 2 ≤
        (2 * p + 2) * V := by
  let K := closedRectangle a (a + R) c (c + R)
  let μ := spatialVolume K
  let area : ℝ := μ.real Set.univ
  let P := q3SpatialAverageCLM (K := K)
    (by rw [spatialVolume_square_real (R := R) hR.le]; positivity)
  let D := q3BandH3Directions a (a + R) c (c + R) β L
  let f : ℕ → C(K, ℝ) := fun j => q3WeightedBandH3Value a (a + R) c (c + R)
    β w L (D j)
  have harea : area = R ^ 2 := by
    dsimp [area, μ, K]
    exact spatialVolume_square_real (a := a) (c := c) (R := R) hR.le
  have harea0 : 0 < area := by rw [harea]; positivity
  have hterm (j : ℕ) : (P (f j)) ^ 2 ≤ area⁻¹ *
      ∫ x, (f j x) ^ 2 ∂μ := by
    simpa only [P, f, area, μ, K] using q3SpatialAverage_sq_le
      (K := K) (by rw [spatialVolume_square_real (R := R) hR.le]; positivity) (f j)
  have hfi (j : ℕ) : Integrable (fun x => (f j x) ^ 2) μ := by
    let g : C(K, ℝ) := (f j) ^ 2
    have hg : MemLp g 1 μ :=
      g.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
    have heq : (fun x => (f j x) ^ 2) = g := by funext x; rfl
    rw [heq]
    exact memLp_one_iff_integrable.mp hg
  have hsumInt := integral_finsetSum (Finset.range N) (fun j hj => hfi j)
  have hpoint (x : K) : ∑ j ∈ Finset.range N, (f j x) ^ 2 ≤ V := by
    dsimp [f, D]
    exact (q3WeightedBandH3Value_partial_variance_le a (a + R) c (c + R)
      β w L hab hcd x N).trans hV
  have hsumBound : (∑ j ∈ Finset.range N, (P (f j)) ^ 2) ≤ V := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, area⁻¹ * ∫ x, (f j x) ^ 2 ∂μ :=
        Finset.sum_le_sum fun j hj => hterm j
      _ = area⁻¹ * ∫ x, ∑ j ∈ Finset.range N, (f j x) ^ 2 ∂μ := by
        rw [← Finset.mul_sum, ← hsumInt]
      _ ≤ area⁻¹ * ∫ _x : K, V ∂μ := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr harea0.le)
        exact integral_mono (integrable_finsetSum (Finset.range N) (fun j hj => hfi j))
          (integrable_const _) hpoint
      _ = V := by
        rw [integral_const, smul_eq_mul]
        dsimp [area]
        calc
          (μ.real Set.univ)⁻¹ * (μ.real Set.univ * V) =
              ((μ.real Set.univ)⁻¹ * μ.real Set.univ) * V := by ring
          _ = V := by rw [inv_mul_cancel₀ (ne_of_gt harea0)]; simp
  simpa only [P, f, K] using q3WeightedBandPartial_observation_lpNorm_sq_le
    a (a + R) c (c + R) β w L P N hsumBound hp

/-- The normalized spatial-average moment bound passes to the full ordinary-H³ band series. -/
theorem q3WeightedBandSeries_spatialAverage_lpNorm_sq_le
    (a c R : ℝ) (hR : 0 < R) (hab : a < a + R) (hcd : c < c + R)
    {V p : ℝ} (hV : (∑ i, w i ^ 2 * β i ^ 2) ≤ V) (hp : 1 ≤ p) :
    (eLpNorm (fun ω => q3SpatialAverageCLM
      (by rw [spatialVolume_square_real (R := R) hR.le]; positivity)
      (q3WeightedBandH3Value a (a + R) c (c + R) β w L
        (q3BandSeries a (a + R) c (c + R) β L ω)))
      (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi).toReal ^ 2 ≤
        (2 * p + 2) * V := by
  let K := closedRectangle a (a + R) c (c + R)
  let P := q3SpatialAverageCLM (K := K)
    (by rw [spatialVolume_square_real (R := R) hR.le]; positivity)
  let T := P.comp (q3WeightedBandH3Value a (a + R) c (c + R) β w L)
  have hsum : Summable (fun j => ‖q3BandH3Directions a (a + R) c (c + R) β L j‖ ^ 2) :=
    q3BandH3Directions_summable a (a + R) c (c + R) β L
  have hpFact : Fact (2 ≤ 2 * p) := ⟨by linarith⟩
  apply @gaussianSeries_image_lpNorm_sq_le
    (Q3BandH3 a (a + R) c (c + R) β L) ℝ inferInstance
    (instQ3BandH3InnerProductSpace a (a + R) c (c + R) β L)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (q3BandH3Directions a (a + R) c (c + R) β L) hsum T (2 * p) _ hpFact
  intro N
  change (eLpNorm (fun ω => P (q3WeightedBandH3Value a (a + R) c (c + R) β w L
      (gaussianPartialSum (q3BandH3Directions a (a + R) c (c + R) β L) N ω)))
      (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi).toReal ^ 2 ≤ (2 * p + 2) * V
  simpa only [P, K, q3WeightedBandPartialValue] using q3WeightedBandPartial_spatialAverage_lpNorm_sq_le
    β w L a c R hR hab hcd N hV hp

/-- Finite weighted model bands and the common ordinary-H³ series have the same
all-order law under every continuous scalar observation. -/
theorem actualWeightedBand_observation_eLpNorm_eq
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin n → ℤ) (hk : Function.Injective k) (weights : Fin n → ℝ)
    (P : C(closedRectangle a b c d, ℝ) →L[ℝ] ℝ) {p : ℝ} :
    eLpNorm (fun ω => P (modelWeightedBand (closedRectangle a b c d) k weights ω))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure =
    eLpNorm (fun ω => P (q3WeightedBandH3Value a b c d
      (fun i => q3ModelAmplitude M h (k i)) weights
      (fun i => q3ModelLength (k i))
      (q3BandSeries a b c d (fun i => q3ModelAmplitude M h (k i))
        (fun i => q3ModelLength (k i)) ω)))
      (ENNReal.ofReal p) standardGaussianInfinitePi := by
  let K := closedRectangle a b c d
  let F : C(K, ℝ) → ℝ := P
  let W := modelWeightedBand K k weights
  let G : (ℕ → ℝ) → C(K, ℝ) := fun ω => q3WeightedBandH3Value a b c d
    (fun i => q3ModelAmplitude M h (k i)) weights (fun i => q3ModelLength (k i))
    (q3BandSeries a b c d (fun i => q3ModelAmplitude M h (k i))
      (fun i => q3ModelLength (k i)) ω)
  have hF : Continuous F := P.continuous
  have hW : Measurable W := measurable_modelWeightedBand K k weights
  have hG : StronglyMeasurable G := by
    let A := q3WeightedBandH3Value a b c d
      (fun i => q3ModelAmplitude M h (k i)) weights (fun i => q3ModelLength (k i))
    change StronglyMeasurable (A ∘ q3BandSeries a b c d
      (fun i => q3ModelAmplitude M h (k i)) (fun i => q3ModelLength (k i)))
    exact A.continuous.comp_stronglyMeasurable (stronglyMeasurable_q3BandSeries a b c d
      (fun i => q3ModelAmplitude M h (k i)) (fun i => q3ModelLength (k i)))
  have hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map W =
      standardGaussianInfinitePi.map G := by
    dsimp [W, G, K]
    exact actualWeightedBandLaw_eq_h3Series a b c d hab hcd M h hM k hk weights
  have hFleft : AEStronglyMeasurable F ((Cutoff.cutoffSampleLaw M).toMeasure.map W) :=
    hF.measurable.aestronglyMeasurable
  have hFright : AEStronglyMeasurable F (standardGaussianInfinitePi.map G) :=
    hF.measurable.aestronglyMeasurable
  have hleft := eLpNorm_map_measure (p := ENNReal.ofReal p)
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (f := W) hFleft hW.aemeasurable
  have hright := eLpNorm_map_measure (p := ENNReal.ofReal p)
    (μ := standardGaussianInfinitePi) (f := G) hFright hG.aemeasurable
  calc
    _ = eLpNorm F (ENNReal.ofReal p) ((Cutoff.cutoffSampleLaw M).toMeasure.map W) := by
      change eLpNorm (F ∘ W) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure = _
      exact hleft.symm
    _ = eLpNorm F (ENNReal.ofReal p) (standardGaussianInfinitePi.map G) := by rw [hlaw]
    _ = _ := by
      change eLpNorm F (ENNReal.ofReal p) (standardGaussianInfinitePi.map G) =
        eLpNorm (F ∘ G) (ENNReal.ofReal p) standardGaussianInfinitePi
      exact hright

end

section

/-- The actual later-shell cube average inherits the protected scalar Gaussian moment bound
from the ordinary H³ realization. The frame is the true earlier-label frame. -/
theorem missingWave_model_average_lpNorm_sq_le {j N : ℤ}
    (hjN : j ≤ N) (hstrict : j < N)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hstate : ASDExplicitGamma.nativeInductionState M h j)
    (a c R : ℝ) (hR : 0 < R) (weights : ℤ → ℝ)
    (hweights : ∀ k ∈ Finset.Ioc j N, 0 ≤ weights k ∧ weights k ≤ 1)
    {p : ℝ} (hp : 1 ≤ p) :
    (eLpNorm (fun ω => q3SpatialAverageCLM
      (by rw [spatialVolume_square_real (R := R) hR.le]; positivity)
      (wholeRootModelBand (a := a) (b := a + R) (c := c) (d := c + R)
        j N weights ω)) (ENNReal.ofReal (2 * p))
      (Cutoff.cutoffSampleLaw M).toMeasure).toReal ^ 2 ≤
      (2 * p + 2) * ((Annealed.sigmaBar M j : ℝ) ^ 2 *
        (9 * M.gamma * (N - j : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)))) := by
  let σ : ℝ := Annealed.sigmaBar M j
  let K := closedRectangle a (a + R) c (c + R)
  let β : Fin (wholeRootBandLength j N) → ℝ := fun i =>
    q3ModelAmplitude M h (wholeRootShellLabel j N i)
  let w : Fin (wholeRootBandLength j N) → ℝ := wholeRootWeights j N weights
  let L : Fin (wholeRootBandLength j N) → {l : ℝ // 0 < l} := fun i =>
    q3ModelLength (wholeRootShellLabel j N i)
  let P : C(K, ℝ) →L[ℝ] ℝ := q3SpatialAverageCLM
    (by rw [spatialVolume_square_real (R := R) hR.le]; positivity)
  have hσ : 0 < σ := (Annealed.sigmaBar M j).2
  have hvar : (∑ i, w i ^ 2 * β i ^ 2) ≤ σ ^ 2 *
      (9 * M.gamma * (N - j : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ))) := by
    change (∑ i, weights (wholeRootShellLabel j N i) ^ 2 *
      q3ModelAmplitude M h (wholeRootShellLabel j N i) ^ 2) ≤ _
    exact wholeRootBand_variance_clock j N hjN M h σ hσ
      (wholeRoot_frame_variance_lower M h j hstate) weights hweights
  have hlength : 0 < wholeRootBandLength j N := by
    have hcast : ((wholeRootBandLength j N : ℕ) : ℤ) = N - j := by
      dsimp [wholeRootBandLength]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hjN)
    have hcastpos : (0 : ℤ) < (wholeRootBandLength j N : ℤ) := by
      rw [hcast]
      omega
    exact_mod_cast hcastpos
  let instMissingWaveBandLengthNeZero : NeZero (wholeRootBandLength j N) :=
    ⟨Nat.ne_of_gt hlength⟩
  have hab : a < a + R := by linarith
  have hcd : c < c + R := by linarith
  have hseries := @q3WeightedBandSeries_spatialAverage_lpNorm_sq_le
    (wholeRootBandLength j N) instMissingWaveBandLengthNeZero
    β w L a c R hR hab hcd
    (σ ^ 2 * (9 * M.gamma * (N - j : ℝ) *
      (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)))) p hvar hp
  have htransfer := @actualWeightedBand_observation_eLpNorm_eq
    (wholeRootBandLength j N) instMissingWaveBandLengthNeZero
    a (a + R) c (c + R) hab hcd M h hM (wholeRootShellLabel j N)
    (wholeRootShellLabel_injective j N) (wholeRootWeights j N weights)
    P (p := 2 * p)
  have hmodel :
      eLpNorm (fun ω => P (wholeRootModelBand (a := a) (b := a + R)
        (c := c) (d := c + R) j N weights ω)) (ENNReal.ofReal (2 * p))
        (Cutoff.cutoffSampleLaw M).toMeasure =
      eLpNorm (fun ω => P (q3WeightedBandH3Value a (a + R) c (c + R) β w L
        (q3BandSeries a (a + R) c (c + R) β L ω)))
        (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi := by
    simpa only [wholeRootModelBand] using htransfer
  change (eLpNorm (fun ω => P (wholeRootModelBand (a := a) (b := a + R)
      (c := c) (d := c + R) j N weights ω)) (ENNReal.ofReal (2 * p))
      (Cutoff.cutoffSampleLaw M).toMeasure).toReal ^ 2 ≤ _
  rw [hmodel]
  exact hseries

/-- The actual later-shell cube average has every finite scalar moment order at least two.
This integrability statement is used when the pointwise shear estimate is passed through
the Lᵖ norm. -/
theorem missingWave_model_average_memLp {j N : ℤ}
    (hjN : j ≤ N) (hstrict : j < N)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (a c R : ℝ) (hR : 0 < R) (weights : ℤ → ℝ) {p : ℝ} (hp : 1 ≤ p) :
    MemLp (fun ω => q3SpatialAverageCLM
      (by rw [spatialVolume_square_real (R := R) hR.le]; positivity)
      (wholeRootModelBand (a := a) (b := a + R) (c := c) (d := c + R)
        j N weights ω)) (ENNReal.ofReal (2 * p))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let K := closedRectangle a (a + R) c (c + R)
  let β : Fin (wholeRootBandLength j N) → ℝ := fun i =>
    q3ModelAmplitude M h (wholeRootShellLabel j N i)
  let w : Fin (wholeRootBandLength j N) → ℝ := wholeRootWeights j N weights
  let L : Fin (wholeRootBandLength j N) → {l : ℝ // 0 < l} := fun i =>
    q3ModelLength (wholeRootShellLabel j N i)
  let P : C(K, ℝ) →L[ℝ] ℝ := q3SpatialAverageCLM
    (by rw [spatialVolume_square_real (R := R) hR.le]; positivity)
  let T : Q3BandH3 a (a + R) c (c + R) β L →L[ℝ] ℝ :=
    P.comp (q3WeightedBandH3Value a (a + R) c (c + R) β w L)
  have hlength : 0 < wholeRootBandLength j N := by
    have hcast : ((wholeRootBandLength j N : ℕ) : ℤ) = N - j := by
      dsimp [wholeRootBandLength]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hjN)
    have hcastpos : (0 : ℤ) < (wholeRootBandLength j N : ℤ) := by
      rw [hcast]
      omega
    exact_mod_cast hcastpos
  let instMissingWaveAverageMemLpBandLengthNeZero :
      NeZero (wholeRootBandLength j N) := ⟨Nat.ne_of_gt hlength⟩
  have hseries : MemLp (q3BandSeries a (a + R) c (c + R) β L)
      (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi :=
    @memLp_q3BandSeries (wholeRootBandLength j N)
      instMissingWaveAverageMemLpBandLengthNeZero
      a (a + R) c (c + R) β L (2 * p) (by linarith)
  have hobs : MemLp (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω))
      (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi :=
    @MemLp.continuousLinearMap_comp (ℕ → ℝ) ℝ
      (Q3BandH3 a (a + R) c (c + R) β L) ℝ inferInstance
      (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi
      inferInstance inferInstance inferInstance
      (instQ3BandH3NormedSpace a (a + R) c (c + R) β L) inferInstance
      (q3BandSeries a (a + R) c (c + R) β L) hseries T
  have hobs' : MemLp (fun ω => P (q3WeightedBandH3Value a (a + R) c (c + R)
      β w L (q3BandSeries a (a + R) c (c + R) β L ω)))
      (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi := by
    simpa [T] using hobs
  have htransfer := @actualWeightedBand_observation_eLpNorm_eq
    (wholeRootBandLength j N) instMissingWaveAverageMemLpBandLengthNeZero
    a (a + R) c (c + R) (by linarith) (by linarith) M h hM
    (wholeRootShellLabel j N) (wholeRootShellLabel_injective j N)
    (wholeRootWeights j N weights) P (p := 2 * p)
  have hmodel :
      eLpNorm (fun ω => P (wholeRootModelBand (a := a) (b := a + R)
        (c := c) (d := c + R) j N weights ω)) (ENNReal.ofReal (2 * p))
        (Cutoff.cutoffSampleLaw M).toMeasure =
      eLpNorm (fun ω => P (q3WeightedBandH3Value a (a + R) c (c + R)
        β w L (q3BandSeries a (a + R) c (c + R) β L ω)))
        (ENNReal.ofReal (2 * p)) standardGaussianInfinitePi := by
    simpa only [wholeRootModelBand] using htransfer
  rw [memLp_iff]
  rw [hmodel]
  exact hobs'.eLpNorm_lt_top

/-- Normalizing the actual cube average by the true earlier frame gives the source variance
clock in every real moment order at least two. -/
theorem missingWave_model_average_normalized_lpNorm_sq_le {j N : ℤ}
    (hjN : j ≤ N) (hstrict : j < N)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hstate : ASDExplicitGamma.nativeInductionState M h j)
    (a c R : ℝ) (hR : 0 < R) (weights : ℤ → ℝ)
    (hweights : ∀ k ∈ Finset.Ioc j N, 0 ≤ weights k ∧ weights k ≤ 1)
    {p : ℝ} (hp : 1 ≤ p) :
    (eLpNorm (fun ω => q3SpatialAverageCLM
      (by rw [spatialVolume_square_real (R := R) hR.le]; positivity)
      (wholeRootModelBand (a := a) (b := a + R) (c := c) (d := c + R)
        j N weights ω) / (Annealed.sigmaBar M j : ℝ))
      (ENNReal.ofReal (2 * p)) (Cutoff.cutoffSampleLaw M).toMeasure).toReal ^ 2 ≤
      (2 * p + 2) * (9 * M.gamma * (N - j : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ))) := by
  let σ : ℝ := Annealed.sigmaBar M j
  let avg : Cutoff.CutoffSample 2 → ℝ := fun ω => q3SpatialAverageCLM
    (by rw [spatialVolume_square_real (R := R) hR.le]; positivity)
    (wholeRootModelBand (a := a) (b := a + R) (c := c) (d := c + R)
      j N weights ω)
  have hσ : 0 < σ := (Annealed.sigmaBar M j).2
  have hmoment := missingWave_model_average_lpNorm_sq_le hjN hstrict M h hM
    hstate a c R hR weights hweights hp
  have hscale : eLpNorm (fun ω => avg ω / σ) (ENNReal.ofReal (2 * p))
      (Cutoff.cutoffSampleLaw M).toMeasure =
      ENNReal.ofReal (σ⁻¹) * eLpNorm avg (ENNReal.ofReal (2 * p))
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    have hfun : (fun ω => avg ω / σ) = σ⁻¹ • avg := by
      funext ω
      simp [avg, div_eq_mul_inv, smul_eq_mul]
      ring
    rw [hfun, eLpNorm_const_smul]
    simp only [Real.enorm_of_nonneg (inv_nonneg.mpr hσ.le)]
  have hσsq : σ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hσ)
  have hbound := hmoment
  have hcalc :
      (σ⁻¹ * (eLpNorm avg (ENNReal.ofReal (2 * p))
        (Cutoff.cutoffSampleLaw M).toMeasure).toReal) ^ 2 ≤
      (2 * p + 2) * (9 * M.gamma * (N - j : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ))) := by
    have hmul := mul_le_mul_of_nonneg_left hbound (sq_nonneg (σ⁻¹))
    have hfactor : (σ⁻¹ *
        (eLpNorm avg (ENNReal.ofReal (2 * p))
          (Cutoff.cutoffSampleLaw M).toMeasure).toReal) ^ 2 =
        (σ⁻¹) ^ 2 * (eLpNorm avg (ENNReal.ofReal (2 * p))
          (Cutoff.cutoffSampleLaw M).toMeasure).toReal ^ 2 := by ring
    rw [hfactor]
    calc
      _ ≤ (σ⁻¹) ^ 2 * ((2 * p + 2) * (σ ^ 2 *
          (9 * M.gamma * (N - j : ℝ) *
            (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ))))) := hmul
      _ = _ := by field_simp [hσsq]
  change (eLpNorm (fun ω => avg ω / σ) (ENNReal.ofReal (2 * p))
      (Cutoff.cutoffSampleLaw M).toMeasure).toReal ^ 2 ≤ _
  calc
    _ = (ENNReal.ofReal (σ⁻¹) * eLpNorm avg (ENNReal.ofReal (2 * p))
        (Cutoff.cutoffSampleLaw M).toMeasure).toReal ^ 2 := by rw [hscale]
    _ = (σ⁻¹ * (eLpNorm avg (ENNReal.ofReal (2 * p))
        (Cutoff.cutoffSampleLaw M).toMeasure).toReal) ^ 2 := by
      rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (inv_nonneg.mpr hσ.le)]
    _ ≤ _ := hcalc

end

section

end

section

/-- The physical block shear as a continuous operator on the doubled Euclidean field
space. The sign convention in `responseShearPointwiseOperator` makes the lower-left block
equal to the average divided by the true frame. -/
noncomputable def missingWaveShearOperator (σ η : ℝ) :
    HilbertBlockVec 2 →L[ℝ] HilbertBlockVec 2 :=
  ContinuousLinearMap.id ℝ _ +
    η • (-Response.responseShearPointwiseOperator σ 1)

/-- The squared operator norm of the physical shear is controlled by the normalized average. -/
theorem missingWaveShearOperator_norm_sq_le (σ η : ℝ) :
    ‖missingWaveShearOperator σ η‖ ^ 2 ≤
      2 + 2 * (η / σ) ^ 2 := by
  have hcorrection :
      ‖η • (-Response.responseShearPointwiseOperator σ 1)‖ ≤ |η / σ| := by
    have hunit := Response.responseShearPointwiseOperator_norm_le σ 1
    calc
      _ = |η| * ‖Response.responseShearPointwiseOperator σ 1‖ := by
        simp [norm_smul]
      _ ≤ |η| * |1 / σ| := mul_le_mul_of_nonneg_left hunit (abs_nonneg η)
      _ = |η / σ| := by
        rw [abs_div]
        simp only [abs_one]
        rw [abs_div]
        ring
  have hnorm : ‖missingWaveShearOperator σ η‖ ≤ 1 + |η / σ| := by
    calc
      _ ≤ ‖ContinuousLinearMap.id ℝ (HilbertBlockVec 2)‖ +
          ‖η • (-Response.responseShearPointwiseOperator σ 1)‖ :=
        ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ 1 + |η / σ| := by simpa using add_le_add_left hcorrection 1
  calc
    _ ≤ (1 + |η / σ|) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
    _ ≤ 2 + 2 * (η / σ) ^ 2 := by
      nlinarith [sq_nonneg (|η / σ| - 1), sq_abs (η / σ)]

/-- The actual physical cube-average shear has the source all-order moment bound, uniformly
in the deterministic spatial square and with the true earlier-label frame. -/
theorem missingWave_model_shear_lpNorm_bound {j N : ℤ}
    (hjN : j ≤ N) (hstrict : j < N)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hstate : ASDExplicitGamma.nativeInductionState M h j)
    (a c R : ℝ) (hR : 0 < R) (weights : ℤ → ℝ)
    (hweights : ∀ k ∈ Finset.Ioc j N, 0 ≤ weights k ∧ weights k ≤ 1)
    {p : ℝ} (hp : 1 ≤ p) :
    (eLpNorm (fun ω => ‖missingWaveShearOperator
      (Annealed.sigmaBar M j)
      (q3SpatialAverageCLM
        (by rw [spatialVolume_square_real (R := R) hR.le]; positivity)
        (wholeRootModelBand (a := a) (b := a + R) (c := c) (d := c + R)
          j N weights ω))‖ ^ 2)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure).toReal ≤
      2 + 80 * (p + 2) *
        (M.gamma * (N - j : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ))) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M j
  let avg : Cutoff.CutoffSample 2 → ℝ := fun ω => q3SpatialAverageCLM
    (by rw [spatialVolume_square_real (R := R) hR.le]; positivity)
    (wholeRootModelBand (a := a) (b := a + R) (c := c) (d := c + R)
      j N weights ω)
  let x : Cutoff.CutoffSample 2 → ℝ := fun ω => avg ω / σ
  let shear : Cutoff.CutoffSample 2 → HilbertBlockVec 2 →L[ℝ] HilbertBlockVec 2 :=
    fun ω => missingWaveShearOperator σ (avg ω)
  have hσ : 0 < σ := (Annealed.sigmaBar M j).2
  have havgMem : MemLp avg (ENNReal.ofReal (2 * p)) μ := by
    simpa [avg, μ] using
      missingWave_model_average_memLp hjN hstrict M h hM a c R hR weights hp
  have hmemX : MemLp x (ENNReal.ofReal (2 * p)) μ := by
    have hfun : x = σ⁻¹ • avg := by
      funext ω
      change avg ω / σ = σ⁻¹ * avg ω
      rw [div_eq_mul_inv]
      ring
    rw [hfun]
    exact havgMem.const_smul σ⁻¹
  have hshearContinuous :
      Continuous (fun η : ℝ => missingWaveShearOperator σ η) := by
    unfold missingWaveShearOperator
    exact continuous_const.add
      (continuous_smul.comp (continuous_id.prodMk continuous_const))
  have hshearMem : AEStronglyMeasurable shear μ := by
    exact hshearContinuous.comp_aestronglyMeasurable havgMem.aestronglyMeasurable
  have hshearNormMem : AEStronglyMeasurable (fun ω => ‖shear ω‖ ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      ((hshearMem.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
  have hxMem : AEStronglyMeasurable x μ := hmemX.aestronglyMeasurable
  have hpoint (ω : Cutoff.CutoffSample 2) : ‖shear ω‖ ^ 2 ≤ 2 + 2 * x ω ^ 2 := by
    have hratio : avg ω / σ = x ω := rfl
    simpa [shear, hratio] using
      missingWaveShearOperator_norm_sq_le σ (avg ω)
  have hpointNorm (ω : Cutoff.CutoffSample 2) :
      ‖‖shear ω‖ ^ 2‖ ≤ 2 + 2 * x ω ^ 2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpoint ω
  have hmono : eLpNorm (fun ω => ‖shear ω‖ ^ 2) (ENNReal.ofReal p) μ ≤
      eLpNorm (fun ω => 2 + 2 * x ω ^ 2) (ENNReal.ofReal p) μ :=
    eLpNorm_mono_ae_real hshearNormMem (Filter.Eventually.of_forall hpointNorm)
  have hpENN : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hdecomp : (fun ω => 2 + 2 * x ω ^ 2) =
      (fun _ : Cutoff.CutoffSample 2 => (2 : ℝ)) +
        (2 : ℝ) • fun ω => x ω ^ 2 := by
    funext ω
    simp
  have hconst : eLpNorm (fun _ : Cutoff.CutoffSample 2 => (2 : ℝ))
      (ENNReal.ofReal p) μ = ENNReal.ofReal 2 := by
    rw [eLpNorm_const]
    · simp [Real.enorm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    · have hp0 : 0 ≤ p := by linarith
      intro hpz
      have hreal := congrArg ENNReal.toReal hpz
      rw [ENNReal.toReal_ofReal hp0] at hreal
      simp at hreal
      linarith
    · exact (Measure.measure_univ_ne_zero).mp (by simp [μ])
  have htriangle : eLpNorm (fun ω => 2 + 2 * x ω ^ 2)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal 2 +
        ENNReal.ofReal 2 * eLpNorm (fun ω => x ω ^ 2) (ENNReal.ofReal p) μ := by
    rw [hdecomp]
    calc
      _ ≤ eLpNorm (fun _ : Cutoff.CutoffSample 2 => (2 : ℝ))
          (ENNReal.ofReal p) μ +
          eLpNorm ((2 : ℝ) • fun ω => x ω ^ 2) (ENNReal.ofReal p) μ :=
        eLpNorm_add_le hpENN
      _ ≤ _ := by
        rw [hconst]
        have hscal : eLpNorm ((2 : ℝ) • fun ω => x ω ^ 2)
            (ENNReal.ofReal p) μ ≤
            ENNReal.ofReal 2 * eLpNorm (fun ω => x ω ^ 2)
              (ENNReal.ofReal p) μ := by
          calc
            eLpNorm ((2 : ℝ) • fun ω => x ω ^ 2) (ENNReal.ofReal p) μ ≤
                ‖(2 : ℝ)‖ₑ * eLpNorm (fun ω => x ω ^ 2)
                  (ENNReal.ofReal p) μ := eLpNorm_const_smul_le
            _ = ENNReal.ofReal 2 * eLpNorm (fun ω => x ω ^ 2)
                  (ENNReal.ofReal p) μ := by
              rw [Real.enorm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
        exact add_le_add le_rfl hscal
  have hpow : eLpNorm (fun ω => x ω ^ 2) (ENNReal.ofReal p) μ =
      eLpNorm x (ENNReal.ofReal (2 * p)) μ ^ 2 := by
    have hnorm := eLpNorm_norm_rpow (p := ENNReal.ofReal p) x hxMem
      (by norm_num : (0 : ℝ) < 2)
    have hexponent : ENNReal.ofReal p * ENNReal.ofReal 2 =
        ENNReal.ofReal (2 * p) := by
      calc
        _ = ENNReal.ofReal (p * 2) :=
          (ENNReal.ofReal_mul (by linarith : 0 ≤ p)).symm
        _ = _ := by congr 1; ring
    rw [hexponent] at hnorm
    have hfun : (fun ω => ‖x ω‖ ^ (2 : ℝ)) = fun ω => x ω ^ 2 := by
      funext ω
      simp [Real.norm_eq_abs, Real.rpow_ofNat, sq_abs]
    rw [hfun] at hnorm
    change eLpNorm (fun ω => x ω ^ 2) (ENNReal.ofReal p) μ =
      eLpNorm x (ENNReal.ofReal (2 * p)) μ ^ (2 : ℝ) at hnorm
    exact hnorm.trans (ENNReal.rpow_natCast _ 2)
  have htop : (ENNReal.ofReal 2 + ENNReal.ofReal 2 *
      eLpNorm (fun ω => x ω ^ 2) (ENNReal.ofReal p) μ) ≠ ∞ := by
    rw [hpow]
    finiteness
  have hreal := ENNReal.toReal_mono htop (hmono.trans htriangle)
  have hprodTop : (ENNReal.ofReal 2 *
      eLpNorm (fun ω => x ω ^ 2) (ENNReal.ofReal p) μ) ≠ ∞ :=
    (ENNReal.add_ne_top.mp htop).2
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hprodTop,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2 : ℝ)),
    hpow, ENNReal.toReal_pow] at hreal
  have hmoment := missingWave_model_average_normalized_lpNorm_sq_le
    hjN hstrict M h hM hstate a c R hR weights hweights hp
  have hA : 0 ≤ M.gamma * (N - j : ℝ) *
      (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) := by
    have hγ : 0 < M.gamma := M.shellPrefix.gamma_pos
    have hgap : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hjN
    have hgap' : 0 ≤ (N - j : ℝ) := by linarith
    positivity
  have hcoef : 2 * (2 * p + 2) * 9 ≤ 80 * (p + 2) := by nlinarith [hp]
  have hnumeric : 2 + 2 *
      (eLpNorm x (ENNReal.ofReal (2 * p)) μ).toReal ^ 2 ≤
      2 + 80 * (p + 2) *
        (M.gamma * (N - j : ℝ) * (3 : ℝ) ^
          (2 * M.gamma * (N - j : ℝ))) := by
    calc
      _ ≤ 2 + 2 * ((2 * p + 2) *
          (9 * (M.gamma * (N - j : ℝ) * (3 : ℝ) ^
            (2 * M.gamma * (N - j : ℝ))))) := by nlinarith [hmoment]
      _ ≤ _ := by
        have hscaled := mul_le_mul_of_nonneg_right hcoef hA
        nlinarith
  exact hreal.trans hnumeric

end

end
end ASDExplicitGamma.Gaussian

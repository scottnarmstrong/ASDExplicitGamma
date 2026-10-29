module

public import ASDExplicitGamma.Gaussian.Q3SpatialNormMoment
public import ASDExplicitGamma.Gaussian.Q3WeightedBandLaw
public import ASDExplicitGamma.Gaussian.ShellFrameClock
public import ASDExplicitGamma.Statements.NativeInductionState
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Actual finite-band whole-root spatial moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization Filter Set
open Algsuperdiff.Section3
open scoped ENNReal Topology

namespace ASDExplicitGamma.Gaussian

/-- The planar quarter-turn matrix used to turn the scalar q3 shell into its skew field. -/
def planarJMatrix : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  if i.val = 0 then (if j.val = 1 then -1 else 0) else if j.val = 0 then 1 else 0

/-- Frobenius norm on the four entries of a planar matrix. -/
noncomputable def matrixFrobenius (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Real.sqrt (A 0 0 ^ 2 + A 0 1 ^ 2 + A 1 0 ^ 2 + A 1 1 ^ 2)

/-- The actual skew-matrix field represented by a scalar q3 shell. -/
noncomputable def planarJField {K : Type*} [TopologicalSpace K] (f : C(K, ℝ)) :
    C(K, Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨fun x => f x • planarJMatrix,
    continuous_smul.comp (f.continuous.prodMk continuous_const)⟩

theorem matrixFrobenius_smul_planarJ (x : ℝ) :
    matrixFrobenius (x • planarJMatrix) = Real.sqrt 2 * |x| := by
  have hentries : (x • planarJMatrix) 0 0 ^ 2 + (x • planarJMatrix) 0 1 ^ 2 +
      (x • planarJMatrix) 1 0 ^ 2 + (x • planarJMatrix) 1 1 ^ 2 = 2 * x ^ 2 := by
    simp [planarJMatrix, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [matrixFrobenius, hentries]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))).mp
  rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * x ^ 2), mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_abs]

/-- The square and finite shell list appearing in the actual observation band. -/
noncomputable def wholeRootBandLength (j N : ℤ) : ℕ := (N - j).toNat

noncomputable def wholeRootShellLabel (j N : ℤ) :
    Fin (wholeRootBandLength j N) → ℤ := fun i => j + 1 + (i.val : ℤ)

noncomputable def wholeRootWeights (j N : ℤ) (b : ℤ → ℝ) :
    Fin (wholeRootBandLength j N) → ℝ := fun i => b (wholeRootShellLabel j N i)

theorem wholeRootShellLabel_injective (j N : ℤ) :
    Function.Injective (wholeRootShellLabel j N) := by
  intro i i' h
  apply Fin.ext
  simp only [wholeRootShellLabel] at h
  omega

/-- The finite shell labels enumerate the actual integer interval `(j,N]`. -/
theorem wholeRootShellLabel_sum_Ioc (j N : ℤ) (f : ℤ → ℝ) :
    (∑ i, f (wholeRootShellLabel j N i)) = ∑ k ∈ Finset.Ioc j N, f k := by
  change (∑ i : Fin ((N - j).toNat), f (j + 1 + (i.val : ℤ))) = _
  have hfin : (∑ i : Fin ((N - j).toNat), f (j + 1 + (i.val : ℤ))) =
      ∑ t ∈ Finset.range (N - j).toNat, f (j + 1 + (t : ℤ)) := by
    exact Fin.sum_univ_eq_sum_range (fun t => f (j + 1 + (t : ℤ))) _
  have hinterval : (∑ k ∈ Finset.Ioc j N, f k) =
      ∑ t ∈ Finset.range (N - j).toNat, f (j + 1 + (t : ℤ)) := by
    rw [Int.Ioc_eq_finset_map, Finset.sum_map]
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
  exact hfin.trans hinterval.symm

theorem wholeRootShellLabel_mem_Ioc (j N : ℤ) (hjN : j ≤ N)
    (i : Fin (wholeRootBandLength j N)) :
    wholeRootShellLabel j N i ∈ Finset.Ioc j N := by
  have hlen : ((wholeRootBandLength j N : ℕ) : ℤ) = N - j := by
    dsimp [wholeRootBandLength]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hjN)
  have hi : (i.val : ℤ) < N - j := by
    have hi' : (i.val : ℤ) < (wholeRootBandLength j N : ℤ) := by
      exact_mod_cast i.isLt
    rw [hlen] at hi'
    exact hi'
  simp only [Finset.mem_Ioc, wholeRootShellLabel]
  omega

/-- The q3 shell length at level `i`, truncated by a side-`3^n` root, is the root side
times the dimensionless spatial clock used in the source estimate. -/
theorem min_three_shell_length_eq (i n : ℤ) :
    min ((3 : ℝ) ^ i) ((3 : ℝ) ^ n) =
      (3 : ℝ) ^ n * min ((3 : ℝ) ^ (i - n)) 1 := by
  have hmul : (3 : ℝ) ^ n * (3 : ℝ) ^ (i - n) = (3 : ℝ) ^ i := by
    calc
      _ = (3 : ℝ) ^ (n + (i - n)) := (zpow_add₀ (by norm_num) _ _).symm
      _ = _ := by congr 1; omega
  by_cases hin : i ≤ n
  · have hpow : (3 : ℝ) ^ (i - n) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    have horder : (3 : ℝ) ^ i ≤ (3 : ℝ) ^ n :=
      zpow_le_zpow_right₀ (by norm_num) hin
    rw [min_eq_left horder, min_eq_left hpow]
    exact hmul.symm
  · have hni : n ≤ i := le_of_not_ge hin
    have hpow : 1 ≤ (3 : ℝ) ^ (i - n) := one_le_zpow₀ (by norm_num) (sub_nonneg.mpr hni)
    have horder : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ i :=
      zpow_le_zpow_right₀ (by norm_num) hni
    rw [min_eq_right horder, min_eq_right hpow]
    ring

/-- The actual product-q3 shell sum on a bounded translated observation rectangle. -/
noncomputable def wholeRootModelBand {a b c d : ℝ} (j N : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) : C(closedRectangle a b c d, ℝ) :=
  modelWeightedBand (closedRectangle a b c d) (wholeRootShellLabel j N)
    (wholeRootWeights j N weights) ω

/-- The normalized squared Frobenius spatial L⁴ norm, with the physical matrix factor two. -/
noncomputable def wholeRootSpatialStatistic {K : Set (Vec 2)} [CompactSpace K]
    (σ R : ℝ) (f : C(K, ℝ)) : ℝ :=
  (2 / (R * σ ^ 2)) * ‖ContinuousMap.toLp 4 (spatialVolume K) ℝ f‖ ^ 2

/-- The normalized squared Frobenius L⁴ norm written as its ordinary spatial integral. -/
noncomputable def normalizedFrobeniusL4Squared {K : Set (Vec 2)} [CompactSpace K]
    (σ R : ℝ) (f : C(K, ℝ)) : ℝ :=
  Real.sqrt ((∫ x : K, matrixFrobenius (planarJField f x) ^ 4 ∂spatialVolume K) / R ^ 2) /
    σ ^ 2

/-- The rectangle carrying an observation square of side `R` has ordinary area `R²`. -/
theorem spatialVolume_square_real {a c R : ℝ} (hR : 0 ≤ R) :
    (spatialVolume (closedRectangle a (a + R) c (c + R))).real Set.univ = R ^ 2 := by
  let K := closedRectangle a (a + R) c (c + R)
  have hK : K = Set.Icc ![a, c] ![a + R, c + R] := by
    ext x
    simp only [K, closedRectangle, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def]
    constructor
    · rintro ⟨⟨h₀₁, h₀₂⟩, ⟨h₁₁, h₁₂⟩⟩
      constructor
      · intro i
        fin_cases i
        · simpa using h₀₁
        · simpa using h₁₁
      · intro i
        fin_cases i
        · simpa using h₀₂
        · simpa using h₁₂
    · rintro ⟨hlo, hhi⟩
      constructor
      · exact ⟨hlo 0, hhi 0⟩
      · exact ⟨hlo 1, hhi 1⟩
  have hcoord : ![a, c] ≤ ![a + R, c + R] := by
    intro i
    fin_cases i <;> simp <;> linarith
  change (spatialVolume K).real Set.univ = R ^ 2
  rw [measureReal_def, spatialVolume_univ K, hK, Real.volume_Icc_pi_toReal hcoord]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- A scalar realization and its literal quarter-turn skew field have the exact source
Frobenius L⁴ normalization. -/
theorem normalizedFrobeniusL4Squared_eq_spatialStatistic {K : Set (Vec 2)}
    [CompactSpace K] (σ R : ℝ) (hσ : 0 < σ) (hR : 0 < R) (f : C(K, ℝ)) :
    normalizedFrobeniusL4Squared σ R f = wholeRootSpatialStatistic σ R f := by
  have hmoment : (∫ x : K, matrixFrobenius (planarJField f x) ^ 4 ∂spatialVolume K) =
      4 * ‖ContinuousMap.toLp 4 (spatialVolume K) ℝ f‖ ^ 4 := by
    calc
      _ = ∫ x : K, 4 * f x ^ 4 ∂spatialVolume K := by
        apply integral_congr_ae
        filter_upwards with x
        change matrixFrobenius (f x • planarJMatrix) ^ 4 = 4 * f x ^ 4
        rw [matrixFrobenius_smul_planarJ]
        have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        have hsqrt4 : Real.sqrt 2 ^ 4 = 4 := by nlinarith [hsqrt]
        rw [mul_pow, hsqrt4]
        have hpow : |f x| ^ 4 = f x ^ 4 := by
          calc
            |f x| ^ 4 = |(f x) ^ 4| := (abs_pow _ _).symm
            _ = (f x) ^ 4 := abs_of_nonneg (by positivity)
        rw [hpow]
      _ = 4 * (∫ x : K, f x ^ 4 ∂spatialVolume K) := by
        rw [integral_const_mul]
      _ = 4 * ‖ContinuousMap.toLp 4 (spatialVolume K) ℝ f‖ ^ 4 := by
        rw [← continuousMap_toLp_norm_pow_four]
  rw [normalizedFrobeniusL4Squared, hmoment]
  have hnorm : 0 ≤ ‖ContinuousMap.toLp 4 (spatialVolume K) ℝ f‖ := norm_nonneg _
  have hroot : Real.sqrt ((4 * ‖ContinuousMap.toLp 4 (spatialVolume K) ℝ f‖ ^ 4) / R ^ 2) =
      2 * ‖ContinuousMap.toLp 4 (spatialVolume K) ℝ f‖ ^ 2 / R := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg (by positivity) hR.le)).mp
    rw [Real.sq_sqrt (by positivity : 0 ≤
      (4 * ‖ContinuousMap.toLp 4 (spatialVolume K) ℝ f‖ ^ 4) / R ^ 2)]
    field_simp
    ring
  rw [hroot]
  dsimp [wholeRootSpatialStatistic]
  field_simp

/-- Integration on a measurable spatial layer is a bounded functional on continuous functions. -/
noncomputable def spatialIntegralCLM {K : Set (Vec 2)} [CompactSpace K]
    (E : Set K) : C(K, ℝ) →L[ℝ] ℝ := by
  let μ := (spatialVolume K).restrict E
  let A : C(K, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := by
        intro f g
        have hf : Integrable f μ := by
          apply memLp_one_iff_integrable.mp
          exact f.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
        have hg : Integrable g μ := by
          apply memLp_one_iff_integrable.mp
          exact g.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
        exact integral_add hf hg
      map_smul' := by
        intro c f
        exact integral_smul c f }
  refine LinearMap.mkContinuous A ((spatialVolume K).real E) ?_
  intro f
  have hbound : ‖∫ x, f x ∂μ‖ ≤ ‖f‖ * μ.real Set.univ :=
    norm_integral_le_of_norm_le_const (ae_of_all μ fun x => f.norm_coe_le_norm x)
  calc
    ‖A f‖ = ‖∫ x, f x ∂μ‖ := rfl
    _ ≤ ‖f‖ * μ.real Set.univ := hbound
    _ = (spatialVolume K).real E * ‖f‖ := by
      rw [measureReal_restrict_apply_univ]
      ring

/-- The actual finite-band Cameron--Martin estimate gives an all-real-order bound for the
normalized squared Frobenius L⁴ statistic of its common Gaussian series realization. -/
theorem wholeRoot_gaussianSeries_lq_bound {b : ℕ} [NeZero b]
    (a c R σ : ℝ) (β w : Fin b → ℝ) (L : Fin b → {l : ℝ // 0 < l})
    (hab : a < a + R) (hcd : c < c + R) (hR : 0 < R) (hσ : 0 < σ)
    (hw : ∀ i, |w i| ≤ 1) {q V C : ℝ} (hq : 2 ≤ q)
    (hvar : (∑ i, w i ^ 2 * β i ^ 2) ≤ V)
    (hcost : (∑ i, β i ^ 2 * min (L i).1 R) ≤ C) :
    (eLpNorm (fun ω => wholeRootSpatialStatistic σ R
      (q3WeightedBandH3Value a (a + R) c (c + R) β w L
        (q3BandSeries a (a + R) c (c + R) β L ω)))
      (ENNReal.ofReal q) standardGaussianInfinitePi).toReal ≤
      (2 / (R * σ ^ 2)) *
        (2 * Real.sqrt ((spatialVolume (closedRectangle a (a + R) c (c + R))).real Set.univ *
          (3 * V ^ 2)) + 4 * q * C) := by
  let T := q3WeightedBandH3Spatial a (a + R) c (c + R) β w L
  let ξ : (ℕ → ℝ) → ℝ := fun ω => ‖T (q3BandSeries a (a + R) c (c + R) β L ω)‖
  have hseries : MemLp (q3BandSeries a (a + R) c (c + R) β L)
      (ENNReal.ofReal (2 * q)) standardGaussianInfinitePi :=
    memLp_q3BandSeries a (a + R) c (c + R) β L (by linarith)
  have hTmem : MemLp (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω))
      (ENNReal.ofReal (2 * q)) standardGaussianInfinitePi :=
    @MemLp.continuousLinearMap_comp (ℕ → ℝ) ℝ
      (Q3BandH3 a (a + R) c (c + R) β L)
      (SpatialLp4 (closedRectangle a (a + R) c (c + R))) inferInstance
      (ENNReal.ofReal (2 * q)) standardGaussianInfinitePi
      inferInstance inferInstance inferInstance
      (instQ3BandH3NormedSpace a (a + R) c (c + R) β L) inferInstance
      (q3BandSeries a (a + R) c (c + R) β L) hseries T
  have hT : AEStronglyMeasurable
      (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω)) standardGaussianInfinitePi :=
    hTmem.aestronglyMeasurable
  have hconst : 0 ≤ 2 / (R * σ ^ 2) := by positivity
  have hstat : (fun ω => wholeRootSpatialStatistic σ R
      (q3WeightedBandH3Value a (a + R) c (c + R) β w L
        (q3BandSeries a (a + R) c (c + R) β L ω))) =
      (2 / (R * σ ^ 2)) • (fun ω => ξ ω ^ 2) := by
    funext ω
    rfl
  have hscale : (eLpNorm (fun ω => wholeRootSpatialStatistic σ R
      (q3WeightedBandH3Value a (a + R) c (c + R) β w L
        (q3BandSeries a (a + R) c (c + R) β L ω)))
      (ENNReal.ofReal q) standardGaussianInfinitePi) =
      ENNReal.ofReal (2 / (R * σ ^ 2)) *
        eLpNorm (fun ω => ξ ω ^ 2) (ENNReal.ofReal q) standardGaussianInfinitePi := by
    rw [hstat, eLpNorm_const_smul]
    simp only [Real.enorm_of_nonneg hconst]
  have hq0 : 0 ≤ q := le_trans (by norm_num : (0 : ℝ) ≤ 2) hq
  have hexponent : ENNReal.ofReal q * ENNReal.ofReal 2 = ENNReal.ofReal (2 * q) := by
    calc
      _ = ENNReal.ofReal (q * 2) := (ENNReal.ofReal_mul hq0).symm
      _ = _ := by congr 1; ring
  have hmoment : (eLpNorm (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω))
        (ENNReal.ofReal (2 * q)) standardGaussianInfinitePi).toReal ^ 2 ≤
      2 * Real.sqrt ((spatialVolume (closedRectangle a (a + R) c (c + R))).real Set.univ *
        (3 * V ^ 2)) + 4 * q * C := by
    have hbase := q3WeightedBandSeries_spatial_lpNorm_sq_le_of_cost
      a (a + R) c (c + R) β w L hab hcd hw (p := 2 * q) (by linarith)
    have harea : (spatialVolume (closedRectangle a (a + R) c (c + R))).real Set.univ = R ^ 2 :=
      spatialVolume_square_real (a := a) (c := c) (R := R) hR.le
    have hvolume : volume.real (closedRectangle a (a + R) c (c + R)) = R ^ 2 := by
      calc
        _ = (spatialVolume (closedRectangle a (a + R) c (c + R))).real Set.univ := by
          change (volume (closedRectangle a (a + R) c (c + R))).toReal =
            (spatialVolume (closedRectangle a (a + R) c (c + R)) Set.univ).toReal
          rw [spatialVolume_univ]
        _ = _ := harea
    have hrootVolume : Real.sqrt (volume.real (closedRectangle a (a + R) c (c + R))) = R := by
      rw [hvolume, Real.sqrt_sq_eq_abs, abs_of_pos hR]
    rw [hrootVolume] at hbase
    have hvar0 : 0 ≤ ∑ i, w i ^ 2 * β i ^ 2 := Finset.sum_nonneg fun i hi => by positivity
    have harea0 : 0 ≤ (spatialVolume (closedRectangle a (a + R) c (c + R))).real Set.univ := by
      positivity
    have hroot : Real.sqrt ((spatialVolume (closedRectangle a (a + R) c (c + R))).real Set.univ *
          (3 * (∑ i, w i ^ 2 * β i ^ 2) ^ 2)) ≤
        Real.sqrt ((spatialVolume (closedRectangle a (a + R) c (c + R))).real Set.univ *
          (3 * V ^ 2)) := by
      apply Real.sqrt_le_sqrt
      have hV : 0 ≤ V := le_trans hvar0 hvar
      have hsumSq : (∑ i, w i ^ 2 * β i ^ 2) ^ 2 ≤ V ^ 2 :=
        (sq_le_sq₀ hvar0 hV).mpr hvar
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsumSq (by norm_num)) harea0
    calc
      _ ≤ 2 * Real.sqrt ((spatialVolume (closedRectangle a (a + R) c (c + R))).real Set.univ *
          (3 * (∑ i, w i ^ 2 * β i ^ 2) ^ 2)) + 4 * q *
            (∑ i, β i ^ 2 * min (L i).1 R) := by
        convert hbase using 1; ring_nf
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hroot (by norm_num))
        (mul_le_mul_of_nonneg_left hcost (by positivity))
  have hpower : eLpNorm (fun ω => ξ ω ^ 2) (ENNReal.ofReal q) standardGaussianInfinitePi =
      eLpNorm (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω))
        (ENNReal.ofReal (2 * q)) standardGaussianInfinitePi ^ 2 := by
    calc
      _ = eLpNorm (fun ω => ξ ω ^ ((2 : ℕ) : ℝ))
          (ENNReal.ofReal q) standardGaussianInfinitePi := by
        congr 1
        funext ω
        exact (Real.rpow_natCast (ξ ω) 2).symm
      _ = eLpNorm (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω))
          (ENNReal.ofReal (2 * q)) standardGaussianInfinitePi ^ (2 : ℝ) := by
        have hnorm := eLpNorm_norm_rpow
          (p := ENNReal.ofReal q)
          (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω)) hT
          (by norm_num : (0 : ℝ) < 2)
        rw [hexponent] at hnorm
        change eLpNorm (fun ω => ‖T (q3BandSeries a (a + R) c (c + R) β L ω)‖ ^ (2 : ℝ))
            (ENNReal.ofReal q) standardGaussianInfinitePi =
          eLpNorm (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω))
            (ENNReal.ofReal (2 * q)) standardGaussianInfinitePi ^ (2 : ℝ)
        exact hnorm
      _ = eLpNorm (fun ω => T (q3BandSeries a (a + R) c (c + R) β L ω))
          (ENNReal.ofReal (2 * q)) standardGaussianInfinitePi ^ 2 :=
        ENNReal.rpow_natCast _ 2
  rw [hscale, hpower, ENNReal.toReal_mul, ENNReal.toReal_ofReal hconst, ENNReal.toReal_pow]
  exact mul_le_mul_of_nonneg_left hmoment hconst

/-- The finite-band law transfers the whole-root statistic from the actual cutoff sample to the
common white-noise realization. -/
theorem wholeRoot_actualBand_eLpNorm_eq {b : ℕ} [NeZero b]
    (a b₀ c d R σ : ℝ) (hab : a < b₀) (hcd : c < d)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    {q : ℝ} :
    eLpNorm (fun ω => wholeRootSpatialStatistic σ R
      (modelWeightedBand (closedRectangle a b₀ c d) k w ω))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure =
    eLpNorm (fun ω => wholeRootSpatialStatistic σ R
      (q3WeightedBandH3Value a b₀ c d (fun i => q3ModelAmplitude M h (k i)) w
        (fun i => q3ModelLength (k i))
        (q3BandSeries a b₀ c d (fun i => q3ModelAmplitude M h (k i))
          (fun i => q3ModelLength (k i)) ω)))
      (ENNReal.ofReal q) standardGaussianInfinitePi := by
  let K := closedRectangle a b₀ c d
  let F : C(K, ℝ) → ℝ := wholeRootSpatialStatistic σ R
  let W := modelWeightedBand K k w
  let G : (ℕ → ℝ) → C(K, ℝ) := fun ω =>
    q3WeightedBandH3Value a b₀ c d (fun i => q3ModelAmplitude M h (k i)) w
      (fun i => q3ModelLength (k i))
      (q3BandSeries a b₀ c d (fun i => q3ModelAmplitude M h (k i))
        (fun i => q3ModelLength (k i)) ω)
  have hF : Continuous F := by
    let P : C(K, ℝ) →L[ℝ] SpatialLp4 K := ContinuousMap.toLp 4 (spatialVolume K) ℝ
    have hP : Continuous P := P.continuous
    change Continuous (fun f => (2 / (R * σ ^ 2)) * ‖P f‖ ^ 2)
    exact continuous_const.mul ((continuous_norm.comp hP).pow 2)
  have hW : Measurable W := by
    exact measurable_modelWeightedBand K k w
  have hG : StronglyMeasurable G := by
    dsimp [G]
    exact (q3WeightedBandH3Value a b₀ c d
      (fun i => q3ModelAmplitude M h (k i)) w
      (fun i => q3ModelLength (k i))).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_q3BandSeries a b₀ c d
        (fun i => q3ModelAmplitude M h (k i)) (fun i => q3ModelLength (k i)))
  have hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map W =
      standardGaussianInfinitePi.map G := by
    dsimp [W, G, K]
    exact actualWeightedBandLaw_eq_h3Series a b₀ c d hab hcd M h hM k hk w
  have hFleft : AEStronglyMeasurable F ((Cutoff.cutoffSampleLaw M).toMeasure.map W) :=
    hF.measurable.aestronglyMeasurable
  have hFright : AEStronglyMeasurable F (standardGaussianInfinitePi.map G) :=
    hF.measurable.aestronglyMeasurable
  have hleft := eLpNorm_map_measure (p := ENNReal.ofReal q)
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (f := W) hFleft hW.aemeasurable
  have hright := eLpNorm_map_measure (p := ENNReal.ofReal q)
    (μ := standardGaussianInfinitePi) (f := G) hFright hG.aemeasurable
  calc
    _ = eLpNorm F (ENNReal.ofReal q) ((Cutoff.cutoffSampleLaw M).toMeasure.map W) := by
      change eLpNorm (F ∘ W) (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure = _
      exact hleft.symm
    _ = eLpNorm F (ENNReal.ofReal q) (standardGaussianInfinitePi.map G) := by
      rw [hlaw]
    _ = _ := by
      change eLpNorm F (ENNReal.ofReal q) (standardGaussianInfinitePi.map G) =
        eLpNorm (F ∘ G) (ENNReal.ofReal q) standardGaussianInfinitePi
      exact hright

/-- Attenuations in `[0,1]` cannot increase the summed shell variance beyond the
unattenuated protected-corridor clock. -/
theorem wholeRootBand_variance_clock (j N : ℤ) (hjN : j ≤ N)
    (M : ABKModel 2) (h σ : ℝ) (hσ : 0 < σ)
    (hframe : shellVarianceSum h M.gamma j / 4 ≤ σ ^ 2)
    (weights : ℤ → ℝ) (hweights : ∀ k ∈ Finset.Ioc j N, 0 ≤ weights k ∧ weights k ≤ 1) :
    (∑ i : Fin (wholeRootBandLength j N),
      weights (wholeRootShellLabel j N i) ^ 2 *
        q3ModelAmplitude M h (wholeRootShellLabel j N i) ^ 2) ≤
      σ ^ 2 * (9 * M.gamma * (N - j : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ))) := by
  have hcoeff (i : Fin (wholeRootBandLength j N)) :
      weights (wholeRootShellLabel j N i) ^ 2 ≤ 1 := by
    obtain ⟨h0, h1⟩ := hweights _ (wholeRootShellLabel_mem_Ioc j N hjN i)
    have hmul := mul_nonneg h0 (sub_nonneg.mpr h1)
    nlinarith
  have hraw : (∑ k ∈ Finset.Ioc j N,
      q3ModelAmplitude M h k ^ 2 / σ ^ 2) ≤
      9 * M.gamma * (N - j : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) :=
    q3_shell_variance_sum_div_frame_sq_le M h σ j N hσ hframe hjN
  have hrawFin : (∑ i : Fin (wholeRootBandLength j N),
      q3ModelAmplitude M h (wholeRootShellLabel j N i) ^ 2 / σ ^ 2) ≤
      9 * M.gamma * (N - j : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) := by
    calc
      _ = ∑ k ∈ Finset.Ioc j N, q3ModelAmplitude M h k ^ 2 / σ ^ 2 :=
        wholeRootShellLabel_sum_Ioc j N (fun k => q3ModelAmplitude M h k ^ 2 / σ ^ 2)
      _ ≤ _ := hraw
  have hscale : (∑ i : Fin (wholeRootBandLength j N),
      q3ModelAmplitude M h (wholeRootShellLabel j N i) ^ 2) =
      σ ^ 2 * ∑ i : Fin (wholeRootBandLength j N),
        q3ModelAmplitude M h (wholeRootShellLabel j N i) ^ 2 / σ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [ne_of_gt hσ]
  calc
    _ ≤ ∑ i : Fin (wholeRootBandLength j N),
        q3ModelAmplitude M h (wholeRootShellLabel j N i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hcoeff i)
        (sq_nonneg (q3ModelAmplitude M h (wholeRootShellLabel j N i)))
    _ = σ ^ 2 * ∑ i : Fin (wholeRootBandLength j N),
        q3ModelAmplitude M h (wholeRootShellLabel j N i) ^ 2 / σ ^ 2 := hscale
    _ ≤ _ := mul_le_mul_of_nonneg_left hrawFin (sq_nonneg σ)

/-- The operator-cost clock splits the fine geometric tail from the coarse unit cost. -/
theorem wholeRootBand_spatial_cost_clock (j n N : ℤ) (hjn : j ≤ n) (hnN : n ≤ N)
    (M : ABKModel 2) (h σ : ℝ) (hσ : 0 < σ)
    (hframe : shellVarianceSum h M.gamma j / 4 ≤ σ ^ 2) :
    (∑ i : Fin (wholeRootBandLength j N),
      q3ModelAmplitude M h (wholeRootShellLabel j N i) ^ 2 *
        min (q3ModelLength (wholeRootShellLabel j N i)).1 ((3 : ℝ) ^ n)) ≤
      9 * M.gamma * σ ^ 2 * (3 : ℝ) ^ n *
        (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) * ((N - n : ℝ) + 3 / 2) := by
  let clock : ℤ → ℝ := fun k => min ((3 : ℝ) ^ (k - n)) 1
  let C : ℝ := 9 * M.gamma * σ ^ 2 * (3 : ℝ) ^ n *
    (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ))
  have hγ : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hR : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hC : 0 ≤ C := by positivity
  have hterm (k : ℤ) (hk : k ∈ Finset.Ioc j N) :
      q3ModelAmplitude M h k ^ 2 * min ((3 : ℝ) ^ k) ((3 : ℝ) ^ n) ≤ C * clock k := by
    have hshell := q3_shell_variance_div_frame_sq_le M h σ j k hσ hframe
    have hkN : k ≤ N := (Finset.mem_Ioc.mp hk).2
    have hexp : 2 * M.gamma * ((k : ℝ) - j) ≤
        2 * M.gamma * ((N : ℝ) - j) := by
      have hkN' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
      nlinarith [hγ.le]
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    have hclock : 0 ≤ clock k := by
      dsimp [clock]
      exact le_min (zpow_nonneg (by norm_num) _) (by norm_num)
    have hscale : q3ModelAmplitude M h k ^ 2 =
        σ ^ 2 * (q3ModelAmplitude M h k ^ 2 / σ ^ 2) := by
      field_simp [ne_of_gt hσ]
    calc
      _ = (σ ^ 2 * (3 : ℝ) ^ n) *
          ((q3ModelAmplitude M h k ^ 2 / σ ^ 2) * clock k) := by
        rw [min_three_shell_length_eq k n]
        field_simp [ne_of_gt hσ]
        ring
      _ ≤ (σ ^ 2 * (3 : ℝ) ^ n) *
          (9 * M.gamma * (3 : ℝ) ^ (2 * M.gamma * ((k : ℝ) - j)) * clock k) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hshell hclock) (by positivity)
      _ ≤ C * clock k := by
        have hpow' : 9 * M.gamma * (3 : ℝ) ^ (2 * M.gamma * ((k : ℝ) - j)) * clock k ≤
            9 * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) * clock k := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (by positivity)) hclock
        calc
          _ = (σ ^ 2 * (3 : ℝ) ^ n) *
              (9 * M.gamma * (3 : ℝ) ^ (2 * M.gamma * ((k : ℝ) - j)) * clock k) := by ring
          _ ≤ (σ ^ 2 * (3 : ℝ) ^ n) *
              (9 * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) * clock k) :=
            mul_le_mul_of_nonneg_left hpow' (by positivity)
          _ = C * clock k := by dsimp [C, clock]; ring
  have hsum : (∑ i : Fin (wholeRootBandLength j N),
      q3ModelAmplitude M h (wholeRootShellLabel j N i) ^ 2 *
        min (q3ModelLength (wholeRootShellLabel j N i)).1 ((3 : ℝ) ^ n)) =
      ∑ k ∈ Finset.Ioc j N,
        q3ModelAmplitude M h k ^ 2 * min ((3 : ℝ) ^ k) ((3 : ℝ) ^ n) := by
    calc
      _ = ∑ k ∈ Finset.Ioc j N,
          q3ModelAmplitude M h k ^ 2 * min (q3ModelLength k).1 ((3 : ℝ) ^ n) :=
        wholeRootShellLabel_sum_Ioc j N (fun k =>
          q3ModelAmplitude M h k ^ 2 * min (q3ModelLength k).1 ((3 : ℝ) ^ n))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [q3ModelLength]
  calc
    _ = ∑ k ∈ Finset.Ioc j N,
        q3ModelAmplitude M h k ^ 2 * min ((3 : ℝ) ^ k) ((3 : ℝ) ^ n) := hsum
    _ ≤ ∑ k ∈ Finset.Ioc j N, C * clock k :=
      Finset.sum_le_sum fun k hk => hterm k hk
    _ = C * ∑ k ∈ Finset.Ioc j N, clock k := by rw [Finset.mul_sum]
    _ ≤ C * ((N - n : ℝ) + 3 / 2) := by
      exact mul_le_mul_of_nonneg_left (q3_spatial_clock_sum_le j n N hjn hnN) hC
    _ = _ := by rfl

/-- The scalar corridor component in the frozen native state implies the quarter-variance
lower bound used for the protected shell clock. -/
theorem wholeRoot_frame_variance_lower (M : ABKModel 2) (h : ℝ) (j : ℤ)
    (hstate : ASDExplicitGamma.nativeInductionState M h j) :
    shellVarianceSum h M.gamma j / 4 ≤ (Annealed.sigmaBar M j : ℝ) ^ 2 := by
  have hγ : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hden : 0 < 1 - (3 : ℝ) ^ (-(2 * M.gamma)) := by
    apply sub_pos.mpr
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3)
    nlinarith [hγ]
  have hB : 0 ≤ shellVarianceSum h M.gamma j := by
    unfold shellVarianceSum
    positivity
  have hlower := hstate.2.2.2.2.2.2.1
  nlinarith [hB, sq_nonneg M.nu]

/-- Actual finite-band whole-root estimate, in the exact Frobenius normalization of the source.
The source square may be translated; the common Cameron--Martin estimate is uniform in its
location. -/
theorem wholeRoot_modelBand_lq_bound {j n N : ℤ} (hjn : j ≤ n) (hnN : n ≤ N)
    (hstrict : j < N) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hstate : ASDExplicitGamma.nativeInductionState M h j)
    (a c : ℝ) (weights : ℤ → ℝ)
    (hweights : ∀ k ∈ Finset.Ioc j N, 0 ≤ weights k ∧ weights k ≤ 1)
    {q : ℝ} (hq : 2 ≤ q) :
    (eLpNorm (fun ω => normalizedFrobeniusL4Squared (Annealed.sigmaBar M j)
      ((3 : ℝ) ^ n) (wholeRootModelBand (a := a) (b := a + (3 : ℝ) ^ n)
        (c := c) (d := c + (3 : ℝ) ^ n) j N weights ω))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure).toReal ≤
      160 * M.gamma * ((n - j : ℝ) + q * ((N - n : ℝ) + 1)) *
        (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) := by
  let R : ℝ := (3 : ℝ) ^ n
  let σ : ℝ := Annealed.sigmaBar M j
  let K := closedRectangle a (a + R) c (c + R)
  let β : Fin (wholeRootBandLength j N) → ℝ := fun i =>
    q3ModelAmplitude M h (wholeRootShellLabel j N i)
  let w : Fin (wholeRootBandLength j N) → ℝ := fun i =>
    weights (wholeRootShellLabel j N i)
  let L : Fin (wholeRootBandLength j N) → {l : ℝ // 0 < l} := fun i =>
    q3ModelLength (wholeRootShellLabel j N i)
  have hjN : j ≤ N := le_trans hjn hnN
  have hσ : 0 < σ := (Annealed.sigmaBar M j).2
  have hR : 0 < R := by positivity
  have hstateFrame := wholeRoot_frame_variance_lower M h j hstate
  have hV : (∑ i, w i ^ 2 * β i ^ 2) ≤
      σ ^ 2 * (9 * M.gamma * (N - j : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ))) := by
    simpa only [β, w] using
      wholeRootBand_variance_clock j N hjN M h σ hσ hstateFrame weights hweights
  let V : ℝ := σ ^ 2 * (9 * M.gamma * (N - j : ℝ) *
    (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)))
  let C : ℝ := 9 * M.gamma * σ ^ 2 * R *
    (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) * ((N - n : ℝ) + 3 / 2)
  have hcost : (∑ i, β i ^ 2 * min (L i).1 R) ≤ C := by
    simpa only [β, L, C, R] using
      wholeRootBand_spatial_cost_clock j n N hjn hnN M h σ hσ hstateFrame
  have hvar : (∑ i, w i ^ 2 * β i ^ 2) ≤ V := by simpa only [V] using hV
  have hw : ∀ i, |w i| ≤ 1 := by
    intro i
    obtain ⟨h0, h1⟩ := hweights _ (wholeRootShellLabel_mem_Ioc j N hjN i)
    rw [abs_of_nonneg h0]
    exact h1
  have hab : a < a + R := by linarith
  have hcd : c < c + R := by linarith
  have hlabels : Function.Injective (wholeRootShellLabel j N) :=
    wholeRootShellLabel_injective j N
  have hlength : 0 < wholeRootBandLength j N := by
    have hcast : ((wholeRootBandLength j N : ℕ) : ℤ) = N - j := by
      dsimp [wholeRootBandLength]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hjN)
    have hcastpos : (0 : ℤ) < (wholeRootBandLength j N : ℤ) := by
      rw [hcast]
      omega
    exact_mod_cast hcastpos
  letI instWholeRootBandLengthNeZero : NeZero (wholeRootBandLength j N) :=
    ⟨Nat.ne_of_gt hlength⟩
  have hgaussian := wholeRoot_gaussianSeries_lq_bound a c R σ β w L hab hcd hR hσ hw
    (q := q) (V := V) (C := C) hq hvar hcost
  have htransfer := wholeRoot_actualBand_eLpNorm_eq
    a (a + R) c (c + R) R σ (by linarith) (by linarith) M h hM
    (wholeRootShellLabel j N) hlabels (fun i => weights (wholeRootShellLabel j N i))
    (q := q)
  have htransfer' :
      (eLpNorm (fun ω => wholeRootSpatialStatistic σ R
        (wholeRootModelBand (a := a) (b := a + R) (c := c) (d := c + R)
          j N weights ω))
        (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure) =
      (eLpNorm (fun ω => wholeRootSpatialStatistic σ R
        (q3WeightedBandH3Value a (a + R) c (c + R)
          (fun i => q3ModelAmplitude M h (wholeRootShellLabel j N i))
          (fun i => weights (wholeRootShellLabel j N i))
          (fun i => q3ModelLength (wholeRootShellLabel j N i))
          (q3BandSeries a (a + R) c (c + R)
            (fun i => q3ModelAmplitude M h (wholeRootShellLabel j N i))
            (fun i => q3ModelLength (wholeRootShellLabel j N i)) ω)))
        (ENNReal.ofReal q) standardGaussianInfinitePi) := by
    change eLpNorm (fun ω => wholeRootSpatialStatistic σ R
        (modelWeightedBand K (wholeRootShellLabel j N)
          (fun i => weights (wholeRootShellLabel j N i)) ω))
        (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure = _
    exact htransfer
  have hstat : ∀ ω,
      normalizedFrobeniusL4Squared σ R
        (wholeRootModelBand (a := a) (b := a + R) (c := c) (d := c + R)
          j N weights ω) =
      wholeRootSpatialStatistic σ R
        (wholeRootModelBand (a := a) (b := a + R) (c := c) (d := c + R)
          j N weights ω) := by
    intro ω
    exact normalizedFrobeniusL4Squared_eq_spatialStatistic (K := K) σ R hσ hR
      (wholeRootModelBand (a := a) (b := a + R) (c := c) (d := c + R)
        j N weights ω)
  have hgauss' :
      (eLpNorm (fun ω => wholeRootSpatialStatistic σ R
        (q3WeightedBandH3Value a (a + R) c (c + R)
          (fun i => q3ModelAmplitude M h (wholeRootShellLabel j N i))
          (fun i => weights (wholeRootShellLabel j N i))
          (fun i => q3ModelLength (wholeRootShellLabel j N i))
          (q3BandSeries a (a + R) c (c + R)
            (fun i => q3ModelAmplitude M h (wholeRootShellLabel j N i))
            (fun i => q3ModelLength (wholeRootShellLabel j N i)) ω)))
        (ENNReal.ofReal q) standardGaussianInfinitePi).toReal ≤
      (2 / (R * σ ^ 2)) *
        (2 * Real.sqrt (R ^ 2 * (3 * V ^ 2)) + 4 * q * C) := by
    simpa only [β, w, L, K, spatialVolume_square_real (R := R) hR.le] using hgaussian
  have hm_nonneg : 0 ≤ (N - j : ℝ) := by exact_mod_cast sub_nonneg.mpr hjN
  have hγ : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hVnonneg : 0 ≤ V := by
    dsimp [V]
    positivity
  have hroot : Real.sqrt (R ^ 2 * (3 * V ^ 2)) ≤ 2 * R * V := by
    have hsquare : R ^ 2 * (3 * V ^ 2) ≤ (2 * R * V) ^ 2 := by nlinarith [sq_nonneg R, sq_nonneg V]
    calc
      _ ≤ Real.sqrt ((2 * R * V) ^ 2) := Real.sqrt_le_sqrt hsquare
      _ = |2 * R * V| := Real.sqrt_sq_eq_abs _
      _ = 2 * R * V := abs_of_nonneg (by nlinarith [hR, hVnonneg])
  have hconst : 0 ≤ 2 / (R * σ ^ 2) := by positivity
  have hupper :
      (eLpNorm (fun ω => wholeRootSpatialStatistic σ R
        (q3WeightedBandH3Value a (a + R) c (c + R)
          (fun i => q3ModelAmplitude M h (wholeRootShellLabel j N i))
          (fun i => weights (wholeRootShellLabel j N i))
          (fun i => q3ModelLength (wholeRootShellLabel j N i))
          (q3BandSeries a (a + R) c (c + R)
            (fun i => q3ModelAmplitude M h (wholeRootShellLabel j N i))
            (fun i => q3ModelLength (wholeRootShellLabel j N i)) ω)))
        (ENNReal.ofReal q) standardGaussianInfinitePi).toReal ≤
      72 * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) *
        ((N - j : ℝ) + q * ((N - n : ℝ) + 3 / 2)) := by
    calc
      _ ≤ (2 / (R * σ ^ 2)) *
          (2 * Real.sqrt (R ^ 2 * (3 * V ^ 2)) + 4 * q * C) := hgauss'
      _ ≤ (2 / (R * σ ^ 2)) * (4 * R * V + 4 * q * C) := by
        have hsum : 2 * Real.sqrt (R ^ 2 * (3 * V ^ 2)) + 4 * q * C ≤
            4 * R * V + 4 * q * C := by nlinarith [hroot]
        exact mul_le_mul_of_nonneg_left
          hsum hconst
      _ = _ := by
        dsimp [V, C]
        field_simp [ne_of_gt hR, ne_of_gt hσ]
        ring
  have hr : 0 ≤ (n - j : ℝ) := by exact_mod_cast sub_nonneg.mpr hjn
  have hD : 0 ≤ (N - n : ℝ) := by exact_mod_cast sub_nonneg.mpr hnN
  have hgap : (N - j : ℝ) = (n - j : ℝ) + (N - n : ℝ) := by ring
  have hcostArg : (N - j : ℝ) + q * ((N - n : ℝ) + 3 / 2) =
      (n - j : ℝ) + (N - n : ℝ) + q * ((N - n : ℝ) + 3 / 2) := by
    rw [hgap]
  have harith : 72 * ((n - j : ℝ) + (N - n : ℝ) + q * ((N - n : ℝ) + 3 / 2)) ≤
      160 * ((n - j : ℝ) + q * ((N - n : ℝ) + 1)) := by
    have hprod := mul_nonneg hD (by linarith : 0 ≤ q - 2)
    nlinarith [hprod]
  have hscale :
      72 * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) *
          ((N - j : ℝ) + q * ((N - n : ℝ) + 3 / 2)) ≤
      160 * M.gamma * ((n - j : ℝ) + q * ((N - n : ℝ) + 1)) *
          (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) := by
    have hpower : 0 < (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hfactor : 0 ≤ M.gamma * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) :=
      mul_nonneg hγ.le hpower.le
    calc
      _ = M.gamma * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) *
          (72 * ((N - j : ℝ) + q * ((N - n : ℝ) + 3 / 2))) := by ring
      _ = M.gamma * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) *
          (72 * ((n - j : ℝ) + (N - n : ℝ) + q * ((N - n : ℝ) + 3 / 2))) := by
        rw [hcostArg]
      _ ≤ M.gamma * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) *
          (160 * ((n - j : ℝ) + q * ((N - n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left harith hfactor
      _ = _ := by ring
  calc
    _ = (eLpNorm (fun ω => wholeRootSpatialStatistic σ R
        (wholeRootModelBand (a := a) (b := a + R) (c := c) (d := c + R)
          j N weights ω))
        (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure).toReal := by
      congr 1
      apply eLpNorm_congr_ae
      exact ae_of_all _ hstat
    _ = (eLpNorm (fun ω => wholeRootSpatialStatistic σ R
          (q3WeightedBandH3Value a (a + R) c (c + R)
            (fun i => q3ModelAmplitude M h (wholeRootShellLabel j N i))
            (fun i => weights (wholeRootShellLabel j N i))
            (fun i => q3ModelLength (wholeRootShellLabel j N i))
            (q3BandSeries a (a + R) c (c + R)
              (fun i => q3ModelAmplitude M h (wholeRootShellLabel j N i))
              (fun i => q3ModelLength (wholeRootShellLabel j N i)) ω)))
          (ENNReal.ofReal q) standardGaussianInfinitePi).toReal := by
      rw [htransfer']
    _ ≤ _ := hupper.trans hscale

/-- The whole-root statistic has finite q-moment under the actual finite-band law. -/
theorem wholeRoot_actualBand_memLp {b : ℕ} [NeZero b]
    (a b₀ c d R σ : ℝ) (hab : a < b₀) (hcd : c < d)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    {q : ℝ} (hq : 2 ≤ q) :
    MemLp (fun ω => wholeRootSpatialStatistic σ R
      (modelWeightedBand (closedRectangle a b₀ c d) k w ω))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure := by
  let β : Fin b → ℝ := fun i => q3ModelAmplitude M h (k i)
  let L : Fin b → {l : ℝ // 0 < l} := fun i => q3ModelLength (k i)
  let T := q3WeightedBandH3Spatial a b₀ c d β w L
  have hseries : MemLp (q3BandSeries a b₀ c d β L)
      (ENNReal.ofReal (2 * q)) standardGaussianInfinitePi :=
    memLp_q3BandSeries a b₀ c d β L (by linarith)
  have hTmem : MemLp (fun ω => T (q3BandSeries a b₀ c d β L ω))
      (ENNReal.ofReal (2 * q)) standardGaussianInfinitePi :=
    @MemLp.continuousLinearMap_comp (ℕ → ℝ) ℝ
      (Q3BandH3 a b₀ c d β L) (SpatialLp4 (closedRectangle a b₀ c d)) inferInstance
      (ENNReal.ofReal (2 * q)) standardGaussianInfinitePi
      inferInstance inferInstance inferInstance
      (instQ3BandH3NormedSpace a b₀ c d β L) inferInstance
      (q3BandSeries a b₀ c d β L) hseries T
  have hq0 : 0 ≤ q := le_trans (by norm_num : (0 : ℝ) ≤ 2) hq
  have hdiv : ENNReal.ofReal (2 * q) / ENNReal.ofReal 2 = ENNReal.ofReal q := by
    calc
      _ = ENNReal.ofReal ((2 * q) / 2) :=
        (ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)).symm
      _ = _ := by congr 1; ring
  have hnorm2 : MemLp (fun ω => ‖T (q3BandSeries a b₀ c d β L ω)‖ ^ 2)
      (ENNReal.ofReal q) standardGaussianInfinitePi := by
    convert hTmem.norm_rpow_div (ENNReal.ofReal 2) using 1
    · simp
    · exact hdiv.symm
  have hstat : (fun ω => wholeRootSpatialStatistic σ R
      (q3WeightedBandH3Value a b₀ c d β w L (q3BandSeries a b₀ c d β L ω))) =
      (2 / (R * σ ^ 2)) •
        (fun ω => ‖T (q3BandSeries a b₀ c d β L ω)‖ ^ 2) := by
    funext ω
    rfl
  have hseriesMem : MemLp
      (fun ω => wholeRootSpatialStatistic σ R
        (q3WeightedBandH3Value a b₀ c d β w L (q3BandSeries a b₀ c d β L ω)))
      (ENNReal.ofReal q) standardGaussianInfinitePi := by
    rw [hstat]
    exact hnorm2.const_smul _
  have htransfer := wholeRoot_actualBand_eLpNorm_eq a b₀ c d R σ hab hcd M h hM k hk w
    (q := q)
  rw [memLp_iff]
  rw [htransfer]
  exact hseriesMem.eLpNorm_lt_top

end ASDExplicitGamma.Gaussian

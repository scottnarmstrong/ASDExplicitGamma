module

public import ASDExplicitGamma.Gaussian.NormalScaledMoments
public import ASDExplicitGamma.Scalar.MolecularTraceMoments
public import ASDExplicitGamma.Scalar.MolecularStartupScale
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Small-gamma molecular initialization for the all-order CIR induction -/

@[expose] public section

open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Scalar ASDExplicitGamma.Variational
open scoped ENNReal NNReal

namespace ASDExplicitGamma.AllOrder

/-- The finite even-order cutoff (P=max(20,2\lfloor 2^{-14}/(2\gamma)\rfloor)
used by the small-gamma CIR seed. -/
noncomputable def smallGammaSeedP (γ : ℝ) : ℕ := max 20 (2 * ⌊(1 / 16384 : ℝ) / (2 * γ)⌋₊)

private theorem cutoffStreamSquareAverage_pow_le (m k : ℤ)
    (ω : Cutoff.CutoffSample 2) {p : ℕ} :
    cutoffStreamSquareAverage m k ω ^ p ≤
      volumeAverage (cubeSet (originCube 2 k))
        (fun x => Cutoff.cutoffValue m ω x 1 0 ^ (2 * p)) := by
  let Q := originCube 2 k
  have hvol : volume (cubeSet Q) ≠ 0 := by
    intro hz
    have hv := volume_cubeSet_toReal_pos Q
    rw [hz, ENNReal.toReal_zero] at hv
    exact lt_irrefl 0 hv
  have hpow : IntegrableOn (fun x => Cutoff.cutoffValue m ω x 1 0 ^ (2 * p))
      (cubeSet Q) := by
    apply ((Cutoff.continuous_cutoffValue_entry m ω 1 0).pow (2 * p)).continuousOn.integrableOn_of_subset_isCompact
      (isBounded_cubeSet Q).isCompact_closure (measurableSet_cubeSet Q) subset_closure
    exact (volume_cubeSet_lt_top Q).ne
  have hcomp : IntegrableOn ((fun z : ℝ => z ^ p) ∘
      (fun x => Cutoff.cutoffValue m ω x 1 0 ^ 2)) (cubeSet Q) := by
    convert hpow using 1
    funext x
    simp only [Function.comp_apply, ← pow_mul]
  have hj := (convexOn_pow (𝕜 := ℝ) p).map_set_average_le (by fun_prop)
    isClosed_Ici hvol (volume_cubeSet_lt_top Q).ne
    (Filter.Eventually.of_forall (fun x => sq_nonneg (Cutoff.cutoffValue m ω x 1 0)))
    (cutoff_stream_square_integrable m k ω) hcomp
  simpa only [MeasureTheory.setAverage_eq, Measure.real, smul_eq_mul,
    cutoffStreamSquareAverage, volumeAverage, ← pow_mul] using hj

private theorem cutoffStreamEvenPower_product_integrable (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) {p : ℕ} (hp : 1 ≤ p) :
    Integrable (fun q : Cutoff.CutoffSample 2 × Vec 2 =>
      Cutoff.cutoffValue m q.1 q.2 1 0 ^ (2 * p))
      ((Cutoff.cutoffSampleLaw M).toMeasure.prod
        (volume.restrict (cubeSet (originCube 2 k)))) := by
  let q : ℕ := 2 * p
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let v : ℝ≥0 := Real.toNNReal (shellVarianceSum h M.gamma m)
  apply (integrable_prod_iff'
    ((measurable_cutoff_stream_joint m).pow_const q).aestronglyMeasurable).mpr
  constructor
  · refine Filter.Eventually.of_forall fun x => ?_
    have hlaw := cutoffStream_gaussian M h hM m x
    have hg : Integrable (fun z : ℝ => z ^ q) (gaussianReal 0 v) := by
      have hmem : MemLp (id : ℝ → ℝ) (q : ℝ≥0∞) (gaussianReal 0 v) :=
        memLp_id_gaussianReal' (μ := 0) (v := v) (q : ℝ≥0∞) ENNReal.coe_ne_top
      have hi := hmem.integrable_norm_pow (show q ≠ 0 by dsimp [q]; omega)
      apply hi.congr
      filter_upwards with z
      change ‖z‖ ^ q = z ^ q
      rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg]
      have hq : 0 ≤ z ^ q := by
        dsimp [q]
        rw [pow_mul]
        exact pow_nonneg (sq_nonneg z) p
      exact hq
    simpa only [q, v] using hlaw.integrable_fun_comp hg
  · have he : (fun x : Vec 2 =>
        ∫ ω, ‖Cutoff.cutoffValue m ω x 1 0 ^ q‖ ∂μ) = fun _ =>
          ∫ z : ℝ, z ^ q ∂gaussianReal 0 v := by
      funext x
      have hg : Integrable (fun z : ℝ => z ^ q) (gaussianReal 0 v) := by
        have hmem : MemLp (id : ℝ → ℝ) (q : ℝ≥0∞) (gaussianReal 0 v) :=
          memLp_id_gaussianReal' (μ := 0) (v := v) (q : ℝ≥0∞) ENNReal.coe_ne_top
        have hi := hmem.integrable_norm_pow (show q ≠ 0 by dsimp [q]; omega)
        apply hi.congr
        filter_upwards with z
        change ‖z‖ ^ q = z ^ q
        rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg]
        have hq : 0 ≤ z ^ q := by
          dsimp [q]
          rw [pow_mul]
          exact pow_nonneg (sq_nonneg z) p
        exact hq
      have hi := (cutoffStream_gaussian M h hM m x).integral_comp
        (f := fun z : ℝ => z ^ q) (by fun_prop)
      calc
        _ = ∫ ω, Cutoff.cutoffValue m ω x 1 0 ^ q ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [Real.norm_eq_abs, abs_of_nonneg]
          have hq : 0 ≤ Cutoff.cutoffValue m ω x 1 0 ^ q := by
            dsimp [q]
            rw [pow_mul]
            exact pow_nonneg (sq_nonneg (Cutoff.cutoffValue m ω x 1 0)) p
          exact hq
        _ = ∫ z : ℝ, z ^ q ∂gaussianReal 0 v := by simpa [q, v] using hi
    rw [he]
    exact integrable_const _

private theorem integral_cutoffStreamSquareAverage_pow (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) {p : ℕ} (hp : 1 ≤ p) :
    Integrable (fun ω => cutoffStreamSquareAverage m k ω ^ p)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, cutoffStreamSquareAverage m k ω ^ p ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (2 * (p : ℝ)) ^ p * shellVarianceSum h M.gamma m ^ p := by
  let Q := originCube 2 k
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let v : ℝ := (volume (cubeSet Q)).toReal
  let q : ℕ := 2 * p
  let F : Cutoff.CutoffSample 2 → Vec 2 → ℝ := fun ω x =>
    Cutoff.cutoffValue m ω x 1 0 ^ q
  have hF := cutoffStreamEvenPower_product_integrable M h hM m k hp
  have havg : Integrable (fun ω => volumeAverage (cubeSet Q) (F ω)) μ :=
    hF.integral_prod_left.const_mul v⁻¹
  have hmoment : (∫ ω, volumeAverage (cubeSet Q) (F ω) ∂μ) =
      ∫ z : ℝ, z ^ q ∂gaussianReal 0 (Real.toNNReal (shellVarianceSum h M.gamma m)) := by
    have hs := integral_integral_swap (f := F) hF
    have he : (fun x : Vec 2 => ∫ ω, F ω x ∂μ) = fun _ =>
        ∫ z : ℝ, z ^ q ∂gaussianReal 0 (Real.toNNReal (shellVarianceSum h M.gamma m)) := by
      funext x
      exact (cutoffStream_gaussian M h hM m x).integral_comp (f := fun z : ℝ => z ^ q)
        (by fun_prop)
    unfold volumeAverage
    rw [integral_const_mul, hs, he]
    exact volumeAverage_const (volume_cubeSet_toReal_pos Q).ne'
  have hA (ω : Cutoff.CutoffSample 2) : 0 ≤ cutoffStreamSquareAverage m k ω := by
    apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    exact integral_nonneg fun x => sq_nonneg _
  have hpower_integrable : Integrable (fun ω => cutoffStreamSquareAverage m k ω ^ p) μ := by
    apply havg.mono' ((measurable_cutoffStreamSquareAverage m k).pow_const p).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (pow_nonneg (hA ω) p)]
      exact cutoffStreamSquareAverage_pow_le m k ω
  have hmono := integral_mono hpower_integrable havg (fun ω =>
    cutoffStreamSquareAverage_pow_le m k ω)
  rw [hmoment] at hmono
  have hB : 0 ≤ shellVarianceSum h M.gamma m := by
    exact ge_of_tendsto (Model.cutoffPartialStream_variance_tendsto M h m)
      (Filter.Eventually.of_forall fun N =>
        (Model.cutoffPartialVariance M h m N).coe_nonneg)
  have hgauss := Gaussian.integral_gaussianReal_pow_even_le
    (Real.toNNReal (shellVarianceSum h M.gamma m)) p
  rw [Real.coe_toNNReal _ hB] at hgauss
  refine ⟨hpower_integrable, ?_⟩
  simpa only [q, mul_pow] using hmono.trans hgauss

private theorem lpNorm_le_of_integral_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {p : ℕ} (hp : 0 < p)
    (hX : MemLp X (p : ℝ≥0∞) μ) {R : ℝ} (hR : 0 ≤ R)
    (hI : ∫ ω, |X ω| ^ p ∂μ ≤ R ^ p) : lpNorm X (p : ℝ≥0∞) μ ≤ R := by
  have hEq := lpNorm_eq_integral_norm_rpow_toReal (p := (p : ℝ≥0∞))
    (by simp [hp.ne']) (by simp) hX.aestronglyMeasurable
  have hEq' : lpNorm X (p : ℝ≥0∞) μ = (∫ ω, |X ω| ^ p ∂μ) ^ ((p : ℝ)⁻¹) := by
    simp [hEq, ENNReal.toReal_natCast, Real.norm_eq_abs, Real.rpow_natCast]
  have hI0 : 0 ≤ ∫ ω, |X ω| ^ p ∂μ := integral_nonneg fun ω => by positivity
  have hroot : (R ^ p) ^ ((p : ℝ)⁻¹) = R := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR, mul_inv_cancel₀ (by exact_mod_cast hp.ne'),
      Real.rpow_one]
  rw [hEq']
  calc
    (∫ ω, |X ω| ^ p ∂μ) ^ ((p : ℝ)⁻¹) ≤ (R ^ p) ^ ((p : ℝ)⁻¹) :=
      Real.rpow_le_rpow hI0 hI (by positivity)
    _ = R := hroot

theorem cutoffStreamSquareAverage_even_lpNorm_le (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m k : ℤ) {p : ℕ} (hp : 1 ≤ p) :
    MemLp (cutoffStreamSquareAverage m k) (p : ℝ≥0∞)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (cutoffStreamSquareAverage m k) (p : ℝ≥0∞)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
          2 * (p + 1 : ℝ) * shellVarianceSum h M.gamma m := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B := shellVarianceSum h M.gamma m
  have hB : 0 ≤ B := by
    exact ge_of_tendsto (Model.cutoffPartialStream_variance_tendsto M h m)
      (Filter.Eventually.of_forall fun N => (Model.cutoffPartialVariance M h m N).coe_nonneg)
  have hpos (ω : Cutoff.CutoffSample 2) : 0 ≤ cutoffStreamSquareAverage m k ω := by
    apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    exact integral_nonneg fun x => sq_nonneg _
  have hi := integral_cutoffStreamSquareAverage_pow M h hM m k hp
  have hmem : MemLp (cutoffStreamSquareAverage m k) (p : ℝ≥0∞) μ := by
    apply (integrable_norm_rpow_iff
      (measurable_cutoffStreamSquareAverage m k).aestronglyMeasurable
      (by simp [Nat.cast_ne_zero.mpr (by omega : p ≠ 0)]) (by simp)).mp
    have he : (fun ω => ‖cutoffStreamSquareAverage m k ω‖ ^
        ((p : ℝ≥0∞).toReal)) =ᵐ[μ] fun ω => cutoffStreamSquareAverage m k ω ^ p := by
      filter_upwards [Filter.Eventually.of_forall hpos] with ω hω
      simp [Real.norm_eq_abs, abs_of_nonneg hω, ENNReal.toReal_natCast]
    exact hi.1.congr he.symm
  have hcap : (∫ ω, cutoffStreamSquareAverage m k ω ^ p ∂μ) ≤
      (2 * (p : ℝ) * B) ^ p := by
    calc
      _ ≤ (2 * (p : ℝ)) ^ p * B ^ p := hi.2
      _ = (2 * (p : ℝ) * B) ^ p := by rw [← mul_pow]
  have hbase : 0 ≤ 2 * ((p : ℝ) + 1) * B := by positivity
  have hpBound : (2 * (p : ℝ) * B) ^ p ≤ (2 * ((p : ℝ) + 1) * B) ^ p := by
    apply pow_le_pow_left₀ (by positivity)
    have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith
  have hnorm := lpNorm_le_of_integral_pow_le (μ := μ) (X := cutoffStreamSquareAverage m k)
    (p := p) (by omega) hmem hbase (by
      have hEq : (fun ω => |cutoffStreamSquareAverage m k ω| ^ p) =ᵐ[μ]
          fun ω => cutoffStreamSquareAverage m k ω ^ p := by
        filter_upwards [Filter.Eventually.of_forall hpos] with ω hω
        simp [abs_of_nonneg hω]
      exact (integral_congr_ae hEq).symm ▸ hcap.trans hpBound)
  refine ⟨hmem, ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one] using hnorm

/-- At all finite even orders through the source cutoff, the true-frame native trace
has a simultaneous molecular start on a left half-line. -/
theorem step_ao_cir_small_gamma_seed (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : 0 < M.gamma)
    (_hγsmall : M.gamma ≤ 1 / 327680)
    (_hcorridor : ∀ n : ℤ,
      M.nu ≤ (Annealed.sigmaBar M n : ℝ) ∧
        (Annealed.sigmaBar M n : ℝ) ^ 2 ≤
          M.nu ^ 2 + (13 / 8 : ℝ) * shellVarianceSum h M.gamma n) :
    ∃ mStar : ℤ, ∀ m : ℤ, m ≤ mStar → ∀ p : ℕ, 12 ≤ p → Even p →
      p ≤ smallGammaSeedP M.gamma →
      MemLp (cutoffTraceDefect M m m) (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (cutoffTraceDefect M m m) (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ 12 * 900000 * M.gamma ∧
        12 * 900000 * M.gamma ≤ 900000 * M.gamma * (p : ℝ) := by
  let P : ℕ := smallGammaSeedP M.gamma
  let ε : ℝ := min 1 (12 * 900000 * M.gamma / (5 * ((P : ℝ) + 1)))
  have hε : 0 < ε := by
    apply lt_min
    · norm_num
    · positivity
  obtain ⟨mStar, hmStar⟩ := Scalar.exists_molecular_variance_halfLine M h ε hε
  refine ⟨mStar, fun m hm p hp12 _heven hpP => ?_⟩
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B := shellVarianceSum h M.gamma m
  let x := B / M.nu ^ 2
  let A := cutoffStreamSquareAverage m m
  let C := x ^ 2 / 2
  let c := 2 / M.nu ^ 2
  have hB : 0 ≤ B := by
    exact ge_of_tendsto (Model.cutoffPartialStream_variance_tendsto M h m)
      (Filter.Eventually.of_forall fun N => (Model.cutoffPartialVariance M h m N).coe_nonneg)
  have hnonneg : 0 ≤ x := div_nonneg hB (sq_nonneg M.nu)
  have hsmall : x ≤ ε := by
    simpa [x, B] using hmStar m hm
  have hx1 : x ≤ 1 := hsmall.trans (min_le_left _ _)
  have hratio : x ≤ 12 * 900000 * M.gamma / (5 * ((P : ℝ) + 1)) :=
    hsmall.trans (min_le_right _ _)
  have hC : 0 ≤ C := by positivity
  have hc : 0 ≤ c := by positivity
  have hA := cutoffStreamSquareAverage_even_lpNorm_le M h hM m m (by omega : 1 ≤ p)
  have hMajor : MemLp (fun ω => C + c * A ω) (p : ℝ≥0∞) μ :=
    (memLp_const C).add (hA.1.const_smul c)
  have hDom : ∀ ω, ‖cutoffTraceDefect M m m ω‖ ≤ C + c * A ω := by
    intro ω
    rw [Real.norm_of_nonneg (cutoffTraceDefect_nonneg M m m ω)]
    have hh := Scalar.cutoffTraceDefect_le_variance_competitor M h hM m m ω
    have heq : C + c * A ω =
        (B / M.nu ^ 2) ^ 2 / 2 + 2 * A ω / M.nu ^ 2 := by
      dsimp [C, c, x]
      field_simp [M.nu_pos.ne']
    rw [heq]
    exact hh
  have hmono := lpNorm_mono_real hMajor hDom
  have hpOrd : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by
    exact_mod_cast (show 1 ≤ p by omega)
  have hconstMem : MemLp (fun _ : Cutoff.CutoffSample 2 => C) (p : ℝ≥0∞) μ :=
    memLp_const C
  have htri := lpNorm_add_le (f := fun _ : Cutoff.CutoffSample 2 => C)
    (g := c • A) (μ := μ) hconstMem hpOrd
  have hsum : (fun _ : Cutoff.CutoffSample 2 => C) + c • A = fun ω => C + c * A ω := by
    funext ω
    rfl
  rw [hsum] at htri
  have hconst : lpNorm (fun _ : Cutoff.CutoffSample 2 => C) (p : ℝ≥0∞) μ = C := by
    rw [lpNorm_const' (show (p : ℝ≥0∞) ≠ 0 by
      exact_mod_cast (show p ≠ 0 by omega)) ENNReal.coe_ne_top C]
    simp [μ, Real.norm_of_nonneg hC]
  have hscale : lpNorm (c • A) (p : ℝ≥0∞) μ = c * lpNorm A (p : ℝ≥0∞) μ := by
    rw [lpNorm_const_smul]
    simp only [Real.nnnorm_of_nonneg hc, NNReal.coe_mk]
  have hAupper : lpNorm A (p : ℝ≥0∞) μ ≤ 2 * ((P : ℝ) + 1) * B := by
    have hpPReal : (p : ℝ) ≤ (P : ℝ) := by exact_mod_cast hpP
    have hle := hA.2
    dsimp [A] at hle ⊢
    have hmul := mul_le_mul_of_nonneg_right (by nlinarith : (p : ℝ) + 1 ≤ (P : ℝ) + 1) hB
    nlinarith [hle, hmul]
  have hLp : lpNorm (cutoffTraceDefect M m m) (p : ℝ≥0∞) μ ≤ C + c * lpNorm A (p : ℝ≥0∞) μ := by
    calc
      _ ≤ lpNorm (fun ω => C + c * A ω) (p : ℝ≥0∞) μ := hmono
      _ ≤ lpNorm (fun _ : Cutoff.CutoffSample 2 => C) (p : ℝ≥0∞) μ +
            lpNorm (c • A) (p : ℝ≥0∞) μ := htri
      _ = C + c * lpNorm A (p : ℝ≥0∞) μ := by rw [hconst, hscale]
  have hrough : C + c * lpNorm A (p : ℝ≥0∞) μ ≤ 12 * 900000 * M.gamma := by
    have hAlp : c * lpNorm A (p : ℝ≥0∞) μ ≤ 4 * ((P : ℝ) + 1) * x := by
      have hprod := mul_le_mul_of_nonneg_left hAupper hc
      calc
        _ ≤ c * (2 * ((P : ℝ) + 1) * B) := hprod
        _ = 4 * ((P : ℝ) + 1) * x := by
          dsimp [c, x]
          field_simp [M.nu_pos.ne']
          ring
    have hCsmall : C ≤ x / 2 := by
      have hx2 : x ^ 2 ≤ x := by
        nlinarith [mul_le_mul_of_nonneg_left hx1 hnonneg]
      dsimp [C]
      linarith
    have hsumcap : C + c * lpNorm A (p : ℝ≥0∞) μ ≤ 5 * ((P : ℝ) + 1) * x := by
      have hPpos : 0 ≤ (P : ℝ) := Nat.cast_nonneg _
      nlinarith [hCsmall, hAlp, hPpos, hnonneg]
    have hlast : 5 * ((P : ℝ) + 1) * x ≤ 12 * 900000 * M.gamma := by
      calc
        _ ≤ 5 * ((P : ℝ) + 1) *
            (12 * 900000 * M.gamma / (5 * ((P : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = _ := by field_simp [(by positivity : 5 * ((P : ℝ) + 1) ≠ 0)]
    exact hsumcap.trans hlast
  have htarget : lpNorm (cutoffTraceDefect M m m) (p : ℝ≥0∞) μ ≤
      12 * 900000 * M.gamma := hLp.trans hrough
  have hfinal : 12 * 900000 * M.gamma ≤ 900000 * M.gamma * (p : ℝ) := by
    have hpR : (12 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp12
    nlinarith [hγ, hpR]
  have hmem : MemLp (cutoffTraceDefect M m m) (p : ℝ≥0∞) μ := by
    apply hMajor.mono'
    · exact (Variational.cutoffTraceDefect_measurable M m m).aestronglyMeasurable
    · exact Filter.Eventually.of_forall hDom
  exact ⟨by simpa [μ] using hmem, by simpa [μ] using htarget, hfinal⟩

end ASDExplicitGamma.AllOrder

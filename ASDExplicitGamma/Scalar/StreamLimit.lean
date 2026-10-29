module

public import ASDExplicitGamma.Scalar.CutoffStream
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.AtTopBot.Field

/-! Large-parent convergence of the concrete solenoidal cutoff. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Corrector
open Filter Topology

private theorem tendsto_gradBound_originCube (L : ℕ) :
    Tendsto (fun k : ℕ => gradBound (originCube 2 (k : ℤ)) L)
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun k : ℕ => (3 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hrad : Tendsto (fun k : ℕ => cubeRadius (originCube 2 (k : ℤ))) atTop atTop := by
    convert hpow.atTop_div_const (by norm_num : (0 : ℝ) < 2) using 1
    ext k
    simp [cubeRadius, cubeScaleFactor_originCube]
    ring
  have hgap : 0 < cutoffOuterRatio L - cutoffInnerRatio L :=
    sub_pos.mpr (cutoffInnerRatio_lt_cutoffOuterRatio L)
  have hden : Tendsto
      (fun k : ℕ => (cutoffOuterRatio L - cutoffInnerRatio L) *
        cubeRadius (originCube 2 (k : ℤ))) atTop atTop := by
    simpa only [mul_comm] using hrad.atTop_mul_const hgap
  have hnum : Tendsto (fun _ : ℕ => (2 : ℝ) * quantitativeCubeCutoffGradientConst 2)
      atTop (𝓝 ((2 : ℝ) * quantitativeCubeCutoffGradientConst 2)) := tendsto_const_nhds
  have hdiv : Tendsto
      (fun k : ℕ => (2 : ℝ) * quantitativeCubeCutoffGradientConst 2 /
        ((cutoffOuterRatio L - cutoffInnerRatio L) *
          cubeRadius (originCube 2 (k : ℤ)))) atTop (𝓝 0) :=
    hnum.div_atTop hden
  have heq : (fun k : ℕ => gradBound (originCube 2 (k : ℤ)) L) =
      fun k : ℕ => (2 : ℝ) * quantitativeCubeCutoffGradientConst 2 /
        ((cutoffOuterRatio L - cutoffInnerRatio L) *
          cubeRadius (originCube 2 (k : ℤ))) := by
    funext k
    simp [gradBound]
    ring
  rw [heq]
  exact hdiv

/-- For any tolerance, one can fix an approximate stationary stream and a
cutoff level so that every sufficiently large parent cube has arbitrarily
small expected normalized (L^2) error from the actual band flux. -/
theorem exists_localStreamApprox_cube_error_eventually
    (M : ABKModel 2) (n m : ℤ) (c : ℝ) (e : Vec 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : CutoffSample 2 → (Fin 2 → HilbertVec 2),
    ∃ D : CutoffSample 2 → HilbertVec 2,
      StronglyMeasurable S ∧
      MemLp S 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ i k : Fin 2,
        ContDiff ℝ (⊤ : ℕ∞) (streamRealization S ω i k)) ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ i k : Fin 2,
        streamRealization S ω k i = -streamRealization S ω i k) ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ x : Vec 2,
        streamDivergence (streamRealization S ω) x = (realize D ω x).toVec) ∧
      StronglyMeasurable D ∧
      MemLp D 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, ‖D ω - cutoffBandFlux M n m c e ω‖ ^ 2
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ δ / 16) ∧
      ∃ L K : ℕ, ∀ k : ℕ, K ≤ k →
        (∫ ω, cubeLpNorm (originCube 2 (k : ℤ)) 2
          (fun x => HilbertVec.ofVec
            (localStreamApprox (originCube 2 (k : ℤ)) L S D ω x) -
              realize (cutoffBandFlux M n m c e) ω x) ^ (2 : ℝ)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ δ := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let j := cutoffBandFlux M n m c e
  obtain ⟨S, D, hSm, hS, hsm, hanti, hdiv, hDm, hD, herr⟩ :=
    exists_cutoff_band_stream M n m c e (by positivity : 0 < δ / 16)
  let D₂ : ℝ := ∫ ω, ‖D ω‖ ^ 2 ∂μ
  let S₂ : ℝ := ∫ ω, ‖S ω‖ ^ 2 ∂μ
  have hD₂_nonneg : 0 ≤ D₂ := integral_nonneg fun ω => sq_nonneg _
  have hS₂_nonneg : 0 ≤ S₂ := integral_nonneg fun ω => sq_nonneg _
  have hD₂_eq : D₂ = ∫ ω, ‖D ω‖ ^ 2 ∂μ := rfl
  have hS₂_eq : S₂ = ∫ ω, ‖S ω‖ ^ 2 ∂μ := rfl
  have hinv : Tendsto (fun L : ℕ => ((3 : ℝ) ^ L)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3))
  have hsmall : ∀ᶠ L : ℕ in atTop,
      ((3 : ℝ) ^ L)⁻¹ * D₂ < δ / 32 :=
    (show Tendsto (fun L : ℕ => ((3 : ℝ) ^ L)⁻¹ * D₂) atTop (𝓝 0) from by
      simpa using hinv.mul_const D₂).eventually
      (Iio_mem_nhds (by positivity : (0 : ℝ) < δ / 32))
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 hsmall
  let L : ℕ := L₀
  have hLsmall : (3 : ℝ) ^ (-(L : ℤ)) * D₂ < δ / 32 := by
    have h := hL₀ L (le_rfl)
    simpa [L, zpow_neg, zpow_natCast] using h
  let r : ℝ := min (1 / 2) (δ / (128 * (S₂ + 1)))
  have hrpos : 0 < r := by
    dsimp [r]
    apply lt_min
    · norm_num
    · positivity
  have hrleone : r ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  have hrle : r ≤ δ / (128 * (S₂ + 1)) := min_le_right _ _
  have hgrad := tendsto_gradBound_originCube L
  obtain ⟨K, hK⟩ := eventually_atTop.1
    (hgrad.eventually (Iio_mem_nhds hrpos))
  have hfluxm : StronglyMeasurable j := stronglyMeasurable_cutoffBandFlux M n m c e
  have hflux : MemLp j 2 μ := memLp_two_cutoffBandFlux M n m c e
  refine ⟨S, D, hSm, hS, hsm, hanti, hdiv, hDm, hD, ?_, L, K, ?_⟩
  · simpa [μ, j, cutoffBandFlux] using herr
  · intro k hk
    have hg : gradBound (originCube 2 (k : ℤ)) L < r := hK k hk
    have hg0 : 0 ≤ gradBound (originCube 2 (k : ℤ)) L := by
      exact gradBound_nonneg _ _
    have hgsq : (gradBound (originCube 2 (k : ℤ)) L) ^ 2 ≤ r := by
      have hsq : (gradBound (originCube 2 (k : ℤ)) L) ^ 2 ≤ r ^ 2 := by
        nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hg.le)
          (add_nonneg hg0 hrpos.le)]
      have hr2 : r ^ 2 ≤ r := by
        have := mul_le_of_le_one_left hrpos.le hrleone
        nlinarith
      exact hsq.trans hr2
    have hgsqmul :
        (gradBound (originCube 2 (k : ℤ)) L) ^ 2 * S₂ ≤ r * S₂ :=
      mul_le_mul_of_nonneg_right hgsq hS₂_nonneg
    have hratio : S₂ / (S₂ + 1) ≤ 1 := by
      apply (div_le_one (by linarith [hS₂_nonneg])).2
      linarith
    have hrS : r * S₂ ≤ δ / 128 := by
      calc
        r * S₂ ≤ (δ / (128 * (S₂ + 1))) * S₂ :=
          mul_le_mul_of_nonneg_right hrle hS₂_nonneg
        _ = (δ / 128) * (S₂ / (S₂ + 1)) := by
          field_simp [ne_of_gt (by positivity : 0 < S₂ + 1)]
        _ ≤ δ / 128 := by
          have hcoef : 0 ≤ δ / 128 := by positivity
          simpa using mul_le_mul_of_nonneg_left hratio hcoef
    have hgradcost :
        16 * (gradBound (originCube 2 (k : ℤ)) L) ^ 2 * S₂ ≤ δ / 8 := by
      calc
        _ ≤ 16 * (r * S₂) := by nlinarith [hgsqmul]
        _ ≤ δ / 8 := by nlinarith [hrS]
    have hfirst :
        4 * (3 : ℝ) ^ (-(L : ℤ)) * D₂ < δ / 8 := by
      calc
        4 * (3 : ℝ) ^ (-(L : ℤ)) * D₂ < 4 * (δ / 32) := by
          rw [show 4 * (3 : ℝ) ^ (-(L : ℤ)) * D₂ =
              4 * ((3 : ℝ) ^ (-(L : ℤ)) * D₂) by ring]
          exact mul_lt_mul_of_pos_left hLsmall (by norm_num)
        _ = δ / 8 := by ring
    have herror :=
      integral_cubeLpNorm_localStreamApprox_sub_le_of_approximateStream
        (μ := μ) (originCube 2 (k : ℤ)) L hSm hS hDm hD hfluxm hflux
    have herror' :
        (∫ ω, cubeLpNorm (originCube 2 (k : ℤ)) 2
          (fun x => HilbertVec.ofVec
            (localStreamApprox (originCube 2 (k : ℤ)) L S D ω x) -
              realize j ω x) ^ (2 : ℝ) ∂μ) ≤
          2 * ((2 : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * D₂ +
            2 * ((2 : ℝ) * gradBound (originCube 2 (k : ℤ)) L) ^ 2 * S₂) +
          2 * (∫ ω, ‖D ω - j ω‖ ^ 2 ∂μ) := by
      convert herror using 1
    have hbound :
        2 * ((2 : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * D₂ +
          2 * ((2 : ℝ) * gradBound (originCube 2 (k : ℤ)) L) ^ 2 * S₂) +
          2 * (δ / 16) ≤ δ := by
      have hgradcost' :
          2 * (2 * ((2 : ℝ) * gradBound (originCube 2 (k : ℤ)) L) ^ 2 * S₂) ≤ δ / 8 := by
        calc
          2 * (2 * ((2 : ℝ) * gradBound (originCube 2 (k : ℤ)) L) ^ 2 * S₂) =
              16 * (gradBound (originCube 2 (k : ℤ)) L) ^ 2 * S₂ := by ring
          _ ≤ δ / 8 := hgradcost
      have hlast : 2 * (δ / 16) = δ / 8 := by ring
      have hfirst' :
          2 * ((2 : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * D₂) < δ / 8 := by
        nlinarith [hfirst]
      rw [hlast]
      nlinarith
    calc
      _ ≤ 2 * ((2 : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * D₂ +
          2 * ((2 : ℝ) * gradBound (originCube 2 (k : ℤ)) L) ^ 2 * S₂) +
          2 * (δ / 16) := by
        have hgapcost :
            2 * (∫ ω, ‖D ω - j ω‖ ^ 2 ∂μ) ≤ 2 * (δ / 16) :=
          mul_le_mul_of_nonneg_left (by simpa [μ, j, cutoffBandFlux] using herr)
            (by norm_num : (0 : ℝ) ≤ 2)
        exact le_trans herror' (add_le_add (le_refl _) hgapcost)
      _ ≤ δ := hbound

end ASDExplicitGamma.Scalar

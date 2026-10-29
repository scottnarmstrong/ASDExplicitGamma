module

public import ASDExplicitGamma.Main.ThetaGeneratorHotObsVl2
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsEnvelope
public import ASDExplicitGamma.Main.ThetaGeneratorHotESourceSquareNode
public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorMixedBridgeLocalCore
public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeA
public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Inverse.MixedBridgeConclusion
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeLocalWeightedTheta
public import ASDExplicitGamma.Inverse.MixedBridgeSharpSlope
public import ASDExplicitGamma.Numerics.Native.Source5
public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Inverse.MixedBridgeLocalCorrector
public import ASDExplicitGamma.Inverse.ParentGapRare
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets
public import ASDExplicitGamma.Native.OldSignedSourceInverseSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotFeedbackPathwise
public import ASDExplicitGamma.Main.ELinearCauchyExpectation
public import ASDExplicitGamma.Main.ObserverParentGapPaired
public import ASDExplicitGamma.Main.RemainderFeedback

/-! Node MA-E-REMAINDER-FEEDBACK: the moment inputs at the observer root.
`E[B*] , E[B*^2]` from the `L^128` cap of the global inverse bank, `E[B* V2] <= beta xi` for the
local corrector squares, and `E[B* avg Theta] <= beta xi` for the OLD proxy Theta (which is not
replaced by `B*`: it enters only as the weight of the reciprocal-error row). -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped ENNReal

noncomputable section

/-- `B*` has an `L²` cap `beta` from the `L^128` cap of the global inverse bank. -/
theorem hot_bstar_memLp_two_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (mixedBridgeBstar M m t) 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (mixedBridgeBstar M m t) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ mainBeta := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
  have hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)) :=
    fun j => hpast _ (by omega)
  have hglobal := mixed_bridge_global_bank_split M h hM hγ m t ht hstate
  have hB0 (ω : Cutoff.CutoffSample 2) : 0 ≤ B ω := mixed_bridge_bstar_nonneg M m t ω
  have hB128ENN : eLpNorm (fun ω => ENNReal.ofReal (B ω)) 128 μ ≤
      ENNReal.ofReal (14103 / 10000) := by
    simpa [B, inverseBankCap, μ] using hglobal.2.1
  have hB128 : eLpNorm B 128 μ ≤ ENNReal.ofReal (14103 / 10000) := by
    rw [← eLpNorm_ofReal B (Filter.Eventually.of_forall hB0)]
    exact hB128ENN
  have hmem : MemLp B 128 μ := hB128.trans_lt ENNReal.ofReal_lt_top
  have hm2 : MemLp B 2 μ := hmem.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 128)
  have hb2 := (eLpNorm_le_eLpNorm_of_exponent_le (f := B) (μ := μ)
    (by norm_num : (2 : ℝ≥0∞) ≤ 128)).trans hB128
  refine ⟨hm2, ?_⟩
  change (eLpNorm B 2 μ).toReal ≤ _
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb2).trans_eq
    (ENNReal.toReal_ofReal (by norm_num))

/-- `E[B*] ≤ β` and `E[B*²] ≤ β²`, with integrability. -/
theorem hot_bstar_moments_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let B := mixedBridgeBstar M m t
    Integrable B μ ∧ (∫ ω, B ω ∂μ) ≤ mainBeta ∧
      Integrable (fun ω => B ω ^ 2) μ ∧ (∫ ω, B ω ^ 2 ∂μ) ≤ mainBeta ^ 2 := by
  intro μ B
  obtain ⟨hmem, hnorm⟩ := hot_bstar_memLp_two_Th M h hM hγ N hpast m hm t ht
  have hB0 : ∀ ω, 0 ≤ B ω := fun ω => mixed_bridge_bstar_nonneg M m t ω
  have hint : Integrable B μ := hmem.integrable (by norm_num)
  have hsq : Integrable (fun ω => B ω ^ 2) μ :=
    (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).mp hmem
  have hsqle : (∫ ω, B ω ^ 2 ∂μ) ≤ mainBeta ^ 2 := by
    rw [← ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hmem]
    exact pow_le_pow_left₀ lpNorm_nonneg hnorm 2
  have hβ : 0 ≤ mainBeta := by norm_num [mainBeta]
  refine ⟨hint, ?_, hsq, hsqle⟩
  obtain ⟨-, hc⟩ := main_cauchy_sqrt_expectation μ (fun ω => B ω ^ 2) (fun _ => (1 : ℝ))
    hsq (integrable_const _) (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    (Filter.Eventually.of_forall fun _ => zero_le_one)
  have e : (fun ω => Real.sqrt (B ω ^ 2) * Real.sqrt 1) = B := by
    funext ω
    rw [Real.sqrt_sq (hB0 ω), Real.sqrt_one, mul_one]
  rw [e] at hc
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, Real.sqrt_one] at hc
  exact hc.trans ((Real.sqrt_le_sqrt hsqle).trans_eq (Real.sqrt_sq hβ))

/-- Per observer cell: `E[B* Θ_U] ≤ β ξ` for the OLD proxy `Θ_U`. -/
theorem hot_obs_avg_theta_weighted_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let v := (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2
    let xi := mainEnvelopeXi v M.gamma (theta M * mainSourceInversePrefix) (theta M) t
    Integrable (fun ω => mixedBridgeBstar M m t ω *
      descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
        (fun U => mixedOldTheta M m U t ω)) μ ∧
      (∫ ω, mixedBridgeBstar M m t ω *
        descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
          (fun U => mixedOldTheta M m U t ω) ∂μ) ≤ mainBeta * xi := by
  classical
  intro μ v xi
  let Q := originCube 2 (m + hobs)
  let D := descendantsAtDepth Q (hobs + 5)
  let Bs : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
  have hbs : mixedGlobalHistoryMax M m t = Bs :=
    funext fun ω => main_hot_bstar_eq_Th M m t ht ω
  have hcell : ∀ U ∈ D, Integrable (fun ω => Bs ω * mixedOldTheta M m U t ω) μ ∧
      (∫ ω, Bs ω * mixedOldTheta M m U t ω ∂μ) ≤ mainBeta * xi := by
    intro U hU
    have hscale := hot_obs_cell_scale_Th m hobs U hU
    have hEnv := main_envelope_xi_depth5_actual_law_Th M h hM hγ N hpast m hm t ht U hscale
      ⟨1, by norm_num⟩
    rw [hbs] at hEnv
    simpa only [pow_one] using hEnv
  have heq : (fun ω => Bs ω * descendantsAverage Q (hobs + 5)
      (fun U => mixedOldTheta M m U t ω)) = fun ω => ((D.card : ℝ)⁻¹) *
        ∑ U ∈ D, Bs ω * mixedOldTheta M m U t ω := by
    funext ω
    show Bs ω * (((D.card : ℝ)⁻¹) * ∑ U ∈ D, mixedOldTheta M m U t ω) = _
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun U _ => ?_
    ring
  have hsumInt : Integrable (fun ω => ∑ U ∈ D, Bs ω * mixedOldTheta M m U t ω) μ :=
    integrable_finsetSum D fun U hU => (hcell U hU).1
  refine ⟨?_, ?_⟩
  · show Integrable (fun ω => Bs ω * descendantsAverage Q (hobs + 5)
      (fun U => mixedOldTheta M m U t ω)) μ
    rw [heq]
    exact hsumInt.const_mul _
  · show (∫ ω, Bs ω * descendantsAverage Q (hobs + 5)
      (fun U => mixedOldTheta M m U t ω) ∂μ) ≤ _
    rw [heq, integral_const_mul, integral_finsetSum D fun U hU => (hcell U hU).1]
    have hle := Finset.sum_le_card_nsmul D _ (mainBeta * xi) fun U hU => (hcell U hU).2
    have hpos : (0 : ℝ) < D.card := by
      exact_mod_cast Finset.card_pos.2 (descendantsAtDepth_nonempty Q (hobs + 5))
    rw [nsmul_eq_mul] at hle
    calc ((D.card : ℝ)⁻¹) * _ ≤ ((D.card : ℝ)⁻¹) * (D.card * (mainBeta * xi)) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hpos.le)
      _ = mainBeta * xi := by field_simp

/-- `E[B* V2] ≤ β ξ` (sharp, without the `ε` allowance), for `V2` the observer-cell average of the
local corrector squares. -/
theorem hot_obs_bv2_sharp_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let v := (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2
    let xi := mainEnvelopeXi v M.gamma (theta M * mainSourceInversePrefix) (theta M) t
    Integrable (fun ω => mixedBridgeBstar M m t ω *
      descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
        (fun U => mixedBridgeVLocal_Th M m U t ω ^ 2)) μ ∧
      (∫ ω, mixedBridgeBstar M m t ω *
        descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
          (fun U => mixedBridgeVLocal_Th M m U t ω ^ 2) ∂μ) ≤ mainBeta * xi := by
  classical
  intro μ v xi
  let Q := originCube 2 (m + hobs)
  let D := descendantsAtDepth Q (hobs + 5)
  let Bs : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
  have hcell : ∀ U ∈ D, Integrable (fun ω => Bs ω * mixedBridgeVLocal_Th M m U t ω ^ 2) μ ∧
      (∫ ω, Bs ω * mixedBridgeVLocal_Th M m U t ω ^ 2 ∂μ) ≤ mainBeta * xi :=
    fun U hU => hot_obs_cell_weighted_moment_Th M h hM hγ N hpast m hm hobs h40 t ht U hU
  have heq : (fun ω => Bs ω * descendantsAverage Q (hobs + 5)
      (fun U => mixedBridgeVLocal_Th M m U t ω ^ 2)) = fun ω => ((D.card : ℝ)⁻¹) *
        ∑ U ∈ D, Bs ω * mixedBridgeVLocal_Th M m U t ω ^ 2 := by
    funext ω
    show Bs ω * (((D.card : ℝ)⁻¹) * ∑ U ∈ D, mixedBridgeVLocal_Th M m U t ω ^ 2) = _
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun U _ => ?_
    ring
  have hsumInt : Integrable (fun ω => ∑ U ∈ D, Bs ω * mixedBridgeVLocal_Th M m U t ω ^ 2) μ :=
    integrable_finsetSum D fun U hU => (hcell U hU).1
  refine ⟨?_, ?_⟩
  · show Integrable (fun ω => Bs ω * descendantsAverage Q (hobs + 5)
      (fun U => mixedBridgeVLocal_Th M m U t ω ^ 2)) μ
    rw [heq]
    exact hsumInt.const_mul _
  · show (∫ ω, Bs ω * descendantsAverage Q (hobs + 5)
      (fun U => mixedBridgeVLocal_Th M m U t ω ^ 2) ∂μ) ≤ _
    rw [heq, integral_const_mul, integral_finsetSum D fun U hU => (hcell U hU).1]
    have hle := Finset.sum_le_card_nsmul D _ (mainBeta * xi) fun U hU => (hcell U hU).2
    have hpos : (0 : ℝ) < D.card := by
      exact_mod_cast Finset.card_pos.2 (descendantsAtDepth_nonempty Q (hobs + 5))
    rw [nsmul_eq_mul] at hle
    calc ((D.card : ℝ)⁻¹) * _ ≤ ((D.card : ℝ)⁻¹) * (D.card * (mainBeta * xi)) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hpos.le)
      _ = mainBeta * xi := by field_simp

end

end ASDExplicitGamma.Main

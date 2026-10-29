module

public import ASDExplicitGamma.Inverse.ParentGapEnergyInputs
public import ASDExplicitGamma.Inverse.ParentGapObserver
public import ASDExplicitGamma.Inverse.BridgeLocalHistory
public import ASDExplicitGamma.Inverse.SourceRows
public import ASDExplicitGamma.Inverse.SourceEnergy
public import ASDExplicitGamma.Inverse.ParentGapSourceEnergy
public import ASDExplicitGamma.Inverse.ParentGapLocalRare
public import ASDExplicitGamma.Inverse.ParentGapGlobalRare
public import ASDExplicitGamma.Inverse.ParentGapRare
public import ASDExplicitGamma.Inverse.BridgeTraceSummability
public import ASDExplicitGamma.Native.OldSignedSourceInverseSplit
public import ASDExplicitGamma.Native.OldSignedNonnegativeSeriesIntegral

/-! The final actual-law OLD parent-gap assembly. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Variational
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Native
open ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal

noncomputable section

/-- The expected actual descendant average agrees with the corresponding
OLD-frame source mean.  The integrability needed to exchange the finite
descendant sum follows from the transported band profile. -/
private theorem mixed_bridge_tbar_mean_eq_source_mean
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ)
    (hprofile : eLpNorm (rawTraceTransportBandObservable M m 0 t j)
      (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal
        (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
          (3 : ℝ) ^ (6 * gammaZero * j))) :
    (∫ ω, mixedBridgeTbar M m t ω j
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      inSourceMeanActual M m j t := by
  let Q := originCube 2 m
  let D := descendantsAtDepth Q j
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let q : ℤ := m - (j : ℤ)
  let U := theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
    (3 : ℝ) ^ (6 * gammaZero * j)
  have hq : q = m - (0 : ℤ) - (j : ℤ) := by dsimp [q]; omega
  have hband : rawTraceTransportBandObservable M m 0 t j =
      rawDepthFourLoadTrace M m q t := by
    funext ω
    rw [rawTraceTransportBandObservable, hq,
      raw_depth_four_load_trace_eq_model_observable]
    rw [raw_trace_transport_band_scalar_eq_inserted_helper M m 0 j (by omega)
      t ht ω]
    rfl
  have hdepthMem : MemLp (rawDepthFourLoadTrace M m q t) 2 μ := by
    have hcast : (ENNReal.ofReal 2) = (2 : ℝ≥0∞) := by norm_num
    rw [hband, hcast] at hprofile
    rw [memLp_iff]
    exact lt_of_le_of_lt hprofile ENNReal.ofReal_lt_top
  have hdepthInt : Integrable (rawDepthFourLoadTrace M m q t) μ :=
    hdepthMem.integrable (by norm_num)
  have hcellInt (V : TriadicCube 2) (hV : V ∈ D) :
      Integrable (rawCubeFourLoadTrace M m V t) μ := by
    have hscale : V.scale = q := by
      have hs := scale_eq_sub_of_mem_descendantsAtDepth hV
      simp [Q, q, originCube] at hs ⊢
      omega
    have hdepthV : Integrable (rawDepthFourLoadTrace M m V.scale t) μ := by
      rw [hscale]
      exact hdepthInt
    have htrans : rawCubeFourLoadTrace M m V t =
        rawDepthFourLoadTrace M m V.scale t ∘
          Cutoff.translateCutoffSample (triadicCubeShift V) := by
      funext ω
      exact raw_cube_four_load_trace_eq_translated_origin_helper M m V t ω
    rw [htrans]
    exact (MeasurePreserving.mk (Cutoff.measurable_translateCutoffSample
      (triadicCubeShift V))
      (Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift V))).integrable_comp_of_integrable hdepthV
  have hcellMean (V : TriadicCube 2) (hV : V ∈ D) :
      (∫ ω, rawCubeFourLoadTrace M m V t ω ∂μ) =
        inSourceMeanActual M m j t := by
    have hscale : V.scale = q := by
      have hs := scale_eq_sub_of_mem_descendantsAtDepth hV
      simp [Q, q, originCube] at hs ⊢
      omega
    have hdepthV : Integrable (rawDepthFourLoadTrace M m V.scale t) μ := by
      rw [hscale]
      exact hdepthInt
    have hmp : MeasurePreserving
        (Cutoff.translateCutoffSample (triadicCubeShift V)) μ μ :=
      ⟨Cutoff.measurable_translateCutoffSample _,
        Cutoff.map_translateCutoffSample_cutoffSampleLaw M _⟩
    have htrans : rawCubeFourLoadTrace M m V t =
        rawDepthFourLoadTrace M m V.scale t ∘
          Cutoff.translateCutoffSample (triadicCubeShift V) := by
      funext ω
      exact raw_cube_four_load_trace_eq_translated_origin_helper M m V t ω
    have hmeas : AEStronglyMeasurable (rawDepthFourLoadTrace M m V.scale t)
        (Measure.map (Cutoff.translateCutoffSample (triadicCubeShift V)) μ) := by
      rw [Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift V)]
      exact hdepthV.aestronglyMeasurable
    have hi := integral_map (μ := μ)
      (Cutoff.measurable_translateCutoffSample (triadicCubeShift V)).aemeasurable
      hmeas
    rw [Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift V)] at hi
    calc
      (∫ ω, rawCubeFourLoadTrace M m V t ω ∂μ) =
          ∫ ω, rawDepthFourLoadTrace M m V.scale t
            (Cutoff.translateCutoffSample (triadicCubeShift V) ω) ∂μ := by
        rw [htrans]
        simp only [Function.comp_apply]
      _ = ∫ ω, rawDepthFourLoadTrace M m V.scale t ω ∂μ := hi.symm
      _ = inSourceMeanActual M m j t := by
        rw [hscale, inSourceMeanActual, modelTraceHeatAverage]
        rfl
  have hm (f : TriadicCube 2 → ℝ) :
      Cold.squareCellMean Q j (fun C => f C.val) = descendantsAverage Q j f := by
    unfold Cold.squareCellMean descendantsAverage
    congr 1
    exact Finset.sum_attach D f
  have hmeanEq : (fun ω => mixedBridgeTbar M m t ω j) =
      fun ω => (D.card : ℝ)⁻¹ *
        ∑ V ∈ D, rawCubeFourLoadTrace M m V t ω := by
    funext ω
    change Cold.squareCellMean Q j (fun C => rawCubeFourLoadTrace M m C.val t ω) = _
    calc
      _ = descendantsAverage Q j (fun V => rawCubeFourLoadTrace M m V t ω) :=
        hm (fun V => rawCubeFourLoadTrace M m V t ω)
      _ = _ := by rfl
  rw [hmeanEq]
  have hsumInt : Integrable
      (fun ω => ∑ V ∈ D, rawCubeFourLoadTrace M m V t ω) μ := by
    exact integrable_finsetSum _ (fun V hV => hcellInt V hV)
  have hsumMean :
      (∫ ω, (∑ V ∈ D, rawCubeFourLoadTrace M m V t ω) ∂μ) =
        (D.card : ℝ) * inSourceMeanActual M m j t := by
    rw [integral_finsetSum _ (fun V hV => hcellInt V hV)]
    calc
      _ = ∑ V ∈ D, inSourceMeanActual M m j t := by
        apply Finset.sum_congr rfl
        intro V hV
        exact hcellMean V hV
      _ = (D.card : ℝ) * inSourceMeanActual M m j t := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (D.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)).ne'
  calc
    (∫ ω, (D.card : ℝ)⁻¹ *
        (∑ V ∈ D, rawCubeFourLoadTrace M m V t ω) ∂μ) =
        (D.card : ℝ)⁻¹ *
          ∫ ω, (∑ V ∈ D, rawCubeFourLoadTrace M m V t ω) ∂μ := by
      rw [integral_const_mul]
    _ = (D.card : ℝ)⁻¹ * ((D.card : ℝ) *
        inSourceMeanActual M m j t) := by rw [hsumMean]
    _ = inSourceMeanActual M m j t := by field_simp [hcard]

/-- The local inverse bank pays the actual parent depth maximum by the OLD
baseline and its correlated depth remainder. -/
private theorem mixed_bridge_parent_depth_inverse_split
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) :
    Measurable (oldSignedSourceDepthRemainder M m t (originCube 2 m) j) ∧
    (∀ ω, 0 ≤ oldSignedSourceDepthRemainder M m t (originCube 2 m) j ω) ∧
    eLpNorm (oldSignedSourceDepthRemainder M m t (originCube 2 m) j) 128
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (inverseBankDepthReserve .localInverse M j) ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      lemmaVInverseDepthMax (originCube 2 m)
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mixedBridgeResponseCoefficient m t ω)) j ≤
        mixedBridgeOldInverseBaseline M j +
          oldSignedSourceDepthRemainder M m t (originCube 2 m) j ω) := by
  let Q := originCube 2 m
  let R := oldSignedSourceDepthRemainder M m t Q j
  have ht' : 0 ≤ t ∧ t ≤ 1 := ⟨ht.1, ht.2⟩
  have hpastM : ∀ k < m, nativeInductionState M h k := by
    intro k hk
    exact hpast k (hk.trans hm)
  have hU : Q ∈ descendantsAtDepth Q 0 := by
    simp [Q, Homogenization.descendantsAtDepth_zero]
  have hbank := old_signed_source_depth_block_bank M h hM hγ m t ht'
    hpastM 0 (by norm_num) Q (by simp [Q, originCube]) j
  have hsplit := old_signed_source_inverse_split M h hM hγ m t ht' hpastM
    0 (by norm_num) Q hU j
  have hmeas : Measurable R := by
    simpa [R, oldSignedSourceDepthRemainder] using hbank.remainder_measurable
  have hnonneg : ∀ ω, 0 ≤ R ω := by
    simpa [R, oldSignedSourceDepthRemainder] using hbank.remainder_nonneg
  have hLp : eLpNorm R 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (inverseBankDepthReserve .localInverse M j) := by
    simpa [R, oldSignedSourceDepthRemainder] using hbank.remainder_L128
  have hframe (ω : Cutoff.CutoffSample 2) :
      lemmaVInverseDepthMax Q (oldSignedPartialFrameField M m 1 t ω) j =
        lemmaVInverseDepthMax Q
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mixedBridgeResponseCoefficient m t ω)) j := by
    have hold := old_signed_partial_inverse_depth M m 1 t ht' ω j
    simp only [Nat.cast_one, add_sub_cancel_right] at hold
    rw [hold, mixed_bridge_frame_inverse_depth_eq_sigma_actual M m t ω ht j]
  have hsplit' : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      lemmaVInverseDepthMax Q
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mixedBridgeResponseCoefficient m t ω)) j ≤
        mixedBridgeOldInverseBaseline M j + R ω := by
    filter_upwards [hsplit] with ω hω
    rw [hframe ω] at hω
    simpa [R, mixedBridgeOldInverseBaseline, bankDepthFrame,
      inverseBankCap] using hω
  exact ⟨hmeas, hnonneg, hLp, hsplit'⟩

private theorem nonnegative_series_integral_ae
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (f : I → Ω → ℝ) (C : I → ℝ)
    (hf : ∀ j, Integrable (f j) μ) (hn : ∀ j ω, 0 ≤ f j ω)
    (hs : ∀ᵐ ω ∂μ, Summable (fun j => f j ω)) (hC : Summable C)
    (hb : ∀ j, (∫ ω, f j ω ∂μ) ≤ C j) :
    Integrable (fun ω => ∑' j, f j ω) μ ∧
      (∫ ω, ∑' j, f j ω ∂μ) ≤ ∑' j, C j := by
  classical
  have hI : Summable (fun j => ∫ ω, f j ω ∂μ) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg (hn j)) hb hC
  have hm : AEStronglyMeasurable (fun ω => ∑' j, f j ω) μ := by
    apply aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun s : Finset I => s.aestronglyMeasurable_fun_sum (fun j _ => (hf j).1))
    filter_upwards [hs] with ω hω
    exact hω.hasSum
  have he : (∫⁻ ω, ENNReal.ofReal (∑' j, f j ω) ∂μ) =
      ENNReal.ofReal (∑' j, ∫ ω, f j ω ∂μ) := by
    calc
      _ = ∫⁻ ω, ∑' j, ENNReal.ofReal (f j ω) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hs] with ω hω
        exact ENNReal.ofReal_tsum_of_nonneg (fun j => hn j ω) hω
      _ = ∑' j, ∫⁻ ω, ENNReal.ofReal (f j ω) ∂μ := by
        rw [lintegral_tsum (fun j => (hf j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
      _ = ∑' j, ENNReal.ofReal (∫ ω, f j ω ∂μ) := by
        apply tsum_congr
        intro j
        exact (ofReal_integral_eq_lintegral_ofReal (hf j)
          (Filter.Eventually.of_forall (hn j))).symm
      _ = ENNReal.ofReal (∑' j, ∫ ω, f j ω ∂μ) := by
        symm
        exact ENNReal.ofReal_tsum_of_nonneg
          (fun j => integral_nonneg (hn j)) hI
  have hi : Integrable (fun ω => ∑' j, f j ω) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm
      (Filter.Eventually.of_forall (fun ω => tsum_nonneg (fun j => hn j ω)))).mp
      (by rw [he]; exact ENNReal.ofReal_ne_top)
  have hnorm : Summable (fun j => ∫ ω, ‖f j ω‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _ _)] using hI
  refine ⟨hi, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm hf hnorm]
  exact hI.tsum_le_tsum hb hC

private theorem parent_source_history_weight_le
    (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) (j : ℕ) :
    inSourceOldEnergyHistoryWeight M j ≤
      (3683 / 2500 : ℝ) * Scalar.inverseHistoryDiscount ^ j := by
  let α := Scalar.inverseHistoryDiscount
  let q := α * (3 : ℝ) ^ (2 * M.gamma)
  have hα := Scalar.inverse_history_discount_range
  have hqeq : q = (3 : ℝ) ^ (-(1 / 4 : ℝ) + 2 * M.gamma) := by
    dsimp [q, α, Scalar.inverseHistoryDiscount]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have hq0 : 0 ≤ q := by rw [hqeq]; positivity
  have hexp : -(1 / 4 : ℝ) + 2 * M.gamma < 0 := by
    dsimp [gammaZero] at hγ ⊢
    norm_num at hγ ⊢
    linarith
  have hq1 : q < 1 := by
    rw [hqeq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
  have hpow : (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) =
      ((3 : ℝ) ^ (2 * M.gamma)) ^ j := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (2 * M.gamma)) j,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hweight : inSourceOldEnergyHistoryWeight M j =
      (1 - α ^ 2) * ((3683 / 2500 : ℝ) * α ^ j) * q ^ j := by
    unfold inSourceOldEnergyHistoryWeight
    rw [show 2 * j = j + j by omega, pow_add, hpow]
    dsimp [q, α]
    ring
  have hfactor : 0 ≤ 1 - α ^ 2 ∧ 1 - α ^ 2 ≤ 1 := by
    constructor
    · nlinarith [hα.1, hα.2]
    · nlinarith [sq_nonneg α]
  have hqpow : 0 ≤ q ^ j ∧ q ^ j ≤ 1 :=
    ⟨pow_nonneg hq0 j, pow_le_one₀ hq0 hq1.le⟩
  rw [hweight]
  calc
    (1 - α ^ 2) * ((3683 / 2500 : ℝ) * α ^ j) * q ^ j ≤
        1 * ((3683 / 2500 : ℝ) * α ^ j) * 1 := by
      have hB : 0 ≤ (3683 / 2500 : ℝ) * α ^ j :=
        mul_nonneg (by norm_num) (pow_nonneg hα.1.le j)
      calc
        (1 - α ^ 2) * ((3683 / 2500 : ℝ) * α ^ j) * q ^ j ≤
            (1 * ((3683 / 2500 : ℝ) * α ^ j)) * q ^ j :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hfactor.2 hB) hqpow.1
        _ ≤ (1 * ((3683 / 2500 : ℝ) * α ^ j)) * 1 :=
          mul_le_mul_of_nonneg_left hqpow.2 (by positivity)
    _ = (3683 / 2500 : ℝ) * α ^ j := by ring

private theorem parent_source_history_weight_nonneg
    (M : ABKModel 2) (j : ℕ) :
    0 ≤ inSourceOldEnergyHistoryWeight M j := by
  have hα := Scalar.inverse_history_discount_range
  have hfactor : 0 ≤ 1 - Scalar.inverseHistoryDiscount ^ 2 := by
    nlinarith [hα.1, hα.2]
  unfold inSourceOldEnergyHistoryWeight
  exact mul_nonneg (mul_nonneg (mul_nonneg hfactor
    (pow_nonneg hα.1.le _)) (by norm_num))
    (Real.rpow_nonneg (by norm_num) _)

/-- The completed source adapter controls the integral of the actual OLD
weighted child-trace history, including genuine a.e. series convergence. -/
private theorem mixed_bridge_source_trace_series_integral
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    Integrable (fun ω => ∑' j : ℕ,
      inSourceOldEnergyHistoryWeight M j * mixedBridgeTbar M m t ω j) μ ∧
    (∫ ω, ∑' j : ℕ,
      inSourceOldEnergyHistoryWeight M j * mixedBridgeTbar M m t ω j ∂μ) ≤
      mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m ∧
    (∀ᵐ ω ∂μ, Summable (fun j : ℕ =>
      inSourceOldEnergyHistoryWeight M j * mixedBridgeTbar M m t ω j)) := by
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let W : ℕ → ℝ := inSourceOldEnergyHistoryWeight M
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω => mixedBridgeTbar M m t ω j
  have hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)) := by
    intro j
    exact hpast (m - (j : ℤ)) (by omega)
  have hsource := parent_gap_source_trace_history_bound M h hM hγ N hpast m hm t ht
  have hraw := raw_parent_gap_source_inputs M h hM hγ m 0 (by omega) t ht
    ({originCube 2 m} : Finset (TriadicCube 2)) ⟨originCube 2 m, Finset.mem_singleton_self _⟩
    (by
      intro j
      simpa using hstate j)
  have hprofile := (raw_trace_transport_profile_and_reserves_source
    M h hM hγ m 0 (by omega) t ht (by intro j; simpa using hstate j)).1
  have hsumT := mixed_bridge_raw_trace_weighted_summable_ae
    M h hM hγ m t ht hstate
  have hwle (j : ℕ) : W j ≤ (3683 / 2500 : ℝ) * Scalar.inverseHistoryDiscount ^ j :=
    parent_source_history_weight_le M hγ j
  have hT0 (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ T j ω := by
    exact raw_weak_trace_sequence_nonneg M m (originCube 2 m) t ⟨ht.1, ht.2⟩ ω j
  have hs : ∀ᵐ ω ∂μ, Summable (fun j : ℕ => W j * T j ω) := by
    filter_upwards [hsumT] with ω hω
    have hmajor : Summable (fun j : ℕ =>
        (3683 / 2500 : ℝ) * Scalar.inverseHistoryDiscount ^ j * T j ω) := by
      simpa [T, mixedBridgeTbar, mul_assoc] using
        hω.mul_left (3683 / 2500 : ℝ)
    apply Summable.of_nonneg_of_le
    · intro j
      exact mul_nonneg (parent_source_history_weight_nonneg M j) (hT0 j ω)
    · intro j
      exact mul_le_mul_of_nonneg_right (hwle j) (hT0 j ω)
    · exact hmajor
  have hmem (j : ℕ) : MemLp (T j) 2 μ := by
    have hp' := hprofile j
    simp only [Nat.cast_zero, sub_zero] at hp'
    have hp : eLpNorm (T j) 2 μ ≤
        ENNReal.ofReal
          (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
            (3 : ℝ) ^ (6 * gammaZero * j)) := by
      simpa [T, mixedBridgeTbar, rawWeakTraceSequence, μ] using hp'
    rw [memLp_iff]
    exact lt_of_le_of_lt hp ENNReal.ofReal_lt_top
  have hf (j : ℕ) : Integrable (fun ω => W j * T j ω) μ :=
    (hmem j).integrable (by norm_num) |>.const_mul (W j)
  have hmean (j : ℕ) : (∫ ω, T j ω ∂μ) = inSourceMeanActual M m j t := by
    have hband := (hraw.2.1.1 j)
    simpa [T, mixedBridgeTbar] using
      mixed_bridge_tbar_mean_eq_source_mean M m t ht j hband
  have hn (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ W j * T j ω :=
    mul_nonneg (parent_source_history_weight_nonneg M j) (hT0 j ω)
  have hb (j : ℕ) :
      (∫ ω, W j * T j ω ∂μ) ≤ W j * inSourceMeanActual M m j t := by
    rw [integral_const_mul, hmean]
  have hseries := nonnegative_series_integral_ae μ
    (fun j ω => W j * T j ω)
    (fun j => W j * inSourceMeanActual M m j t) hf hn hs hsource.1 hb
  refine ⟨?_, ?_, hs⟩
  · simpa [T, W, mixedBridgeTbar] using hseries.1
  · calc
      (∫ ω, ∑' j : ℕ, W j * T j ω ∂μ) ≤
          ∑' j : ℕ, W j * inSourceMeanActual M m j t := hseries.2
      _ ≤ mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m := hsource.2

/-- The OLD baseline series retains the exact parent trace subtraction. Its
integral is bounded by the source-history cap minus the original coefficient
times the actual reference mean. -/
private theorem mixed_bridge_parent_baseline_gap_integral
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    Integrable (fun ω => ∑' j : ℕ,
      inSourceOldEnergyHistoryWeight M j *
        (mixedBridgeTbar M m t ω j - mixedBridgeAnchorTrace M m t ω)) μ ∧
    (∫ ω, ∑' j : ℕ,
      inSourceOldEnergyHistoryWeight M j *
        (mixedBridgeTbar M m t ω j - mixedBridgeAnchorTrace M m t ω) ∂μ) ≤
      mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m -
        (3683 / 2500 : ℝ) * mixedBridgeAnchorMean M m t ∧
    (∀ᵐ ω ∂μ, Summable (fun j : ℕ =>
      inSourceOldEnergyHistoryWeight M j *
        (mixedBridgeTbar M m t ω j - mixedBridgeAnchorTrace M m t ω))) := by
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let Q := originCube 2 m
  let W : ℕ → ℝ := inSourceOldEnergyHistoryWeight M
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω => mixedBridgeTbar M m t ω j
  let A : Cutoff.CutoffSample 2 → ℝ := mixedBridgeAnchorTrace M m t
  let C : ℕ → ℝ := fun j => W j *
    (inSourceMeanActual M m j t - mixedBridgeAnchorMean M m t)
  have hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)) := by
    intro j
    exact hpast (m - (j : ℤ)) (by omega)
  have hscalar := parent_gap_source_trace_history_bound
    M h hM hγ N hpast m hm t ht
  have hraw := raw_parent_gap_source_inputs M h hM hγ m 0 (by omega) t ht
    ({Q} : Finset (TriadicCube 2)) ⟨Q, Finset.mem_singleton_self _⟩
    (by intro j; simpa [Q] using hstate j)
  have hα := Scalar.inverse_history_discount_range
  have hWnonneg (j : ℕ) : 0 ≤ W j :=
    parent_source_history_weight_nonneg M j
  have hWle (j : ℕ) : W j ≤ (3683 / 2500 : ℝ) * α ^ j :=
    parent_source_history_weight_le M hγ j
  have hgeom : Summable (fun j : ℕ => α ^ j) :=
    summable_geometric_of_lt_one hα.1.le hα.2
  have hWsum : Summable W := by
    apply Summable.of_nonneg_of_le hWnonneg hWle
    exact hgeom.mul_left (3683 / 2500 : ℝ)
  have hTprofile (j : ℕ) : eLpNorm (T j) 2 μ ≤
      ENNReal.ofReal (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
        (3 : ℝ) ^ (6 * gammaZero * j)) := by
    have hp := hraw.1.1 j
    have hcast : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
    simpa [T, W, Q, mixedBridgeTbar, μ, hcast] using hp
  have hTmem (j : ℕ) : MemLp (T j) 2 μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt (hTprofile j) ENNReal.ofReal_lt_top
  have hTint (j : ℕ) : Integrable (T j) μ :=
    (hTmem j).integrable (by norm_num)
  have hAeq (ω : Cutoff.CutoffSample 2) : A ω = T 0 ω := by
    have hmean (f : TriadicCube 2 → ℝ) :
        Cold.squareCellMean Q 0 (fun C => f C.val) = descendantsAverage Q 0 f := by
      unfold Cold.squareCellMean descendantsAverage
      congr 1
    have hm := hmean (fun U => rawCubeFourLoadTrace M m U t ω)
    change rawCubeFourLoadTrace M m Q t ω =
      Cold.squareCellMean Q 0 (fun C => rawCubeFourLoadTrace M m C.val t ω)
    rw [hm]
    simp [descendantsAverage]
  have hAint : Integrable A μ := by
    rw [show A = T 0 by funext ω; exact hAeq ω]
    exact hTint 0
  have hA0 (ω : Cutoff.CutoffSample 2) : 0 ≤ A ω := by
    exact raw_cube_four_load_trace_nonneg M m Q t ⟨ht.1, ht.2⟩ ω
  have hF : 0 ≤ mixedBridgeAnchorMean M m t := by
    unfold mixedBridgeAnchorMean
    exact integral_nonneg hA0
  have hmean (j : ℕ) : (∫ ω, T j ω ∂μ) = inSourceMeanActual M m j t := by
    have hband := hraw.2.1.1 j
    simpa [T, μ] using mixed_bridge_tbar_mean_eq_source_mean M m t ht j hband
  have hgap (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ T j ω - A ω := by
    change 0 ≤ mixedBridgeTbar M m t ω j - mixedBridgeAnchorTrace M m t ω
    let k := mixedBridgeResponseCoefficient m t ω
    let σ : ℝ := Annealed.sigmaBar M m
    have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
    have hparent := old_signed_parent_trace_le_child Q j M.nu σ M.nu_pos hσ k
    have hframe : mixedBridgeFrameAnchorTrace M m t ω ≤
        mixedBridgeFrameTbar M m t ω j := by
      simpa [mixedBridgeFrameAnchorTrace, mixedBridgeFrameTbar,
        Q, k, σ] using hparent
    rw [mixed_bridge_tbar_eq_frame M m t ω ht j,
      mixed_bridge_anchor_trace_eq_frame M m t ω ht]
    exact sub_nonneg.mpr hframe
  have hbaseSummable : ∀ᵐ ω ∂μ, Summable (fun j : ℕ => W j * T j ω) := by
    have hsum := mixed_bridge_raw_trace_weighted_summable_ae
      M h hM hγ m t ht hstate
    have hfactor (j : ℕ) : 0 ≤ (3683 / 2500 : ℝ) * α ^ j :=
      mul_nonneg (by norm_num) (pow_nonneg hα.1.le _)
    filter_upwards [hsum] with ω hω
    have hmajor : Summable (fun j : ℕ => (3683 / 2500 : ℝ) * α ^ j * T j ω) := by
      simpa [T, mixedBridgeTbar, mul_assoc] using hω.mul_left (3683 / 2500 : ℝ)
    apply Summable.of_nonneg_of_le
    · intro j
      exact mul_nonneg (hWnonneg j) (raw_weak_trace_sequence_nonneg M m Q t
        ⟨ht.1, ht.2⟩ ω j)
    · intro j
      exact mul_le_mul_of_nonneg_right (hWle j)
        (raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j)
    · exact hmajor
  have hf (j : ℕ) : Integrable (fun ω => W j * (T j ω - A ω)) μ := by
    exact (hTint j).sub hAint |>.const_mul (W j)
  have hn (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      0 ≤ W j * (T j ω - A ω) := mul_nonneg (hWnonneg j) (hgap j ω)
  have hs : ∀ᵐ ω ∂μ, Summable (fun j : ℕ => W j * (T j ω - A ω)) := by
    filter_upwards [hbaseSummable] with ω hω
    apply Summable.of_nonneg_of_le
    · intro j
      exact hn j ω
    · intro j
      have hA : 0 ≤ A ω := hA0 ω
      exact mul_le_mul_of_nonneg_left (sub_le_self _ hA) (hWnonneg j)
    · exact hω
  have hCsum : Summable C := by
    have hdiff := hscalar.1.sub (hWsum.mul_right (mixedBridgeAnchorMean M m t))
    apply hdiff.congr
    intro j
    dsimp [C, W]
    ring
  have hterm (j : ℕ) :
      (∫ ω, W j * (T j ω - A ω) ∂μ) = C j := by
    calc
      _ = W j * ((∫ ω, T j ω ∂μ) - ∫ ω, A ω ∂μ) := by
        rw [integral_const_mul, integral_sub (hTint j) hAint]
      _ = C j := by
        rw [hmean j]
        rfl
  have hCnonneg (j : ℕ) : 0 ≤ C j := by
    rw [← hterm j]
    exact integral_nonneg (hn j)
  have hseries := nonnegative_series_integral_ae μ
    (fun j ω => W j * (T j ω - A ω)) C hf hn hs hCsum
    (fun j => (hterm j).le)
  have hαsq0 : 0 ≤ α ^ 2 := sq_nonneg α
  have hαsq1 : α ^ 2 < 1 := by nlinarith [hα.1, hα.2]
  have hgeomSq : Summable (fun j : ℕ => α ^ (2 * j)) := by
    have h := summable_geometric_of_lt_one hαsq0 hαsq1
    apply h.congr
    intro j
    rw [pow_mul]
  have hgeomNorm : (∑' j : ℕ, (1 - α ^ 2) * α ^ (2 * j)) = 1 := by
    calc
      _ = (1 - α ^ 2) * (∑' j : ℕ, (α ^ 2) ^ j) := by
        rw [tsum_mul_left]
        congr 1
        apply tsum_congr
        intro j
        rw [pow_mul]
      _ = 1 := by
        rw [tsum_geometric_of_lt_one hαsq0 hαsq1]
        have hne : 1 - α ^ 2 ≠ 0 := ne_of_gt (by nlinarith [hα.2])
        field_simp
  have hbaseWeight (j : ℕ) :
      (3683 / 2500 : ℝ) * ((1 - α ^ 2) * α ^ (2 * j)) ≤ W j := by
    have hpow : 1 ≤ (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity [M.shellPrefix.gamma_pos])
    have hscale : 0 ≤ 1 - α ^ 2 := by nlinarith [hα.1, hα.2]
    have hcoef : 0 ≤ ((1 - α ^ 2) * α ^ (2 * j) * (3683 / 2500 : ℝ)) :=
      mul_nonneg (mul_nonneg hscale (pow_nonneg hα.1.le _)) (by norm_num)
    calc
      (3683 / 2500 : ℝ) * ((1 - α ^ 2) * α ^ (2 * j)) =
          ((1 - α ^ 2) * α ^ (2 * j) * (3683 / 2500 : ℝ)) * 1 := by ring
      _ ≤ ((1 - α ^ 2) * α ^ (2 * j) * (3683 / 2500 : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow hcoef
      _ = W j := by
        simp only [W, inSourceOldEnergyHistoryWeight]
        ring
  have hWlower : (3683 / 2500 : ℝ) ≤ ∑' j : ℕ, W j := by
    have hgeomBase : Summable (fun j : ℕ =>
        (3683 / 2500 : ℝ) * ((1 - α ^ 2) * α ^ (2 * j))) := by
      have hh := hgeomSq.mul_left ((3683 / 2500 : ℝ) * (1 - α ^ 2))
      apply hh.congr
      intro j
      ring
    calc
      (3683 / 2500 : ℝ) =
          ∑' j : ℕ, (3683 / 2500 : ℝ) * ((1 - α ^ 2) * α ^ (2 * j)) := by
        calc
          _ = (3683 / 2500 : ℝ) *
              (∑' j : ℕ, (1 - α ^ 2) * α ^ (2 * j)) := by rw [hgeomNorm]; ring
          _ = _ := (tsum_mul_left).symm
      _ ≤ ∑' j : ℕ, W j :=
        hgeomBase.tsum_le_tsum hbaseWeight hWsum
  have hsumC : (∑' j : ℕ, C j) =
      (∑' j : ℕ, W j * inSourceMeanActual M m j t) -
        mixedBridgeAnchorMean M m t * (∑' j : ℕ, W j) := by
    calc
      _ = ∑' j : ℕ,
          (W j * inSourceMeanActual M m j t -
            W j * mixedBridgeAnchorMean M m t) := by
        apply tsum_congr
        intro j
        dsimp [C]
        ring
      _ = (∑' j : ℕ, W j * inSourceMeanActual M m j t) -
            ∑' j : ℕ, W j * mixedBridgeAnchorMean M m t :=
        hscalar.1.tsum_sub (hWsum.mul_right (mixedBridgeAnchorMean M m t))
      _ = _ := by rw [tsum_mul_right]; ring
  have hsumBound : (∑' j : ℕ, C j) ≤
      mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m -
        (3683 / 2500 : ℝ) * mixedBridgeAnchorMean M m t := by
    rw [hsumC]
    have hmul : (3683 / 2500 : ℝ) * mixedBridgeAnchorMean M m t ≤
        (∑' j : ℕ, W j) * mixedBridgeAnchorMean M m t :=
      mul_le_mul_of_nonneg_right hWlower hF
    calc
      _ ≤ (mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m) -
          mixedBridgeAnchorMean M m t * (∑' j : ℕ, W j) :=
        sub_le_sub_right hscalar.2 _
      _ ≤ _ := by nlinarith [hmul]
  refine ⟨hseries.1, ?_, hs⟩
  exact hseries.2.trans hsumBound

private theorem rareExpansionTail_mono
    (β R X Y : ℝ) (k : ℕ)
    (hβ : 0 ≤ β) (hR : 0 ≤ R) (hXY : X ≤ Y) :
    rareExpansionTail β R X k ≤ rareExpansionTail β R Y k := by
  unfold rareExpansionTail
  apply Finset.sum_le_sum
  intro i hi
  have hcoeff : 0 ≤ (Nat.choose k i : ℝ) * β ^ (k - i) * R ^ i := by
    positivity
  calc
    (Nat.choose k i : ℝ) * β ^ (k - i) * R ^ i * X =
        ((Nat.choose k i : ℝ) * β ^ (k - i) * R ^ i) * X := by ring
    _ ≤ ((Nat.choose k i : ℝ) * β ^ (k - i) * R ^ i) * Y :=
      mul_le_mul_of_nonneg_left hXY hcoeff
    _ = (Nat.choose k i : ℝ) * β ^ (k - i) * R ^ i * Y := by ring

private theorem mixed_bridge_parent_trace_gap_nonneg
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ mixedBridgeTbar M m t ω j - mixedBridgeAnchorTrace M m t ω := by
  let Q := originCube 2 m
  let k := mixedBridgeResponseCoefficient m t ω
  let σ : ℝ := Annealed.sigmaBar M m
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hparent := old_signed_parent_trace_le_child Q j M.nu σ M.nu_pos hσ k
  have hframe : mixedBridgeFrameAnchorTrace M m t ω ≤
      mixedBridgeFrameTbar M m t ω j := by
    simpa [mixedBridgeFrameAnchorTrace, mixedBridgeFrameTbar, Q, k, σ] using hparent
  rw [mixed_bridge_tbar_eq_frame M m t ω ht j,
    mixed_bridge_anchor_trace_eq_frame M m t ω ht]
  exact sub_nonneg.mpr hframe

/-- Summing the exact per-depth primal projection gap keeps the parent trace
subtraction intact in the complete weak energy. -/
private theorem mixed_bridge_parent_primal_gap_proxy
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ mixedBridgeV2 M m t ω ∧
    mixedBridgeV2 M m t ω ≤
      rawWeakTraceProxy
        (lemmaVInverseDepthMax (originCube 2 m)
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mixedBridgeResponseCoefficient m t ω)))
        (fun j => mixedBridgeTbar M m t ω j -
          mixedBridgeAnchorTrace M m t ω) ∧
    Summable (fun j : ℕ =>
      ((1 - Scalar.inverseHistoryDiscount ^ 2) *
        Scalar.inverseHistoryDiscount ^ (2 * j)) *
        lemmaVInverseDepthMax (originCube 2 m)
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mixedBridgeResponseCoefficient m t ω)) j *
        (mixedBridgeTbar M m t ω j - mixedBridgeAnchorTrace M m t ω)) := by
  let Q := originCube 2 m
  let k := mixedBridgeResponseCoefficient m t ω
  let σ : ℝ := Annealed.sigmaBar M m
  let a := responseFramePlanarCoefficientField M.nu σ k
  let F : BlockCoord 2 → Vec 2 → Vec 2 := fun c x =>
    (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k (blockBasis c) x).1 -
      (blockBasis c).1
  have hEll : IsEllipticFieldOn M.nu
      (((2 : ℝ) * 2 *
        (Model.partialInsertedEntryBound M (m + 40) m ω)^2 + M.nu^2) / M.nu)
      (openCubeSet Q) (Model.partialInsertedCoefficient M m t ω).toFun := by
    have hEll' := partialInserted_parent_cube_elliptic M m t ω ht
    simpa [Q] using hEll'
  have hF (c : BlockCoord 2) (i : Fin 2) :
      MemLp (fun x => F c x i) 2 (normalizedCubeMeasure Q) := by
    have hm := (memVectorL2_fst_of_memBlockL2
      (Lp.memLp (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
        (Annealed.sigmaBar_characterization M m).1 k (blockBasis c)))).sub
        (memVectorL2_const (blockBasis c).1)
    exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hm i)
  have hseries := old_signed_finite_weak_projection_series Q F hF
  have hdepth (j : ℕ) :
      (∑ c : BlockCoord 2, ∑ i : Fin 2,
        energy Q (cubeProjection Q j (fun x => F c x i))) ≤
      lemmaVInverseDepthMax Q a j *
        (mixedBridgeTbar M m t ω j - mixedBridgeAnchorTrace M m t ω) := by
    have hproj := mixed_bridge_primal_projection_raw_gap_at_depth
      M m t ω ht j
    simpa [mixedBridgeVDepthSq, oldSignedPrimalProjectionEnergy,
      F, Q, a, k, σ, mixedBridgeResponseCoefficient,
      mixedBridgeFrameTbar, mixedBridgeFrameAnchorTrace] using hproj
  have hgap (j : ℕ) :
      0 ≤ mixedBridgeTbar M m t ω j - mixedBridgeAnchorTrace M m t ω := by
    have hparent := old_signed_parent_trace_le_child Q j M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k
    have hframe : mixedBridgeFrameAnchorTrace M m t ω ≤
        mixedBridgeFrameTbar M m t ω j := by
      simpa [mixedBridgeFrameAnchorTrace, mixedBridgeFrameTbar,
        Q, k, σ, a] using hparent
    rw [mixed_bridge_tbar_eq_frame M m t ω ht j,
      mixed_bridge_anchor_trace_eq_frame M m t ω ht]
    exact sub_nonneg.mpr hframe
  have hproxy := old_signed_weak_trace_proxy_summable Q a
    (responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k)
  have hgapSeries : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount^(2*j) *
      lemmaVInverseDepthMax Q a j *
        (mixedBridgeTbar M m t ω j - mixedBridgeAnchorTrace M m t ω)) := by
    apply Summable.of_nonneg_of_le
    · intro j
      exact mul_nonneg (mul_nonneg (pow_nonneg Scalar.inverse_history_discount_range.1.le _) 
        (lemmaVInverseDepthMax_nonneg Q a j)) (hgap j)
    · intro j
      have hTframe := mixed_bridge_tbar_eq_frame M m t ω ht j
      have hsub : mixedBridgeTbar M m t ω j - mixedBridgeAnchorTrace M m t ω ≤
          mixedBridgeFrameTbar M m t ω j := by
        have hanchor : 0 ≤ mixedBridgeAnchorTrace M m t ω := by
          exact raw_cube_four_load_trace_nonneg M m Q t ht ω
        rw [hTframe]
        linarith
      have hcoef : 0 ≤ Scalar.inverseHistoryDiscount^(2*j) *
          lemmaVInverseDepthMax Q a j :=
        mul_nonneg (pow_nonneg Scalar.inverse_history_discount_range.1.le (2*j))
          (lemmaVInverseDepthMax_nonneg Q a j)
      have hmul := mul_le_mul_of_nonneg_left hsub hcoef
      simpa only [mul_assoc] using hmul
    · simpa [a, Q, σ, k, mixedBridgeResponseCoefficient,
        mixedBridgeFrameTbar, mul_assoc] using hproxy
  have hcompare := hseries.1.tsum_le_tsum
    (fun j => by
      have hj := hdepth j
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hj
        (pow_nonneg Scalar.inverse_history_discount_range.1.le (2*j)))
    hgapSeries
  have hcompare' :
      (∑' j : ℕ, Scalar.inverseHistoryDiscount^(2*j) *
        (∑ c : BlockCoord 2, ∑ i : Fin 2,
          energy Q (cubeProjection Q j (fun x => F c x i)))) ≤
      ∑' j : ℕ, Scalar.inverseHistoryDiscount^(2*j) *
        (lemmaVInverseDepthMax Q a j *
          (mixedBridgeTbar M m t ω j - mixedBridgeAnchorTrace M m t ω)) := by
    simpa only [mul_assoc] using hcompare
  have hscale : 0 ≤ 1 - Scalar.inverseHistoryDiscount^2 := by
    have hα := Scalar.inverse_history_discount_range
    nlinarith [hα.1, hα.2]
  have hVeq : mixedBridgeV2 M m t ω =
      (1 - Scalar.inverseHistoryDiscount^2) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount^(2*j) *
          (∑ c : BlockCoord 2, ∑ i : Fin 2,
            energy Q (cubeProjection Q j (fun x => F c x i))) := by
    rw [mixedBridgeV2, old_signed_primal_error_size_sq]
    change (∑ c : BlockCoord 2, vectorWeakHaarEnergy Q (F c)) = _
    exact hseries.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hVeq]
    apply mul_nonneg hscale
    exact tsum_nonneg (fun j => mul_nonneg
      (pow_nonneg Scalar.inverse_history_discount_range.1.le _)
      (Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun i _ => energy_nonneg Q _))
  · rw [hVeq]
    calc
      _ ≤ (1 - Scalar.inverseHistoryDiscount^2) *
          ∑' j : ℕ, Scalar.inverseHistoryDiscount^(2*j) *
            (lemmaVInverseDepthMax Q a j *
              (mixedBridgeTbar M m t ω j - mixedBridgeAnchorTrace M m t ω)) :=
        mul_le_mul_of_nonneg_left hcompare' hscale
      _ = rawWeakTraceProxy (lemmaVInverseDepthMax Q a)
          (fun j => mixedBridgeTbar M m t ω j -
            mixedBridgeAnchorTrace M m t ω) := by
        rw [rawWeakTraceProxy]
        congr 1
        apply tsum_congr
        intro j
        ring
  · have hscaled := hgapSeries.mul_left
      (1 - Scalar.inverseHistoryDiscount ^ 2)
    apply hscaled.congr
    intro j
    ring

/-- The complete OLD parent-gap transport: the exact reference subtraction is
retained in the primal row, while the paired primal/reciprocal row uses the
unsubtracted trace. Both rows are proved for the actual cutoff law. -/
theorem in_parent_gap
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∀ ω : Cutoff.CutoffSample 2, 0 ≤ mixedBridgeV2 M m t ω) ∧
    (∀ k : ℕ, k ≤ 3 →
      Integrable (fun ω => mixedBridgeBstar M m t ω ^ k *
        mixedBridgeV2 M m t ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, mixedBridgeBstar M m t ω ^ k *
        mixedBridgeV2 M m t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (14103 / 10000 : ℝ) ^ k *
          (mixedBridgeXi M h m t -
            (3683 / 2500 : ℝ) * mixedBridgeAnchorMean M m t)) ∧
    (∀ k : ℕ, k ≤ 3 →
      Integrable (fun ω => mixedBridgeBstar M m t ω ^ k *
        (mixedBridgeV2 M m t ω + mixedBridge M m t ω))
          (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, mixedBridgeBstar M m t ω ^ k *
        (mixedBridgeV2 M m t ω + mixedBridge M m t ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        2 * (14103 / 10000 : ℝ) ^ k * mixedBridgeXi M h m t) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let β : ℝ := 14103 / 10000
  let Q := originCube 2 m
  let B : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
  let b : ℕ → ℝ := mixedBridgeOldInverseBaseline M
  let w : ℕ → ℝ := fun j => (1 - α ^ 2) * α ^ (2 * j)
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω => mixedBridgeTbar M m t ω j
  let A : Cutoff.CutoffSample 2 → ℝ := mixedBridgeAnchorTrace M m t
  let gap : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω => T j ω - A ω
  let D : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    lemmaVInverseDepthMax Q
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ)
        (mixedBridgeResponseCoefficient m t ω)) j
  let εj : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    oldSignedSourceDepthRemainder M m t Q j ω
  let R : Cutoff.CutoffSample 2 → ℝ := inverseBankPopulationRemainder .globalInverse
    (mixedBridgeObserverSourceRoots m) M m (m + 40)
    (bankPartialInsertionWeights m 1 t)
  let baseGap : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ∑' j : ℕ, w j * b j * gap j ω
  let baseTrace : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ∑' j : ℕ, w j * b j * T j ω

  have hβ0 : 0 ≤ β := by norm_num [β]
  have hβ1 : 1 ≤ β := by norm_num [β]
  have hα := Scalar.inverse_history_discount_range
  have hw0 (j : ℕ) : 0 ≤ w j := by
    dsimp [w]
    exact mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hα.1.le hα.2.le))
      (pow_nonneg hα.1.le _)
  have hb0 (j : ℕ) : 0 ≤ b j := by
    dsimp [b, mixedBridgeOldInverseBaseline]
    positivity
  have hθ : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hpow0 (k : ℕ) : 0 ≤ β ^ k := pow_nonneg hβ0 k
  have hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)) := by
    intro j
    exact hpast (m - (j : ℤ)) (by omega)

  have hsource := mixed_bridge_source_trace_series_integral
    M h hM hγ N hpast m hm t ht
  have hbaseline := mixed_bridge_parent_baseline_gap_integral
    M h hM hγ N hpast m hm t ht
  have hWeq (j : ℕ) : inSourceOldEnergyHistoryWeight M j = w j * b j := by
    dsimp [w, b, α, inSourceOldEnergyHistoryWeight,
      mixedBridgeOldInverseBaseline]
    ring
  have hbaseGapEq : baseGap = fun ω => ∑' j : ℕ,
      inSourceOldEnergyHistoryWeight M j * gap j ω := by
    funext ω
    apply tsum_congr
    intro j
    rw [hWeq j]
  have hbaseTraceEq : baseTrace = fun ω => ∑' j : ℕ,
      inSourceOldEnergyHistoryWeight M j * T j ω := by
    funext ω
    apply tsum_congr
    intro j
    rw [hWeq j]
  have hbaseGapInt : Integrable baseGap μ := by
    rw [hbaseGapEq]
    exact hbaseline.1
  have hbaseTraceInt : Integrable baseTrace μ := by
    rw [hbaseTraceEq]
    exact hsource.1
  have hbaseGapBound : (∫ ω, baseGap ω ∂μ) ≤
      mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m -
        (3683 / 2500 : ℝ) * mixedBridgeAnchorMean M m t := by
    rw [hbaseGapEq]
    exact hbaseline.2.1
  have hbaseTraceBound : (∫ ω, baseTrace ω ∂μ) ≤
      mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m := by
    rw [hbaseTraceEq]
    exact hsource.2.1
  have hbaseGapSummable : ∀ᵐ ω ∂μ,
      Summable (fun j : ℕ => w j * b j * gap j ω) := by
    filter_upwards [hbaseline.2.2] with ω hω
    apply hω.congr
    intro j
    rw [hWeq j]
  have hbaseTraceSummable : ∀ᵐ ω ∂μ,
      Summable (fun j : ℕ => w j * b j * T j ω) := by
    filter_upwards [hsource.2.2] with ω hω
    apply hω.congr
    intro j
    rw [hWeq j]

  have hbank := mixed_bridge_global_bank_inputs M h hM hγ m t ht hstate
  have hglobal := mixed_bridge_global_bank_split M h hM hγ m t ht hstate
  have hB0 (ω : Cutoff.CutoffSample 2) : 0 ≤ B ω :=
    mixed_bridge_bstar_nonneg M m t ω
  have hR0 (ω : Cutoff.CutoffSample 2) : 0 ≤ R ω := by
    simpa [R] using hbank.remainder_nonneg ω
  have hRmeas : Measurable R := by
    simpa [R] using hbank.remainder_measurable
  have hBsplit : ∀ᵐ ω ∂μ, B ω ≤ β + R ω := by
    filter_upwards [hglobal.1] with ω hω
    have hω' : ENNReal.ofReal (B ω) ≤ ENNReal.ofReal β + ENNReal.ofReal (R ω) := by
      simpa [B, β, inverseBankCap] using hω
    rw [← ENNReal.ofReal_add hβ0 (hR0 ω)] at hω'
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hβ0 (hR0 ω))).mp hω'

  have hdepth : ∀ j : ℕ,
      Measurable (εj j) ∧ (∀ ω, 0 ≤ εj j ω) ∧
      eLpNorm (εj j) 128 μ ≤ ENNReal.ofReal (inverseBankDepthReserve .localInverse M j) ∧
      (∀ᵐ ω ∂μ, D j ω ≤ b j + εj j ω) := by
    intro j
    simpa only [εj, D, b, Q, μ] using
      mixed_bridge_parent_depth_inverse_split M h hM hγ N hpast m hm t ht j
  have hdepthAll : ∀ᵐ ω ∂μ, ∀ j : ℕ, D j ω ≤ b j + εj j ω := by
    apply ae_all_iff.mpr
    intro j
    exact (hdepth j).2.2.2

  have hgap0 (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ gap j ω := by
    exact mixed_bridge_parent_trace_gap_nonneg M m t ht j ω
  have hgapLeT (j : ℕ) (ω : Cutoff.CutoffSample 2) : gap j ω ≤ T j ω := by
    have hA : 0 ≤ A ω := by
      exact raw_cube_four_load_trace_nonneg M m Q t ⟨ht.1, ht.2⟩ ω
    dsimp [gap]
    linarith

  constructor
  · intro ω
    exact (mixed_bridge_parent_primal_gap_proxy M m t ω ht).1
  constructor
  · intro k hk
    let globalRare : Cutoff.CutoffSample 2 → ℝ := fun ω =>
      ∑' j : ℕ, w j * rareExpansionTail β (R ω) (b j * T j ω) k
    let localRare : Cutoff.CutoffSample 2 → ℝ := fun ω =>
      ∑' j : ℕ, w j * B ω ^ k * εj j ω * T j ω
    let Vint : Cutoff.CutoffSample 2 → ℝ := fun ω => B ω ^ k * mixedBridgeV2 M m t ω
    have hglobalRare := parent_gap_global_population_rare_series
      M h hM hγ N hpast m hm t ht k hk
    have hglobalRareSummableSource :=
      parent_gap_global_population_rare_series_summable
        M h hM hγ N hpast m hm t ht k hk
    have hlocalRare := parent_gap_local_depth_rare_series_summable
      M h hM hγ N hpast m hm t ht k hk
    have hglobalRareInt : Integrable globalRare μ := by
      simpa only [globalRare, w, α, β, R, b, T, μ] using hglobalRare.1
    have hlocalRareInt : Integrable localRare μ := by
      simpa only [localRare, w, α, B, εj, T, μ] using hlocalRare.1
    have hglobalRareSummable : ∀ᵐ ω ∂μ,
        Summable (fun j : ℕ => w j * rareExpansionTail β (R ω) (b j * T j ω) k) := by
      simpa only [w, α, β, R, b, T, μ] using hglobalRareSummableSource.2.2
    have hlocalRareSummable : ∀ᵐ ω ∂μ,
        Summable (fun j : ℕ => w j * B ω ^ k * εj j ω * T j ω) := by
      simpa only [w, α, B, εj, T, μ] using hlocalRare.2.2
    have hglobalRareBound : (∫ ω, globalRare ω ∂μ) ≤
        β ^ k * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
      simpa only [globalRare, w, α, β, R, b, T, μ] using hglobalRare.2
    have hlocalRareBound : (∫ ω, localRare ω ∂μ) ≤
        β ^ k * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
      simpa only [localRare, w, α, B, εj, T, μ] using hlocalRare.2.1

    -- The per-depth bank and rare expansion bound the proxy before expectation.
    have hVle : ∀ᵐ ω ∂μ,
        Vint ω ≤ β ^ k * baseGap ω + globalRare ω + localRare ω := by
      filter_upwards [hBsplit, hdepthAll, hbaseGapSummable,
        hglobalRareSummable, hlocalRareSummable] with ω hBω hDω hbaseω hrareω hlocalω
      have hVpoint := mixed_bridge_parent_primal_gap_proxy M m t ω ht
      have hproxyMult : Vint ω ≤ B ω ^ k *
          rawWeakTraceProxy (D · ω) (gap · ω) := by
        dsimp [Vint, B, D, gap, Q]
        exact mul_le_mul_of_nonneg_left hVpoint.2.1 (pow_nonneg (hB0 ω) k)
      have hterms : ∀ j : ℕ,
          w j * (B ω ^ k * D j ω * gap j ω) ≤
            (w j * (β ^ k * b j * gap j ω) +
              w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
              w j * B ω ^ k * εj j ω * T j ω := by
        intro j
        have hD := hDω j
        have hBpow : 0 ≤ B ω ^ k := pow_nonneg (hB0 ω) k
        have hX0 : 0 ≤ b j * gap j ω := mul_nonneg (hb0 j) (hgap0 j ω)
        have hXle : b j * gap j ω ≤ b j * T j ω :=
          mul_le_mul_of_nonneg_left (hgapLeT j ω) (hb0 j)
        have hexp := rare_factor_pointwise_expansion (B ω) β (R ω)
          (b j * gap j ω) k (hB0 ω) hX0 hBω hk
        have htail := rareExpansionTail_mono β (R ω)
          (b j * gap j ω) (b j * T j ω) k hβ0 (hR0 ω) hXle
        have hlocal : B ω ^ k * εj j ω * gap j ω ≤
            B ω ^ k * εj j ω * T j ω := by
          exact mul_le_mul_of_nonneg_left (hgapLeT j ω)
            (mul_nonneg hBpow ((hdepth j).2.1 ω))
        have hcore : B ω ^ k * D j ω * gap j ω ≤
            β ^ k * b j * gap j ω +
              rareExpansionTail β (R ω) (b j * T j ω) k +
              B ω ^ k * εj j ω * T j ω := by
          calc
            _ ≤ B ω ^ k * (b j + εj j ω) * gap j ω := by
              have hmul := mul_le_mul_of_nonneg_right hD
                (mul_nonneg hBpow (hgap0 j ω))
              nlinarith [hmul]
            _ = B ω ^ k * (b j * gap j ω) +
                B ω ^ k * εj j ω * gap j ω := by ring
            _ ≤ β ^ k * b j * gap j ω +
                rareExpansionTail β (R ω) (b j * gap j ω) k +
                B ω ^ k * εj j ω * gap j ω := by
              nlinarith [hexp]
            _ ≤ _ := by
              nlinarith [htail, hlocal]
        calc
          _ ≤ w j * (β ^ k * b j * gap j ω +
              rareExpansionTail β (R ω) (b j * T j ω) k +
              B ω ^ k * εj j ω * T j ω) :=
            mul_le_mul_of_nonneg_left hcore (hw0 j)
          _ = _ := by ring
      have hsumRhs : Summable (fun j : ℕ =>
          (w j * (β ^ k * b j * gap j ω) +
            w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
            w j * B ω ^ k * εj j ω * T j ω) := by
        have hbase := hbaseω.mul_left (β ^ k)
        have hright := (hbase.add hrareω).add hlocalω
        have heq : (fun j : ℕ =>
            (w j * (β ^ k * b j * gap j ω) +
              w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
              w j * B ω ^ k * εj j ω * T j ω) =
            fun j => ((β ^ k * (w j * b j * gap j ω) +
              w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
              w j * B ω ^ k * εj j ω * T j ω) := by
          funext j
          ring
        rw [heq]
        exact hright
      have hseriesLhs : Summable (fun j : ℕ =>
          w j * (B ω ^ k * D j ω * gap j ω)) := by
        have hscaled := hVpoint.2.2.mul_left (B ω ^ k)
        have heq : (fun j : ℕ => w j * (B ω ^ k * D j ω * gap j ω)) =
            fun j => B ω ^ k * (w j * D j ω * gap j ω) := by
          funext j
          ring
        rw [heq]
        exact hscaled
      have hseriesLe :
          (∑' j : ℕ, w j * (B ω ^ k * D j ω * gap j ω)) ≤
            (∑' j : ℕ,
              ((w j * (β ^ k * b j * gap j ω) +
                w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
                w j * B ω ^ k * εj j ω * T j ω)) :=
        hseriesLhs.tsum_le_tsum hterms hsumRhs
      have hproxyEq : B ω ^ k *
          rawWeakTraceProxy (D · ω) (gap · ω) =
          ∑' j : ℕ, w j * (B ω ^ k * D j ω * gap j ω) := by
        unfold rawWeakTraceProxy
        calc
          _ = (B ω ^ k * (1 - α ^ 2)) *
              (∑' j : ℕ, α ^ (2 * j) * D j ω * gap j ω) := by ring
          _ = ∑' j : ℕ,
              (B ω ^ k * (1 - α ^ 2)) *
                (α ^ (2 * j) * D j ω * gap j ω) := by
            rw [← tsum_mul_left]
          _ = _ := by
            apply tsum_congr
            intro j
            dsimp [w, α]
            ring
      have hsumEq :
          (∑' j : ℕ, w j * (β ^ k * b j * gap j ω)) = β ^ k * baseGap ω := by
        unfold baseGap
        rw [← tsum_mul_left]
        apply tsum_congr
        intro j
        ring
      have hbaseScaled : Summable (fun j : ℕ =>
          w j * (β ^ k * b j * gap j ω)) := by
        have hs := hbaseω.mul_left (β ^ k)
        have heq : (fun j : ℕ => w j * (β ^ k * b j * gap j ω)) =
            fun j => β ^ k * (w j * b j * gap j ω) := by
          funext j
          ring
        rw [heq]
        exact hs
      have hsumSplit :
          (∑' j : ℕ,
            ((w j * (β ^ k * b j * gap j ω) +
              w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
              w j * B ω ^ k * εj j ω * T j ω)) =
            (∑' j : ℕ, w j * (β ^ k * b j * gap j ω)) +
              (∑' j : ℕ, w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
              (∑' j : ℕ, w j * B ω ^ k * εj j ω * T j ω) := by
        rw [((hbaseScaled.add hrareω).tsum_add hlocalω),
          hbaseScaled.tsum_add hrareω]
      dsimp [Vint, globalRare, localRare, baseGap, w, α, β, B, D, εj, T, R, b, gap]
      calc
        _ ≤ B ω ^ k * rawWeakTraceProxy (D · ω) (gap · ω) := hproxyMult
        _ = ∑' j : ℕ, w j * (B ω ^ k * D j ω * gap j ω) := hproxyEq
        _ ≤ _ := hseriesLe
        _ = β ^ k * baseGap ω + globalRare ω + localRare ω := by
          rw [hsumSplit, hsumEq]

    have hVmeas : AEStronglyMeasurable Vint μ := by
      have hBmeas : Measurable B := parent_gap_bstar_measurable M m t
      have hBpow : Measurable (fun ω => B ω ^ k) := hBmeas.pow_const k
      have hV2meas : Measurable (fun ω => mixedBridgeV2 M m t ω) :=
        (parent_gap_vg_measurable M m t).1
      have hVmeas' : Measurable Vint := by
        change Measurable (fun ω => B ω ^ k * mixedBridgeV2 M m t ω)
        exact hBpow.mul hV2meas
      exact hVmeas'.aestronglyMeasurable
    have hdomInt : Integrable (fun ω => β ^ k * baseGap ω +
        globalRare ω + localRare ω) μ := by
      exact (hbaseGapInt.const_mul (β ^ k)).add hglobalRareInt |>.add hlocalRareInt
    have hVint : Integrable Vint μ := by
      apply hdomInt.mono' hVmeas
      filter_upwards [hVle] with ω hω
      have hleft : 0 ≤ Vint ω := mul_nonneg (pow_nonneg (hB0 ω) k)
        (mixed_bridge_parent_primal_gap_proxy M m t ω ht).1
      have hright : 0 ≤ β ^ k * baseGap ω + globalRare ω + localRare ω := by
        apply add_nonneg
        · apply add_nonneg
          · exact mul_nonneg (hpow0 k) (tsum_nonneg fun j =>
              mul_nonneg (mul_nonneg (hw0 j) (hb0 j)) (hgap0 j ω))
          · exact tsum_nonneg fun j => mul_nonneg (hw0 j) (by
              unfold rareExpansionTail
              apply Finset.sum_nonneg
              intro i hi
              exact mul_nonneg (mul_nonneg (mul_nonneg
                (Nat.cast_nonneg _) (pow_nonneg hβ0 _))
                (pow_nonneg (hR0 ω) _))
                (mul_nonneg (hb0 j)
                  (raw_weak_trace_sequence_nonneg M m Q t
                    ⟨ht.1, ht.2⟩ ω j)))
        · exact tsum_nonneg fun j =>
            mul_nonneg
              (mul_nonneg
                (mul_nonneg (hw0 j) (pow_nonneg (hB0 ω) k))
                ((hdepth j).2.1 ω))
              (raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j)
      simpa [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] using hω
    have hVbound : (∫ ω, Vint ω ∂μ) ≤
        β ^ k * (mixedBridgeXi M h m t -
          (3683 / 2500 : ℝ) * mixedBridgeAnchorMean M m t) := by
      have hmajorInt : Integrable (fun ω => β ^ k * baseGap ω +
          globalRare ω + localRare ω) μ := hdomInt
      calc
        _ ≤ ∫ ω, β ^ k * baseGap ω + globalRare ω + localRare ω ∂μ :=
          integral_mono_ae hVint hmajorInt hVle
        _ = (∫ ω, β ^ k * baseGap ω + globalRare ω ∂μ) +
            (∫ ω, localRare ω ∂μ) := by
          exact integral_add
            ((hbaseGapInt.const_mul (β ^ k)).add hglobalRareInt) hlocalRareInt
        _ = β ^ k * (∫ ω, baseGap ω ∂μ) +
            (∫ ω, globalRare ω ∂μ) + (∫ ω, localRare ω ∂μ) := by
          rw [integral_add (hbaseGapInt.const_mul (β ^ k)) hglobalRareInt,
            integral_const_mul]
        _ ≤ β ^ k * (mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m -
            (3683 / 2500 : ℝ) * mixedBridgeAnchorMean M m t) +
              β ^ k * (1 / (13 * 10 ^ 12 : ℝ)) * theta M +
              β ^ k * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
          have hbaseScaled := mul_le_mul_of_nonneg_left hbaseGapBound (hpow0 k)
          exact add_le_add (add_le_add hbaseScaled hglobalRareBound)
            hlocalRareBound
        _ ≤ β ^ k * (mixedBridgeXi M h m t -
            (3683 / 2500 : ℝ) * mixedBridgeAnchorMean M m t) := by
          unfold mixedBridgeXi mixedBridgeReserve
          have hreserve : (1 / (13 * 10 ^ 12 : ℝ)) * theta M +
              (1 / (13 * 10 ^ 12 : ℝ)) * theta M ≤
                (1 / 10 ^ 12 : ℝ) * theta M := by
            nlinarith [hθ]
          have hreserve' := mul_le_mul_of_nonneg_left hreserve (hpow0 k)
          nlinarith [hreserve']
    refine ⟨hVint, ?_⟩
    simpa [Vint, B, β, mixedBridgeBstarVIntegrand] using hVbound

  · intro k hk
    let globalRare : Cutoff.CutoffSample 2 → ℝ := fun ω =>
      ∑' j : ℕ, w j * rareExpansionTail β (R ω) (b j * T j ω) k
    let localRare : Cutoff.CutoffSample 2 → ℝ := fun ω =>
      ∑' j : ℕ, w j * B ω ^ k * εj j ω * T j ω
    let baseAndRare : Cutoff.CutoffSample 2 → ℝ := fun ω =>
      β ^ k * baseTrace ω + globalRare ω + localRare ω
    let PairInt : Cutoff.CutoffSample 2 → ℝ := fun ω =>
      B ω ^ k * (mixedBridgeV2 M m t ω + mixedBridge M m t ω)
    have hglobalRare := parent_gap_global_population_rare_series
      M h hM hγ N hpast m hm t ht k hk
    have hglobalRareSummableSource :=
      parent_gap_global_population_rare_series_summable
        M h hM hγ N hpast m hm t ht k hk
    have hlocalRare := parent_gap_local_depth_rare_series_summable
      M h hM hγ N hpast m hm t ht k hk
    have hglobalRareInt : Integrable globalRare μ := by
      simpa only [globalRare, w, α, β, R, b, T, μ] using hglobalRare.1
    have hlocalRareInt : Integrable localRare μ := by
      simpa only [localRare, w, α, B, εj, T, μ] using hlocalRare.1
    have hglobalRareSummable : ∀ᵐ ω ∂μ,
        Summable (fun j : ℕ => w j * rareExpansionTail β (R ω) (b j * T j ω) k) := by
      simpa only [w, α, β, R, b, T, μ] using hglobalRareSummableSource.2.2
    have hlocalRareSummable : ∀ᵐ ω ∂μ,
        Summable (fun j : ℕ => w j * B ω ^ k * εj j ω * T j ω) := by
      simpa only [w, α, B, εj, T, μ] using hlocalRare.2.2
    have hglobalRareBound : (∫ ω, globalRare ω ∂μ) ≤
        β ^ k * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
      simpa only [globalRare, w, α, β, R, b, T, μ] using hglobalRare.2
    have hlocalRareBound : (∫ ω, localRare ω ∂μ) ≤
        β ^ k * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
      simpa only [localRare, w, α, B, εj, T, μ] using hlocalRare.2.1
    have hPairLe : ∀ᵐ ω ∂μ, PairInt ω ≤ 2 * baseAndRare ω := by
      filter_upwards [hBsplit, hdepthAll, hbaseTraceSummable,
        hglobalRareSummable, hlocalRareSummable] with ω hBω hDω hbaseω hrareω hlocalω
      have hPairPoint := mixed_bridge_parent_pair_raw_trace_proxy M m t ω ht
      have hproxyMult : PairInt ω ≤ 2 * (B ω ^ k *
          rawWeakTraceProxy (D · ω) (T · ω)) := by
        dsimp [PairInt, B, D, Q]
        have hpow := pow_nonneg (hB0 ω) k
        calc
          _ ≤ B ω ^ k * (2 * rawWeakTraceProxy (D · ω) (T · ω)) := by
            exact mul_le_mul_of_nonneg_left hPairPoint hpow
          _ = _ := by ring
      have hterms : ∀ j : ℕ,
          w j * (B ω ^ k * D j ω * T j ω) ≤
            (w j * (β ^ k * b j * T j ω) +
              w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
              w j * B ω ^ k * εj j ω * T j ω := by
        intro j
        have hBpow : 0 ≤ B ω ^ k := pow_nonneg (hB0 ω) k
        have hX0 : 0 ≤ b j * T j ω := mul_nonneg (hb0 j)
          (raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j)
        have hexp := rare_factor_pointwise_expansion (B ω) β (R ω)
          (b j * T j ω) k (hB0 ω) hX0 hBω hk
        have hD := hDω j
        have hcore : B ω ^ k * D j ω * T j ω ≤
            β ^ k * b j * T j ω +
              rareExpansionTail β (R ω) (b j * T j ω) k +
              B ω ^ k * εj j ω * T j ω := by
          calc
            _ ≤ B ω ^ k * (b j + εj j ω) * T j ω := by
              have hmul := mul_le_mul_of_nonneg_right hD
                (mul_nonneg hBpow (raw_weak_trace_sequence_nonneg M m Q t
                  ⟨ht.1, ht.2⟩ ω j))
              calc
                _ = D j ω * (B ω ^ k * T j ω) := by ring
                _ ≤ (b j + εj j ω) * (B ω ^ k * T j ω) := hmul
                _ = B ω ^ k * (b j + εj j ω) * T j ω := by ring
            _ = B ω ^ k * (b j * T j ω) +
                B ω ^ k * εj j ω * T j ω := by ring
            _ ≤ β ^ k * b j * T j ω +
                rareExpansionTail β (R ω) (b j * T j ω) k +
                B ω ^ k * εj j ω * T j ω := by
              simpa [mul_assoc, add_assoc] using
                (add_le_add hexp (le_rfl :
                  B ω ^ k * εj j ω * T j ω ≤ B ω ^ k * εj j ω * T j ω))
        calc
          _ ≤ w j * (β ^ k * b j * T j ω +
              rareExpansionTail β (R ω) (b j * T j ω) k +
              B ω ^ k * εj j ω * T j ω) :=
            mul_le_mul_of_nonneg_left hcore (hw0 j)
          _ = _ := by ring
      have hsumRhs : Summable (fun j : ℕ =>
          (w j * (β ^ k * b j * T j ω) +
            w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
            w j * B ω ^ k * εj j ω * T j ω) := by
        have hbase := hbaseω.mul_left (β ^ k)
        have hright := (hbase.add hrareω).add hlocalω
        have heq : (fun j : ℕ =>
            (w j * (β ^ k * b j * T j ω) +
              w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
              w j * B ω ^ k * εj j ω * T j ω) =
            fun j => ((β ^ k * (w j * b j * T j ω) +
              w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
              w j * B ω ^ k * εj j ω * T j ω) := by
          funext j
          ring
        rw [heq]
        exact hright
      have hseriesD : Summable (fun j : ℕ => w j * D j ω * T j ω) := by
        let κ := mixedBridgeResponseCoefficient m t ω
        let σ : ℝ := Annealed.sigmaBar M m
        let a := responseFramePlanarCoefficientField M.nu σ κ
        have hproxy := old_signed_weak_trace_proxy_summable Q a
          (responseFramePlanarCoefficientField_isElliptic
            (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
            (Annealed.sigmaBar_characterization M m).1 κ)
        have hbaseFrame : Summable (fun j : ℕ =>
            α ^ (2 * j) * D j ω * mixedBridgeFrameTbar M m t ω j) := by
          simpa [D, Q, a, σ, κ, α, mixedBridgeResponseCoefficient,
            mixedBridgeFrameTbar,
            mul_assoc] using hproxy
        have hbase : Summable (fun j : ℕ =>
            α ^ (2 * j) * D j ω * T j ω) := by
          have heq : (fun j : ℕ => α ^ (2 * j) * D j ω * T j ω) =
              fun j => α ^ (2 * j) * D j ω *
                mixedBridgeFrameTbar M m t ω j := by
            funext j
            dsimp [T]
            rw [mixed_bridge_tbar_eq_frame M m t ω ht j]
          rw [heq]
          exact hbaseFrame
        have hscaled := hbase.mul_left (1 - α ^ 2)
        have heq : (fun j : ℕ => w j * D j ω * T j ω) =
            fun j => (1 - α ^ 2) * (α ^ (2 * j) * D j ω * T j ω) := by
          funext j
          dsimp [w]
          ring
        rw [heq]
        exact hscaled
      have hseriesLhs : Summable (fun j : ℕ =>
          w j * (B ω ^ k * D j ω * T j ω)) := by
        have hscaled := hseriesD.mul_left (B ω ^ k)
        have heq : (fun j : ℕ => w j * (B ω ^ k * D j ω * T j ω)) =
            fun j => B ω ^ k * (w j * D j ω * T j ω) := by
          funext j
          ring
        rw [heq]
        exact hscaled
      have hseriesLe :
          (∑' j : ℕ, w j * (B ω ^ k * D j ω * T j ω)) ≤
            (∑' j : ℕ,
              ((w j * (β ^ k * b j * T j ω) +
                w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
                w j * B ω ^ k * εj j ω * T j ω)) :=
        hseriesLhs.tsum_le_tsum hterms hsumRhs
      have hproxyEq : B ω ^ k *
          rawWeakTraceProxy (D · ω) (T · ω) =
          ∑' j : ℕ, w j * (B ω ^ k * D j ω * T j ω) := by
        unfold rawWeakTraceProxy
        calc
          _ = (B ω ^ k * (1 - α ^ 2)) *
              (∑' j : ℕ, α ^ (2 * j) * D j ω * T j ω) := by ring
          _ = ∑' j : ℕ,
              (B ω ^ k * (1 - α ^ 2)) *
                (α ^ (2 * j) * D j ω * T j ω) := by rw [← tsum_mul_left]
          _ = _ := by
            apply tsum_congr
            intro j
            dsimp [w, α]
            ring
      have hsumEq :
          (∑' j : ℕ, w j * (β ^ k * b j * T j ω)) = β ^ k * baseTrace ω := by
        unfold baseTrace
        rw [← tsum_mul_left]
        apply tsum_congr
        intro j
        ring
      have hbaseScaled : Summable (fun j : ℕ =>
          w j * (β ^ k * b j * T j ω)) := by
        have hs := hbaseω.mul_left (β ^ k)
        have heq : (fun j : ℕ => w j * (β ^ k * b j * T j ω)) =
            fun j => β ^ k * (w j * b j * T j ω) := by
          funext j
          ring
        rw [heq]
        exact hs
      have hsumSplit :
          (∑' j : ℕ,
            ((w j * (β ^ k * b j * T j ω) +
              w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
              w j * B ω ^ k * εj j ω * T j ω)) =
            (∑' j : ℕ, w j * (β ^ k * b j * T j ω)) +
              (∑' j : ℕ, w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
              (∑' j : ℕ, w j * B ω ^ k * εj j ω * T j ω) := by
        rw [((hbaseScaled.add hrareω).tsum_add hlocalω),
          hbaseScaled.tsum_add hrareω]
      have htwo : PairInt ω ≤ 2 *
          (∑' j : ℕ, w j * (B ω ^ k * D j ω * T j ω)) := by
        rw [hproxyEq] at hproxyMult
        exact hproxyMult
      calc
        PairInt ω ≤ 2 *
            (∑' j : ℕ, w j * (B ω ^ k * D j ω * T j ω)) := htwo
        _ ≤ 2 *
            (∑' j : ℕ,
              ((w j * (β ^ k * b j * T j ω) +
                w j * rareExpansionTail β (R ω) (b j * T j ω) k) +
                w j * B ω ^ k * εj j ω * T j ω)) := by
          exact mul_le_mul_of_nonneg_left hseriesLe (by norm_num)
        _ = 2 * baseAndRare ω := by
          rw [hsumSplit, hsumEq]
    have hPairmeas : AEStronglyMeasurable PairInt μ := by
      have hBmeas : Measurable B := parent_gap_bstar_measurable M m t
      have hBpow : Measurable (fun ω => B ω ^ k) := hBmeas.pow_const k
      have hVGmeas := parent_gap_vg_measurable M m t
      have hPairmeas' : Measurable PairInt := by
        change Measurable (fun ω => B ω ^ k *
          (mixedBridgeV2 M m t ω + mixedBridge M m t ω))
        exact hBpow.mul (hVGmeas.1.add hVGmeas.2)
      exact hPairmeas'.aestronglyMeasurable
    have hbaseAndRareInt : Integrable baseAndRare μ := by
      exact (hbaseTraceInt.const_mul (β ^ k)).add hglobalRareInt |>.add hlocalRareInt
    have hPairmajorInt : Integrable (fun ω => 2 * baseAndRare ω) μ :=
      hbaseAndRareInt.const_mul 2
    have hPairint : Integrable PairInt μ := by
      apply hPairmajorInt.mono' hPairmeas
      filter_upwards [hPairLe] with ω hω
      have hleft : 0 ≤ PairInt ω := by
        exact mul_nonneg (pow_nonneg (hB0 ω) k)
          (add_nonneg (sq_nonneg _) (sq_nonneg _))
      have hright : 0 ≤ 2 * baseAndRare ω := by
        apply mul_nonneg (by norm_num)
        unfold baseAndRare globalRare localRare
        apply add_nonneg
        · apply add_nonneg
          · exact mul_nonneg (hpow0 k) (tsum_nonneg fun j =>
              mul_nonneg (mul_nonneg (hw0 j) (hb0 j))
                (raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j))
          · exact tsum_nonneg fun j => mul_nonneg (hw0 j) (by
              unfold rareExpansionTail
              apply Finset.sum_nonneg
              intro i hi
              exact mul_nonneg (mul_nonneg (mul_nonneg
                (Nat.cast_nonneg _) (pow_nonneg hβ0 _))
                (pow_nonneg (hR0 ω) _))
                (mul_nonneg (hb0 j)
                  (raw_weak_trace_sequence_nonneg M m Q t
                    ⟨ht.1, ht.2⟩ ω j)))
        · exact tsum_nonneg fun j =>
            mul_nonneg
              (mul_nonneg
                (mul_nonneg (hw0 j) (pow_nonneg (hB0 ω) k))
                ((hdepth j).2.1 ω))
              (raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j)
      simpa [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] using hω
    have hPairbound : (∫ ω, PairInt ω ∂μ) ≤
        2 * β ^ k * mixedBridgeXi M h m t := by
      calc
        _ ≤ ∫ ω, 2 * baseAndRare ω ∂μ := integral_mono_ae hPairint hPairmajorInt hPairLe
        _ = 2 * (∫ ω, baseAndRare ω ∂μ) := by
          rw [integral_const_mul]
        _ = 2 * ((∫ ω, β ^ k * baseTrace ω ∂μ) +
            (∫ ω, globalRare ω ∂μ) + (∫ ω, localRare ω ∂μ) ) := by
          congr 1
          dsimp [baseAndRare]
          calc
            (∫ ω, (β ^ k * baseTrace ω + globalRare ω) + localRare ω ∂μ) =
                (∫ ω, β ^ k * baseTrace ω + globalRare ω ∂μ) +
                  (∫ ω, localRare ω ∂μ) := by
              exact integral_add
                ((hbaseTraceInt.const_mul (β ^ k)).add hglobalRareInt) hlocalRareInt
            _ = _ := by
              rw [integral_add (hbaseTraceInt.const_mul (β ^ k)) hglobalRareInt,
                integral_const_mul]
        _ ≤ 2 * (β ^ k * (mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m) +
            β ^ k * (1 / (13 * 10 ^ 12 : ℝ)) * theta M +
            β ^ k * (1 / (13 * 10 ^ 12 : ℝ)) * theta M) := by
          have hbaseScaled := mul_le_mul_of_nonneg_left hbaseTraceBound (hpow0 k)
          have hbaseIntegral : (∫ ω, β ^ k * baseTrace ω ∂μ) ≤
              β ^ k * (mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m) := by
            rw [integral_const_mul]
            exact hbaseScaled
          have hsum := add_le_add (add_le_add hbaseIntegral hglobalRareBound)
            hlocalRareBound
          exact mul_le_mul_of_nonneg_left hsum (by norm_num)
        _ ≤ 2 * β ^ k * mixedBridgeXi M h m t := by
          unfold mixedBridgeXi mixedBridgeReserve
          have hreserve : (1 / (13 * 10 ^ 12 : ℝ)) * theta M +
              (1 / (13 * 10 ^ 12 : ℝ)) * theta M ≤
                (1 / 10 ^ 12 : ℝ) * theta M := by
            nlinarith [hθ]
          have hreserve' := mul_le_mul_of_nonneg_left hreserve (hpow0 k)
          nlinarith [hreserve']
    refine ⟨hPairint, ?_⟩
    simpa [PairInt, B, β, mixedBridgeBstarPairIntegrand] using hPairbound

end
end ASDExplicitGamma.Inverse

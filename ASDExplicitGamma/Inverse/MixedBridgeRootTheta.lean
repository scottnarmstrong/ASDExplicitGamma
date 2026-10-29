module

public import ASDExplicitGamma.Inverse.ParentGapSourceEnergy
public import ASDExplicitGamma.Inverse.ParentGapLocalRare
public import ASDExplicitGamma.Inverse.ParentGapGlobalRare
public import ASDExplicitGamma.Inverse.BankLocal
public import ASDExplicitGamma.Inverse.BridgeGlobalBank
public import ASDExplicitGamma.Inverse.BridgeTraceSummability
public import ASDExplicitGamma.Inverse.RawRareExpansion
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Main.LoadsAndSlopes

/-! The actual root-scale OLD-Theta row for the mixed bridge. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Filter Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Inverse ASDExplicitGamma.Response
open ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open ASDExplicitGamma.Main
open scoped ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

private theorem nonneg_series_integral_ae
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (f : I → Ω → ℝ) (C : I → ℝ)
    (hf : ∀ j, Integrable (f j) μ)
    (hn : ∀ j ω, 0 ≤ f j ω)
    (hs : ∀ᵐ ω ∂μ, Summable (fun j => f j ω))
    (hC : Summable C)
    (hb : ∀ j, (∫ ω, f j ω ∂μ) ≤ C j) :
    Integrable (fun ω => ∑' j, f j ω) μ ∧
      (∫ ω, ∑' j, f j ω ∂μ) ≤ ∑' j, C j := by
  classical
  have hI : Summable (fun j => ∫ ω, f j ω ∂μ) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg (hn j)) hb hC
  have hm : AEStronglyMeasurable (fun ω => ∑' j, f j ω) μ := by
    apply aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun s : Finset I => s.aestronglyMeasurable_fun_sum
        (fun j _ => (hf j).1))
    filter_upwards [hs] with ω hω
    exact hω.hasSum
  have hsumENN : ∀ᵐ ω ∂μ,
      ENNReal.ofReal (∑' j, f j ω) = ∑' j, ENNReal.ofReal (f j ω) := by
    filter_upwards [hs] with ω hω
    exact ENNReal.ofReal_tsum_of_nonneg (fun j => hn j ω) hω
  have he :
      (∫⁻ ω, ENNReal.ofReal (∑' j, f j ω) ∂μ) =
        ENNReal.ofReal (∑' j, ∫ ω, f j ω ∂μ) := by
    rw [lintegral_congr_ae hsumENN,
      lintegral_tsum
        (fun j => (hf j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (hf _)
      (Filter.Eventually.of_forall (hn _))]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun j => integral_nonneg (hn j)) hI).symm
  have hi : Integrable (fun ω => ∑' j, f j ω) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm
      (Filter.Eventually.of_forall (fun ω => tsum_nonneg (fun j => hn j ω)))).mp
      (by rw [he]; exact ENNReal.ofReal_ne_top)
  have hnorm : Summable (fun j => ∫ ω, ‖f j ω‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _ _)] using hI
  refine ⟨hi, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm hf hnorm]
  exact hI.tsum_le_tsum hb hC

private theorem parent_source_history_weight_le'
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
    constructor <;> nlinarith [hα.1, hα.2, sq_nonneg α]
  have hqpow : 0 ≤ q ^ j ∧ q ^ j ≤ 1 :=
    ⟨pow_nonneg hq0 j, pow_le_one₀ hq0 hq1.le⟩
  rw [hweight]
  calc
    (1 - α ^ 2) * ((3683 / 2500 : ℝ) * α ^ j) * q ^ j ≤
        1 * ((3683 / 2500 : ℝ) * α ^ j) * 1 := by
      have hB : 0 ≤ (3683 / 2500 : ℝ) * α ^ j :=
        mul_nonneg (by norm_num) (pow_nonneg hα.1.le j)
      calc
        _ ≤ (1 * ((3683 / 2500 : ℝ) * α ^ j)) * q ^ j :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hfactor.2 hB) hqpow.1
        _ ≤ (1 * ((3683 / 2500 : ℝ) * α ^ j)) * 1 :=
          mul_le_mul_of_nonneg_left hqpow.2 (by positivity)
    _ = (3683 / 2500 : ℝ) * α ^ j := by ring

private theorem parent_source_history_weight_nonneg'
    (M : ABKModel 2) (j : ℕ) :
    0 ≤ inSourceOldEnergyHistoryWeight M j := by
  have hα := Scalar.inverse_history_discount_range
  have hfactor : 0 ≤ 1 - Scalar.inverseHistoryDiscount ^ 2 := by
    nlinarith [hα.1, hα.2]
  unfold inSourceOldEnergyHistoryWeight
  exact mul_nonneg (mul_nonneg (mul_nonneg hfactor
    (pow_nonneg hα.1.le _)) (by norm_num))
    (Real.rpow_nonneg (by norm_num) _)

private theorem mixed_bridge_tbar_mean_eq_source_mean'
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
    have hcast : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
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
      (fun ω => ∑ V ∈ D, rawCubeFourLoadTrace M m V t ω) μ :=
    integrable_finsetSum _ (fun V hV => hcellInt V hV)
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

private theorem mixed_union_depth_remainder_nonneg
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (j : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    0 ≤ mixedOldLocalDepthRemainder M m t j ω := by
  change 0 ≤ positiveSplitRemainder _ _ _
  exact (positive_split _ _ _).1

private theorem mixed_union_depth_remainder_le_response_max
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (j : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    mixedOldLocalDepthRemainder M m t j ω ≤
      (bankFiniteRootResponseMax
        (bankObserverDepthRootUnion (originCube 2 (m + 40)) 5 j)
        M m (m + 40) (bankPartialInsertionWeights m 1 t) ω).toReal := by
  change positiveSplitRemainder
      (bankFiniteRootResponseMax
        (bankObserverDepthRootUnion (originCube 2 (m + 40)) 5 j)
        M m (m + 40) (bankPartialInsertionWeights m 1 t) ω).toReal
      (inverseBankDepthA .localInverse M j) (inverseBankDepthSlack M j) ≤ _
  have hnonneg := inverse_bank_depth_nonneg .localInverse M j
  have hA : 0 ≤ inverseBankDepthA .localInverse M j := hnonneg.1
  have hδ : 0 ≤ inverseBankDepthSlack M j := hnonneg.2.2.le
  unfold positiveSplitRemainder
  apply max_le_iff.mpr
  constructor
  · exact ENNReal.toReal_nonneg
  · linarith

private theorem mixed_union_depth_response_discount_le_bstar
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    Scalar.inverseHistoryDiscount ^ j *
      (bankFiniteRootResponseMax
        (bankObserverDepthRootUnion (originCube 2 (m + 40)) 5 j)
        M m (m + 40) (bankPartialInsertionWeights m 1 t) ω).toReal ≤
      mixedBridgeBstar M m t ω := by
  classical
  let Q : TriadicCube 2 := originCube 2 (m + 40)
  let S : Finset (TriadicCube 2) := mixedBridgeObserverSourceRoots m
  let D : Finset (TriadicCube 2) := bankObserverDepthRootUnion Q 5 j
  let a : CoeffField 2 := (Model.partialInsertedCoefficient M m t ω).toFun
  let σ : ℝ := Annealed.sigmaBar M m
  have hσ : 0 < σ := by dsimp [σ]; exact (Annealed.sigmaBar_characterization M m).1
  have hσ0 : 0 ≤ σ := hσ.le
  have hcoeff : attenuatedCoefficient M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω = a := by
    dsimp [a]
    calc
      _ = (Model.partialInsertedCoefficient M (m + (1 : ℤ) - 1) t ω).toFun :=
        bank_one_pass_partial_coefficient M m 1 (by norm_num) t ω
      _ = _ := by rw [show m + (1 : ℤ) - 1 = m by omega]
  have hS : mixedBridgeObserverSourceRoots m =
      bankObserverRootUnion (originCube 2 (m + 40)) 5 :=
    mixed_bridge_observer_roots_eq_bank_union m
  have hS_nonempty : S.Nonempty := by
    exact ⟨originCube 2 m, mixed_bridge_parent_cube_mem_observer m⟩
  have hEllS : ∀ A ∈ S, ∃ Lam : ℝ,
      IsEllipticFieldOn M.nu Lam (openCubeSet A) a := by
    intro A hA
    have hA' : A ∈ bankObserverRootUnion (originCube 2 (m + 40)) 5 := by
      exact hS ▸ hA
    change A ∈ (Finset.range 6).biUnion (bankObserverRoots Q) at hA'
    obtain ⟨r0, hr0, hAroots⟩ := Finset.mem_biUnion.mp hA'
    have hAdepth : A ∈ descendantsAtDepth Q (40 + r0) := by
      exact hAroots
    have hEll := Model.partialInsertedCoefficient_isEllipticFieldOn M (m + 40) m ω
      ht (measurableSet_openCubeSet A)
      (openCubeSet_subset_of_mem_descendantsAtDepth hAdepth)
    refine ⟨((2 : ℝ) * (2 : ℝ) *
      (Model.partialInsertedEntryBound M (m + 40) m ω) ^ 2 + M.nu ^ 2) / M.nu, ?_⟩
    simpa only [a] using hEll
  have hEllDiscount := raw_finite_inverse_depth_discount_bound_of_per_root_ellipticity
    S hS_nonempty a M.nu σ hσ0 hEllS j
  have hRaw0 : 0 ≤ rawFiniteInverseDepthMax S a σ j := by
    have hroot : originCube 2 m ∈ S := by
      exact mixed_bridge_parent_cube_mem_observer m
    have hlow := rawFiniteInverseDepthMax_lower_of_mem S hroot a σ j
    have hnonneg := mul_nonneg hσ0 (lemmaVInverseDepthMax_nonneg (originCube 2 m) a j)
    exact hnonneg.trans hlow
  have hmax : bankFiniteRootResponseMax D M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω ≤
      ENNReal.ofReal (rawFiniteInverseDepthMax S a σ j) := by
    unfold bankFiniteRootResponseMax
    apply Finset.sup_le
    intro V hV
    have hVmem : V.1 ∈ D := V.2
    change V.1 ∈ (Finset.range 6).biUnion
      (fun r0 => bankObserverDepthRoots Q r0 j) at hVmem
    obtain ⟨r0, hr0, hVdepth⟩ := Finset.mem_biUnion.mp hVmem
    have hVdepth' : V.1 ∈ descendantsAtDepth Q (40 + r0 + j) := by
      change V.1 ∈ descendantsAtDepth Q (40 + r0 + j) at hVdepth
      exact hVdepth
    obtain ⟨A, hAdepth, hVA⟩ := exists_descendant_ancestor_at_depth
      (40 + r0) j hVdepth'
    have hAroots : A ∈ bankObserverRoots Q r0 := by
      change A ∈ descendantsAtDepth Q (40 + r0)
      exact hAdepth
    have hA : A ∈ S := by
      have hAUnion : A ∈ bankObserverRootUnion Q 5 := by
        change A ∈ (Finset.range 6).biUnion (bankObserverRoots Q)
        exact Finset.mem_biUnion.mpr ⟨r0, hr0, hAroots⟩
      change A ∈ mixedBridgeObserverSourceRoots m
      exact hS.symm ▸ hAUnion
    have hEllA0 := Model.partialInsertedCoefficient_isEllipticFieldOn M (m + 40) m ω
      ht (measurableSet_openCubeSet A)
      (openCubeSet_subset_of_mem_descendantsAtDepth hAdepth)
    have hEllA : IsEllipticFieldOn M.nu
        (((2 : ℝ) * (2 : ℝ) *
          (Model.partialInsertedEntryBound M (m + 40) m ω) ^ 2 + M.nu ^ 2) / M.nu)
        (openCubeSet A) a := by
      simpa only [a] using hEllA0
    have hEllV := hEllA.mono (measurableSet_openCubeSet V.1)
      (openCubeSet_subset_of_mem_descendantsAtDepth hVA)
    have hresponseEq : rootInverseResponse M V.1 m (m + 40)
        (bankPartialInsertionWeights m 1 t) ω =
        σ * Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet V.1) a) := by
      unfold rootInverseResponse Book.Ch02.matrixNorm
      rw [hcoeff, ← Scalar.inverse_history_lowerRight V.1 a hEllV]
    have hdepth : Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet V.1) a) ≤
        lemmaVInverseDepthMax A a j := by
      unfold lemmaVInverseDepthMax
      exact Algsuperdiff.Section3.Provider.ErrorComparison.le_finsetSupReal
        (α := TriadicCube 2) (descendantsAtDepth A j)
        (fun R => Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R) a)) hVA
    have hresponseReal : rootInverseResponse M V.1 m (m + 40)
        (bankPartialInsertionWeights m 1 t) ω ≤ σ * lemmaVInverseDepthMax A a j := by
      rw [hresponseEq]
      exact mul_le_mul_of_nonneg_left hdepth hσ0
    have hrootLower := rawFiniteInverseDepthMax_lower_of_mem S hA a σ j
    have hbound : rootInverseResponse M V.1 m (m + 40)
        (bankPartialInsertionWeights m 1 t) ω ≤ rawFiniteInverseDepthMax S a σ j :=
      hresponseReal.trans (hrootLower)
    exact ENNReal.ofReal_le_ofReal hbound
  have hmaxReal :
      (bankFiniteRootResponseMax D M m (m + 40)
        (bankPartialInsertionWeights m 1 t) ω).toReal ≤
        rawFiniteInverseDepthMax S a σ j := by
    calc
      _ ≤ (ENNReal.ofReal (rawFiniteInverseDepthMax S a σ j)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
      _ = rawFiniteInverseDepthMax S a σ j :=
        ENNReal.toReal_ofReal hRaw0
  have hBstar : rawFiniteInverseHistoryMax S a σ = mixedBridgeBstar M m t ω := by
    dsimp [S, a, σ]
    exact (mixedBridgeBstar_eq_raw_history_max M m t ω).symm
  calc
    _ ≤ Scalar.inverseHistoryDiscount ^ j * rawFiniteInverseDepthMax S a σ j :=
      mul_le_mul_of_nonneg_left hmaxReal
        (pow_nonneg Scalar.inverse_history_discount_range.1.le j)
    _ ≤ rawFiniteInverseHistoryMax S a σ := hEllDiscount
    _ = mixedBridgeBstar M m t ω := hBstar

theorem mixed_old_local_depth_remainder_discount_le_global
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    Scalar.inverseHistoryDiscount ^ j * mixedOldLocalDepthRemainder M m t j ω ≤
      mixedBridgeBstar M m t ω := by
  have hα := Scalar.inverse_history_discount_range
  have hpos := mixed_union_depth_remainder_le_response_max M m t j ω
  calc
    _ ≤ Scalar.inverseHistoryDiscount ^ j *
        (bankFiniteRootResponseMax
          (bankObserverDepthRootUnion (originCube 2 (m + 40)) 5 j)
          M m (m + 40) (bankPartialInsertionWeights m 1 t) ω).toReal :=
      mul_le_mul_of_nonneg_left hpos (pow_nonneg hα.1.le j)
    _ ≤ mixedBridgeBstar M m t ω :=
      mixed_union_depth_response_discount_le_bstar M m t ht j ω

private theorem mixed_profile_weighted_summable (M : ABKModel 2) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
        (3 : ℝ) ^ (6 * gammaZero * j))) := by
  let α := Scalar.inverseHistoryDiscount
  let q : ℝ := α * (3 : ℝ) ^ (6 * gammaZero)
  have hα := Scalar.inverse_history_discount_range
  have hqeq : q = (3 : ℝ) ^ (6 * gammaZero - 1 / 4) := by
    dsimp [q, α, Scalar.inverseHistoryDiscount]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hq0 : 0 ≤ q := by rw [hqeq]; positivity
  have hq1 : q < 1 := by
    rw [hqeq]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3)
    norm_num [gammaZero]
  have hqnorm : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq0]; exact hq1
  have hgeom : Summable (fun j : ℕ => q ^ j) :=
    summable_geometric_of_lt_one hq0 hq1
  have hlin : Summable (fun j : ℕ => (j : ℝ) * q ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hqnorm
  have hquad : Summable (fun j : ℕ => (j : ℝ) ^ 2 * q ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 2 hqnorm
  have hpoly : Summable (fun j : ℕ => (1 + (j : ℝ)) ^ 2 * q ^ j) := by
    have hs := (hquad.add (hlin.mul_left 2)).add hgeom
    apply hs.congr
    intro j
    ring
  have hpow (j : ℕ) :
      (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) =
        ((3 : ℝ) ^ (6 * gammaZero)) ^ j := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (6 * gammaZero)) j,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hterm (j : ℕ) :
      α ^ j * (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
        (3 : ℝ) ^ (6 * gammaZero * j)) =
      (theta M * (invTraceM : ℚ)) * ((1 + (j : ℝ)) ^ 2 * q ^ j) := by
    rw [hpow]
    dsimp [q, α]
    ring
  have hscaled := hpoly.mul_left (theta M * (invTraceM : ℚ))
  exact hscaled.congr (fun j => (hterm j).symm)

private theorem weighted_rare_series_summable_ae''
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (α : ℝ)
    (B : Ω → ℝ) (R T : ℕ → Ω → ℝ) (k : ℕ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hB0 : ∀ ω, 0 ≤ B ω) (hR0 : ∀ j ω, 0 ≤ R j ω)
    (hT0 : ∀ j ω, 0 ≤ T j ω)
    (hRbound : ∀ j ω, α ^ j * R j ω ≤ B ω)
    (htrace : ∀ᵐ ω ∂μ, Summable (fun j => α ^ j * T j ω)) :
    ∀ᵐ ω ∂μ, Summable (fun j =>
      ((1 - α ^ 2) * α ^ (2 * j)) * B ω ^ k * R j ω * T j ω) := by
  filter_upwards [htrace] with ω htrace
  have hlead : Summable (fun j : ℕ =>
      ((1 - α ^ 2) * B ω ^ (k + 1)) * (α ^ j * T j ω)) :=
    htrace.mul_left ((1 - α ^ 2) * B ω ^ (k + 1))
  have hineq (j : ℕ) :
      ((1 - α ^ 2) * α ^ (2 * j)) * B ω ^ k * R j ω * T j ω ≤
        ((1 - α ^ 2) * B ω ^ (k + 1)) * (α ^ j * T j ω) := by
    have hBpower : B ω ^ k * (α ^ j * R j ω) ≤ B ω ^ (k + 1) := by
      calc
        _ ≤ B ω ^ k * B ω :=
          mul_le_mul_of_nonneg_left (hRbound j ω) (pow_nonneg (hB0 ω) k)
        _ = B ω ^ (k + 1) := by rw [pow_succ]
    have hTα : 0 ≤ α ^ j * T j ω :=
      mul_nonneg (pow_nonneg hα0 j) (hT0 j ω)
    calc
      _ = (1 - α ^ 2) * (B ω ^ k * (α ^ j * R j ω)) *
          (α ^ j * T j ω) := by ring
      _ ≤ (1 - α ^ 2) * B ω ^ (k + 1) * (α ^ j * T j ω) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hBpower
            (sub_nonneg.mpr (pow_le_one₀ hα0 hα1))) hTα
      _ = _ := by ring
  have hW0 (j : ℕ) : 0 ≤ (1 - α ^ 2) * α ^ (2 * j) :=
    mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hα0 hα1)) (pow_nonneg hα0 _)
  have hmajor : Summable (fun j : ℕ =>
      ((1 - α ^ 2) * α ^ (2 * j)) * B ω ^ k * (R j ω * T j ω)) := by
    apply Summable.of_nonneg_of_le
      (fun j => mul_nonneg (mul_nonneg (hW0 j) (pow_nonneg (hB0 ω) k))
        (mul_nonneg (hR0 j ω) (hT0 j ω)))
      (fun j => by simpa only [mul_assoc] using hineq j) hlead
  simpa only [mul_assoc] using hmajor

private theorem correlated_B_power_trace_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B T : Ω → ℝ) (β C : ℝ) (k : ℕ) (hk : k ≤ 3)
    (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hB0 : ∀ ω, 0 ≤ B ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (hBmeas : AEStronglyMeasurable B μ) (hTmeas : AEStronglyMeasurable T μ)
    (hB128 : eLpNorm B 128 μ ≤ ENNReal.ofReal β)
    (hT2 : eLpNorm T 2 μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => B ω ^ k * T ω) μ ∧
      (∫ ω, B ω ^ k * T ω ∂μ) ≤ β ^ k * C := by
  have hholder := parent_gap_rare_trace_holder B T β C k (by omega)
    hβ hB0 hT0 hBmeas hTmeas hB128 hT2
  have hnonneg (ω : Ω) : 0 ≤ B ω ^ k * T ω :=
    mul_nonneg (pow_nonneg (hB0 ω) k) (hT0 ω)
  have hreal (ω : Ω) :
      ENNReal.ofReal (B ω ^ k * T ω) =
        ENNReal.ofReal (B ω) ^ k * ENNReal.ofReal (T ω) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (hB0 ω) k), ENNReal.ofReal_pow (hB0 ω)]
  have hbound :
      ∫⁻ ω, ENNReal.ofReal (B ω ^ k * T ω) ∂μ ≤
        ENNReal.ofReal (β ^ k * C) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (B ω) ^ k * ENNReal.ofReal (T ω) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with ω
        exact hreal ω
      _ ≤ ENNReal.ofReal (β ^ k * C) := hholder
  have hmeas : AEStronglyMeasurable (fun ω => B ω ^ k * T ω) μ :=
    (hBmeas.pow k).mul hTmeas
  have hi : Integrable (fun ω => B ω ^ k * T ω) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas
      (Filter.Eventually.of_forall hnonneg)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall hnonneg)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (pow_nonneg hβ k) hC)).mp hbound

private theorem correlated_B_power_R_trace_integrable''
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B R T : Ω → ℝ) (β ε C : ℝ) (k : ℕ) (hk : k ≤ 3)
    (hβ : 0 ≤ β) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hB0 : ∀ ω, 0 ≤ B ω) (hR0 : ∀ ω, 0 ≤ R ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (hBmeas : AEStronglyMeasurable B μ) (hRmeas : AEStronglyMeasurable R μ)
    (hTmeas : AEStronglyMeasurable T μ)
    (hB128 : eLpNorm B 128 μ ≤ ENNReal.ofReal β)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hT2 : eLpNorm T 2 μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => B ω ^ k * R ω * T ω) μ ∧
      (∫ ω, B ω ^ k * R ω * T ω ∂μ) ≤ β ^ k * ε * C := by
  have hholder := parent_gap_global_local_rare_term B R T β ε C k hk
    hB0 hR0 hT0 hBmeas hRmeas hTmeas hB128 hR128 hT2
  have hnonneg (ω : Ω) : 0 ≤ B ω ^ k * R ω * T ω :=
    mul_nonneg (mul_nonneg (pow_nonneg (hB0 ω) k) (hR0 ω)) (hT0 ω)
  have hreal (ω : Ω) :
      ENNReal.ofReal (B ω ^ k * R ω * T ω) =
        ENNReal.ofReal (B ω) ^ k * ENNReal.ofReal (R ω) * ENNReal.ofReal (T ω) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (hB0 ω) k) (hR0 ω)),
      ENNReal.ofReal_mul (pow_nonneg (hB0 ω) k), ENNReal.ofReal_pow (hB0 ω)]
  have hbound :
      ∫⁻ ω, ENNReal.ofReal (B ω ^ k * R ω * T ω) ∂μ ≤
        ENNReal.ofReal (β ^ k * ε * C) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (B ω) ^ k * ENNReal.ofReal (R ω) *
          ENNReal.ofReal (T ω) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with ω
        exact hreal ω
      _ ≤ ENNReal.ofReal C *
          (ENNReal.ofReal β ^ k * ENNReal.ofReal ε) := hholder
      _ = ENNReal.ofReal (β ^ k * ε * C) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hβ k) hε),
          ENNReal.ofReal_mul (pow_nonneg hβ k), ENNReal.ofReal_pow hβ]
        ring
  have hmeas : AEStronglyMeasurable
      (fun ω => B ω ^ k * R ω * T ω) μ := (hBmeas.pow k).mul hRmeas |>.mul hTmeas
  have hi : Integrable (fun ω => B ω ^ k * R ω * T ω) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas
      (Filter.Eventually.of_forall hnonneg)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall hnonneg)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg (pow_nonneg hβ k) hε) hC)).mp hbound

private theorem mixed_global_union_depth_block
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    InverseBankDepthBlockConclusion M .localInverse
      (bankObserverDepthRootUnion (originCube 2 (m + 40)) 5 j)
      m (m + 40) (bankPartialInsertionWeights m 1 t) j := by
  have hpastM : ∀ n < m, nativeInductionState M h n := by
    intro n hn
    exact hpast n (hn.trans hm)
  have hQ : (originCube 2 (m + 40)).scale = m + 40 := rfl
  have hw : ∀ k ∈ Finset.Ioc m (m + 40),
      0 ≤ bankPartialInsertionWeights m 1 t k ∧
        bankPartialInsertionWeights m 1 t k ≤ 1 :=
    fun k _ => bank_partial_insertion_weights_bounds m 1 t ht.2 k
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hγ m hpastM).2
  exact (inverse_bank_observer_union_depths M h hM hγ .localInverse
    (originCube 2 (m + 40)) m (m + 40) hQ (by omega)
    (bankPartialInsertionWeights m 1 t) hw 5 le_rfl hpastM hmean j).2

/-- The root OLD-Theta moment row on the actual cutoff law. The baseline uses
the completed source-history bound, the global positive split uses the
population payment, and the OLD local remainder is the full six-offset
observer-depth union carried by `mixedOldLocalDepthRemainder`. -/
theorem mixed_root_old_theta_row
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    ∀ k : Fin 4,
      Integrable (fun ω => mixedGlobalHistoryMax M m t ω ^ k.val *
        mixedOldTheta M m (originCube 2 m) t ω) μ ∧
      (∫ ω, mixedGlobalHistoryMax M m t ω ^ k.val *
        mixedOldTheta M m (originCube 2 m) t ω ∂μ) ≤
        mainBeta ^ k.val * mixedXi M h m t := by
  classical
  dsimp only
  intro k
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let β : ℝ := 14103 / 10000
  let w : ℕ → ℝ := fun j => (1 - α ^ 2) * α ^ (2 * j)
  let b : ℕ → ℝ := mixedBridgeOldInverseBaseline M
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    rawWeakTraceSequence M m (originCube 2 m) t ω j
  let W : ℕ → ℝ := inSourceOldEnergyHistoryWeight M
  let C : ℕ → ℝ := fun j =>
    theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
      (3 : ℝ) ^ (6 * gammaZero * j)
  let B : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
  let Rglobal : Cutoff.CutoffSample 2 → ℝ := inverseBankPopulationRemainder
    .globalInverse (mixedBridgeObserverSourceRoots m) M m (m + 40)
    (bankPartialInsertionWeights m 1 t)
  let Rlocal : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    mixedOldLocalDepthRemainder M m t j ω
  let sourceTerm : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω => W j * T j ω
  let sourceSeries : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑' j, sourceTerm j ω
  let globalRareTerm : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    w j * rareExpansionTail β (Rglobal ω) (b j * T j ω) k.val
  let globalRare : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑' j, globalRareTerm j ω
  let baseTerm : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    w j * B ω ^ k.val * b j * T j ω
  let baseSeries : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑' j, baseTerm j ω
  let localTerm : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    w j * B ω ^ k.val * Rlocal j ω * T j ω
  let localSeries : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑' j, localTerm j ω

  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hβ0 : 0 ≤ β := by norm_num [β]
  have hβ1 : 1 ≤ β := by norm_num [β]
  have hθ : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hinvTraceQ : 0 ≤ invTraceM := by
    rw [invTrace_coefficient.1]
    positivity
  have hinvTrace : 0 ≤ (invTraceM : ℝ) := by exact_mod_cast hinvTraceQ
  have hw0 (j : ℕ) : 0 ≤ w j := by
    dsimp [w]
    exact mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hα0 hα.2.le))
      (pow_nonneg hα0 _)
  have hT0 (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ T j ω := by
    exact raw_weak_trace_sequence_nonneg M m (originCube 2 m) t
      ⟨ht.1, ht.2⟩ ω j
  have hb0 (j : ℕ) : 0 ≤ b j := by
    dsimp [b, mixedBridgeOldInverseBaseline]
    positivity
  have hC0 (j : ℕ) : 0 ≤ C j := by
    dsimp [C]
    positivity
  have hW0 (j : ℕ) : 0 ≤ W j :=
    parent_source_history_weight_nonneg' M j
  have hWle (j : ℕ) : W j ≤ (3683 / 2500 : ℝ) * α ^ j :=
    parent_source_history_weight_le' M hγ j
  have hWeq (j : ℕ) : W j = w j * b j := by
    dsimp [W, w, b, α, inSourceOldEnergyHistoryWeight,
      mixedBridgeOldInverseBaseline, Scalar.inverseHistoryDiscount]
    ring

  have hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)) := by
    intro j
    apply hpast
    omega
  have hglobal := mixed_bridge_global_bank_split M h hM hγ m t ht hstate
  have hbank := mixed_bridge_global_bank_inputs M h hM hγ m t ht hstate
  have hB0 (ω : Cutoff.CutoffSample 2) : 0 ≤ B ω :=
    mixed_bridge_bstar_nonneg M m t ω
  have hRglobal0 (ω : Cutoff.CutoffSample 2) : 0 ≤ Rglobal ω := by
    simpa [Rglobal] using hbank.remainder_nonneg ω
  have hB128ENN : eLpNorm (fun ω => ENNReal.ofReal (B ω)) 128 μ ≤
      ENNReal.ofReal β := by
    simpa [B, β, inverseBankCap, μ] using hglobal.2.1
  have hB128 : eLpNorm B 128 μ ≤ ENNReal.ofReal β := by
    rw [← eLpNorm_ofReal B (Filter.Eventually.of_forall hB0)]
    exact hB128ENN
  have hBmeas : AEStronglyMeasurable B μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top
      (hB128.trans_lt ENNReal.ofReal_lt_top).ne
  have hBsplit : ∀ᵐ ω ∂μ, B ω ≤ β + Rglobal ω := by
    filter_upwards [hglobal.1] with ω hω
    have hω' : ENNReal.ofReal (B ω) ≤
        ENNReal.ofReal β + ENNReal.ofReal (Rglobal ω) := by
      simpa [B, β, Rglobal, inverseBankCap] using hω
    rw [← ENNReal.ofReal_add hβ0 (hRglobal0 ω)] at hω'
    exact (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg hβ0 (hRglobal0 ω))).mp hω'

  have hTstate : ∀ j : ℕ, nativeInductionState M h
      (m - (0 : ℤ) - (j : ℤ)) := by
    intro j
    simpa using hstate j
  have hraw := raw_parent_gap_source_inputs M h hM hγ m 0 (by omega) t ht
    ({originCube 2 m} : Finset (TriadicCube 2))
    ⟨originCube 2 m, Finset.mem_singleton_self _⟩
    (by intro j; simpa using hTstate j)
  have hsource := parent_gap_source_trace_history_bound
    M h hM hγ N hpast m hm t ht
  let hShell := raw_trace_transport_shell_family_source
    M h hM hγ m 0 t ht hTstate
  have hprofile := raw_weak_trace_sequence_profile_of_shell_transport_helper
    M h hγ m 0 (by omega) t ht hTstate hShell
  have hTprofile (j : ℕ) : eLpNorm (T j) 2 μ ≤ ENNReal.ofReal (C j) := by
    have hh := hprofile j
    simpa [T, C, μ, mixedBridgeTbar, rawWeakTraceProfileEnvelope] using hh
  have hTmem (j : ℕ) : MemLp (T j) 2 μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt (hTprofile j) ENNReal.ofReal_lt_top
  have hTInt (j : ℕ) : Integrable (T j) μ :=
    (hTmem j).integrable (by norm_num)
  have hTmeas (j : ℕ) : AEStronglyMeasurable (T j) μ :=
    (hTmem j).aestronglyMeasurable
  have hsourceMean (j : ℕ) :
      (∫ ω, T j ω ∂μ) = inSourceMeanActual M m j t := by
    have hband := hraw.2.1.1 j
    simpa [T, μ, mixedBridgeTbar] using
      mixed_bridge_tbar_mean_eq_source_mean' M m t ht j hband

  have htraceSummable := mixed_bridge_raw_trace_weighted_summable_ae
    M h hM hγ m t ht hstate
  have hsourceSeriesAe : ∀ᵐ ω ∂μ, Summable (fun j => sourceTerm j ω) := by
    filter_upwards [htraceSummable] with ω hω
    have hmajor0 : Summable (fun j : ℕ =>
        (3683 / 2500 : ℝ) * (α ^ j * T j ω)) :=
      hω.mul_left (3683 / 2500 : ℝ)
    have hmajor : Summable (fun j : ℕ =>
        (3683 / 2500 : ℝ) * α ^ j * T j ω) := by
      apply hmajor0.congr
      intro j
      ring
    apply Summable.of_nonneg_of_le
    · intro j
      exact mul_nonneg (hW0 j) (hT0 j ω)
    · intro j
      exact mul_le_mul_of_nonneg_right (hWle j) (hT0 j ω)
    · exact hmajor
  have hsourceTermInt (j : ℕ) : Integrable (sourceTerm j) μ := by
    simpa [sourceTerm] using (hTInt j).const_mul (W j)
  have hsourceTermNonneg (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      0 ≤ sourceTerm j ω := by
    exact mul_nonneg (hW0 j) (hT0 j ω)
  have hsourceCoeffSummable : Summable (fun j : ℕ =>
      W j * inSourceMeanActual M m j t) := hsource.1
  have hsourceTermCap (j : ℕ) :
      (∫ ω, sourceTerm j ω ∂μ) ≤
        W j * inSourceMeanActual M m j t := by
    change (∫ ω, W j * T j ω ∂μ) ≤ W j * inSourceMeanActual M m j t
    rw [integral_const_mul, hsourceMean]
  have hsourceSeriesIntegral := nonneg_series_integral_ae μ
    sourceTerm (fun j => W j * inSourceMeanActual M m j t)
    hsourceTermInt hsourceTermNonneg hsourceSeriesAe hsourceCoeffSummable
    hsourceTermCap
  have hsourceSeriesInt : Integrable sourceSeries μ := by
    simpa [sourceSeries] using hsourceSeriesIntegral.1
  have hsourceSeriesBound :
      (∫ ω, sourceSeries ω ∂μ) ≤
        mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m := by
    calc
      _ ≤ ∑' j : ℕ, W j * inSourceMeanActual M m j t := by
        simpa [sourceSeries, sourceTerm] using hsourceSeriesIntegral.2
      _ ≤ mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m := hsource.2

  have hGlobalRare := parent_gap_global_population_rare_series
    M h hM hγ N hpast m hm t ht k.val (by omega)
  have hGlobalRareAe := parent_gap_global_population_rare_series_summable
    M h hM hγ N hpast m hm t ht k.val (by omega)
  have hglobalRareInt : Integrable globalRare μ := by
    simpa [globalRare, globalRareTerm, w, α, β, Rglobal, b, T, μ,
      mixedBridgeTbar] using hGlobalRare.1
  have hglobalRareBound :
      (∫ ω, globalRare ω ∂μ) ≤ β ^ k.val *
        (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
    simpa [globalRare, globalRareTerm, w, α, β, Rglobal, b, T, μ,
      mixedBridgeTbar] using hGlobalRare.2
  have hglobalRareAe' : ∀ᵐ ω ∂μ, Summable (fun j => globalRareTerm j ω) := by
    simpa [globalRareTerm, w, α, β, Rglobal, b, T, μ,
      mixedBridgeTbar] using hGlobalRareAe.2.2

  have hbaseCorrTermInt (j : ℕ) : Integrable (baseTerm j) μ := by
    have hholder := correlated_B_power_trace_integrable B (T j) β (C j)
      k.val (by omega) hβ0 (hC0 j) hB0 (hT0 j) hBmeas (hTmeas j) hB128
      (hTprofile j)
    have heq : baseTerm j = fun ω => (w j * b j) * (B ω ^ k.val * T j ω) := by
      funext ω
      dsimp [baseTerm]
      ring
    rw [heq]
    exact hholder.1.const_mul (w j * b j)
  have hbaseCorrTermNonneg (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      0 ≤ baseTerm j ω := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (hw0 j)
      (pow_nonneg (hB0 ω) k.val)) (hb0 j)) (hT0 j ω)
  have hbaseCorrCoeffSummable : Summable (fun j : ℕ =>
      W j * (β ^ k.val * C j)) := by
    have hprofile := mixed_profile_weighted_summable M
    have hmajor : Summable (fun j : ℕ =>
        ((3683 / 2500 : ℝ) * β ^ k.val) * (α ^ j * C j)) :=
      hprofile.mul_left ((3683 / 2500 : ℝ) * β ^ k.val)
    apply Summable.of_nonneg_of_le
    · intro j
      exact mul_nonneg (hW0 j)
        (mul_nonneg (pow_nonneg hβ0 k.val) (hC0 j))
    · intro j
      calc
        W j * (β ^ k.val * C j) ≤
            ((3683 / 2500 : ℝ) * α ^ j) * (β ^ k.val * C j) :=
          mul_le_mul_of_nonneg_right (hWle j)
            (mul_nonneg (pow_nonneg hβ0 k.val) (hC0 j))
        _ = ((3683 / 2500 : ℝ) * β ^ k.val) * (α ^ j * C j) := by ring
    · simpa [C] using hmajor
  have hbaseCorrTermCap (j : ℕ) :
      (∫ ω, baseTerm j ω ∂μ) ≤ W j * (β ^ k.val * C j) := by
    have hholder := correlated_B_power_trace_integrable B (T j) β (C j)
      k.val (by omega) hβ0 (hC0 j) hB0 (hT0 j) hBmeas (hTmeas j) hB128
      (hTprofile j)
    have heq : baseTerm j = fun ω => (w j * b j) * (B ω ^ k.val * T j ω) := by
      funext ω
      dsimp [baseTerm]
      ring
    rw [heq, integral_const_mul]
    rw [hWeq]
    exact mul_le_mul_of_nonneg_left hholder.2 (mul_nonneg (hw0 j) (hb0 j))
  have hbaseCorrAe : ∀ᵐ ω ∂μ, Summable (fun j => baseTerm j ω) := by
    filter_upwards [hsourceSeriesAe] with ω hω
    have hs := hω.mul_left (B ω ^ k.val)
    apply hs.congr
    intro j
    dsimp [baseTerm, sourceTerm]
    rw [hWeq]
    ring
  have hbaseCorrIntegral := nonneg_series_integral_ae μ
    baseTerm (fun j => W j * (β ^ k.val * C j)) hbaseCorrTermInt
    hbaseCorrTermNonneg hbaseCorrAe hbaseCorrCoeffSummable hbaseCorrTermCap
  have hbaseCorrInt : Integrable baseSeries μ := by
    simpa [baseSeries] using hbaseCorrIntegral.1

  have hlocalBlock (j : ℕ) := mixed_global_union_depth_block
    M h hM hγ N hpast m hm t ht j
  have hRlocal0 (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ Rlocal j ω := by
    simpa [Rlocal] using mixed_union_depth_remainder_nonneg M m t j ω
  have hRlocalMeas (j : ℕ) : AEStronglyMeasurable (Rlocal j) μ :=
    (hlocalBlock j).remainder_measurable.aestronglyMeasurable
  have hRlocal128 (j : ℕ) :
      eLpNorm (Rlocal j) 128 μ ≤
        ENNReal.ofReal (inverseBankDepthReserve .localInverse M j) := by
    change eLpNorm
      (inverseBankDepthBlockRemainder .localInverse
        (bankObserverDepthRootUnion (originCube 2 (m + 40)) 5 j)
        M m (m + 40) (bankPartialInsertionWeights m 1 t) j) 128 μ ≤ _
    exact (hlocalBlock j).remainder_L128
  have hlocalCoeffNonneg (j : ℕ) :
      0 ≤ inverseBankDepthReserve .localInverse M j := by
    unfold inverseBankDepthReserve inverseBankReserve bankDepthFrame
    positivity
  have hlocalDiscount (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      α ^ j * Rlocal j ω ≤ B ω := by
    simpa [Rlocal, B, α] using
      mixed_old_local_depth_remainder_discount_le_global M m t ht j ω
  have hlocalSeriesAe : ∀ᵐ ω ∂μ, Summable (fun j => localTerm j ω) := by
    have hs := weighted_rare_series_summable_ae'' μ α B Rlocal T k.val
      hα0 hα.2.le hB0 hRlocal0 (fun j ω => hT0 j ω) hlocalDiscount
      (by simpa [T, α, μ, mixedBridgeTbar] using htraceSummable)
    simpa [localTerm, w, α] using hs
  have hlocalTermInt (j : ℕ) : Integrable (localTerm j) μ := by
    have hholder := correlated_B_power_R_trace_integrable'' B (Rlocal j) (T j)
      β (inverseBankDepthReserve .localInverse M j) (C j) k.val (by omega)
      hβ0 (hlocalCoeffNonneg j) (hC0 j) hB0 (hRlocal0 j) (hT0 j)
      hBmeas (hRlocalMeas j) (hTmeas j) hB128 (hRlocal128 j) (hTprofile j)
    have heq : localTerm j = fun ω => w j *
        (B ω ^ k.val * Rlocal j ω * T j ω) := by
      funext ω
      dsimp [localTerm]
      ring
    rw [heq]
    exact hholder.1.const_mul (w j)
  have hlocalTermNonneg (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      0 ≤ localTerm j ω := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (hw0 j)
      (pow_nonneg (hB0 ω) k.val)) (hRlocal0 j ω)) (hT0 j ω)
  have hlocalCoeffSummable : Summable (fun j : ℕ =>
      w j * (β ^ k.val * inverseBankDepthReserve .localInverse M j * C j)) := by
    have hbase := old_signed_depth_rare_summable M hγ
    have hscale : Summable (fun j : ℕ =>
        ((1 - α ^ 2) * β ^ k.val) *
          (α ^ (2 * j) * inverseBankDepthReserve .localInverse M j *
            (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
              (3 : ℝ) ^ (6 * gammaZero * j)))) :=
      hbase.mul_left ((1 - α ^ 2) * β ^ k.val)
    apply hscale.congr
    intro j
    simp only [w, C, α, pow_mul]
    ring
  have hlocalCoeffBound :
      (∑' j : ℕ, w j *
        (β ^ k.val * inverseBankDepthReserve .localInverse M j * C j)) ≤
        β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
    have hbudget := old_signed_directional_rare_delta M hγ
    have hsum0 : 0 ≤ ∑' j : ℕ,
        α ^ (2 * j) * inverseBankDepthReserve .localInverse M j * C j :=
      tsum_nonneg (fun j => mul_nonneg
        (mul_nonneg (pow_nonneg hα0 _) (hlocalCoeffNonneg j)) (hC0 j))
    have hraw : 13 * ((1 - α ^ 2) *
        (∑' j : ℕ, α ^ (2 * j) * inverseBankDepthReserve .localInverse M j * C j)) ≤
        (1 / 10 ^ 12 : ℝ) * theta M := by
      simpa [C, pow_mul, mul_assoc, mul_left_comm, mul_comm] using hbudget
    have hbase : (1 - α ^ 2) *
        (∑' j : ℕ, α ^ (2 * j) * inverseBankDepthReserve .localInverse M j * C j) ≤
        (1 / (13 * 10 ^ 12) : ℝ) * theta M := by
      have hscaled := mul_le_mul_of_nonneg_left hraw
        (by norm_num : (0 : ℝ) ≤ 1 / 13)
      calc
        _ = (1 / 13 : ℝ) *
            (13 * ((1 - α ^ 2) *
              (∑' j : ℕ, α ^ (2 * j) * inverseBankDepthReserve .localInverse M j * C j))) := by
          ring
        _ ≤ (1 / 13 : ℝ) * ((1 / 10 ^ 12 : ℝ) * theta M) := hscaled
        _ = (1 / (13 * 10 ^ 12) : ℝ) * theta M := by ring
    have hident : (∑' j : ℕ, w j *
        (β ^ k.val * inverseBankDepthReserve .localInverse M j * C j)) =
        β ^ k.val * ((1 - α ^ 2) *
          (∑' j : ℕ, α ^ (2 * j) * inverseBankDepthReserve .localInverse M j * C j)) := by
      calc
        _ = ∑' j : ℕ, ((1 - α ^ 2) * β ^ k.val) *
            (α ^ (2 * j) * inverseBankDepthReserve .localInverse M j * C j) := by
          apply tsum_congr
          intro j
          simp only [w]
          ring
        _ = _ := by rw [tsum_mul_left]; ring
    rw [hident]
    calc
      _ ≤ β ^ k.val * ((1 / (13 * 10 ^ 12 : ℝ)) * theta M) :=
        mul_le_mul_of_nonneg_left hbase (pow_nonneg hβ0 k.val)
      _ = β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by ring
  have hlocalTermCap (j : ℕ) :
      (∫ ω, localTerm j ω ∂μ) ≤
        w j * (β ^ k.val * inverseBankDepthReserve .localInverse M j * C j) := by
    have hholder := correlated_B_power_R_trace_integrable'' B (Rlocal j) (T j)
      β (inverseBankDepthReserve .localInverse M j) (C j) k.val (by omega)
      hβ0 (hlocalCoeffNonneg j) (hC0 j) hB0 (hRlocal0 j) (hT0 j)
      hBmeas (hRlocalMeas j) (hTmeas j) hB128 (hRlocal128 j) (hTprofile j)
    have heq : localTerm j = fun ω => w j *
        (B ω ^ k.val * Rlocal j ω * T j ω) := by
      funext ω
      dsimp [localTerm]
      ring
    rw [heq, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hholder.2 (hw0 j)
  have hlocalIntegral := nonneg_series_integral_ae μ
    localTerm (fun j => w j *
      (β ^ k.val * inverseBankDepthReserve .localInverse M j * C j))
    hlocalTermInt hlocalTermNonneg hlocalSeriesAe hlocalCoeffSummable hlocalTermCap
  have hlocalInt : Integrable localSeries μ := by
    simpa [localSeries] using hlocalIntegral.1
  have hlocalBound :
      (∫ ω, localSeries ω ∂μ) ≤
        β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
    calc
      _ ≤ ∑' j : ℕ, w j *
          (β ^ k.val * inverseBankDepthReserve .localInverse M j * C j) := by
        simpa [localSeries, localTerm] using hlocalIntegral.2
      _ ≤ β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := hlocalCoeffBound

  have hbasePointwise : ∀ᵐ ω ∂μ,
      baseSeries ω ≤ β ^ k.val * sourceSeries ω + globalRare ω := by
    filter_upwards [hBsplit, hsourceSeriesAe, hglobalRareAe', hbaseCorrAe] with
      ω hBω hsourceω hrareω hbaseω
    have hterm (j : ℕ) : baseTerm j ω ≤
        β ^ k.val * sourceTerm j ω + globalRareTerm j ω := by
      have hX0 : 0 ≤ b j * T j ω := mul_nonneg (hb0 j) (hT0 j ω)
      have hexp := rare_factor_pointwise_expansion (B ω) β (Rglobal ω)
        (b j * T j ω) k.val (hB0 ω) hX0 hBω (by omega)
      calc
        _ = w j * (B ω ^ k.val * (b j * T j ω)) := by
          dsimp [baseTerm]
          ring
        _ ≤ w j * (β ^ k.val * (b j * T j ω) +
            rareExpansionTail β (Rglobal ω) (b j * T j ω) k.val) :=
          mul_le_mul_of_nonneg_left hexp (hw0 j)
        _ = β ^ k.val * sourceTerm j ω + globalRareTerm j ω := by
          dsimp [globalRareTerm, sourceTerm]
          rw [hWeq]
          ring
    have hsumRhs : Summable (fun j : ℕ =>
        β ^ k.val * sourceTerm j ω + globalRareTerm j ω) :=
      (hsourceω.mul_left (β ^ k.val)).add hrareω
    have hsum := Summable.tsum_le_tsum hterm hbaseω hsumRhs
    dsimp [baseSeries, sourceSeries, globalRare]
    rw [(hsourceω.mul_left (β ^ k.val)).tsum_add hrareω,
      tsum_mul_left] at hsum
    exact hsum
  have hbaseDomInt :
      Integrable (fun ω => β ^ k.val * sourceSeries ω + globalRare ω) μ :=
    (hsourceSeriesInt.const_mul (β ^ k.val)).add hglobalRareInt
  have hbaseBound :
      (∫ ω, baseSeries ω ∂μ) ≤
        β ^ k.val * (mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m) +
          β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
    calc
      _ ≤ ∫ ω, β ^ k.val * sourceSeries ω + globalRare ω ∂μ :=
        integral_mono_ae hbaseCorrInt hbaseDomInt hbasePointwise
      _ = β ^ k.val * (∫ ω, sourceSeries ω ∂μ) +
          ∫ ω, globalRare ω ∂μ := by
        rw [integral_add (hsourceSeriesInt.const_mul _) hglobalRareInt,
          integral_const_mul]
      _ ≤ β ^ k.val * (mixedBridgeXiPre M +
          t * mixedBridgeXiSlope M h m) +
          β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M :=
        add_le_add (mul_le_mul_of_nonneg_left hsourceSeriesBound
          (pow_nonneg hβ0 k.val)) hglobalRareBound

  have hthetaDecomp : ∀ᵐ ω ∂μ,
      B ω ^ k.val * mixedOldTheta M m (originCube 2 m) t ω =
        baseSeries ω + localSeries ω := by
    filter_upwards [hbaseCorrAe, hlocalSeriesAe] with ω hbaseω hlocalω
    have hterm (j : ℕ) :
        B ω ^ k.val * mixedOldThetaTerm M m (originCube 2 m) t j ω =
          baseTerm j ω + localTerm j ω := by
      dsimp [mixedOldThetaTerm, mixedDepthTraceAverage]
      rw [mixed_old_depth_coefficient_formula]
      dsimp [baseTerm, localTerm, b, Rlocal, T, w, α,
        mixedBridgeOldInverseBaseline]
      ring
    calc
      _ = ∑' j : ℕ, B ω ^ k.val *
          mixedOldThetaTerm M m (originCube 2 m) t j ω := by
        simp [mixedOldTheta, tsum_mul_left]
      _ = ∑' j : ℕ, (baseTerm j ω + localTerm j ω) := by
        apply tsum_congr
        exact hterm
      _ = baseSeries ω + localSeries ω := by
        exact hbaseω.tsum_add hlocalω
  have hsumInt : Integrable (fun ω => baseSeries ω + localSeries ω) μ :=
    hbaseCorrInt.add hlocalInt
  have hthetaReverse : (fun ω => baseSeries ω + localSeries ω) =ᵐ[μ]
      (fun ω => B ω ^ k.val *
        mixedOldTheta M m (originCube 2 m) t ω) := by
    filter_upwards [hthetaDecomp] with ω hω
    exact hω.symm
  have htargetInt :
      Integrable (fun ω => B ω ^ k.val *
        mixedOldTheta M m (originCube 2 m) t ω) μ :=
    hsumInt.congr hthetaReverse
  have htargetIntegral :
      (∫ ω, B ω ^ k.val *
        mixedOldTheta M m (originCube 2 m) t ω ∂μ) =
        (∫ ω, baseSeries ω ∂μ) + (∫ ω, localSeries ω ∂μ) := by
    rw [integral_congr_ae hthetaDecomp,
      integral_add hbaseCorrInt hlocalInt]
  have hreserve :
      (1 / (13 * 10 ^ 12 : ℝ)) * theta M +
        (1 / (13 * 10 ^ 12 : ℝ)) * theta M ≤
          (1 / 10 ^ 12 : ℝ) * theta M := by
    nlinarith [hθ]
  have hxiSlopeEq : mixedXiSlope M h m = mixedBridgeXiSlope M h m := by
    rw [mixed_bridge_xi_slope_eq_source_series]
    rfl
  have hxiEq : mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m +
      (1 / 10 ^ 12 : ℝ) * theta M = mixedXi M h m t := by
    rw [← hxiSlopeEq]
    simp [mixedXi, mixedXiPreCap, mixedBridgeXiPre]
    ring
  have hfinalBound :
      (∫ ω, B ω ^ k.val *
        mixedOldTheta M m (originCube 2 m) t ω ∂μ) ≤
        β ^ k.val * mixedXi M h m t := by
    rw [htargetIntegral]
    calc
      _ ≤ β ^ k.val *
          (mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m) +
            β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M +
            β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M :=
        add_le_add hbaseBound hlocalBound
      _ = β ^ k.val * (mixedBridgeXiPre M +
          t * mixedBridgeXiSlope M h m +
          (1 / (13 * 10 ^ 12 : ℝ)) * theta M +
          (1 / (13 * 10 ^ 12 : ℝ)) * theta M) := by ring
      _ ≤ β ^ k.val *
          (mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m +
            (1 / 10 ^ 12 : ℝ) * theta M) := by
        have hfactor :
            mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m +
              (1 / (13 * 10 ^ 12 : ℝ)) * theta M +
              (1 / (13 * 10 ^ 12 : ℝ)) * theta M ≤
            mixedBridgeXiPre M + t * mixedBridgeXiSlope M h m +
              (1 / 10 ^ 12 : ℝ) * theta M := by
          linarith [hreserve]
        exact mul_le_mul_of_nonneg_left hfactor (pow_nonneg hβ0 k.val)
      _ = β ^ k.val * mixedXi M h m t := by rw [hxiEq]

  have hBcarrier (ω : Cutoff.CutoffSample 2) :
      mixedGlobalHistoryMax M m t ω = B ω := by
    dsimp [mixedGlobalHistoryMax, mixedObserverRoots, B]
    rw [← mixed_bridge_observer_roots_eq_bank_union m,
      ← mixed_bridge_bstar_eq_bank_finite_history M m t ht ω]
    exact ENNReal.toReal_ofReal (mixed_bridge_bstar_nonneg M m t ω)
  refine ⟨?_, ?_⟩
  · exact htargetInt.congr (Filter.Eventually.of_forall fun ω => by
      simp only [hBcarrier])
  · simpa [hBcarrier, mainBeta, β] using hfinalBound

end
end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Inverse.MixedBridgeLocalBudget
public import ASDExplicitGamma.Inverse.RawTraceSpatialAverage
public import ASDExplicitGamma.Inverse.StoppedDensitySumNorm
public import ASDExplicitGamma.Inverse.WeakHistoryIneq

/-! Observer-cell version of the translated local OLD trace rows (hypothesis: cell scale only). -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Native
open ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem mixed_bridge_local_root_scale'
    (m : ℤ) (r : ℕ) (U : TriadicCube 2)
    (hU : U.scale = m - (r : ℤ)) :
    U.scale = m - (r : ℤ) := by
  exact hU

theorem mixed_bridge_local_descendant_scale'
    (m : ℤ) (r j : ℕ) (U V : TriadicCube 2)
    (hU : U.scale = m - (r : ℤ))
    (hV : V ∈ descendantsAtDepth U j) :
    V.scale = m - (r + j : ℕ) := by
  have hscaleU := mixed_bridge_local_root_scale' m r U hU
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hV
  rw [hscaleU] at hs
  push_cast at hs ⊢
  omega

theorem mixed_bridge_local_origin_trace_profile'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (r j : ℕ) (hr : r ≤ 5) :
    eLpNorm (rawDepthFourLoadTrace M m (m - (r : ℤ) - (j : ℤ)) t)
      (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
  have hstate : ∀ q : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (q : ℤ)) := by
    intro q
    apply hpast
    omega
  have hband := raw_trace_band_profile_source M h hM hγ m r hr
    t ht hstate j
  have hbandEq : rawTraceTransportBandObservable M m r t j =
      rawDepthFourLoadTrace M m (m - (r : ℤ) - (j : ℤ)) t := by
    funext ω
    rw [rawTraceTransportBandObservable,
      raw_depth_four_load_trace_eq_model_observable]
    rw [raw_trace_transport_band_scalar_eq_inserted_helper M m r j hr
      t ⟨ht.1, ht.2⟩ ω]
  simpa only [hbandEq, rawWeakTraceProfileEnvelope] using hband

theorem mixed_bridge_raw_depth_aestronglyMeasurable'
    (M : ABKModel 2) (m q : ℤ) (t : ℝ) :
    AEStronglyMeasurable (rawDepthFourLoadTrace M m q t)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let K := closure (cubeSet (originCube 2 q))
  haveI : CompactSpace K := modelHeatCubeClosureCompact q
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  have hscalar : Measurable (modelInsertedScalar K m t) := by
    change Measurable (fun ω => olderField K m ω +
      Real.sqrt t • shellFieldScalarRestriction K (ω.1 (m + 1)))
    exact (measurable_olderField K ell m hK).add
      (((measurable_shellFieldScalarRestriction K).comp
        ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)).const_smul
          (Real.sqrt t))
  have hobs := (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1).1.continuous.measurable.comp hscalar
  have heq : rawDepthFourLoadTrace M m q t =
      fun ω => modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ)
        (modelInsertedScalar K m t ω) := by
    funext ω
    exact raw_depth_four_load_trace_eq_model_observable M m q t ω
  rw [heq]
  exact hobs.aestronglyMeasurable

theorem mixed_bridge_local_trace_cell_profile'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (r : ℕ) (hr : r ≤ 5)
    (j : ℕ) (V : TriadicCube 2)
    (hscale : V.scale = m - (r + j : ℕ)) :
    eLpNorm (rawCubeFourLoadTrace M m V t) (ENNReal.ofReal 2)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have horigin : eLpNorm
      (rawDepthFourLoadTrace M m (m - (r : ℤ) - (j : ℤ)) t)
      (ENNReal.ofReal 2) μ ≤
      ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) :=
    mixed_bridge_local_origin_trace_profile' M h hM hγ N hpast m hm t ht r j hr
  have htrans : rawCubeFourLoadTrace M m V t =
      rawDepthFourLoadTrace M m V.scale t ∘
        Cutoff.translateCutoffSample (triadicCubeShift V) := by
    funext ω
    exact raw_cube_four_load_trace_eq_translated_origin_helper M m V t ω
  have hscale' : V.scale = m - (r : ℤ) - (j : ℤ) := by
    rw [hscale]
    push_cast
    omega
  have hprofileV : eLpNorm (rawDepthFourLoadTrace M m V.scale t)
      (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
    rw [hscale']
    exact horigin
  have hdepthMeas : AEStronglyMeasurable
      (rawDepthFourLoadTrace M m V.scale t) μ :=
    mixed_bridge_raw_depth_aestronglyMeasurable' M m V.scale t
  rw [htrans]
  change eLpNorm
    (rawDepthFourLoadTrace M m V.scale t ∘
      (fun ω => triadicCubeShift V +ᵥ ω)) (ENNReal.ofReal 2) μ ≤ _
  rw [eLpNorm_comp_measurePreserving hdepthMeas
    (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd
      (μ := μ) (triadicCubeShift V))]
  exact hprofileV

theorem mixed_bridge_local_trace_average_bound'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (r : ℕ) (hr : r ≤ 5) (U : TriadicCube 2)
    (hU : U.scale = m - (r : ℤ))
    (j : ℕ) :
    eLpNorm (fun ω => mixedDepthTraceAverage M m U t ω j)
      (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let D := descendantsAtDepth U j
  let I := SquareCells U j
  have hscaleU := mixed_bridge_local_root_scale' m r U hU
  have hscaleV (V : TriadicCube 2) (hV : V ∈ D) :
      V.scale = m - (r + j : ℕ) := by
    change V ∈ descendantsAtDepth U j at hV
    exact mixed_bridge_local_descendant_scale' m r j U V hU hV
  have hcell (V : TriadicCube 2) (hV : V ∈ D) :
      eLpNorm (rawCubeFourLoadTrace M m V t) (ENNReal.ofReal 2) μ ≤
        ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) :=
    mixed_bridge_local_trace_cell_profile' M h hM hγ N hpast m hm t ht r hr j V
      (hscaleV V hV)
  have hnonneg : 0 ≤ rawWeakTraceProfileEnvelope M j := by
    have htheta : 0 ≤ theta M := by
      unfold theta
      exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
    have hMrat : 0 ≤ invTraceM := by
      rw [invTrace_coefficient.1]
      positivity
    have hM : 0 ≤ (invTraceM : ℝ) := by exact_mod_cast hMrat
    unfold rawWeakTraceProfileEnvelope
    positivity
  have hcardNat : 0 < D.card := Finset.card_pos.mpr (descendantsAtDepth_nonempty U j)
  have hcardR : 0 < (D.card : ℝ) := by exact_mod_cast hcardNat
  have hcardI : Fintype.card I = D.card := by
    simp [I, SquareCells, D]
  have hcardIr : (Fintype.card I : ℝ) = (D.card : ℝ) := by exact_mod_cast hcardI
  have hcardIpos : 0 < Fintype.card I := by rw [hcardI]; exact hcardNat
  have hmeanEq : (fun ω => mixedDepthTraceAverage M m U t ω j) =
      fun ω => ((D.card : ℝ)⁻¹) *
        ∑ C : I, rawCubeFourLoadTrace M m C.val t ω := by
    funext ω
    rfl
  have hmeanfun : (fun ω => mixedDepthTraceAverage M m U t ω j) =
      fun ω => ∑ C : I, (D.card : ℝ)⁻¹ * rawCubeFourLoadTrace M m C.val t ω := by
    funext ω
    simpa [Finset.mul_sum] using congrFun hmeanEq ω
  have hmeanfun' : (fun ω => mixedDepthTraceAverage M m U t ω j) =
      fun ω => ((Fintype.card I : ℝ)⁻¹) *
        ∑ C : I, rawCubeFourLoadTrace M m C.val t ω := by
    calc
      _ = fun ω => ∑ C : I,
          (D.card : ℝ)⁻¹ * rawCubeFourLoadTrace M m C.val t ω := hmeanfun
      _ = fun ω => ((D.card : ℝ)⁻¹) *
          ∑ C : I, rawCubeFourLoadTrace M m C.val t ω := by
        funext ω
        rw [← Finset.mul_sum]
      _ = fun ω => ((Fintype.card I : ℝ)⁻¹) *
          ∑ C : I, rawCubeFourLoadTrace M m C.val t ω := by
        funext ω
        rw [← hcardIr]
  have hmeanfun'' :
      (fun ω => ((Fintype.card I : ℝ)⁻¹) *
        ∑ C : I, rawCubeFourLoadTrace M m C.val t ω) =
      fun ω => ∑ C : I,
        (Fintype.card I : ℝ)⁻¹ * rawCubeFourLoadTrace M m C.val t ω := by
    funext ω
    rw [← Finset.mul_sum]
  rw [hmeanfun']
  rw [hmeanfun'']
  have hLp := finite_density_sum_Lp μ (ENNReal.ofReal 2)
    (ENNReal.one_le_ofReal.mpr (by norm_num : (1 : ℝ) ≤ 2))
    (fun C : I => fun ω => rawCubeFourLoadTrace M m C.val t ω)
    (fun _ => (Fintype.card I : ℝ)⁻¹)
    (fun _ => rawWeakTraceProfileEnvelope M j)
    (fun _ => inv_nonneg.mpr (by exact_mod_cast hcardIpos.le)) (fun _ => hnonneg)
    (fun C => hcell C.val C.property)
  simpa [Finset.sum_const, nsmul_eq_mul, hcardIpos.ne'] using hLp

/-- Every translated depth-five source cell has the same actual L² trace
profile as its origin-cell representative, with the fixed OLD frame at `m`. -/
theorem mixed_bridge_local_trace_profile'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (r : ℕ) (hr : r ≤ 5) (U : TriadicCube 2)
    (hU : U.scale = m - (r : ℤ)) :
    ∀ j : ℕ,
      eLpNorm (mixedDepthTraceAverage M m U t · j)
        (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
  intro j
  simpa only [mixedDepthTraceAverage] using
    mixed_bridge_local_trace_average_bound' M h hM hγ N hpast m hm t ht
      r hr U hU j

/-- The expectation of the actual local descendant trace is precisely the
`r=5+j` source mean in the same cutoff law and frame. -/
theorem mixed_bridge_local_trace_mean'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (r : ℕ) (hr : r ≤ 5) (U : TriadicCube 2)
    (hU : U.scale = m - (r : ℤ))
    (j : ℕ) :
    Integrable (fun ω => mixedDepthTraceAverage M m U t ω j)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, mixedDepthTraceAverage M m U t ω j
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      inSourceMeanActual M m (r + j) t := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let D := descendantsAtDepth U j
  let hprofile := mixed_bridge_local_trace_profile' M h hM hγ N hpast
    m hm t ht r hr U hU j
  have hTmem : MemLp (mixedDepthTraceAverage M m U t · j) 2 μ := by
    apply memLp_iff.mpr
    have hcast : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
    rw [← hcast]
    exact lt_of_le_of_lt hprofile ENNReal.ofReal_lt_top
  have hTInt : Integrable (mixedDepthTraceAverage M m U t · j) μ :=
    hTmem.integrable (by norm_num)
  have hscaleU := mixed_bridge_local_root_scale' m r U hU
  have hscaleV (V : TriadicCube 2) (hV : V ∈ D) :
      V.scale = m - (r + j : ℕ) := by
    change V ∈ descendantsAtDepth U j at hV
    exact mixed_bridge_local_descendant_scale' m r j U V hU hV
  have hcellInt (V : TriadicCube 2) (hV : V ∈ D) :
      Integrable (rawCubeFourLoadTrace M m V t) μ := by
    have hcell := mixed_bridge_local_trace_cell_profile' M h hM hγ N hpast
      m hm t ht r hr j V (hscaleV V hV)
    have hcast : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
    have hcell' : eLpNorm (rawCubeFourLoadTrace M m V t) 2 μ ≤
        ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
      simpa only [hcast] using hcell
    exact (memLp_iff.mpr
      (lt_of_le_of_lt hcell' ENNReal.ofReal_lt_top)).integrable
      (by norm_num)
  have hcellMean (V : TriadicCube 2) (hV : V ∈ D) :
      (∫ ω, rawCubeFourLoadTrace M m V t ω ∂μ) =
        inSourceMeanActual M m (r + j) t := by
    have hscale := hscaleV V hV
    have hscale' : V.scale = m - (r : ℤ) - (j : ℤ) := by
      rw [hscale]
      push_cast
      omega
    have hdepthProfile : eLpNorm
        (rawDepthFourLoadTrace M m V.scale t) (ENNReal.ofReal 2) μ ≤
        ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
      rw [hscale']
      exact mixed_bridge_local_origin_trace_profile' M h hM hγ N hpast
        m hm t ht r j hr
    have hdepthMem : MemLp (rawDepthFourLoadTrace M m V.scale t) 2 μ := by
      apply memLp_iff.mpr
      have hcast : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
      rw [← hcast]
      exact lt_of_le_of_lt hdepthProfile ENNReal.ofReal_lt_top
    have hdepthInt : Integrable (rawDepthFourLoadTrace M m V.scale t) μ :=
      hdepthMem.integrable (by norm_num)
    have htrans : rawCubeFourLoadTrace M m V t =
        rawDepthFourLoadTrace M m V.scale t ∘
          Cutoff.translateCutoffSample (triadicCubeShift V) := by
      funext ω
      exact raw_cube_four_load_trace_eq_translated_origin_helper M m V t ω
    have hmp : MeasurePreserving
        (Cutoff.translateCutoffSample (triadicCubeShift V)) μ μ :=
      ⟨Cutoff.measurable_translateCutoffSample _,
        Cutoff.map_translateCutoffSample_cutoffSampleLaw M _⟩
    have hi := integral_map (μ := μ)
      (Cutoff.measurable_translateCutoffSample (triadicCubeShift V)).aemeasurable
      (by rw [Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift V)]
          exact hdepthInt.aestronglyMeasurable)
    rw [Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift V)] at hi
    calc
      (∫ ω, rawCubeFourLoadTrace M m V t ω ∂μ) =
          ∫ ω, rawDepthFourLoadTrace M m V.scale t
            (Cutoff.translateCutoffSample (triadicCubeShift V) ω) ∂μ := by
        rw [htrans]
        simp only [Function.comp_apply]
      _ = ∫ ω, rawDepthFourLoadTrace M m V.scale t ω ∂μ := hi.symm
      _ = inSourceMeanActual M m (r + j) t := by
        rw [hscale, inSourceMeanActual, modelTraceHeatAverage]
        rfl
  have hmeanEq : (fun ω => mixedDepthTraceAverage M m U t ω j) =
      fun ω => (D.card : ℝ)⁻¹ *
        ∑ V ∈ D, rawCubeFourLoadTrace M m V t ω := by
    funext ω
    change squareCellMean U j
      (fun C => rawCubeFourLoadTrace M m C.val t ω) = _
    unfold squareCellMean Cold.SquareCells
    congr 1
    exact Finset.sum_attach D (fun V => rawCubeFourLoadTrace M m V t ω)
  have hsumInt : Integrable
      (fun ω => ∑ V ∈ D, rawCubeFourLoadTrace M m V t ω) μ :=
    integrable_finsetSum _ (fun V hV => hcellInt V hV)
  have hsumMean :
      (∫ ω, (∑ V ∈ D, rawCubeFourLoadTrace M m V t ω) ∂μ) =
        (D.card : ℝ) * inSourceMeanActual M m (r + j) t := by
    rw [integral_finsetSum _ (fun V hV => hcellInt V hV)]
    calc
      _ = ∑ V ∈ D, inSourceMeanActual M m (r + j) t := by
        apply Finset.sum_congr rfl
        intro V hV
        exact hcellMean V hV
      _ = (D.card : ℝ) * inSourceMeanActual M m (r + j) t := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (D.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (descendantsAtDepth_nonempty U j)).ne'
  refine ⟨?_, ?_⟩
  · simpa only [hmeanEq] using hTInt
  calc
    _ = ∫ ω, ((D.card : ℝ)⁻¹ *
        ∑ V ∈ D, rawCubeFourLoadTrace M m V t ω) ∂μ := by
      rw [hmeanEq]
    _ = (D.card : ℝ)⁻¹ *
        ∫ ω, (∑ V ∈ D, rawCubeFourLoadTrace M m V t ω) ∂μ := by
      rw [integral_const_mul]
    _ = inSourceMeanActual M m (r + j) t := by
      rw [hsumMean]
      field_simp


theorem mixed_bridge_local_profile_nonneg'
    (M : ABKModel 2) (j : ℕ) :
    0 ≤ rawWeakTraceProfileEnvelope M j := by
  have htheta : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by
    rw [invTrace_coefficient.1]
    positivity
  have hM : 0 ≤ (invTraceM : ℝ) := by exact_mod_cast hMrat
  unfold rawWeakTraceProfileEnvelope
  positivity

theorem mixed_bridge_local_profile_weighted_summable'
    (M : ABKModel 2) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      rawWeakTraceProfileEnvelope M j) := by
  let α : ℝ := Scalar.inverseHistoryDiscount
  let q : ℝ := α * (3 : ℝ) ^ (6 * gammaZero)
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
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hq0]
    exact hq1
  have hgeom : Summable (fun j : ℕ => q ^ j) :=
    summable_geometric_of_lt_one hq0 hq1
  have hlin : Summable (fun j : ℕ => (j : ℝ) * q ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hqnorm
  have hquad : Summable (fun j : ℕ => (j : ℝ) ^ 2 * q ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 2 hqnorm
  have hpoly : Summable (fun j : ℕ => (1 + (j : ℝ)) ^ 2 * q ^ j) := by
    have hsum := hquad.add (hlin.mul_left 2)
    have hsum' := hsum.add hgeom
    apply hsum'.congr
    intro j
    ring
  have hpow (j : ℕ) :
      (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) =
        ((3 : ℝ) ^ (6 * gammaZero)) ^ j := by
    rw [show 6 * gammaZero * (j : ℝ) =
      (6 * gammaZero) * (j : ℝ) by ring]
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (6 * gammaZero)) j]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hterm (j : ℕ) :
      Scalar.inverseHistoryDiscount ^ j * rawWeakTraceProfileEnvelope M j =
        (theta M * (invTraceM : ℚ)) *
          ((1 + (j : ℝ)) ^ 2 * q ^ j) := by
    rw [rawWeakTraceProfileEnvelope, hpow]
    dsimp [q]
    ring
  have hpoly' := hpoly.mul_left (theta M * (invTraceM : ℚ))
  exact hpoly'.congr fun j => (hterm j).symm

/-- The translated depth-five trace sequence has the same weighted a.e.
summability as the root sequence. The proof uses its actual-law L² profile
and positivity; no independence or translated global-bank assertion enters. -/
theorem mixed_bridge_local_trace_weighted_summable_ae'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2)
    (hU : U.scale = m - ((5 : ℕ) : ℤ)) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
        mixedDepthTraceAverage M m U t ω j) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ :=
    fun j ω => mixedDepthTraceAverage M m U t ω j
  let F : ℕ → Cutoff.CutoffSample 2 → ℝ :=
    fun j ω => α ^ j * T j ω
  have hα := Scalar.inverse_history_discount_range
  have hprofile (j : ℕ) : eLpNorm (T j) 2 μ ≤
      ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
    simpa [T, μ] using
      mixed_bridge_local_trace_profile' M h hM hγ N hpast m hm t ht
        5 (by omega) U hU j
  have hTmem (j : ℕ) : MemLp (T j) 2 μ := by
    have hne : eLpNorm (T j) 2 μ < ⊤ :=
      (hprofile j).trans_lt ENNReal.ofReal_lt_top
    exact (memLp_iff).mpr hne
  have hFmem (j : ℕ) : MemLp (F j) 2 μ := by
    change MemLp ((α ^ j) • T j) 2 μ
    exact (hTmem j).const_smul (α ^ j)
  have hprofileSummable : Summable (fun j : ℕ =>
      α ^ j * rawWeakTraceProfileEnvelope M j) := by
    simpa [α] using mixed_bridge_local_profile_weighted_summable' M
  have hFbound (j : ℕ) : lpNorm (F j) 2 μ ≤
      α ^ j * rawWeakTraceProfileEnvelope M j := by
    have hαj : 0 ≤ α ^ j := pow_nonneg hα.1.le j
    have hCj : 0 ≤ rawWeakTraceProfileEnvelope M j :=
      mixed_bridge_local_profile_nonneg' M j
    have hscaled : eLpNorm (F j) 2 μ ≤
        ENNReal.ofReal (α ^ j * rawWeakTraceProfileEnvelope M j) := by
      have hFfun : F j = (α ^ j) • T j := by
        funext ω
        rfl
      calc
        eLpNorm (F j) 2 μ =
            ENNReal.ofReal (α ^ j) * eLpNorm (T j) 2 μ := by
          rw [hFfun, eLpNorm_const_smul, Real.enorm_eq_ofReal hαj]
        _ ≤ ENNReal.ofReal (α ^ j) *
            ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) :=
          mul_le_mul_of_nonneg_left (hprofile j) (by positivity)
        _ = ENNReal.ofReal
            (α ^ j * rawWeakTraceProfileEnvelope M j) :=
          (ENNReal.ofReal_mul hαj).symm
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hscaled
    rw [ENNReal.toReal_ofReal (mul_nonneg hαj hCj)] at hreal
    rw [← toReal_eLpNorm]
    exact hreal
  have hnormSummable : Summable (fun j : ℕ => lpNorm (F j) 2 μ) :=
    Summable.of_nonneg_of_le (fun j => lpNorm_nonneg) hFbound
      hprofileSummable
  have hnormSumFinite : (∑' j : ℕ, eLpNorm (F j) 2 μ) ≠ ⊤ := by
    have hsumEq : (∑' j : ℕ, eLpNorm (F j) 2 μ) =
        ∑' j : ℕ, ENNReal.ofReal (lpNorm (F j) 2 μ) := by
      apply tsum_congr
      intro j
      exact (ofReal_lpNorm (hFmem j)).symm
    rw [hsumEq]
    exact ne_of_lt hnormSummable.tsum_ofReal_lt_top
  have hpoint := summable_norm_of_tsum_eLpNorm_ne_top
    (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal)) hnormSumFinite
  have hTnonneg (ω : Cutoff.CutoffSample 2) (j : ℕ) : 0 ≤ T j ω := by
    simpa [T, mixedDepthTraceAverage] using
      raw_weak_trace_sequence_nonneg M m U t ⟨ht.1, ht.2⟩ ω j
  filter_upwards [hpoint] with ω hω
  apply hω.congr
  intro j
  change |α ^ j * T j ω| = α ^ j * T j ω
  exact abs_of_nonneg (mul_nonneg (pow_nonneg hα.1.le j) (hTnonneg ω j))



end

end ASDExplicitGamma.Inverse

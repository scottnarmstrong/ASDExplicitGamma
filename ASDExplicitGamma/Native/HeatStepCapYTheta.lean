module

public import ASDExplicitGamma.Native.HeatStepCapY
public import ASDExplicitGamma.Native.HeatStepCapXTheta
public import ASDExplicitGamma.Native.HeatInitialThetaGaussian

/-! The theta-scaled heat-augmented average cap `θ · frames.y` of the refined child traces. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ProbabilityTheory
  ASDExplicitGamma.Inverse
open scoped ENNReal NNReal Topology Nat

section CapYTheta

variable (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)

/-- The twentieth moment of the center quadratic of the series realization. -/
theorem nativeHeatStep_quad_L20_theta (hgen : NativeHeatGenNum ns)
    (hfr : NativeHeatStepFrameNum ns)
    (hg : M.gamma ≤ gammaZero) (hstate : nativeInductionState M h (m + 1)) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) :
    eLpNorm (fun ξ : ℕ → ℝ => ∑ i : nativeHeatQ3RefinedCarrierIndex,
        heatVHEATDriftRefinedWeight *
          (nativeHeatStepAux ns M h hM m t i ξ / (Annealed.sigmaBar M (m + 1) : ℝ)) ^ 2) 20
      standardGaussianInfinitePi ≤ ENNReal.ofReal (theta M * ((nativeHeatQNGen ns : ℚ) : ℝ)) := by
  classical
  let Ffam := nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns
  let hA := nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen Ffam
  let T := nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
  let S : (ℕ → ℝ) → C(nativeHeatQ3RefinedCarrierDomain m, ℝ) := gaussianSeriesLimitE hA T
  have hSm : Measurable S := (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable
  have hPsiM : Measurable (nativeHeatStepPsi M m) := (nativeHeatStep_psi_continuous M m).measurable
  have hcard : (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ) = 9 ^ 10 := by
    rw [nativeHeatQ3RefinedCarrierIndex_card]; norm_num
  have hpt : ∀ ξ, ∑ i : nativeHeatQ3RefinedCarrierIndex, heatVHEATDriftRefinedWeight *
      (nativeHeatStepAux ns M h hM m t i ξ / (Annealed.sigmaBar M (m + 1) : ℝ)) ^ 2 =
      (1 - t) * nativeHeatStepPsi M m (S ξ) := by
    intro ξ
    have hσ : (Annealed.sigmaBar M (m + 1) : ℝ) ≠ 0 :=
      ne_of_gt (Annealed.sigmaBar_characterization M (m + 1)).1
    unfold nativeHeatStepPsi heatVHEATDriftRefinedWeight
    rw [hcard, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hax := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_eq_backwardCenterInput M m ns
      Ffam (nativeHeatTheta : ℝ) t i ξ
    change nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns Ffam (nativeHeatTheta : ℝ) t i ξ = _ at hax
    show (9 ^ 10 : ℝ)⁻¹ * (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns Ffam
        (nativeHeatTheta : ℝ) t i ξ / (Annealed.sigmaBar M (m + 1) : ℝ)) ^ 2 = _
    rw [hax]
    have h1 : (0 : ℝ) ≤ 1 + (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
    have h2 : (0 : ℝ) ≤ 1 - t := by linarith [ht.2]
    rw [div_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt (mul_nonneg h1 h2), Real.sq_sqrt h1]
    simp only [nativeHeatQ3RefinedCarrierSourceCenterMapGen]
    ring
  have hfun : (fun ξ : ℕ → ℝ => ∑ i : nativeHeatQ3RefinedCarrierIndex,
      heatVHEATDriftRefinedWeight *
        (nativeHeatStepAux ns M h hM m t i ξ / (Annealed.sigmaBar M (m + 1) : ℝ)) ^ 2) =
      fun ξ => (1 - t) * nativeHeatStepPsi M m (S ξ) := funext hpt
  rw [hfun]
  have hmeas : AEStronglyMeasurable (fun ξ => (1 - t) * nativeHeatStepPsi M m (S ξ))
      standardGaussianInfinitePi :=
    (measurable_const.mul (hPsiM.comp hSm)).aestronglyMeasurable
  apply eLpNorm_le_of_twentieth_lintegral _ hmeas
  have h1t : 0 ≤ 1 - t := by linarith [ht.2]
  have h1t' : 1 - t ≤ 1 := by linarith [ht.1]
  have hle : ∀ ξ, ‖(1 - t) * nativeHeatStepPsi M m (S ξ)‖ₑ ≤
      ‖nativeHeatStepPsi M m (S ξ)‖ₑ := by
    intro ξ
    rw [Real.enorm_eq_ofReal (mul_nonneg h1t (nativeHeatStep_psi_nonneg M m _)),
      Real.enorm_eq_ofReal (nativeHeatStep_psi_nonneg M m _)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [nativeHeatStep_psi_nonneg M m (S ξ)]
  calc ∫⁻ ξ, ‖(1 - t) * nativeHeatStepPsi M m (S ξ)‖ₑ ^ (20 : ℝ) ∂standardGaussianInfinitePi
      ≤ ∫⁻ ξ, ‖nativeHeatStepPsi M m (S ξ)‖ₑ ^ (20 : ℝ) ∂standardGaussianInfinitePi :=
        lintegral_mono fun ξ => ENNReal.rpow_le_rpow (hle ξ) (by norm_num)
    _ = ∫⁻ c, ‖nativeHeatStepPsi M m c‖ₑ ^ (20 : ℝ) ∂(standardGaussianInfinitePi.map S) := by
        rw [lintegral_map (by fun_prop) hSm]
    _ = ∫⁻ c, ‖nativeHeatStepPsi M m c‖ₑ ^ (20 : ℝ)
          ∂((Cutoff.cutoffSampleLaw M).toMeasure.map
            (modelBand (nativeHeatQ3RefinedCarrierDomain m)
              (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns))) := by
        rw [nativeHeatQ3RefinedCarrierFreshShellSeriesLawGen Ffam]
    _ = ∫⁻ ω, ENNReal.ofReal
          (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ 20)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
        rw [lintegral_map (by fun_prop) (measurable_modelBand _ _)]
        apply lintegral_congr
        intro ω
        have hq : nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω =
            nativeHeatStepPsi M m (modelBand (nativeHeatQ3RefinedCarrierDomain m)
              (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) ω) := rfl
        rw [hq, Real.enorm_eq_ofReal (nativeHeatStep_psi_nonneg M m _),
          ENNReal.ofReal_rpow_of_nonneg (nativeHeatStep_psi_nonneg M m _) (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal (theta M ^ 20 * (((nativeHeatGenQm ns).getD 20 0 : ℚ) : ℝ)) :=
        nativeHeatQ3RefinedCarrierSourceCenterQuadraticMoment_theta ns hgen M h hM hg m
          hstate 20 le_rfl
    _ ≤ ENNReal.ofReal (theta M * ((nativeHeatQNGen ns : ℚ) : ℝ)) ^ (20 : ℝ) := by
        have hroot := (of_decide_eq_true hfr.qN_root).2.2.2
        have hq0 : (0 : ℝ) ≤ ((nativeHeatQNGen ns : ℚ) : ℝ) := by
          exact_mod_cast (of_decide_eq_true hfr.qN_root).2.2.1
        have hτ0 := (theta_pos_le_one M hg).1
        rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hτ0.le hq0) (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        have := (Rat.cast_le (K := ℝ)).2 hroot
        push_cast at this
        have h2 : (((nativeHeatGenQm ns).getD 20 0 : ℚ) : ℝ) ≤ ((nativeHeatQNGen ns : ℚ) : ℝ) ^ 20 := by
          simpa [nativeHeatQNGen] using this
        calc theta M ^ 20 * (((nativeHeatGenQm ns).getD 20 0 : ℚ) : ℝ)
            ≤ theta M ^ 20 * ((nativeHeatQNGen ns : ℚ) : ℝ) ^ 20 :=
              mul_le_mul_of_nonneg_left h2 (pow_nonneg hτ0.le _)
          _ = (theta M * ((nativeHeatQNGen ns : ℚ) : ℝ)) ^ (20 : ℝ) := by
              rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow]

include hM in
/-- The heat-augmented average cap: `Y₀ = frames.y` bounds the average norm at every heat time. -/
theorem nativeHeatStep_yCap_theta (hnum : NativeHeatStepPassNum ns)
    (hfr : NativeHeatStepFrameNum ns) (hgen : NativeHeatGenNum ns)
    (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ j < m + 1, nativeInductionState M h j)
    (hstate : nativeInductionState M h (m + 1))
    (hchild : NativeHeatStepChildAllTimeCap M m ns (theta M * (nativeHeatY0Gen ns : ℝ))) :
    ∀ t ∈ Ioo (0 : ℝ) 1,
      (nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t ≤ theta M * ((nativeHeatFramesGen ns).y : ℝ) := by
  classical
  intro t ht
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  let Ffam := nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns
  let σ : ℝ := Annealed.sigmaBar M (m + 1)
  let g := nativeHeatStepAux ns M h hM m t
  let μc := (Cutoff.cutoffSampleLaw M).toMeasure
  haveI : IsProbabilityMeasure μc := (Cutoff.cutoffSampleLaw M).property
  have hy0q := nativeHeatStep_rootValid_nonneg _ hfr.y0_root
  have hy0 : (0 : ℝ) ≤ (nativeHeatY0Gen ns : ℝ) := by exact_mod_cast hy0q
  have hgm0 : 0 ≤ ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ) := by
    exact_mod_cast nativeHeatGM20_powers.1
  have hV0 : (0 : ℝ) ≤ (nativeHeatGenVariance ns : ℝ) := by
    have h1 := (Rat.cast_le (K := ℝ)).2
      (nativeUp_ge ((1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e * (ns : ℚ)))
    rw [nativeHeatGenVariance_eq]
    refine le_trans ?_ h1
    have : (0 : ℚ) ≤ (1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e * (ns : ℚ) := by
      have := hnum.old_e_nonneg
      have h2 : (0 : ℚ) ≤ 1 + nativeHeatTheta := by norm_num [nativeHeatTheta]
      positivity
    exact_mod_cast this
  have hBn : (0 : ℝ) ≤ (nativeHeatB : ℝ) := by
    have : (0 : ℚ) ≤ nativeHeatB := by
      norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB]
    exact_mod_cast this
  have hB : (3683 / 2500 : ℝ) ≤ (nativeHeatB : ℝ) := by
    have : (3683 / 2500 : ℚ) ≤ nativeHeatB := by
      norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB]
    calc (3683 / 2500 : ℝ) = ((3683 / 2500 : ℚ) : ℝ) := by norm_num
      _ ≤ _ := Rat.cast_le.mpr this
  have hE : (3 / 10 ^ 46 : ℝ) ≤ (nativeHeatEps : ℝ) := by
    have : (3 / 10 ^ 46 : ℚ) ≤ nativeHeatEps := by
      norm_num [nativeHeatEps, nativeHeatRQ, nativeE, nativeGamma, nativeEps]
    calc (3 / 10 ^ 46 : ℝ) = ((3 / 10 ^ 46 : ℚ) : ℝ) := by norm_num
      _ ≤ _ := Rat.cast_le.mpr this
  have hqN : (0 : ℝ) ≤ ((nativeHeatQNGen ns : ℚ) : ℝ) := by
    exact_mod_cast (of_decide_eq_true hfr.qN_root).2.2.1
  have hgmeas : ∀ i, Measurable (g i) := fun i =>
    nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_measurable M m ns Ffam
      (nativeHeatTheta : ℝ) t i
  have hlaw : ∀ i, standardGaussianInfinitePi.map (fun ξ => g i ξ / σ) =
      gaussianReal 0 (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam
        (nativeHeatTheta : ℝ) t i) := fun i =>
    nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_law M m ns Ffam (nativeHeatTheta : ℝ) t i
  have hq : originCube 2 (m + 1 - 1) ∈ descendantsAtDepth (originCube 2 (m + 1)) 1 := by
    simpa only [Nat.cast_one] using originCube_mem_descendantsAtDepth' 2 (m + 1) 1
  have hshift : ∀ i, MeasurePreserving
      (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i)) μc μc := fun i =>
    ⟨Cutoff.measurable_translateCutoffSample _,
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M _⟩
  have hw := heatVHEATDrift_refined_weights
  -- the pointwise envelope
  have hpoint : ∀ᵐ z ∂μc.prod standardGaussianInfinitePi, ∀ i,
      heatRefinedTranslatedTrace M (m + 1) ns t (heatVHEATDriftRefinedShift m i) (g i) z ≤
        (Real.sqrt (nativeHeatStepFi ns M m t i z.1) + |g i z.2 / σ| *
          Real.sqrt (2 * ((3683 / 2500 : ℝ) + nativeHeatStepRi ns M m t i z.1))) ^ 2 := by
    rw [ae_all_iff]
    intro i
    have hae := heat_refined_observer_shear_trace_ae_le M h hM hg (m + 1 - 1) (m + 1) 1
      (by norm_num) hq ns hpast t ht.2.le
    have hmp : MeasurePreserving (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
        Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1)
        (μc.prod standardGaussianInfinitePi) μc :=
      (hshift i).comp (measurePreserving_fst (μ := μc) (ν := standardGaussianInfinitePi))
    filter_upwards [hmp.quasiMeasurePreserving.ae hae] with z hz
    exact hz (g i z.2)
  have hA0 : eLpNorm (fun ω => ∑ i : nativeHeatQ3RefinedCarrierIndex,
      heatVHEATDriftRefinedWeight * nativeHeatStepFi ns M m t i ω) 20 μc ≤
      ENNReal.ofReal (theta M * (nativeHeatY0Gen ns : ℝ)) := by
    have hfi : ∀ i, eLpNorm (nativeHeatStepFi ns M m t i) 20 μc ≤
        ENNReal.ofReal (theta M * (nativeHeatY0Gen ns : ℝ)) := by
      intro i
      have hΦ := (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives (m + 1 - 1) M.nu
        (Annealed.sigmaBar M (m + 1)) M.nu_pos
        (Annealed.sigmaBar_characterization M (m + 1)).1).1
      have hmeas0 : AEStronglyMeasurable (fun ω : Cutoff.CutoffSample 2 =>
          modelTraceObservable (m + 1 - 1) M.nu (Annealed.sigmaBar M (m + 1))
            (parentBoundaryObserverBandScalar (m + 1 - 1) (m + 1) ns t ω)) μc :=
        (hΦ.continuous.measurable.comp
          (parent_boundary_observer_band_scalar_measurable (m + 1 - 1) (m + 1) ns t)).aestronglyMeasurable
      have := eLpNorm_comp_measurePreserving (p := (20 : ℝ≥0∞)) hmeas0 (hshift i)
      exact this.le.trans (hchild t ht)
    have hp1 : (1 : ℝ≥0∞) ≤ 20 := by norm_num
    have h1 := eLpNorm_sum_le (μ := μc) (s := Finset.univ)
      (f := fun i ω => heatVHEATDriftRefinedWeight * nativeHeatStepFi ns M m t i ω) hp1
    have hsumeq : (fun ω => ∑ i : nativeHeatQ3RefinedCarrierIndex,
        heatVHEATDriftRefinedWeight * nativeHeatStepFi ns M m t i ω) =
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          (fun ω => heatVHEATDriftRefinedWeight * nativeHeatStepFi ns M m t i ω) := by
      funext ω; simp [Finset.sum_apply]
    rw [hsumeq]
    refine h1.trans ?_
    have h2 : ∀ i : nativeHeatQ3RefinedCarrierIndex,
        eLpNorm (fun ω => heatVHEATDriftRefinedWeight * nativeHeatStepFi ns M m t i ω) 20 μc ≤
          ENNReal.ofReal heatVHEATDriftRefinedWeight * ENNReal.ofReal (theta M * (nativeHeatY0Gen ns : ℝ)) := by
      intro i
      change eLpNorm (heatVHEATDriftRefinedWeight • nativeHeatStepFi ns M m t i) 20 μc ≤ _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hw.1]
      exact mul_le_mul' le_rfl (hfi i)
    refine (Finset.sum_le_sum fun i _ => h2 i).trans ?_
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw.1), hw.2]
    simp
  have hQ := nativeHeatStep_quad_L20_theta ns M h hM m hgen hfr hg hstate t ⟨ht.1.le, ht.2.le⟩
  have hGn : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      eLpNorm (fun ξ => (g i ξ / σ) ^ 2) 20 standardGaussianInfinitePi ≤
        ENNReal.ofReal ((theta M * (nativeHeatGenVariance ns : ℝ)) *
          ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ)) := by
    intro i
    have hG40 := nativeHeatStep_gaussian40_le standardGaussianInfinitePi
      (fun ξ => g i ξ / σ) ((hgmeas i).div_const _) _ (hlaw i)
    have hvar := nativeHeatStep_auxVariance_le_genVar_theta ns hgen M h hM hg m hstate t
      ⟨ht.1.le, ht.2.le⟩ i
    have hv0 : (0 : ℝ) ≤ ((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam
        (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) := NNReal.coe_nonneg _
    have hGm : AEStronglyMeasurable (fun ξ => g i ξ / σ) standardGaussianInfinitePi :=
      ((hgmeas i).div_const _).aestronglyMeasurable
    have habsm : AEStronglyMeasurable (fun ξ => |g i ξ / σ|) standardGaussianInfinitePi := by
      simpa only [Real.norm_eq_abs] using hGm.norm
    have hsq := nativeHeat_square_Lp standardGaussianInfinitePi (fun ξ => |g i ξ / σ|)
      habsm (fun ξ => abs_nonneg _) 20 (by norm_num)
    have hnormeq : eLpNorm (fun ξ => |g i ξ / σ|) (ENNReal.ofReal (2 * 20)) standardGaussianInfinitePi =
        eLpNorm (fun ξ => g i ξ / σ) (ENNReal.ofReal (2 * 20)) standardGaussianInfinitePi := by
      simpa only [Real.norm_eq_abs] using eLpNorm_norm (fun ξ => g i ξ / σ) (p := ENNReal.ofReal (2 * 20))
        (μ := standardGaussianInfinitePi) hGm
    have e20 : (20 : ℝ≥0∞) = ENNReal.ofReal 20 := by simp
    have hsq' : eLpNorm (fun ξ => (g i ξ / σ) ^ 2) (ENNReal.ofReal 20) standardGaussianInfinitePi =
        eLpNorm (fun ξ => g i ξ / σ) (ENNReal.ofReal (2 * 20)) standardGaussianInfinitePi ^ 2 := by
      have := hsq
      simp only [sq_abs] at this
      rw [hnormeq] at this
      exact this
    rw [e20, hsq']
    have hvg : ENNReal.ofReal (Real.sqrt (((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
        Ffam (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) *
        ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ))) ^ 2 =
        ENNReal.ofReal (((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
        Ffam (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) * ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ)) := by
      rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (mul_nonneg hv0 hgm0)]
    calc _ ≤ ENNReal.ofReal (Real.sqrt (((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
        Ffam (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) *
        ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ))) ^ 2 := pow_le_pow_left' hG40 2
      _ = _ := hvg
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hvar hgm0)
  have hRn : ∀ i, eLpNorm (nativeHeatStepRi ns M m t i) 20 μc ≤ ENNReal.ofReal (3 / 10 ^ 46 : ℝ) :=
    fun i => (nativeHeatStep_ri_facts ns M h hM m hg hpast t ht.2.le i).2.2
  have key := nativeHeatStep_avgAug_L20 (Ω := Cutoff.CutoffSample 2) (Ξ := ℕ → ℝ)
    (ι := nativeHeatQ3RefinedCarrierIndex) μc standardGaussianInfinitePi
    (fun _ => heatVHEATDriftRefinedWeight) (fun _ => hw.1) hw.2
    (fun i z => heatRefinedTranslatedTrace M (m + 1) ns t (heatVHEATDriftRefinedShift m i) (g i) z)
    (fun i ω => nativeHeatStepFi ns M m t i ω) (fun i ω => nativeHeatStepRi ns M m t i ω)
    (fun i ξ => g i ξ / σ) (3683 / 2500) (by norm_num)
    (fun i => (heat_refined_translated_trace_measurable_nonneg M (m + 1) ns t _ (g i)
      (hgmeas i)).1.aestronglyMeasurable)
    (fun i z => (heat_refined_translated_trace_measurable_nonneg M (m + 1) ns t _ (g i)
      (hgmeas i)).2 z)
    (fun i => (nativeHeatStep_fi_measurable ns M m t i).aestronglyMeasurable)
    (fun i ω => nativeHeatStep_fi_nonneg ns M m t i ω)
    (fun i => (nativeHeatStep_ri_facts ns M h hM m hg hpast t ht.2.le i).1.aestronglyMeasurable)
    (fun i ω => (nativeHeatStep_ri_facts ns M h hM m hg hpast t ht.2.le i).2.1 ω)
    (fun i => ((hgmeas i).div_const _).aestronglyMeasurable)
    hpoint (theta M * (nativeHeatY0Gen ns : ℝ)) (theta M * ((nativeHeatQNGen ns : ℚ) : ℝ)) (3 / 10 ^ 46)
    ((theta M * (nativeHeatGenVariance ns : ℝ)) * ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ))
    (mul_nonneg hτ0.le hy0) (mul_nonneg hτ0.le hqN) (by norm_num)
    (mul_nonneg (mul_nonneg hτ0.le hV0) hgm0) hA0 hQ hRn hGn
  -- identify the average norm
  have hAvg : (heatVHEATDriftRefinedAverageGen ns) M m t g =
      fun z => ∑ i : nativeHeatQ3RefinedCarrierIndex, heatVHEATDriftRefinedWeight *
        heatRefinedTranslatedTrace M (m + 1) ns t (heatVHEATDriftRefinedShift m i) (g i) z := by
    funext z; rfl
  have hyp : ((nativeHeatFramesGen ns).y : ℚ) =
      nativeUp ((nativeRootUp (nativeHeatY0Gen ns) +
        nativeRootUp (2 * nativeHeatB * nativeHeatQNGen ns +
          2 * nativeHeatEps * nativeHeatParametersData.gm.getD 20 0 *
            nativeHeatGenVariance ns)) ^ 2) := by
    simp [nativeHeatFramesGen, nativeHeatFrames, nativeHeatY0Gen]
  have hnu := (Rat.cast_le (K := ℝ)).2
    (nativeUp_ge ((nativeRootUp (nativeHeatY0Gen ns) +
      nativeRootUp (2 * nativeHeatB * nativeHeatQNGen ns +
        2 * nativeHeatEps * nativeHeatParametersData.gm.getD 20 0 *
          nativeHeatGenVariance ns)) ^ 2))
  rw [← hyp] at hnu
  push_cast at hnu
  have t1 : Real.sqrt ((nativeHeatY0Gen ns : ℚ) : ℝ) ≤ (nativeRootUp (nativeHeatY0Gen ns) : ℝ) :=
    nativeHeatStep_sqrt_le_rootUp _ hfr.y0_root
  have hle2 : 2 * (3683 / 2500 : ℝ) * ((nativeHeatQNGen ns : ℚ) : ℝ) +
      2 * (3 / 10 ^ 46 : ℝ) * ((nativeHeatGenVariance ns : ℝ) *
        ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ)) ≤
      (((2 * nativeHeatB * nativeHeatQNGen ns +
        2 * nativeHeatEps * nativeHeatParametersData.gm.getD 20 0 * nativeHeatGenVariance ns : ℚ)) : ℝ) := by
    push_cast
    have e1 := mul_le_mul_of_nonneg_right hB (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hqN)
    have e2 := mul_le_mul_of_nonneg_right hE (mul_nonneg hV0 hgm0)
    nlinarith [e1, e2]
  have t2 : Real.sqrt (2 * (3683 / 2500 : ℝ) * (theta M * ((nativeHeatQNGen ns : ℚ) : ℝ)) +
      2 * (3 / 10 ^ 46 : ℝ) * ((theta M * (nativeHeatGenVariance ns : ℝ)) *
        ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ))) ≤
      Real.sqrt (theta M) * (nativeRootUp (2 * nativeHeatB * nativeHeatQNGen ns +
        2 * nativeHeatEps * nativeHeatParametersData.gm.getD 20 0 * nativeHeatGenVariance ns) : ℝ) := by
    have hX : 2 * (3683 / 2500 : ℝ) * (theta M * ((nativeHeatQNGen ns : ℚ) : ℝ)) +
        2 * (3 / 10 ^ 46 : ℝ) * ((theta M * (nativeHeatGenVariance ns : ℝ)) *
          ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ)) =
        theta M * (2 * (3683 / 2500 : ℝ) * ((nativeHeatQNGen ns : ℚ) : ℝ) +
          2 * (3 / 10 ^ 46 : ℝ) * ((nativeHeatGenVariance ns : ℝ) *
            ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ))) := by ring
    rw [hX, Real.sqrt_mul hτ0.le]
    exact mul_le_mul_of_nonneg_left
      ((Real.sqrt_le_sqrt hle2).trans (nativeHeatStep_sqrt_le_rootUp _ hfr.yp_root))
      (Real.sqrt_nonneg _)
  have t1' : Real.sqrt (theta M * ((nativeHeatY0Gen ns : ℚ) : ℝ)) ≤
      Real.sqrt (theta M) * (nativeRootUp (nativeHeatY0Gen ns) : ℝ) := by
    rw [Real.sqrt_mul hτ0.le]
    exact mul_le_mul_of_nonneg_left t1 (Real.sqrt_nonneg _)
  have hs0 : 0 ≤ Real.sqrt (theta M * ((nativeHeatY0Gen ns : ℚ) : ℝ)) +
      Real.sqrt (2 * (3683 / 2500 : ℝ) * (theta M * ((nativeHeatQNGen ns : ℚ) : ℝ)) +
      2 * (3 / 10 ^ 46 : ℝ) * ((theta M * (nativeHeatGenVariance ns : ℝ)) *
        ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ))) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ hs0 (add_le_add t1' t2) 2
  have hsqθ : Real.sqrt (theta M) ^ 2 = theta M := Real.sq_sqrt hτ0.le
  have hfin : (nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m Ffam
      (nativeHeatTheta : ℝ) t ≤ theta M * ((nativeHeatFramesGen ns).y : ℝ) := by
    unfold nativeHeatQ3RefinedCarrierSourceAverageNormGen
    rw [hAvg]
    have hynn : (0 : ℝ) ≤ theta M * ((nativeHeatFramesGen ns).y : ℝ) :=
      mul_nonneg hτ0.le (by exact_mod_cast hnum.y_nonneg)
    refine ENNReal.toReal_le_of_le_ofReal hynn ?_
    refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    refine hsq.trans ?_
    calc (Real.sqrt (theta M) * (nativeRootUp (nativeHeatY0Gen ns) : ℝ) +
          Real.sqrt (theta M) * (nativeRootUp (2 * nativeHeatB * nativeHeatQNGen ns +
        2 * nativeHeatEps * nativeHeatParametersData.gm.getD 20 0 * nativeHeatGenVariance ns) : ℝ)) ^ 2
        = Real.sqrt (theta M) ^ 2 * ((nativeRootUp (nativeHeatY0Gen ns) : ℝ) +
          (nativeRootUp (2 * nativeHeatB * nativeHeatQNGen ns +
        2 * nativeHeatEps * nativeHeatParametersData.gm.getD 20 0 * nativeHeatGenVariance ns) : ℝ)) ^ 2 := by
          ring
      _ = theta M * ((nativeRootUp (nativeHeatY0Gen ns) : ℝ) +
          (nativeRootUp (2 * nativeHeatB * nativeHeatQNGen ns +
        2 * nativeHeatEps * nativeHeatParametersData.gm.getD 20 0 * nativeHeatGenVariance ns) : ℝ)) ^ 2 := by
          rw [hsqθ]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hτ0.le
        push_cast at hnu ⊢
        exact hnu
  exact hfin

end CapYTheta

end ASDExplicitGamma.Native

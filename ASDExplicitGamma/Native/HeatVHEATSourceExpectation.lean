/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Native.HeatVHEATSourcePointwise
public import ASDExplicitGamma.Native.HeatVHEATSourceDriftAssembly
public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaGeneratorBound
public import ASDExplicitGamma.Native.HeatVHEATRefinedFinalAssembly

/-! The source-carrier generator is integrable on the common cutoff/auxiliary
product law, and its scalar backward generator is exactly that expectation. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory Homogenization Gaussian
open ASDExplicitGamma.Gaussian Algsuperdiff.Section3 Numerics.Native
open scoped ENNReal NNReal
noncomputable section

local instance heatVHEATSourceExpectationIndexNeZero :
    NeZero (3 ^ 10 * 3 ^ 10) :=
  ⟨Nat.mul_ne_zero (pow_ne_zero 10 (by decide))
    (pow_ne_zero 10 (by decide))⟩

local instance heatVHEATSourceExpectationChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

local instance heatVHEATSourceExpectationChildCompact (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

private theorem add_le_add_left_of_le {a b c : ℝ} (h : b ≤ c) :
    a + b ≤ a + c := by linarith only [h]

/-- The cancelled source-carrier generator has every polynomial moment on the exact
cutoff/auxiliary product law used by the heat path. -/
theorem nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ t : ℝ) (hθ : 0 < θ) (k : ℕ) :
    Integrable
      (nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand M h hM m θ t k)
      (nativeHeatRemainderJointLaw M) := by
  classical
  let K := nativeHeatQ3RefinedCarrierDomain m
  let bands := nativeHeatQ3RefinedCarrierPhysicalShells m
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
    fun i => cubeSet (nativeHeatQ3RefinedCarrierChild m i)
  let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet _
  let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos _
  let σ : ℝ := Annealed.sigmaBar M (m + 1)
  let I := childConstantMap (fun i => closure (U i))
  let P₀ := nativeHeatQ3RefinedCarrierOldMap m
  let T₀ := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  let W := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
  let hW := nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m
  let L₀ := nativeHeatQ3RefinedCarrierSourceCenterMap m
  let P := P₀.comp T₀
  let L := L₀.comp T₀
  let S := I.comp L
  let Φ := childPower U hU hvol M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1 k
  let Ψ := cancelledGenerator W P L I Φ θ
  let μcut := (Cutoff.cutoffSampleLaw M).toMeasure
  let μjoint := nativeHeatRemainderJointLaw M
  letI : IsProbabilityMeasure μjoint :=
    inferInstanceAs (IsProbabilityMeasure
      ((Cutoff.cutoffSampleLaw M).toMeasure.prod standardGaussianInfinitePi))
  let field : Cutoff.CutoffSample 2 → C(K, ℝ) :=
    fun ω => olderField K (m + 1) ω + Real.sqrt t • modelBand K bands ω
  let base : Cutoff.CutoffSample 2 →
      (∀ i : nativeHeatQ3RefinedCarrierIndex,
        C(closure (U i), ℝ)) :=
    fun ω => P₀ (field ω)
  have hcompact : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K hcompact
  have hbands : ∀ d : Fin 9, m + 1 < bands d := by
    intro d
    simpa only [bands] using nativeHeatQ3RefinedCarrierBands_afterOldLabel m d
  have hbandLaw := nativeHeatQ3RefinedCarrierBandLaw M h hM m
  have hOldMeas : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      olderField K (m + 1) ω) := measurable_olderField K ell (m + 1) hK
  have hBandMeas : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      modelBand K bands ω) := measurable_modelBand K bands
  have hIndBand : (fun ω => olderField K (m + 1) ω) ⟂ᵢ[μcut]
      (fun ω => modelBand K bands ω) := by
    exact (indepFun_olderField_band K M ell (m + 1) hK bands hbands)
  have hOldMom : ∀ d : ℕ,
      Integrable (fun x : C(K, ℝ) => (1 + ‖x‖) ^ d)
        (μcut.map (olderField K (m + 1))) := by
    intro d
    exact (integrable_polynomial_olderFieldLaw K M ell (m + 1) hK) d
  have hFieldPowerMeas (d : ℕ) :
      Measurable (fun x : C(K, ℝ) => (1 + ‖x‖) ^ d) := by fun_prop
  have hFieldPowerGrowth (d : ℕ) : HasPolynomialGrowth
      (fun x : C(K, ℝ) => (1 + ‖x‖) ^ d) := by
    refine ⟨1, by norm_num, d, fun x => ?_⟩
    change ‖(1 + ‖x‖) ^ d‖ ≤ 1 * (1 + ‖x‖) ^ d
    calc
      ‖(1 + ‖x‖) ^ d‖ = (1 + ‖x‖) ^ d := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ 1 * (1 + ‖x‖) ^ d := by norm_num
  have hFieldMeas : Measurable field := by
    dsimp [field]
    exact hOldMeas.add (hBandMeas.const_smul (Real.sqrt t))
  have hFieldMom (d : ℕ) : Integrable (fun x : C(K, ℝ) => (1 + ‖x‖) ^ d)
      (μcut.map field) := by
    have hh := integral_independent_insertion
      (Ω := Cutoff.CutoffSample 2) (V := BandHilbert 9) (E := C(K, ℝ)) μcut
      (olderField K (m + 1)) (modelBand K bands) hOldMeas hBandMeas
      (indepFun_olderField_band K M ell (m + 1) hK bands hbands)
      (v := W) hW T₀ hbandLaw hOldMom
      (fun x : C(K, ℝ) => (1 + ‖x‖) ^ d)
      (hFieldPowerMeas d) (hFieldPowerGrowth d) t
    exact (integrable_map_measure (hFieldPowerMeas d).aestronglyMeasurable
      hFieldMeas.aemeasurable).mpr (by
        change Integrable (fun ω => (1 + ‖field ω‖) ^ d) μcut
        simpa [field] using hh.1)
  have hBaseLaw : μcut.map base = (μcut.map field).map P₀ := by
    change μcut.map (P₀ ∘ field) = _
    exact (Measure.map_map P₀.continuous.measurable hFieldMeas).symm
  have hBaseMom (d : ℕ) : Integrable (fun x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (U i), ℝ) => (1 + ‖x‖) ^ d) (μcut.map base) := by
    rw [hBaseLaw]
    exact polynomial_moments_map _ hFieldMom P₀ d
  have hΦ : HasPolynomiallyBoundedC2Derivatives Φ :=
    childPower_polynomial U hU hvol M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M (m + 1)).1 k
  have hPsum : Summable (fun j => ‖P (W j)‖ ^ 2) :=
    summable_sq_norm_map hW P
  have hLsum : Summable (fun j => ‖I (L (W j))‖ ^ 2) :=
    summable_sq_norm_map hW (I.comp L)
  have hcancel := generator_cancellation hW P L I hΦ.1 θ
  have hΨreg : Continuous Ψ ∧ HasPolynomialGrowth Ψ := by
    change Continuous (cancelledGenerator W P L I Φ θ) ∧
      HasPolynomialGrowth (cancelledGenerator W P L I Φ θ)
    rw [← hcancel]
    exact backwardGenerator_continuous_polynomial hΦ
      (fun j => P (W j)) (fun j => I (L (W j))) hPsum hLsum θ
  let Yaux : (Cutoff.CutoffSample 2 × (ℕ → ℝ)) →
      (∀ i : nativeHeatQ3RefinedCarrierIndex,
        C(closure (U i), ℝ)) :=
    fun z => gaussianSeriesLimitE hW S z.2
  have hBaseMeas : Measurable base := by
    dsimp [base]
    exact P₀.continuous.measurable.comp
      ((measurable_olderField K ell (m + 1) hK).add
        ((measurable_modelBand K bands).const_smul (Real.sqrt t)))
  have hbaseJointMeas : Measurable
      (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) => base z.1) :=
    hBaseMeas.comp measurable_fst
  have hYauxMeas : Measurable Yaux := by
    exact (stronglyMeasurable_gaussianSeriesLimitE hW S).measurable.comp measurable_snd
  have hIndProd : (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) => base z.1) ⟂ᵢ[μjoint] Yaux := by
    have hfst : (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) => z.1) ⟂ᵢ[μjoint]
        (fun z => z.2) := indepFun_prod measurable_id measurable_id
    exact hfst.comp hBaseMeas (stronglyMeasurable_gaussianSeriesLimitE hW S).measurable
  have hMapBase : μjoint.map (fun z => base z.1) = μcut.map base := by
    change μjoint.map (base ∘ Prod.fst) = μcut.map base
    rw [← Measure.map_map hBaseMeas measurable_fst]
    simp [μjoint, μcut, nativeHeatRemainderJointLaw]
  have hBaseMomJoint (d : ℕ) :
      Integrable (fun x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
        C(closure (U i), ℝ) => (1 + ‖x‖) ^ d)
        (μjoint.map (fun z => base z.1)) := by
    rw [hMapBase]
    exact hBaseMom d
  have hAuxLaw : μjoint.map Yaux =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hW S) := by
    rw [show Yaux = (gaussianSeriesLimitE hW S) ∘ Prod.snd by rfl,
      ← Measure.map_map (stronglyMeasurable_gaussianSeriesLimitE hW S).measurable
        measurable_snd]
    simp [μjoint, nativeHeatRemainderJointLaw]
  have hGenInt := integral_independent_insertion μjoint
    (fun z => base z.1) Yaux hbaseJointMeas hYauxMeas hIndProd
    hW S hAuxLaw hBaseMomJoint Ψ hΨreg.1.measurable hΨreg.2
    ((1 + θ) * (1 - t))
  let c (ξ : ℕ → ℝ) := fun i =>
    nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t i ξ
  have hcenter (ξ : ℕ → ℝ) :
      I (c ξ) = Real.sqrt ((1 + θ) * (1 - t)) •
        gaussianSeriesLimitE hW S ξ := by
    ext i x
    have haux := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_eq_backwardCenterInput
      M h hM m θ t i ξ
    simpa only [I, c, S, L, childConstantMap, gaussianSeriesLimitE,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
      Pi.smul_apply, ContinuousMap.one_apply, ContinuousMap.smul_apply,
      smul_eq_mul, mul_one] using haux
  have hEq :
      nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand M h hM m θ t k =
        fun z => Ψ (base z.1 +
          Real.sqrt ((1 + θ) * (1 - t)) • gaussianSeriesLimitE hW S z.2) := by
    funext z
    change cancelledGenerator W P L I Φ θ
        (base z.1 + I (c z.2)) =
      Ψ (base z.1 + Real.sqrt ((1 + θ) * (1 - t)) •
        gaussianSeriesLimitE hW S z.2)
    rw [hcenter]
  rw [hEq]
  exact hGenInt.1

/-- The source scalar generator is the expectation of its actual pointwise
cancelled-generator integrand under the original joint law. -/
theorem nativeHeatQ3RefinedCarrierSourceMomentGenerator_eq_integral
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ t : ℝ) (hθ : 0 < θ) (k : ℕ) (hk : 1 ≤ k) :
    nativeHeatQ3RefinedCarrierSourceMomentGenerator M h hM m k θ t =
      ∫ z, nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
        M h hM m θ t k z ∂nativeHeatRemainderJointLaw M := by
  classical
  let K := nativeHeatQ3RefinedCarrierDomain m
  let bands := nativeHeatQ3RefinedCarrierPhysicalShells m
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
    fun i => cubeSet (nativeHeatQ3RefinedCarrierChild m i)
  let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet _
  let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos _
  let σ : ℝ := Annealed.sigmaBar M (m + 1)
  let I := childConstantMap (fun i => closure (U i))
  let T₀ := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  let W := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
  let hW := nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m
  let L₀ := nativeHeatQ3RefinedCarrierSourceCenterMap m
  let P₀ := nativeHeatQ3RefinedCarrierOldMap m
  let P := P₀.comp T₀
  let L := L₀.comp T₀
  let Φ := childPower U hU hvol M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1 k
  let Ψ := cancelledGenerator W P L I Φ θ
  have hk0 : k ≠ 0 := by omega
  let f : (Cutoff.CutoffSample 2 × (ℕ → ℝ)) → ℝ :=
    nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand M h hM m θ t k
  have hf : Integrable f (nativeHeatRemainderJointLaw M) :=
    nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand_integrable
      M h hM m θ t hθ k
  have hΦ : HasPolynomiallyBoundedC2Derivatives Φ :=
    childPower_polynomial U hU hvol M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M (m + 1)).1 k
  have hcancel := generator_cancellation hW P L I hΦ.1 θ
  have hTsum : Summable (fun j => ‖T₀ (W j)‖ ^ 2) :=
    summable_sq_norm_map hW T₀
  have hcancelScalar := generator_cancellation hTsum P₀ L₀ I hΦ.1 θ
  dsimp only [nativeHeatQ3RefinedCarrierSourceMomentGenerator,
    nativeHeatChildBandMomentGenerator]
  simp only [if_neg hk0]
  let S := (I.comp L₀).comp T₀
  let base : Cutoff.CutoffSample 2 → (∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (U i), ℝ)) := fun ω => P₀ (olderField K (m + 1) ω +
        Real.sqrt t • modelBand K bands ω)
  have hcenter (ξ : ℕ → ℝ) :
      I (fun i => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t i ξ) =
        Real.sqrt ((1 + θ) * (1 - t)) • gaussianSeriesLimitE hW S ξ := by
    ext i x
    have haux := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_eq_backwardCenterInput
      M h hM m θ t i ξ
    simpa only [I, S, childConstantMap, gaussianSeriesLimitE,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
      Pi.smul_apply, ContinuousMap.one_apply, ContinuousMap.smul_apply,
      smul_eq_mul, mul_one] using haux
  have hΨeq (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (U i), ℝ)) :
      Ψ x = cancelledGenerator (fun j => T₀ (W j)) P₀ L₀ I Φ θ x := by
    calc
      Ψ x = backwardGenerator Φ (fun j => P (W j))
          (fun j => I (L (W j))) θ x := (congrFun hcancel x).symm
      _ = backwardGenerator Φ (fun j => P₀ (T₀ (W j)))
          (fun j => I (L₀ (T₀ (W j)))) θ x := by
            congr 2 <;> funext j <;> simp [P, L]
      _ = cancelledGenerator (fun j => T₀ (W j)) P₀ L₀ I Φ θ x :=
            congrFun hcancelScalar x
  have hbasePoint (ω : Cutoff.CutoffSample 2) :
      nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t ω = base ω := by
    change P₀ (olderField K (m + 1) ω + Real.sqrt t • modelBand K bands ω) = _
    rfl
  have hbaseLinear (ω : Cutoff.CutoffSample 2) :
      P₀ (olderField K (m + 1) ω) + Real.sqrt t • P₀ (modelBand K bands ω) =
        base ω := by
    calc
      P₀ (olderField K (m + 1) ω) + Real.sqrt t • P₀ (modelBand K bands ω) =
          P₀ (olderField K (m + 1) ω + Real.sqrt t • modelBand K bands ω) := by
        rw [← map_smul, ← map_add]
      _ = base ω := rfl
  have hpoint (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : f z =
      cancelledGenerator (fun j => T₀ (W j)) P₀ L₀ I Φ θ
        (base z.1 + Real.sqrt ((1 + θ) * (1 - t)) •
          gaussianSeriesLimitE hW S z.2) := by
    change Ψ (nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 + I (fun i =>
      nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t i z.2)) = _
    rw [hbasePoint]
    rw [hΨeq, hcenter]
  let G := cancelledGenerator (fun j => T₀ (W j)) P₀ L₀ I Φ θ
  let F : (Cutoff.CutoffSample 2 × (ℕ → ℝ)) → ℝ := fun z =>
    G (base z.1 + Real.sqrt ((1 + θ) * (1 - t)) •
      gaussianSeriesLimitE hW S z.2)
  have hF : Integrable F (nativeHeatRemainderJointLaw M) := by
    have heq : f = F := funext hpoint
    rw [← heq]
    exact hf
  change bandModelBackwardAverage K M (m + 1) bands P₀ hW
      ((I.comp L₀).comp T₀) G θ t =
        ∫ z, f z ∂nativeHeatRemainderJointLaw M
  calc
    bandModelBackwardAverage K M (m + 1) bands P₀ hW
        ((I.comp L₀).comp T₀) G θ t =
        ∫ z, F z ∂nativeHeatRemainderJointLaw M := by
      unfold bandModelBackwardAverage bandModelAverage backwardTest gaussianSeriesHeatAverage
      simp only [nativeHeatRemainderJointLaw]
      rw [integral_prod _ hF]
      apply integral_congr_ae
      filter_upwards [] with ω
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ξ => by
        simp only [F, G, gaussianSeriesHeatArgument]
        rw [← hbaseLinear ω]
        )
    _ = ∫ z, f z ∂nativeHeatRemainderJointLaw M := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hpoint z).symm)

local instance heatVHEATSourceMomentIndexNeZero :
    NeZero (3 ^ 10 * 3 ^ 10) := ⟨by norm_num⟩

local instance heatVHEATSourceMomentChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn
      (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

local instance heatVHEATSourceMomentChildCompact (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

/-- The scalar moment on the refined finite-band path is the moment of the
actual correlated child-trace average, with both noises retained on the
product law. -/
theorem nativeHeatQ3RefinedCarrierSourceMoment_eq_physicalAverage_integral
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (θ t : ℝ) (hθ : 0 < θ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20) :
    nativeHeatQ3RefinedCarrierSourceMoment M h hM m k θ t =
      ∫ z, (heatVHEATDriftRefinedPhysicalAverage M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z) ^ k
        ∂nativeHeatRemainderJointLaw M := by
  classical
  let K := nativeHeatQ3RefinedCarrierDomain m
  let bands := nativeHeatQ3RefinedCarrierPhysicalShells m
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
    fun i => cubeSet (nativeHeatQ3RefinedCarrierChild m i)
  let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet _
  let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos _
  let σ : ℝ := Annealed.sigmaBar M (m + 1)
  let P₀ := nativeHeatQ3RefinedCarrierOldMap m
  let L₀ := nativeHeatQ3RefinedCarrierSourceCenterMap m
  let T₀ := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  let W := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
  let hW := nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m
  let g := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t
  let A := heatVHEATDriftRefinedPhysicalAverage M m t g
  let μ := nativeHeatRemainderJointLaw M
  let μcut := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := heatVHEATDriftSourceXExtended Finset.univ M (m + 1) t
    (heatVHEATDriftRefinedShift m) g
  letI : IsProbabilityMeasure μ := inferInstanceAs
    (IsProbabilityMeasure ((Cutoff.cutoffSampleLaw M).toMeasure.prod standardGaussianInfinitePi))
  have hcompact : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K hcompact
  have hbands : ∀ d : Fin 9, m + 1 < bands d := by
    intro d
    simpa only [bands] using nativeHeatQ3RefinedCarrierBands_afterOldLabel m d
  have hgm : ∀ i : nativeHeatQ3RefinedCarrierIndex, Measurable (g i) := by
    intro i
    exact nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_measurable M h hM m θ t i
  have hlaw : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      standardGaussianInfinitePi.map
        (fun ξ => g i ξ / (Annealed.sigmaBar M (m + 1) : ℝ)) =
        gaussianReal 0 (nativeHeatQ3RefinedCarrierSourceAuxCenterVariance M h hM m θ t i) := by
    intro i
    exact nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_law M h hM m θ t i
  let v := nativeHeatQ3RefinedCarrierSourceAuxCenterVariance M h hM m θ t
  have hnorms := heatVHEATDrift_source_norms M h hM hg (m + 1) hpast t ht.2.le
    Finset.univ (fun _ => heatVHEATDriftRefinedWeight)
    (fun _ _ => heatVHEATDrift_refined_weights.1)
    heatVHEATDrift_refined_weights.2
    (heatVHEATDriftRefinedShift m) g (fun i _ => hgm i) v
    (fun i _ => hlaw i)
  have hAvgEq : A = heatVHEATDriftRefinedAverage M m t g := by
    funext z
    exact (heatVHEATDrift_refined_physical_family_eq M h m t 0 g z).1
  have hA0 : ∀ z, 0 ≤ A z := by
    intro z
    rw [hAvgEq]
    unfold heatVHEATDriftRefinedAverage heatVHEATDriftRefinedWeight
      heatRefinedTraceAverage
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg heatVHEATDrift_refined_weights.1
      ((heat_refined_translated_trace_measurable_nonneg M (m + 1) 9 t
        (heatVHEATDriftRefinedShift m i) (g i) (hgm i)).2 z)
  have hAmeas : Measurable A := by
    rw [hAvgEq]
    unfold heatVHEATDriftRefinedAverage heatVHEATDriftRefinedWeight
      heatRefinedTraceAverage
    exact Finset.measurable_sum Finset.univ (fun i hi =>
      ((heat_refined_translated_trace_measurable_nonneg M (m + 1) 9 t
        (heatVHEATDriftRefinedShift m i) (g i) (hgm i)).1).const_mul
        ((9 ^ 10 : ℝ)⁻¹))
  have hA20 : eLpNorm A 20 μ ≤ ENNReal.ofReal X.toReal := by
    rw [hAvgEq]
    simpa [X, heatVHEATDriftRefinedAverage] using hnorms.2.2.2.1
  have hMem20 : MemLp A 20 μ := by
    rw [memLp_iff]
    exact hA20.trans_lt ENNReal.ofReal_lt_top
  have hMemK : MemLp A k μ :=
    hMem20.mono_exponent (by exact_mod_cast hk20)
  have hAPowInt : Integrable (fun z => A z ^ k) μ := by
    have hh := hMemK.integrable_norm_pow (p := k) (by omega : k ≠ 0)
    convert hh using 1
    ext z
    rw [Real.norm_eq_abs, abs_of_nonneg (hA0 z)]
  have hProd :
      (∫ z, A z ^ k ∂μ) =
        ∫ ω, ∫ ξ, A (ω, ξ) ^ k ∂standardGaussianInfinitePi ∂μcut := by
    dsimp [μ, nativeHeatRemainderJointLaw]
    exact integral_prod _ hAPowInt
  have hback := bandModelChildBackwardAverage_eq U hU hvol M.nu σ
    M.nu_pos (Annealed.sigmaBar_characterization M (m + 1)).1 k K M (m + 1)
    bands P₀ L₀ hW T₀ θ t
  have hmoment : nativeHeatQ3RefinedCarrierSourceMoment M h hM m k θ t =
      ∫ ω, ∫ ξ, childW U hU hvol M.nu σ M.nu_pos
        (Annealed.sigmaBar_characterization M (m + 1)).1 k
        (P₀ (olderField K (m + 1) ω + Real.sqrt t • modelBand K bands ω))
        (Real.sqrt ((1 + θ) * (1 - t)) •
          L₀ (gaussianSeriesLimitE hW T₀ ξ))
        ∂standardGaussianInfinitePi ∂μcut := by
    simpa only [nativeHeatQ3RefinedCarrierSourceMoment,
      nativeHeatChildBandMoment, U, hU, hvol, σ, P₀, L₀, T₀, W, hW,
      K, bands] using hback
  have hpoint (ω : Cutoff.CutoffSample 2) (ξ : ℕ → ℝ) :
      childW U hU hvol M.nu σ M.nu_pos
          (Annealed.sigmaBar_characterization M (m + 1)).1 k
          (P₀ (olderField K (m + 1) ω +
            Real.sqrt t • modelBand K bands ω))
          (Real.sqrt ((1 + θ) * (1 - t)) •
            L₀ (gaussianSeriesLimitE hW T₀ ξ)) = A (ω, ξ) ^ k := by
    have hcenter (i : nativeHeatQ3RefinedCarrierIndex) :
        g i ξ = Real.sqrt ((1 + θ) * (1 - t)) *
          L₀ (gaussianSeriesLimitE hW T₀ ξ) i := by
      exact nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_eq_backwardCenterInput
        M h hM m θ t i ξ
    have hfields :
        (fun i => P₀ (olderField K (m + 1) ω +
            Real.sqrt t • modelBand K bands ω) i +
          ContinuousMap.const _
            (Real.sqrt ((1 + θ) * (1 - t)) *
              L₀ (gaussianSeriesLimitE hW T₀ ξ) i)) =
        (fun i => heatVHEATDriftRefinedChildField m t g (ω, ξ) i) := by
      funext i
      rw [← hcenter i]
      rfl
    let base := P₀ (olderField K (m + 1) ω +
      Real.sqrt t • modelBand K bands ω)
    let u := Real.sqrt ((1 + θ) * (1 - t)) •
      L₀ (gaussianSeriesLimitE hW T₀ ξ)
    have hvec : base + childConstantMap (fun i => closure (U i)) u =
        (fun i => heatVHEATDriftRefinedChildField m t g (ω, ξ) i) := by
      have hconst (i : nativeHeatQ3RefinedCarrierIndex) :
          (childConstantMap (fun j => closure (U j)) u) i =
            ContinuousMap.const _ (u i) := by
        ext y
        simp [childConstantMap]
      funext i
      change base i + (childConstantMap (fun j => closure (U j)) u) i = _
      rw [hconst i]
      have hi := congrFun hfields i
      simpa only [base, u, Pi.smul_apply, smul_eq_mul] using hi
    have hmean :
        childMeanTrace U hU hvol M.nu σ M.nu_pos
            (Annealed.sigmaBar_characterization M (m + 1)).1 (base +
              childConstantMap (fun i => closure (U i)) u) = A (ω, ξ) := by
      calc
        _ = childMeanTrace U hU hvol M.nu σ M.nu_pos
            (Annealed.sigmaBar_characterization M (m + 1)).1
            (fun i => heatVHEATDriftRefinedChildField m t g (ω, ξ) i) := by
              rw [hvec]
        _ = A (ω, ξ) := by
          simpa only [A, U, hU, hvol, σ] using
            (nativeHeatQ3RefinedCarrierPhysicalAverage_eq_childMeanTrace
              M m t g (ω, ξ)).symm
    unfold childW childPower
    rw [hmean]
  calc
    nativeHeatQ3RefinedCarrierSourceMoment M h hM m k θ t =
        ∫ ω, ∫ ξ, childW U hU hvol M.nu σ M.nu_pos
          (Annealed.sigmaBar_characterization M (m + 1)).1 k
          (P₀ (olderField K (m + 1) ω + Real.sqrt t • modelBand K bands ω))
          (Real.sqrt ((1 + θ) * (1 - t)) •
            L₀ (gaussianSeriesLimitE hW T₀ ξ))
          ∂standardGaussianInfinitePi ∂μcut := hmoment
    _ = ∫ ω, ∫ ξ, A (ω, ξ) ^ k ∂standardGaussianInfinitePi ∂μcut := by
      apply integral_congr_ae
      filter_upwards [] with ω
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => hpoint ω ξ
    _ = ∫ z, A z ^ k ∂μ := hProd.symm

/-- The coefficient-four VHEAT expectation row on the source carrier.
The individual trace cap `X`, the average cap `Y`, and the raw envelope cap
`F` are independent inputs. In the bounded Hölder term, `Y` is the L20 cap
of the actual source-carrier spatial average. -/
theorem nativeHeatQ3RefinedCarrierGeneratorBound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (X Y F : ℝ)
    (hXcap : (heatVHEATDriftRefinedPhysicalXExtended M m t
      (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m
        (nativeHeatTheta : ℝ) t)).toReal ≤ X)
    (hYcap : nativeHeatQ3RefinedCarrierSourceAverageNorm M h hM m
      (nativeHeatTheta : ℝ) t ≤ Y)
    (hFcap : heatRefinedRawEnvelope 9
      (heatVHEATDriftAuxVariance Finset.univ
        (nativeHeatQ3RefinedCarrierSourceAuxCenterVariance M h hM m
          (nativeHeatTheta : ℝ) t)) ≤ F) :
    nativeHeatQ3RefinedCarrierSourceMomentGenerator M h hM m k
        (nativeHeatTheta : ℝ) t ≤
      (k : ℝ) * heatVHEATDriftE9 M *
        (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
          (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) *
        (nativeHeatQ3RefinedCarrierSourceMoment M h hM m k
            (nativeHeatTheta : ℝ) t +
          4 * nativeHeatQ3RefinedCarrierSourceMoment M h hM m (k - 1)
            (nativeHeatTheta : ℝ) t) +
      nativeHeatVHEATErrorEk k 20 (heatVHEATDriftE9 M)
        (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
        (nativeHeatTheta : ℝ) (3683 / 2500 : ℝ) X Y
        (3 / 10 ^ 46 : ℝ) F := by
  classical
  let θ : ℝ := nativeHeatTheta
  let μ := nativeHeatRemainderJointLaw M
  let g := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t
  have hgCanonical : g =
      nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t := rfl
  let v := nativeHeatQ3RefinedCarrierSourceAuxCenterVariance M h hM m θ t
  let A := heatVHEATDriftRefinedPhysicalAverage M m t g
  let X₀ := (heatVHEATDriftRefinedPhysicalXExtended M m t g).toReal
  let F₀ := heatRefinedRawEnvelope 9 (heatVHEATDriftAuxVariance Finset.univ v)
  let b : ℝ := 3683 / 2500
  let ε : ℝ := 3 / 10 ^ 46
  letI : IsProbabilityMeasure μ := inferInstanceAs
    (IsProbabilityMeasure ((Cutoff.cutoffSampleLaw M).toMeasure.prod standardGaussianInfinitePi))
  have hθ : 0 < θ := by dsimp [θ]; norm_num [nativeHeatTheta]
  have hX : 0 ≤ X := (ENNReal.toReal_nonneg).trans hXcap
  have hY : 0 ≤ Y := (ENNReal.toReal_nonneg).trans hYcap
  have hF₀nonneg : 0 ≤ F₀ := by dsimp [F₀, heatRefinedRawEnvelope]; exact sq_nonneg _
  have hF : 0 ≤ F := le_trans hF₀nonneg hFcap
  have hX₀nonneg : 0 ≤ X₀ := ENNReal.toReal_nonneg
  have hXsourceEq :
      (heatVHEATDriftSourceXExtended Finset.univ M (m + 1) t
        (heatVHEATDriftRefinedShift m) g).toReal = X₀ := by
    have hnorm := congrArg ENNReal.toReal
      (heatVHEATDrift_refined_physical_norm_eq M m t g)
    simpa only [X₀] using hnorm.symm
  have hFsourceEq :
      heatRefinedRawEnvelope 9
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVariance M h hM m θ t)) = F₀ := rfl
  have he9 : 0 ≤ heatVHEATDriftE9 M := by
    unfold heatVHEATDriftE9
    exact mul_nonneg (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hK : 0 ≤ (nativeHeatK : ℝ) := by norm_num [nativeHeatK]
  have hM0 : 0 ≤ (nativeHeatM : ℝ) := by norm_num [nativeHeatM]
  have hSB : 0 ≤ (nativeHeatSB : ℝ) := by norm_num [nativeHeatSB]
  have hb : 0 ≤ b := by dsimp [b]; norm_num
  have hgmeas : ∀ i : nativeHeatQ3RefinedCarrierIndex, Measurable (g i) := by
    intro i
    exact nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_measurable
      M h hM m θ t i
  have hglaw : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      standardGaussianInfinitePi.map
        (fun ξ => g i ξ / (Annealed.sigmaBar M (m + 1) : ℝ)) =
        gaussianReal 0 (v i) := by
    intro i
    exact nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_law
      M h hM m θ t i
  have hdrift := nativeHeatQ3RefinedCarrierSourceDriftExpectation
    M h hM hg m hpast hstate θ t ⟨ht.1.le, ht.2.le⟩ k hk hk20
  have hnorms := heatVHEATDrift_source_norms M h hM hg (m + 1) hpast t
    ht.2.le Finset.univ (fun _ => heatVHEATDriftRefinedWeight)
    (fun _ _ => heatVHEATDrift_refined_weights.1)
    heatVHEATDrift_refined_weights.2 (heatVHEATDriftRefinedShift m)
    g (fun _ _ => hgmeas _) v (fun _ _ => hglaw _)
  have hAvgEq : A = heatVHEATDriftRefinedAverage M m t g := by
    funext z
    exact (heatVHEATDrift_refined_physical_family_eq M h m t 0 g z).1
  have hTraceEq (i : nativeHeatQ3RefinedCarrierIndex) :
      (fun z => heatVHEATDriftRefinedPhysicalTrace M m t g z i) =
        heatRefinedTranslatedTrace M (m + 1) 9 t
          (heatVHEATDriftRefinedShift m i) (g i) := by
    funext z
    exact heatVHEATDrift_refined_physical_trace_eq_of_observer
      M m t g z i
      (heatVHEATDrift_refined_child_observer M m t g z i)
  have hTraceProperties (i : nativeHeatQ3RefinedCarrierIndex) :
      Measurable (heatRefinedTranslatedTrace M (m + 1) 9 t
        (heatVHEATDriftRefinedShift m i) (g i)) ∧
        ∀ z, 0 ≤ heatRefinedTranslatedTrace M (m + 1) 9 t
          (heatVHEATDriftRefinedShift m i) (g i) z := by
    have hh := heat_refined_translated_trace_measurable_nonneg M (m + 1) 9 t
      (heatVHEATDriftRefinedShift m i) (g i) (hgmeas i)
    exact hh
  have hAmeas : Measurable A := by
    rw [hAvgEq]
    unfold heatVHEATDriftRefinedAverage heatRefinedTraceAverage
    exact Finset.measurable_sum Finset.univ (fun i hi =>
      (hTraceProperties i).1.const_mul heatVHEATDriftRefinedWeight)
  have hA0 : ∀ z, 0 ≤ A z := by
    intro z
    rw [hAvgEq]
    unfold heatVHEATDriftRefinedAverage heatRefinedTraceAverage
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg heatVHEATDrift_refined_weights.1
      ((hTraceProperties i).2 z)
  have hX₀cap : X₀ ≤ X := by
    calc
      X₀ = (heatVHEATDriftRefinedPhysicalXExtended M m t g).toReal := rfl
      _ ≤ X := hXcap
  have hA20 : eLpNorm A 20 μ ≤ ENNReal.ofReal X₀ := by
    have hXeq := heatVHEATDrift_refined_physical_norm_eq M m t g
    have hXreal : X₀ =
        (heatVHEATDriftSourceXExtended Finset.univ M (m + 1) t
          (heatVHEATDriftRefinedShift m) g).toReal := by
      change (heatVHEATDriftRefinedPhysicalXExtended M m t g).toReal = _
      exact congrArg ENNReal.toReal hXeq
    have hh := hnorms.2.2.2.1
    rw [← hXreal] at hh
    rw [hAvgEq]
    exact hh
  have hAX20 := hA20
  have hT20 (i : nativeHeatQ3RefinedCarrierIndex) :
      eLpNorm (heatVHEATDriftRefinedPhysicalTrace M m t g · i) 20 μ ≤
        ENNReal.ofReal X₀ := by
    have hh := hnorms.2.2.1 i (Finset.mem_univ i)
    have hXeq := heatVHEATDrift_refined_physical_norm_eq M m t g
    have hXreal : X₀ =
        (heatVHEATDriftSourceXExtended Finset.univ M (m + 1) t
          (heatVHEATDriftRefinedShift m) g).toReal := by
      change (heatVHEATDriftRefinedPhysicalXExtended M m t g).toReal = _
      exact congrArg ENNReal.toReal hXeq
    rw [← hXreal] at hh
    rw [hTraceEq i]
    exact hh
  have hYavg : eLpNorm A 20 μ ≤ ENNReal.ofReal Y := by
    have hYreal : (eLpNorm A 20 μ).toReal ≤ Y := by
      change (eLpNorm (heatVHEATDriftRefinedAverage M m t g) 20 μ).toReal ≤ Y at hYcap
      rw [← hAvgEq] at hYcap
      exact hYcap
    have hfinite : eLpNorm A 20 μ < ⊤ :=
      lt_of_le_of_lt hA20 (by simp : ENNReal.ofReal X₀ < ⊤)
    apply (ENNReal.toReal_le_toReal hfinite.ne ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hY]
    exact hYreal
  have hA128 : eLpNorm A 128 μ ≤ ENNReal.ofReal F₀ := by
    have hh := hnorms.2.2.2.2.2
    rw [hAvgEq]
    exact hh
  have hT128 (i : nativeHeatQ3RefinedCarrierIndex) :
      eLpNorm (heatVHEATDriftRefinedPhysicalTrace M m t g · i) 128 μ ≤
        ENNReal.ofReal F₀ := by
    have hh := hnorms.2.2.2.2.1 i (Finset.mem_univ i)
    rw [hTraceEq i]
    exact hh
  have hRmeas (i : nativeHeatQ3RefinedCarrierIndex) :
      Measurable (heatRefinedTranslatedRare M (m + 1) 9 t
        (heatVHEATDriftRefinedShift m i)) :=
    (heat_refined_translated_rare_profiles M h hM hg (m + 1) 9 hpast t
      ht.2.le (heatVHEATDriftRefinedShift m i)).1
  have hR0 (i : nativeHeatQ3RefinedCarrierIndex) (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) :
      0 ≤ heatRefinedTranslatedRare M (m + 1) 9 t
        (heatVHEATDriftRefinedShift m i) z :=
    (heat_refined_translated_rare_profiles M h hM hg (m + 1) 9 hpast t
      ht.2.le (heatVHEATDriftRefinedShift m i)).2.1 z
  have hR128 (i : nativeHeatQ3RefinedCarrierIndex) :
      eLpNorm (heatRefinedTranslatedRare M (m + 1) 9 t
        (heatVHEATDriftRefinedShift m i)) 128 μ ≤
        ENNReal.ofReal (3 / 10 ^ 46 : ℝ) := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (128 : ℝ≥0∞) ≠ 0) (by norm_num)
      (hRmeas i).aestronglyMeasurable]
    exact (heat_refined_translated_rare_profiles M h hM hg (m + 1) 9 hpast t
      ht.2.le (heatVHEATDriftRefinedShift m i)).2.2
  have havg : ∀ z, A z = ∑ i ∈ (Finset.univ : Finset nativeHeatQ3RefinedCarrierIndex),
      heatVHEATDriftRefinedWeight *
        heatVHEATDriftRefinedPhysicalTrace M m t g z i := by
    intro z
    rw [hAvgEq]
    unfold heatVHEATDriftRefinedAverage heatRefinedTraceAverage
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hTraceEq i]
  have hRowsAE := nativeHeatQ3RefinedCarrierSourceRows_le_correlatedBank
    M h hM hg m hpast hstate t ht.2.le g
  have hRowsFields : ∀ z,
      nativeHeatQ3RefinedCarrierSourceRowsForFields M h m
        (fun i => nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 i +
          childConstantMap
            (fun j => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)))
            (fun j => g j z.2) i) =
      nativeHeatQ3RefinedCarrierSourceRows M h m t g z := by
    intro z
    change nativeHeatQ3RefinedCarrierSourceRowsForFields M h m
        (fun i => nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 i +
          childConstantMap
            (fun j => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)))
            (fun j => g j z.2) i) =
      nativeHeatQ3RefinedCarrierSourceRowsForFields M h m
        (fun i => heatVHEATDriftRefinedChildField m t g z i)
    apply congrArg (nativeHeatQ3RefinedCarrierSourceRowsForFields M h m)
    funext i
    ext x
    simp [nativeHeatQ3RefinedCarrierPhysicalBaseChildren,
      heatVHEATDriftRefinedChildField, childConstantMap, g]
  have hWeightEq : heatVHEATDriftRefinedWeight =
      ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹) := by
    unfold heatVHEATDriftRefinedWeight
    rw [nativeHeatQ3RefinedCarrierIndex_card]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hRowsAE' : ∀ᵐ z ∂μ,
      nativeHeatQ3RefinedCarrierSourceRowsForFields M h m
          (fun i => nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 i +
            childConstantMap
              (fun j => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)))
              (fun j => g j z.2) i) ≤
        4 * heatVHEATDriftE9 M * (nativeHeatSB : ℝ) *
          (∑ i ∈ (Finset.univ : Finset nativeHeatQ3RefinedCarrierIndex),
            heatVHEATDriftRefinedWeight *
              ((b + heatRefinedTranslatedRare M (m + 1) 9 t
                  (heatVHEATDriftRefinedShift m i) z) ^ 2 *
                heatVHEATDriftRefinedPhysicalTrace M m t g z i *
                  (heatVHEATDriftRefinedPhysicalTrace M m t g z i + 4))) := by
    filter_upwards [hRowsAE] with z hz
    rw [hRowsFields z]
    have hsum :
        ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
          ∑ i : nativeHeatQ3RefinedCarrierIndex,
            (3683 / 2500 + heatRefinedTranslatedRare M (m + 1) 9 t
              (heatVHEATDriftRefinedShift m i) z) ^ 2 *
              heatVHEATDriftRefinedPhysicalTrace M m t g z i *
                (heatVHEATDriftRefinedPhysicalTrace M m t g z i + 4)) =
        ∑ i ∈ (Finset.univ : Finset nativeHeatQ3RefinedCarrierIndex),
          heatVHEATDriftRefinedWeight *
            ((b + heatRefinedTranslatedRare M (m + 1) 9 t
                (heatVHEATDriftRefinedShift m i) z) ^ 2 *
              heatVHEATDriftRefinedPhysicalTrace M m t g z i *
                (heatVHEATDriftRefinedPhysicalTrace M m t g z i + 4)) := by
      calc
        _ = heatVHEATDriftRefinedWeight * ∑ i : nativeHeatQ3RefinedCarrierIndex,
              (3683 / 2500 + heatRefinedTranslatedRare M (m + 1) 9 t
                (heatVHEATDriftRefinedShift m i) z) ^ 2 *
                heatVHEATDriftRefinedPhysicalTrace M m t g z i *
                  (heatVHEATDriftRefinedPhysicalTrace M m t g z i + 4) := by
            rw [hWeightEq]
        _ = ∑ i : nativeHeatQ3RefinedCarrierIndex,
              heatVHEATDriftRefinedWeight *
                ((b + heatRefinedTranslatedRare M (m + 1) 9 t
                    (heatVHEATDriftRefinedShift m i) z) ^ 2 *
                  heatVHEATDriftRefinedPhysicalTrace M m t g z i *
                    (heatVHEATDriftRefinedPhysicalTrace M m t g z i + 4)) := by
            rw [Finset.mul_sum]
        _ = _ := by simp
    have hbound := hz.trans_eq (congrArg (fun q =>
      4 * heatVHEATDriftE9 M * (nativeHeatSB : ℝ) * q) hsum)
    simpa only [b] using hbound
  by_cases hk2 : 2 ≤ k
  · let R : nativeHeatQ3RefinedCarrierIndex →
        Cutoff.CutoffSample 2 × (ℕ → ℝ) → ℝ := fun i z =>
      heatRefinedTranslatedRare M (m + 1) 9 t
        (heatVHEATDriftRefinedShift m i) z
    let T : nativeHeatQ3RefinedCarrierIndex →
        Cutoff.CutoffSample 2 × (ℕ → ℝ) → ℝ := fun i z =>
      heatVHEATDriftRefinedPhysicalTrace M m t g z i
    let Bfun : (Cutoff.CutoffSample 2 × (ℕ → ℝ)) → ℝ := fun z =>
      A z ^ (k - 2) *
        ∑ i ∈ (Finset.univ : Finset nativeHeatQ3RefinedCarrierIndex),
          heatVHEATDriftRefinedWeight *
            ((b + R i z) ^ 2 * T i z * (T i z + 4))
    let Cbr : ℝ := 2 * (k : ℝ) * ((k : ℝ) - 1) *
      heatVHEATDriftE9 M * (nativeHeatSB : ℝ) * (1 + θ⁻¹)
    have hTproperties (i : nativeHeatQ3RefinedCarrierIndex) :
        Measurable (heatVHEATDriftRefinedPhysicalTrace M m t g · i) ∧
          ∀ z, 0 ≤ heatVHEATDriftRefinedPhysicalTrace M m t g z i := by
      refine ⟨?_, ?_⟩
      · rw [hTraceEq i]
        exact (hTraceProperties i).1
      · intro z
        rw [congrFun (hTraceEq i) z]
        exact (hTraceProperties i).2 z
    have hT20' : ∀ i ∈ Finset.univ,
        eLpNorm (T i) 20 μ ≤ ENNReal.ofReal X₀ := by
      intro i _hi
      simpa only [T] using hT20 i
    have hT128' : ∀ i ∈ Finset.univ,
        eLpNorm (T i) 128 μ ≤ ENNReal.ofReal F₀ := by
      intro i _hi
      simpa only [T] using hT128 i
    have hR128' : ∀ i ∈ Finset.univ,
        eLpNorm (R i) 128 μ ≤ ENNReal.ofReal ε := by
      intro i _hi
      simpa only [R, ε] using hR128 i
    have hBracketAvg := heatVHEATThetaBracketAverages μ Finset.univ
      (fun _ : nativeHeatQ3RefinedCarrierIndex => heatVHEATDriftRefinedWeight)
      (fun _ _ => heatVHEATDrift_refined_weights.1)
      heatVHEATDrift_refined_weights.2 R T A
      (fun i hi => (hRmeas i).aestronglyMeasurable)
      (fun i hi => (hTproperties i).1.aestronglyMeasurable)
      hAmeas.aestronglyMeasurable
      (fun i hi z => hR0 i z) (fun i hi z => (hTproperties i).2 z)
      hA0 havg ε X₀ Y F₀ b (by norm_num) hX₀nonneg hY hF₀nonneg hb
      hR128' hYavg hAX20 hT20' hA128 hT128'
      (k - 2) (by omega)
    have hBracketInt : Integrable Bfun μ := by
      simpa only [Bfun, R, T] using hBracketAvg.1
    have hBracketBound :
        (∫ z, Bfun z ∂μ) ≤
          b ^ 2 * Y ^ (k - 2) * (4 * X₀ + X₀ ^ 2) +
            2 * b * (4 * nativeHeatVHEATJ (3 / 10 ^ 46 : ℝ) X₀ F₀ 20 1 (k - 1) +
              nativeHeatVHEATJ (3 / 10 ^ 46 : ℝ) X₀ F₀ 20 1 k) +
            4 * nativeHeatVHEATJ (3 / 10 ^ 46 : ℝ) X₀ F₀ 20 2 (k - 1) +
              nativeHeatVHEATJ (3 / 10 ^ 46 : ℝ) X₀ F₀ 20 2 k := by
      have hshift₁ : k - 2 + 1 = k - 1 := by omega
      have hshift₂ : k - 2 + 2 = k := by omega
      simpa only [Bfun, R, T, ε, hshift₁, hshift₂] using hBracketAvg.2.1
    have hPoint : ∀ᵐ z ∂μ,
        nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
            M h hM m θ t k z ≤
          heatVHEATDriftRefinedPhysicalDrift M h m t k g z + Cbr * Bfun z := by
      filter_upwards [hRowsAE'] with z hz
      have hp := nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGenerator_le_driftAndBracket
        M h hM m θ hθ M.shellPrefix.gamma_pos hstate t k hk2 z
      have hkcast : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      have hcoeff : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) *
          (heatVHEATDriftRefinedPhysicalAverage M m t g z) ^ (k - 2) := by
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith))
          (pow_nonneg (hA0 z) _)
      have hfactor : 0 ≤ (1 + θ⁻¹) := by positivity
      have hhalf : 0 ≤
          ((k : ℝ) * ((k : ℝ) - 1) * A z ^ (k - 2) / 2) :=
        div_nonneg hcoeff (by norm_num : (0 : ℝ) ≤ 2)
      have hrows' :
          nativeHeatQ3RefinedCarrierSourceRowsForFields M h m
              (fun i => nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 i +
                childConstantMap
                  (fun j => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)))
                  (fun j => g j z.2) i) ≤
            4 * heatVHEATDriftE9 M * (nativeHeatSB : ℝ) *
              (∑ i ∈ (Finset.univ : Finset nativeHeatQ3RefinedCarrierIndex),
                heatVHEATDriftRefinedWeight *
                  ((b + R i z) ^ 2 * T i z * (T i z + 4))) := by
        simpa only [b, R, T] using hz
      let cHalf : ℝ := (k : ℝ) * ((k : ℝ) - 1) * A z ^ (k - 2) / 2
      have hcHalf : 0 ≤ cHalf := hhalf
      have hfieldsEq :
          nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 +
              childConstantMap
                (fun j => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)))
                (fun j => g j z.2) =
            (fun i => nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 i +
              childConstantMap
                (fun j => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)))
                (fun j => g j z.2) i) := by
        funext i
        rfl
      have hp' :
          nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
              M h hM m θ t k z ≤
            heatVHEATDriftRefinedPhysicalDrift M h m t k g z +
              cHalf * ((1 + θ⁻¹) *
                nativeHeatQ3RefinedCarrierSourceRowsForFields M h m
                  (fun i => nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 i +
                    childConstantMap
                      (fun j => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)))
                      (fun j => g j z.2) i)) := by
        simpa only [A, g, cHalf, hfieldsEq] using hp
      have hbracket' :
          cHalf * ((1 + θ⁻¹) *
            nativeHeatQ3RefinedCarrierSourceRowsForFields M h m
              (fun i => nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 i +
                childConstantMap
                  (fun j => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)))
                  (fun j => g j z.2) i)) ≤
          cHalf * ((1 + θ⁻¹) *
            (4 * heatVHEATDriftE9 M * (nativeHeatSB : ℝ) *
              (∑ i ∈ (Finset.univ : Finset nativeHeatQ3RefinedCarrierIndex),
                heatVHEATDriftRefinedWeight *
                  ((b + R i z) ^ 2 * T i z * (T i z + 4))))) := by
        calc
          _ = (cHalf * (1 + θ⁻¹)) *
                nativeHeatQ3RefinedCarrierSourceRowsForFields M h m
                  (fun i => nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 i +
                    childConstantMap
                      (fun j => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)))
                      (fun j => g j z.2) i) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hrows'
            (mul_nonneg hcHalf hfactor)
          _ = _ := by ring
      have hscale :
          cHalf *
              ((1 + θ⁻¹) *
                (4 * heatVHEATDriftE9 M * (nativeHeatSB : ℝ) *
                  (∑ i ∈ (Finset.univ : Finset nativeHeatQ3RefinedCarrierIndex),
                    heatVHEATDriftRefinedWeight *
                      ((b + R i z) ^ 2 * T i z * (T i z + 4))))) =
            Cbr * Bfun z := by
        dsimp [cHalf, A, Cbr, Bfun]
        ring
      have hDriftRow :
          heatVHEATDriftRefinedPhysicalDrift M h m t k g z +
              cHalf * ((1 + θ⁻¹) *
                nativeHeatQ3RefinedCarrierSourceRowsForFields M h m
                  (fun i => nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 i +
                    childConstantMap
                      (fun j => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)))
                      (fun j => g j z.2) i)) ≤
            heatVHEATDriftRefinedPhysicalDrift M h m t k g z +
              cHalf * ((1 + θ⁻¹) *
                (4 * heatVHEATDriftE9 M * (nativeHeatSB : ℝ) *
                  (∑ i ∈ (Finset.univ : Finset nativeHeatQ3RefinedCarrierIndex),
                    heatVHEATDriftRefinedWeight *
                      ((b + R i z) ^ 2 * T i z * (T i z + 4))))) :=
        add_le_add_left_of_le hbracket'
      have hgenBound :
          nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
              M h hM m θ t k z ≤
            heatVHEATDriftRefinedPhysicalDrift M h m t k g z +
              cHalf * ((1 + θ⁻¹) *
                (4 * heatVHEATDriftE9 M * (nativeHeatSB : ℝ) *
                  (∑ i ∈ (Finset.univ : Finset nativeHeatQ3RefinedCarrierIndex),
                    heatVHEATDriftRefinedWeight *
                      ((b + R i z) ^ 2 * T i z * (T i z + 4))))) :=
        hp'.trans hDriftRow
      calc
        nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
            M h hM m θ t k z ≤
          heatVHEATDriftRefinedPhysicalDrift M h m t k g z +
            cHalf * ((1 + θ⁻¹) *
              (4 * heatVHEATDriftE9 M * (nativeHeatSB : ℝ) *
                (∑ i ∈ (Finset.univ : Finset nativeHeatQ3RefinedCarrierIndex),
                  heatVHEATDriftRefinedWeight *
                    ((b + R i z) ^ 2 * T i z * (T i z + 4))))) := by
          exact hgenBound
        _ = heatVHEATDriftRefinedPhysicalDrift M h m t k g z + Cbr * Bfun z :=
          congrArg (fun x => heatVHEATDriftRefinedPhysicalDrift M h m t k g z + x) hscale
    have hDriftEq : heatVHEATDriftRefinedPhysicalDrift M h m t k g =
        heatVHEATDriftRefinedSource M h m t k g := by
      funext z
      exact (heatVHEATDrift_refined_physical_family_eq M h m t k g z).2
    have hRhsInt : Integrable
        (fun z => heatVHEATDriftRefinedSource M h m t k g z + Cbr * Bfun z) μ :=
      hdrift.2.1.add (hBracketInt.const_mul Cbr)
    have hPointSource : ∀ᵐ z ∂μ,
        nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
            M h hM m θ t k z ≤
          heatVHEATDriftRefinedSource M h m t k g z + Cbr * Bfun z := by
      filter_upwards [hPoint] with z hz
      simpa only [hDriftEq] using hz
    have hIntegral := integral_mono_ae
      (nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand_integrable
        M h hM m θ t hθ k) hRhsInt hPointSource
    rw [← nativeHeatQ3RefinedCarrierSourceMomentGenerator_eq_integral
      M h hM m θ t hθ k hk] at hIntegral
    have hMomentK := nativeHeatQ3RefinedCarrierSourceMoment_eq_physicalAverage_integral
      M h hM hg m hpast θ t hθ ht k hk hk20
    have hMomentKm1 := nativeHeatQ3RefinedCarrierSourceMoment_eq_physicalAverage_integral
      M h hM hg m hpast θ t hθ ht (k - 1) (by omega) (by omega)
    rw [hMomentK, hMomentKm1]
    have hDriftBound := hdrift.2.2
    rw [hXsourceEq, hFsourceEq] at hDriftBound
    nth_rewrite 1 [← hgCanonical] at hDriftBound
    change (∫ z, heatVHEATDriftRefinedSource M h m t k g z ∂μ) ≤ _
      at hDriftBound
    have hkminus : 0 ≤ (k : ℝ) - 1 := by
      exact_mod_cast (show 0 ≤ k - 1 by omega)
    have hthetaFactor : 0 ≤ 1 + θ⁻¹ := by positivity
    have hCbrNonneg : 0 ≤ Cbr := by
      dsimp [Cbr]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg k))
              hkminus)
            he9)
          hSB)
        hthetaFactor
    have hBracketBound' := mul_le_mul_of_nonneg_left hBracketBound hCbrNonneg
    have hsum := add_le_add hDriftBound hBracketBound'
    have hIntegralSplit :
        (∫ z, heatVHEATDriftRefinedSource M h m t k g z +
          Cbr * Bfun z ∂μ) =
          (∫ z, heatVHEATDriftRefinedSource M h m t k g z ∂μ) +
            Cbr * (∫ z, Bfun z ∂μ) := by
      rw [integral_add hdrift.2.1 (hBracketInt.const_mul Cbr), integral_const_mul]
    have hIntegral' :
        nativeHeatQ3RefinedCarrierSourceMomentGenerator M h hM m k θ t ≤
          (∫ z, heatVHEATDriftRefinedSource M h m t k g z ∂μ) +
            Cbr * (∫ z, Bfun z ∂μ) := by
      rw [← hIntegralSplit]
      exact hIntegral
    let e₀ : ℝ := nativeHeatVHEATErrorEk k 20 (heatVHEATDriftE9 M)
      (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
      θ b X₀ Y (3 / 10 ^ 46 : ℝ) F₀
    let e₁ : ℝ := nativeHeatVHEATErrorEk k 20 (heatVHEATDriftE9 M)
      (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
      θ b X Y (3 / 10 ^ 46 : ℝ) F
    have hErrorSplitFull :
        heatVHEATDriftFirstLine k (heatVHEATDriftE9 M)
            (nativeHeatK : ℝ) (nativeHeatM : ℝ) (3683 / 2500 : ℝ)
            (3 / 10 ^ 46 : ℝ) X₀ F₀ +
            Cbr * (b ^ 2 * Y ^ (k - 2) * (4 * X₀ + X₀ ^ 2) +
              2 * b * (4 * nativeHeatVHEATJ (3 / 10 ^ 46 : ℝ) X₀ F₀ 20 1 (k - 1) +
                nativeHeatVHEATJ (3 / 10 ^ 46 : ℝ) X₀ F₀ 20 1 k) +
              4 * nativeHeatVHEATJ (3 / 10 ^ 46 : ℝ) X₀ F₀ 20 2 (k - 1) +
              nativeHeatVHEATJ (3 / 10 ^ 46 : ℝ) X₀ F₀ 20 2 k) =
          nativeHeatVHEATErrorEk k 20 (heatVHEATDriftE9 M)
            (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
            θ b X₀ Y (3 / 10 ^ 46 : ℝ) F₀ := by
      rw [nativeHeatVHEATErrorEk_eq_driftFirstLine_add_bracket
        k (heatVHEATDriftE9 M) (nativeHeatK : ℝ) (nativeHeatM : ℝ)
        (nativeHeatSB : ℝ) θ b X₀ Y (3 / 10 ^ 46 : ℝ) F₀]
      simp only [if_pos hk2, Cbr]
      have hFirstLineEq :
          heatVHEATDriftFirstLine k (heatVHEATDriftE9 M)
              (nativeHeatK : ℝ) (nativeHeatM : ℝ) (3683 / 2500 : ℝ)
              (3 / 10 ^ 46 : ℝ) X₀ F₀ =
            heatVHEATDriftFirstLine k (heatVHEATDriftE9 M)
              (nativeHeatK : ℝ) (nativeHeatM : ℝ) b
              (3 / 10 ^ 46 : ℝ) X₀ F₀ := rfl
      rw [hFirstLineEq]
    have hErrorSplit := hErrorSplitFull
    change _ = e₀ at hErrorSplit
    have hErrorMonoFull :
        nativeHeatVHEATErrorEk k 20 (heatVHEATDriftE9 M)
            (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
            θ b X₀ Y (3 / 10 ^ 46 : ℝ) F₀ ≤
          nativeHeatVHEATErrorEk k 20 (heatVHEATDriftE9 M)
            (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
            θ b X Y (3 / 10 ^ 46 : ℝ) F := by
      by_cases hXpos : 0 < X
      · have hstepX := nativeHeatVHEATErrorEk_mono_X_p20_of_nonneg
          k (heatVHEATDriftE9 M) (nativeHeatK : ℝ) (nativeHeatM : ℝ)
          (nativeHeatSB : ℝ) θ b X₀ X Y (3 / 10 ^ 46 : ℝ) F₀ hk20
          he9 hK hM0 hSB hθ hb hX₀nonneg hXpos hX₀cap hY
          (by norm_num) hF₀nonneg
        have hstepF := nativeHeatVHEATErrorEk_mono_F k 20
          (heatVHEATDriftE9 M) (nativeHeatK : ℝ) (nativeHeatM : ℝ)
          (nativeHeatSB : ℝ) θ b X Y F₀ F (3 / 10 ^ 46 : ℝ)
          he9 hK hM0 hSB hθ hb hXpos (by norm_num) hF₀nonneg hFcap
          (by norm_num : 20 < 128)
        exact hstepX.trans hstepF
      · have hXzero : X = 0 := le_antisymm (le_of_not_gt hXpos) hX
        have hX₀zero : X₀ = 0 :=
          le_antisymm (by simpa [hXzero] using hX₀cap) hX₀nonneg
        have hFirrelevant :
            nativeHeatVHEATErrorEk k 20 (heatVHEATDriftE9 M)
                (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
                θ b 0 Y (3 / 10 ^ 46 : ℝ) F₀ =
              nativeHeatVHEATErrorEk k 20 (heatVHEATDriftE9 M)
                (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
                θ b 0 Y (3 / 10 ^ 46 : ℝ) F := by
          by_cases htop : k = 20
          · subst k
            simp [nativeHeatVHEATErrorEk, nativeHeatVHEATJ]
          · have hkl : k < 20 := by omega
            rw [nativeHeatVHEATErrorEk_of_lt k 20 hk2 hkl,
              nativeHeatVHEATErrorEk_of_lt k 20 hk2 hkl]
        rw [hX₀zero, hXzero]
        exact le_of_eq hFirrelevant
    have hErrorMono : e₀ ≤ e₁ := by
      simpa only [e₀, e₁] using hErrorMonoFull
    have hsumFinal := hIntegral'.trans hsum
    rw [add_assoc, hErrorSplit] at hsumFinal
    refine hsumFinal.trans ?_
    have hPhysEq : heatVHEATDriftRefinedPhysicalAverage M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m
          (nativeHeatTheta : ℝ) t) =
        heatVHEATDriftRefinedAverage M m t
          (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m
            (nativeHeatTheta : ℝ) t) := hAvgEq
    rw [hPhysEq]
    simp only [θ, b, e₀, e₁] at hsumFinal hErrorMono ⊢
    linarith only [hErrorMono]
  · have hkEq : k = 1 := by omega
    subst k
    have hM1 := nativeHeatQ3RefinedCarrierSourceMoment_eq_physicalAverage_integral
      M h hM hg m hpast θ t hθ ht 1 (by norm_num) hk20
    have hMomentZero : nativeHeatQ3RefinedCarrierSourceMoment M h hM m 0 θ t = 1 := by
      simp [nativeHeatQ3RefinedCarrierSourceMoment, nativeHeatChildBandMoment,
        bandModelBackwardAverage, bandModelAverage, backwardTest,
        gaussianSeriesHeatAverage, childPower, childMeanTrace]
    rw [hM1, hMomentZero]
    have hGenInt :=
      nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand_integrable
        M h hM m θ t hθ 1
    have hGenPoint (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) :
        nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
            M h hM m θ t 1 z ≤
          heatVHEATDriftRefinedPhysicalDrift M h m t 1
            (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z :=
      nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGenerator_le_drift_one
        M h hM m θ t hθ z
    have hDriftEq :
        heatVHEATDriftRefinedPhysicalDrift M h m t 1
            (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) =
          heatVHEATDriftRefinedSource M h m t 1
            (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) := by
      funext z
      exact (heatVHEATDrift_refined_physical_family_eq M h m t 1
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z).2
    have hDriftInt :
        Integrable (heatVHEATDriftRefinedPhysicalDrift M h m t 1
          (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t))
          (nativeHeatRemainderJointLaw M) := by
      rw [hDriftEq]
      exact hdrift.2.1
    have hIntegral := integral_mono_ae hGenInt hDriftInt
      (Filter.Eventually.of_forall hGenPoint)
    rw [← nativeHeatQ3RefinedCarrierSourceMomentGenerator_eq_integral
      M h hM m θ t hθ 1 (by norm_num)] at hIntegral
    have hIntegralSource :
        nativeHeatQ3RefinedCarrierSourceMomentGenerator M h hM m 1 θ t ≤
          ∫ z, heatVHEATDriftRefinedSource M h m t 1
            (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z
            ∂nativeHeatRemainderJointLaw M := by
      calc
        _ ≤ ∫ z, heatVHEATDriftRefinedPhysicalDrift M h m t 1
              (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z
            ∂nativeHeatRemainderJointLaw M := hIntegral
        _ = _ := by rw [hDriftEq]
    have hDriftBound := hdrift.2.2
    rw [hXsourceEq, hFsourceEq] at hDriftBound
    have hPhysEq1 : heatVHEATDriftRefinedAverage M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) =
        heatVHEATDriftRefinedPhysicalAverage M m t
          (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) := by
      funext z
      exact (heatVHEATDrift_refined_physical_family_eq M h m t 0
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z).1.symm
    rw [hPhysEq1] at hDriftBound
    have hzeroInt :
        (∫ z, (heatVHEATDriftRefinedPhysicalAverage M m t
          (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z) ^
            (1 - 1) ∂nativeHeatRemainderJointLaw M) = 1 := by
      have hconst : (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
          (heatVHEATDriftRefinedPhysicalAverage M m t
            (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z) ^
              (1 - 1)) = fun _ => (1 : ℝ) := by
        funext z
        norm_num
      letI : IsProbabilityMeasure (nativeHeatRemainderJointLaw M) :=
        inferInstanceAs (IsProbabilityMeasure
          ((Cutoff.cutoffSampleLaw M).toMeasure.prod standardGaussianInfinitePi))
      rw [hconst, integral_const, measureReal_def, measure_univ,
        ENNReal.toReal_one, one_smul]
    have hE1Zero := nativeHeatVHEATErrorEk_eq_driftFirstLine_add_bracket
      1 (heatVHEATDriftE9 M) (nativeHeatK : ℝ) (nativeHeatM : ℝ)
      (nativeHeatSB : ℝ) θ b X₀ Y (3 / 10 ^ 46 : ℝ) F₀
    have hE1Zero' :
        nativeHeatVHEATErrorEk 1 20 (heatVHEATDriftE9 M)
          (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
          θ b X₀ Y (3 / 10 ^ 46 : ℝ) F₀ =
        heatVHEATDriftFirstLine 1 (heatVHEATDriftE9 M)
          nativeHeatK nativeHeatM b (3 / 10 ^ 46 : ℝ) X₀ F₀ := by
      rw [hE1Zero]
      norm_num
    have hErrorF :
        nativeHeatVHEATErrorEk 1 20 (heatVHEATDriftE9 M)
            (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
            θ b X₀ Y (3 / 10 ^ 46 : ℝ) F₀ =
          nativeHeatVHEATErrorEk 1 20 (heatVHEATDriftE9 M)
            (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
            θ b X₀ Y (3 / 10 ^ 46 : ℝ) F := by
      rw [nativeHeatVHEATErrorEk_one_eq 20 (by norm_num : 2 ≤ 20),
        nativeHeatVHEATErrorEk_one_eq 20 (by norm_num : 2 ≤ 20)]
    have hErrorX :
        nativeHeatVHEATErrorEk 1 20 (heatVHEATDriftE9 M)
            (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
            θ b X₀ Y (3 / 10 ^ 46 : ℝ) F ≤
          nativeHeatVHEATErrorEk 1 20 (heatVHEATDriftE9 M)
            (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
            θ b X Y (3 / 10 ^ 46 : ℝ) F := by
      by_cases hXpos : 0 < X
      · exact nativeHeatVHEATErrorEk_mono_X_p20_of_nonneg
          1 (heatVHEATDriftE9 M) (nativeHeatK : ℝ) (nativeHeatM : ℝ)
          (nativeHeatSB : ℝ) θ b X₀ X Y (3 / 10 ^ 46 : ℝ) F
          (by norm_num) he9 hK hM0 hSB hθ hb hX₀nonneg hXpos hX₀cap hY
          (by norm_num) hF
      · have hXzero : X = 0 := le_antisymm (le_of_not_gt hXpos) hX
        have hX₀zero : X₀ = 0 :=
          le_antisymm (by simpa [hXzero] using hX₀cap) hX₀nonneg
        rw [hX₀zero, hXzero]
    have hErrorMono := (le_of_eq hErrorF).trans hErrorX
    have hSourceBound :
        ∫ z, heatVHEATDriftRefinedSource M h m t 1
            (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z
            ∂nativeHeatRemainderJointLaw M ≤
          heatVHEATDriftE9 M *
              (2 * (nativeHeatK : ℝ) * (3683 / 2500) +
                (nativeHeatM : ℝ) * (3683 / 2500) ^ 2) *
            (∫ z, (heatVHEATDriftRefinedPhysicalAverage M m t
                (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z) ^ 1
                ∂nativeHeatRemainderJointLaw M +
              4 * 1) +
            nativeHeatVHEATErrorEk 1 20 (heatVHEATDriftE9 M)
              (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
              θ b X₀ Y (3 / 10 ^ 46 : ℝ) F₀ := by
      have hFirstLineEq :
          heatVHEATDriftFirstLine 1 (heatVHEATDriftE9 M)
              (nativeHeatK : ℝ) (nativeHeatM : ℝ) (3683 / 2500 : ℝ)
              (3 / 10 ^ 46 : ℝ) X₀ F₀ =
            heatVHEATDriftFirstLine 1 (heatVHEATDriftE9 M)
              (nativeHeatK : ℝ) (nativeHeatM : ℝ) b
              (3 / 10 ^ 46 : ℝ) X₀ F₀ := rfl
      let mainRaw : ℝ := ((↑(1 : ℕ) : ℝ) * heatVHEATDriftE9 M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500) +
            (nativeHeatM : ℝ) * (3683 / 2500) ^ 2)) *
        ((∫ z, (heatVHEATDriftRefinedPhysicalAverage M m t
            (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z) ^ 1
            ∂nativeHeatRemainderJointLaw M) +
          4 * (∫ z, (heatVHEATDriftRefinedPhysicalAverage M m t
            (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z) ^ (1 - 1)
            ∂nativeHeatRemainderJointLaw M))
      let mainTarget : ℝ := heatVHEATDriftE9 M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500) +
            (nativeHeatM : ℝ) * (3683 / 2500) ^ 2) *
        ((∫ z, (heatVHEATDriftRefinedPhysicalAverage M m t
            (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z) ^ 1
            ∂nativeHeatRemainderJointLaw M) + 4 * 1)
      have hmainEq : mainRaw = mainTarget := by
        dsimp [mainRaw, mainTarget]
        rw [Nat.cast_one, one_mul]
        exact congrArg (fun q : ℝ =>
          heatVHEATDriftE9 M *
            (2 * (nativeHeatK : ℝ) * (3683 / 2500) +
              (nativeHeatM : ℝ) * (3683 / 2500) ^ 2) *
            ((∫ z, (heatVHEATDriftRefinedPhysicalAverage M m t
                (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z) ^ 1
                ∂nativeHeatRemainderJointLaw M) + 4 * q)) hzeroInt
      have hrowRhsEq :
          mainRaw + heatVHEATDriftFirstLine 1 (heatVHEATDriftE9 M)
            (nativeHeatK : ℝ) (nativeHeatM : ℝ) (3683 / 2500 : ℝ)
            (3 / 10 ^ 46 : ℝ) X₀ F₀ =
          mainTarget + nativeHeatVHEATErrorEk 1 20 (heatVHEATDriftE9 M)
            (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
            θ b X₀ Y (3 / 10 ^ 46 : ℝ) F₀ := by
        calc
          _ = mainRaw + heatVHEATDriftFirstLine 1 (heatVHEATDriftE9 M)
                (nativeHeatK : ℝ) (nativeHeatM : ℝ) b
                (3 / 10 ^ 46 : ℝ) X₀ F₀ :=
              congrArg (fun q : ℝ => mainRaw + q) hFirstLineEq
          _ = mainTarget + heatVHEATDriftFirstLine 1 (heatVHEATDriftE9 M)
                (nativeHeatK : ℝ) (nativeHeatM : ℝ) b
                (3 / 10 ^ 46 : ℝ) X₀ F₀ :=
              congrArg (fun q : ℝ => q +
                heatVHEATDriftFirstLine 1 (heatVHEATDriftE9 M)
                  (nativeHeatK : ℝ) (nativeHeatM : ℝ) b
                  (3 / 10 ^ 46 : ℝ) X₀ F₀) hmainEq
          _ = _ := congrArg (fun q : ℝ => mainTarget + q) hE1Zero'.symm
      refine hDriftBound.trans (le_of_eq ?_)
      exact hrowRhsEq
    rw [Nat.cast_one, one_mul]
    have hs := hIntegralSource.trans hSourceBound
    simp only [θ, b] at hs hErrorMono ⊢
    linarith only [hs, hErrorMono]

end
end ASDExplicitGamma.Native

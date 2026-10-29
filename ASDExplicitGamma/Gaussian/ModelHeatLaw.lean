module

public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Gaussian.Q3RealizationFourier
public import Mathlib.MeasureTheory.Integral.Prod

/-! # The compact fresh-shell law at the insertion scale -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The actual scalar coefficient along a partial insertion, on a compact set. -/
noncomputable def modelInsertedScalar (K : Set (Vec 2)) [CompactSpace K]
    (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : C(K, ℝ) :=
  olderField K m ω + Real.sqrt t • shellFieldScalarRestriction K (ω.1 (m + 1))

/-- The completed compact older field and the next scalar shell are independent. -/
theorem indepFun_olderField_freshShell (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell)) :
    IndepFun (olderField K m)
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (m + 1)))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let X : Cutoff.ShellSeq 2 → C(K, ℝ) := fun ω =>
    ∑' r : ℕ, shellFieldScalarRestriction K (ω (m - (r : ℤ)))
  let Y : Cutoff.ShellSeq 2 → C(K, ℝ) := fun ω => shellFieldScalarRestriction K (ω (m + 1))
  have hX : @Measurable _ _ (Cutoff.shellIndexSigma (Iic m)) _ X := by
    let : MeasurableSpace (Cutoff.ShellSeq 2) := Cutoff.shellIndexSigma (Iic m)
    change Measurable X
    exact Measurable.tsum fun r => (measurable_shellFieldScalarRestriction K).comp
      (Cutoff.measurable_shellCoordinate_shellIndexSigma (by change m - (r : ℤ) ≤ m; omega))
  have hY : @Measurable _ _ (Cutoff.shellIndexSigma ({m + 1} : Set ℤ)) _ Y :=
    by
      let : MeasurableSpace (Cutoff.ShellSeq 2) := Cutoff.shellIndexSigma ({m + 1} : Set ℤ)
      exact (measurable_shellFieldScalarRestriction K).comp
        (Cutoff.measurable_shellCoordinate_shellIndexSigma (by simp))
  have hXb : Measurable X := hX.mono (Cutoff.shellIndexSigma_le_borel _) le_rfl
  have hYb : Measurable Y := hY.mono (Cutoff.shellIndexSigma_le_borel _) le_rfl
  have hind := Cutoff.indepFun_of_measurable_shellIndexSigma_of_disjoint M
    (Set.disjoint_left.mpr (fun k hk hk' => by simp only [mem_Iic, mem_singleton_iff] at *; omega)) hX hY
  have hpair := hind.map_prod_eq_prod_map_map hXb.aemeasurable hYb.aemeasurable
  rw [← Cutoff.map_cutoffSampleLaw_val M,
    Measure.map_map (hXb.prodMk hYb) measurable_subtype_coe,
    Measure.map_map hXb measurable_subtype_coe,
    Measure.map_map hYb measurable_subtype_coe] at hpair
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_olderField K ell m hK).aemeasurable
    ((measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)).aemeasurable).mpr
  exact hpair

private theorem summable_modelOlderRestrictions (K : Set (Vec 2)) [CompactSpace K]
    (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell)) (ω : Cutoff.CutoffSample 2) :
    Summable (fun r : ℕ => ‖shellFieldScalarRestriction K (ω.1 (m - (r : ℤ)))‖) := by
  apply Summable.of_norm_bounded (Cutoff.summable_cutoffLocalControl ell m ω)
  intro r
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  apply (ContinuousMap.norm_le _ (Cutoff.localCubeControl_nonneg ell _)).mpr
  intro x
  rw [Real.norm_eq_abs]
  exact Cutoff.abs_entry_le_localCubeControl ell _ (hK x.2) 1 0

/-- The compact older field is literally the scalar entry of the model's coefficient cutoff. -/
theorem olderField_apply_eq_coefficientCutoff (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell))
    (ω : Cutoff.CutoffSample 2) (x : K) :
    olderField K m ω x = Cutoff.coefficientCutoff M.nu m ω x 1 0 := by
  have hs := (summable_modelOlderRestrictions K ell m hK ω).of_norm
  have heval := (ContinuousMap.evalCLM ℝ x).map_tsum hs
  rw [Model.coefficientCutoff_eq_nu_add_olderField_entry]
  simp only [Matrix.smul_apply, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
    smul_eq_mul, mul_zero, zero_add]
  exact heval

/-- This restriction agrees with the actual partially inserted coefficient at every point. -/
theorem modelInsertedScalar_apply (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell))
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (x : K) :
    modelInsertedScalar K m t ω x = Model.partialInsertedCoefficient M m t ω x 1 0 := by
  simp only [modelInsertedScalar, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    olderField_apply_eq_coefficientCutoff K M ell m hK, Model.partialInsertedCoefficient,
    RegCoeffField.add_apply, RegCoeffField.smul_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  rfl

/-- The older continuous coefficient has all finite moments, from the proved cutoff control. -/
theorem memLp_olderField (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell))
    {p : ℝ} (hp : 1 ≤ p) :
    MemLp (olderField K m) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
  apply (memLp_olderShellSupNormSum M K ell m hK hp).mono'
    (measurable_olderField K ell m hK).aestronglyMeasurable
  exact Eventually.of_forall fun ω => norm_tsum_le_tsum_norm
    (summable_modelOlderRestrictions K ell m hK ω)

/-- All natural polynomial moments of the marginal older coefficient law are finite. -/
theorem integrable_polynomial_olderFieldLaw (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell)) (d : ℕ) :
    Integrable (fun x : C(K, ℝ) => (1 + ‖x‖) ^ d)
      ((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)) := by
  have hmeas := measurable_olderField K ell m hK
  apply (integrable_map_measure (by fun_prop) hmeas.aemeasurable).mpr
  have hmem : MemLp (olderField K m) ((d + 2 : ℕ) : ℝ≥0∞)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    convert memLp_olderField K M ell m hK (p := (d + 2 : ℕ)) (by exact_mod_cast (show 1 ≤ d + 2 by omega)) using 1
    simp [ENNReal.ofReal_add]
  have hplus := (memLp_const (1 : ℝ) (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (p := ((d + 2 : ℕ) : ℝ≥0∞))).add hmem.norm
  have hhigh := hplus.integrable_norm_pow (by omega : d + 2 ≠ 0)
  have hlow := integrable_norm_pow_of_le hplus.aestronglyMeasurable (by omega : d ≤ d + 2) hhigh
  simpa only [Function.comp_def, Pi.add_apply, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) + ‖olderField K m _‖)] using hlow

/-- Triadic dilation transports a compact-set Gaussian-series realization to every shell level. -/
theorem shellMarginalLaw_map_scalarRestriction_eq_gaussianSeries
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (k : ℤ)
    {K : Set (Vec 2)} [CompactSpace K] :
    ∃ (T : GaussianFactorL2 ℕ →L[ℝ] C(K, ℝ))
      (v : ℕ → GaussianFactorL2 ℕ) (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (ShellField.shellMarginalLaw M.P k).toMeasure.map (shellFieldScalarRestriction K) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) := by
  let s : ℝ := ((3 : ℝ) ^ k)⁻¹
  let K' : Set (Vec 2) := (fun x : Vec 2 => s • x) '' K
  have hcompact : IsCompact K' :=
    (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace K)).image
      (show Continuous (fun x : Vec 2 => s • x) from continuous_id.const_smul s)
  let : CompactSpace K' := isCompact_iff_compactSpace.mp hcompact
  let f : C(K, K') := ⟨fun x => ⟨s • x.1, ⟨x.1, x.2, rfl⟩⟩,
    (continuous_subtype_val.const_smul s).subtype_mk _⟩
  let A : C(K', ℝ) →L[ℝ] C(K, ℝ) :=
    (3 : ℝ) ^ (M.gamma * (k : ℝ)) • ContinuousMap.compCLM ℝ ℝ f
  obtain ⟨T, v, hA, hlaw⟩ :=
    zeroShellLaw_map_shellFieldScalarRestriction_eq_gaussianSeries M h hM (K := K')
  refine ⟨A.comp T, v, hA, ?_⟩
  have hrestrict : (fun j => shellFieldScalarRestriction K (ShellField.triadicScale M.gamma k j)) =
      fun j => A (shellFieldScalarRestriction K' j) := by
    funext j
    ext x
    simp only [shellFieldScalarRestriction, planarShellScalarStream, planarShellMatrixEntry,
      ContinuousMap.comp_apply, ContinuousMap.restrict_apply, ContinuousMap.coe_mk,
      ShellField.triadicScale_apply, Matrix.smul_apply, smul_eq_mul]
    rfl
  rw [M.shellPrefix.marginal_scaling k, ProbabilityMeasure.toMeasure_map,
    Measure.map_map (measurable_shellFieldScalarRestriction K)
      (ShellField.measurable_triadicScale M.gamma k)]
  change (ShellField.zeroShellLaw M.P).toMeasure.map
    (fun j => shellFieldScalarRestriction K (ShellField.triadicScale M.gamma k j)) = _
  rw [hrestrict]
  change ((ShellField.zeroShellLaw M.P).toMeasure).map (A ∘ shellFieldScalarRestriction K') = _
  rw [← Measure.map_map A.continuous.measurable
    (measurable_shellFieldScalarRestriction K'), hlaw,
    Measure.map_map A.continuous.measurable
      (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable]
  rfl

/-- The fresh scalar shell on the actual cutoff probability space is a Gaussian series. -/
theorem freshShell_map_scalarRestriction_eq_gaussianSeries
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {K : Set (Vec 2)} [CompactSpace K] :
    ∃ (T : GaussianFactorL2 ℕ →L[ℝ] C(K, ℝ))
      (v : ℕ → GaussianFactorL2 ℕ) (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (m + 1))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) := by
  obtain ⟨T, v, hA, hlaw⟩ :=
    shellMarginalLaw_map_scalarRestriction_eq_gaussianSeries M h hM (m + 1) (K := K)
  refine ⟨T, v, hA, ?_⟩
  rw [← Model.map_freshShell_eq_shellMarginalLaw M m,
    Measure.map_map (measurable_shellFieldScalarRestriction K)
      ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)] at hlaw
  exact hlaw

end ASDExplicitGamma.Gaussian

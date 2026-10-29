module

public import ASDExplicitGamma.Native.HeatStepCurves
public import ASDExplicitGamma.Native.GenericSourceChildBandEndpoint
public import ASDExplicitGamma.Native.GenericSourceChildBandFactors
public import ASDExplicitGamma.Native.GenericSourceBandCoefficient
public import ASDExplicitGamma.Native.StepEndpoint
public import ASDExplicitGamma.Native.StepEndpointLp
public import ASDExplicitGamma.Native.HeatVHEATChild
public import ASDExplicitGamma.Variational.Subadditivity
public import ASDExplicitGamma.Inverse.HistoryTraceMonotone
public import ASDExplicitGamma.Triadic.DiagMesh

/-! Time-one endpoint of the `ns`-shell refined carrier: the carrier moments are the moments of
the average of the actual child traces under the completed cutoff `m+1+ns`, and the physical
parent trace is bounded by that average (ordinary subadditivity). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Inverse
open scoped ENNReal Topology

local instance nativeHeatStepEndChildFinite (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- The physical parent trace in the frame of the old cutoff `m+1`, under the cutoff `m+1+ns`. -/
noncomputable def nativeHeatStepParentTrace (M : ABKModel 2) (m : ℤ) (ns : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  traceDefect (cubeSet (originCube 2 (m + 10)))
    (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
    (Annealed.sigmaBar M (m + 1) : ℝ)

/-- The trace of the refined child `i`, same cutoff and frame. -/
noncomputable def nativeHeatStepChildTrace (M : ABKModel 2) (m : ℤ) (ns : ℕ)
    (i : nativeHeatQ3RefinedCarrierIndex) (ω : Cutoff.CutoffSample 2) : ℝ :=
  traceDefect (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
    (Annealed.sigmaBar M (m + 1) : ℝ)

/-- The average of the `9^10` child traces. -/
noncomputable def nativeHeatStepChildAverage (M : ABKModel 2) (m : ℤ) (ns : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  ((9 ^ 10 : ℝ)⁻¹) * Finset.univ.sum (fun i => nativeHeatStepChildTrace M m ns i ω)

/-- The compact scalar `older + √t band` on any compact observation set is the scalar entry of the
attenuated coefficient. -/
theorem nativeHeatStep_field_apply (M : ABKModel 2) (K : Set (Vec 2)) [CompactSpace K]
    (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) (x : K) :
    (olderField K n ω + Real.sqrt t • modelBand K (nativeSourceBandIndex n height) ω) x =
      attenuatedCoefficient M n (n + (height : ℤ)) (fun _ => Real.sqrt t) ω x 1 0 := by
  have hc : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K hc
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply,
    modelBand, ContinuousMap.sum_apply, smul_eq_mul]
  rw [olderField_apply_eq_coefficientCutoff K M ell n hK ω x]
  rw [Finset.mul_sum]
  have hsum := native_source_band_index_sum n height
    (fun j => Real.sqrt t * (shellFieldScalarRestriction K (ω.1 j) x))
  rw [hsum]
  simp only [attenuatedCoefficient, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  rfl

theorem nativeHeatStep_bandIndex (m : ℤ) (ns : ℕ) :
    nativeSourceBandIndex (m + 1) ns = nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns := by
  funext d
  simp only [nativeSourceBandIndex, nativeHeatQ3RefinedCarrierPhysicalShellsGen]
  ring

/-- The time-one carrier field. -/
noncomputable def nativeHeatStepFieldOne (m : ℤ) (ns : ℕ) (ω : Cutoff.CutoffSample 2) :
    C(nativeHeatQ3RefinedCarrierDomain m, ℝ) :=
  olderField (nativeHeatQ3RefinedCarrierDomain m) (m + 1) ω +
    Real.sqrt 1 • modelBand (nativeHeatQ3RefinedCarrierDomain m)
      (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) ω

/-- On every refined child the time-one carrier field is the completed coefficient. -/
theorem nativeHeatStep_childField_coefficient (M : ABKModel 2) (m : ℤ) (ns : ℕ)
    (ω : Cutoff.CutoffSample 2) (i : nativeHeatQ3RefinedCarrierIndex) (x : Vec 2)
    (hx : x ∈ cubeSet (nativeHeatQ3RefinedCarrierChild m i)) :
    responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact
        (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) ℝ ℝ
        (nativeHeatQ3RefinedCarrierOldMap m (nativeHeatStepFieldOne m ns ω) i)) x =
      (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun x := by
  have hmem : x ∈ nativeHeatQ3RefinedCarrierDomain m :=
    nativeHeatQ3RefinedCarrierChild_closure_subset m i (subset_closure hx)
  have hfield := nativeHeatStep_field_apply M (nativeHeatQ3RefinedCarrierDomain m)
    (m + 1) ns 1 ω ⟨x, hmem⟩
  rw [nativeHeatStep_bandIndex] at hfield
  rw [responsePlanarCoefficientField, responseCoefficientExtension_eq _ hx,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]
  have hval : (nativeHeatQ3RefinedCarrierOldMap m (nativeHeatStepFieldOne m ns ω) i)
      ⟨x, subset_closure hx⟩ = (nativeHeatStepFieldOne m ns ω) ⟨x, hmem⟩ := rfl
  rw [hval]
  have hsymm := native_source_band_attenuated_symm M (m + 1) ns 1 ω x
  have hplanar := native_source_planar_of_symm M.nu _ hsymm
  have hcoef := full_response_coefficient_unit M (m + 1) (m + 1 + (ns : ℤ)) (by omega) ω
  simp only [Real.sqrt_one] at hfield hplanar hsymm
  have hcoefx : attenuatedCoefficient M (m + 1) (m + 1 + (ns : ℤ)) (fun _ => 1) ω x =
      (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun x := by
    rw [hcoef]
  have hF : nativeHeatStepFieldOne m ns ω ⟨x, hmem⟩ =
      attenuatedCoefficient M (m + 1) (m + 1 + (ns : ℤ)) (fun _ => 1) ω x 1 0 := by
    simpa [nativeHeatStepFieldOne, Real.sqrt_one] using hfield
  rw [hF, ← hcoefx]
  exact hplanar

/-- The four-load child trace of the carrier field is the actual child trace. -/
theorem nativeHeatStep_childTrace_eq (M : ABKModel 2) (m : ℤ) (ns : ℕ)
    (ω : Cutoff.CutoffSample 2) (i : nativeHeatQ3RefinedCarrierIndex) :
    childTraceObservable (measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
      (volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i)) M.nu
      (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M (m + 1)).1
      (nativeHeatQ3RefinedCarrierOldMap m (nativeHeatStepFieldOne m ns ω) i) =
      nativeHeatStepChildTrace M m ns i ω := by
  rw [nativeHeat_childTrace_eq_traceDefect]
  have hae : responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact
        (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) ℝ ℝ
        (nativeHeatQ3RefinedCarrierOldMap m (nativeHeatStepFieldOne m ns ω) i))
      =ᵐ[volume.restrict (cubeSet (nativeHeatQ3RefinedCarrierChild m i))]
      (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun := by
    filter_upwards [ae_restrict_mem (μ := volume)
      (measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))] with x hx
    exact nativeHeatStep_childField_coefficient M m ns ω i x hx
  unfold nativeHeatStepChildTrace traceDefect
  rw [coarseBlockMatrix_congr_of_ae_eq hae]

/-- At time one the source moment is the moment of the average of the actual child traces. -/
theorem nativeHeatStep_moment_one_eq (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m : ℤ) (k : ℕ) :
    nativeHeatStepMoment ns M h hM m k 1 =
      ∫ ω, (nativeHeatStepChildAverage M m ns ω) ^ k ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  unfold nativeHeatStepMoment nativeHeatQ3RefinedCarrierSourceMomentGen
  rw [nativeHeatChildBandMoment_one_eq_actualBandAverage]
  unfold bandModelAverage
  apply integral_congr_ae
  filter_upwards with ω
  have hfield : (nativeHeatQ3RefinedCarrierOldMap m) (olderField (nativeHeatQ3RefinedCarrierDomain m)
        (m + 1) ω) + Real.sqrt 1 • (nativeHeatQ3RefinedCarrierOldMap m)
        (modelBand (nativeHeatQ3RefinedCarrierDomain m)
          (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) ω) =
      nativeHeatQ3RefinedCarrierOldMap m (nativeHeatStepFieldOne m ns ω) := by
    unfold nativeHeatStepFieldOne
    rw [map_add, map_smul]
  rw [hfield]
  unfold childPower childMeanTrace nativeHeatStepChildAverage
  congr 1
  have hsum : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      childTraceObservable (measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i)) M.nu
        (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M (m + 1)).1
        (nativeHeatQ3RefinedCarrierOldMap m (nativeHeatStepFieldOne m ns ω) i) =
        nativeHeatStepChildTrace M m ns i ω :=
    fun i => nativeHeatStep_childTrace_eq M m ns ω i
  simp only [hsum]
  congr 1
  norm_num

theorem nativeHeatStep_cutoff_trace_subadditive (M : ABKModel 2)
    (n : ℤ) (Q : TriadicCube 2) (r : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (ω : Cutoff.CutoffSample 2) :
    traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun σ ≤
      descendantsAverage Q r (fun R =>
        traceDefect (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun σ) := by
  have h := Inverse.history_weighted_trace_mono
    (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun)
    (descendantsAverageBlockMat Q r (fun R =>
      coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun))
    σ hσ (Variational.cutoff_coarse_matrix_subadditive M n Q r ω)
  have he : descendantsAverage Q r (fun R =>
      traceDefect (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun σ) =
      σ⁻¹ * Matrix.trace
          (descendantsAverageBlockMat Q r (fun R =>
            coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun)).upperLeft +
        σ * Matrix.trace
          (descendantsAverageBlockMat Q r (fun R =>
            coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun)).lowerRight - 4 := by
    simp only [traceDefect, Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply]
    dsimp only [descendantsAverageBlockMat, descendantsAverageMat]
    simp only [sub_eq_add_neg, descendantsAverage_add, descendantsAverage_mul_left,
      descendantsAverage_const]
  rw [he]
  exact h

/-- The carrier index enumerates the depth-ten mesh cells. -/
noncomputable def nativeHeatStepIndexEquiv :
    nativeHeatQ3RefinedCarrierIndex ≃ (Fin 2 → Fin (3 ^ 10)) :=
  finProdFinEquiv.symm.trans (piFinTwoEquiv (fun _ : Fin 2 => Fin (3 ^ 10))).symm

theorem nativeHeatStepIndexEquiv_child (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex) :
    nativeHeatQ3RefinedCarrierChild m i =
      diagMeshCell (originCube 2 (m + 10)) 10 (nativeHeatStepIndexEquiv i) := by
  unfold nativeHeatQ3RefinedCarrierChild nativeHeatQ3RefinedChildCube
    nativeHeatQ3RefinedChildDigits
  congr 1

theorem nativeHeatStep_parent_le_average (M : ABKModel 2) (m : ℤ) (ns : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    0 ≤ nativeHeatStepParentTrace M m ns ω ∧
      nativeHeatStepParentTrace M m ns ω ≤ nativeHeatStepChildAverage M m ns ω := by
  have hσ := (Annealed.sigmaBar_characterization M (m + 1)).1
  refine ⟨?_, ?_⟩
  · obtain ⟨Λ, hEll⟩ := cutoff_isEllipticFieldOn_cube M (m + 1 + (ns : ℤ)) ω
      (originCube 2 (m + 10))
    exact traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll hσ
  · have hsub := nativeHeatStep_cutoff_trace_subadditive M (m + 1 + (ns : ℤ))
      (originCube 2 (m + 10)) 10 (Annealed.sigmaBar M (m + 1) : ℝ) hσ ω
    rw [diagDescendantsAverage_eq_grid_average] at hsub
    have hsum : (∑ k : Fin 2 → Fin (3 ^ 10),
        traceDefect (cubeSet (diagMeshCell (originCube 2 (m + 10)) 10 k))
          (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
          (Annealed.sigmaBar M (m + 1) : ℝ)) =
        ∑ i : nativeHeatQ3RefinedCarrierIndex, nativeHeatStepChildTrace M m ns i ω := by
      symm
      refine Fintype.sum_equiv nativeHeatStepIndexEquiv _ _ ?_
      intro i
      unfold nativeHeatStepChildTrace
      rw [nativeHeatStepIndexEquiv_child]
    have hc : (((3 ^ 10 : ℕ) : ℝ)⁻¹) ^ 2 = (9 ^ 10 : ℝ)⁻¹ := by norm_num
    rw [hc, hsum] at hsub
    exact hsub

theorem nativeHeatStep_trace_aemeasurable (M : ABKModel 2) (N : ℤ) (Q : TriadicCube 2)
    (σ : ℝ) :
    AEMeasurable (fun ω => traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu N ω).toFun σ)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have h := ASDExplicitGamma.Model.aemeasurable_traceDefect_cutoffLaw M N Q σ
  rw [Cutoff.coefficientCutoffLaw_eq_map] at h
  exact h.comp_aemeasurable (Cutoff.measurable_coefficientCutoff M.nu N).aemeasurable

/-- Every refined child trace has the law of the origin cell trace of the same scale. -/
theorem nativeHeatStep_childTrace_law (M : ABKModel 2) (m : ℤ) (ns : ℕ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    Measure.map (nativeHeatStepChildTrace M m ns i) (Cutoff.cutoffSampleLaw M).toMeasure =
      Measure.map (fun ω => traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
        (Annealed.sigmaBar M (m + 1) : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hlaw := ASDExplicitGamma.Model.map_traceDefect_cube_eq_origin M (m + 1 + (ns : ℤ))
    (nativeHeatQ3RefinedCarrierChild m i) (Annealed.sigmaBar M (m + 1) : ℝ)
  rw [nativeHeatQ3RefinedCarrierChild_scale, Cutoff.coefficientCutoffLaw_eq_map] at hlaw
  have hm := Cutoff.measurable_coefficientCutoff (d := 2) M.nu (m + 1 + (ns : ℤ))
  have hf1 := ASDExplicitGamma.Model.aemeasurable_traceDefect_cutoffLaw M (m + 1 + (ns : ℤ))
    (nativeHeatQ3RefinedCarrierChild m i) (Annealed.sigmaBar M (m + 1) : ℝ)
  have hf2 := ASDExplicitGamma.Model.aemeasurable_traceDefect_cutoffLaw M (m + 1 + (ns : ℤ))
    (originCube 2 m) (Annealed.sigmaBar M (m + 1) : ℝ)
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hf1 hf2
  rw [AEMeasurable.map_map_of_aemeasurable hf1 hm.aemeasurable] at hlaw
  rw [AEMeasurable.map_map_of_aemeasurable hf2 hm.aemeasurable] at hlaw
  exact hlaw

/-- Every child trace is in `L^20`. -/
theorem nativeHeatStep_childTrace_memLp (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ) (ns : ℕ)
    (hpast : ∀ j < m + 1, nativeInductionState M h j)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    MemLp (nativeHeatStepChildTrace M m ns i) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hfac := (native_source_child_band_raw_factors M h hM hg (m + 1) ns hpast 1 le_rfl).1
  have hO : MemLp (fun ω => traceDefect (cubeSet (originCube 2 m))
      (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
      (Annealed.sigmaBar M (m + 1) : ℝ)) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
    have hfun : (fun ω : Cutoff.CutoffSample 2 => modelTraceObservable (m + 1 - 1) M.nu
        (Annealed.sigmaBar M (m + 1) : ℝ) (nativeSourceChildBandScalar (m + 1) ns 1 ω)) =
        fun ω => traceDefect (cubeSet (originCube 2 m))
          (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
          (Annealed.sigmaBar M (m + 1) : ℝ) := by
      funext ω
      rw [native_source_child_band_trace_one M (m + 1) ns ω]
      simp only [Int.add_sub_cancel]
    simpa [hfun] using hfac
  have hTi := nativeHeatStep_trace_aemeasurable M (m + 1 + (ns : ℤ))
    (nativeHeatQ3RefinedCarrierChild m i) (Annealed.sigmaBar M (m + 1) : ℝ)
  have hlaw := nativeHeatStep_childTrace_law M m ns i
  have hOm := nativeHeatStep_trace_aemeasurable M (m + 1 + (ns : ℤ)) (originCube 2 m)
    (Annealed.sigmaBar M (m + 1) : ℝ)
  have h1 : MemLp (id : ℝ → ℝ) 20 (Measure.map (fun ω => traceDefect (cubeSet (originCube 2 m))
      (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
      (Annealed.sigmaBar M (m + 1) : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hOm).2 hO
  rw [← hlaw] at h1
  exact (memLp_map_measure_iff aestronglyMeasurable_id hTi).1 h1

theorem nativeHeatStep_average_memLp (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ) (ns : ℕ)
    (hpast : ∀ j < m + 1, nativeInductionState M h j) :
    MemLp (nativeHeatStepChildAverage M m ns) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hs := (memLp_finsetSum' (Finset.univ : Finset nativeHeatQ3RefinedCarrierIndex)
    (fun i _ => nativeHeatStep_childTrace_memLp M h hM hg m ns hpast i)).const_mul
    ((9 ^ 10 : ℝ)⁻¹)
  convert hs using 1
  funext ω
  simp [nativeHeatStepChildAverage, Finset.sum_apply]

theorem nativeHeatStep_average_nonneg (M : ABKModel 2) (m : ℤ) (ns : ℕ)
    (ω : Cutoff.CutoffSample 2) : 0 ≤ nativeHeatStepChildAverage M m ns ω :=
  (nativeHeatStep_parent_le_average M m ns ω).1.trans
    (nativeHeatStep_parent_le_average M m ns ω).2

theorem nativeHeatStep_average_integrable_pow (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ) (ns : ℕ)
    (hpast : ∀ j < m + 1, nativeInductionState M h j) (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20) :
    Integrable (fun ω => (nativeHeatStepChildAverage M m ns ω) ^ k)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  letI : IsProbabilityMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
    (Cutoff.cutoffSampleLaw M).property
  have hmem := (nativeHeatStep_average_memLp M h hM hg m ns hpast).mono_exponent
    (by exact_mod_cast hk20 : (k : ℝ≥0∞) ≤ 20)
  have hh := hmem.integrable_norm_pow (p := k) (by omega)
  convert hh using 1
  ext ω
  rw [Real.norm_eq_abs, abs_of_nonneg (nativeHeatStep_average_nonneg M m ns ω)]

/-- The parent trace is in `L^20` once the time-one twentieth moment is capped. -/
theorem nativeHeatStep_parent_L20_le (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m : ℤ) (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l) (y : ℝ) (hy : 0 ≤ y)
    (hM20 : nativeHeatStepMoment ns M h hM m 20 1 ≤ y ^ 20) :
    eLpNorm (nativeHeatStepParentTrace M m ns) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal y := by
  set μ := (Cutoff.cutoffSampleLaw M).toMeasure with hμ
  have hP := nativeHeatStep_parent_le_average M m ns
  have hPm : AEStronglyMeasurable (nativeHeatStepParentTrace M m ns) μ :=
    (nativeHeatStep_trace_aemeasurable M (m + 1 + (ns : ℤ)) (originCube 2 (m + 10))
      (Annealed.sigmaBar M (m + 1) : ℝ)).aestronglyMeasurable
  have hint := nativeHeatStep_average_integrable_pow M h hM hg m ns hpast 20 (by norm_num)
    le_rfl
  have hpow : Integrable (fun ω => (nativeHeatStepChildAverage M m ns ω) ^ (20 : ℝ)) μ := by
    have hfun : (fun ω => (nativeHeatStepChildAverage M m ns ω) ^ (20 : ℝ)) =
        fun ω => (nativeHeatStepChildAverage M m ns ω) ^ (20 : ℕ) := by
      funext ω
      rw [← Real.rpow_natCast]
      norm_num
    rw [hfun]
    exact hint
  apply eLpNorm_le_of_twentieth_lintegral μ hPm
  calc ∫⁻ ω, ‖nativeHeatStepParentTrace M m ns ω‖ₑ ^ (20 : ℝ) ∂μ
      ≤ ∫⁻ ω, ‖nativeHeatStepChildAverage M m ns ω‖ₑ ^ (20 : ℝ) ∂μ := by
        apply lintegral_mono
        intro ω
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        rw [Real.enorm_eq_ofReal (hP ω).1,
          Real.enorm_eq_ofReal (nativeHeatStep_average_nonneg M m ns ω)]
        exact ENNReal.ofReal_le_ofReal (hP ω).2
    _ = ENNReal.ofReal (∫ ω, (nativeHeatStepChildAverage M m ns ω) ^ (20 : ℝ) ∂μ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hpow
          (Filter.Eventually.of_forall fun ω =>
            Real.rpow_nonneg (nativeHeatStep_average_nonneg M m ns ω) _)]
        apply lintegral_congr
        intro ω
        rw [Real.enorm_eq_ofReal (nativeHeatStep_average_nonneg M m ns ω),
          ENNReal.ofReal_rpow_of_nonneg (nativeHeatStep_average_nonneg M m ns ω)
            (by norm_num)]
    _ ≤ (ENNReal.ofReal y) ^ (20 : ℝ) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hy (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        have e : ∫ ω, (nativeHeatStepChildAverage M m ns ω) ^ (20 : ℝ) ∂μ =
            nativeHeatStepMoment ns M h hM m 20 1 := by
          rw [nativeHeatStep_moment_one_eq]
          apply integral_congr_ae
          filter_upwards with ω
          rw [← Real.rpow_natCast]
          norm_num
        rw [e, show y ^ (20 : ℝ) = y ^ 20 by norm_cast]
        exact hM20

/-- The mean of the parent trace is at most the first carrier moment at time one. -/
theorem nativeHeatStep_parent_mean_le (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m : ℤ) (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l) (a : ℝ)
    (hM1 : nativeHeatStepMoment ns M h hM m 1 1 ≤ a) :
    ∫ ω, nativeHeatStepParentTrace M m ns ω ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ a := by
  set μ := (Cutoff.cutoffSampleLaw M).toMeasure with hμ
  have hP := nativeHeatStep_parent_le_average M m ns
  have hPm : AEStronglyMeasurable (nativeHeatStepParentTrace M m ns) μ :=
    (nativeHeatStep_trace_aemeasurable M (m + 1 + (ns : ℤ)) (originCube 2 (m + 10))
      (Annealed.sigmaBar M (m + 1) : ℝ)).aestronglyMeasurable
  have hA : Integrable (nativeHeatStepChildAverage M m ns) μ := by
    have := nativeHeatStep_average_integrable_pow M h hM hg m ns hpast 1 le_rfl
      (by norm_num)
    simpa only [pow_one] using this
  have hPi : Integrable (nativeHeatStepParentTrace M m ns) μ := by
    refine hA.mono' hPm (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (hP ω).1]
    exact (hP ω).2
  have h1 : ∫ ω, nativeHeatStepParentTrace M m ns ω ∂μ ≤
      ∫ ω, nativeHeatStepChildAverage M m ns ω ∂μ :=
    integral_mono hPi hA (fun ω => (hP ω).2)
  have e : ∫ ω, nativeHeatStepChildAverage M m ns ω ∂μ =
      nativeHeatStepMoment ns M h hM m 1 1 := by
    rw [nativeHeatStep_moment_one_eq]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (pow_one _).symm)
  linarith

end ASDExplicitGamma.Native

end

module

public import ASDExplicitGamma.Gaussian.BandFactor
public import ASDExplicitGamma.Gaussian.ModelHeatLaw

/-! # Actual finite fresh bands on the completed cutoff probability space -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal NNReal

namespace ASDExplicitGamma.Gaussian

/-- Finite sums here are the physical shell fields, before restrictions to child cells. -/
noncomputable def modelBand {b : ℕ} (K : Set (Vec 2)) [CompactSpace K]
    (k : Fin b → ℤ) (ω : Cutoff.CutoffSample 2) : C(K, ℝ) :=
  ∑ i, shellFieldScalarRestriction K (ω.1 (k i))

theorem measurable_modelBand {b : ℕ} (K : Set (Vec 2)) [CompactSpace K]
    (k : Fin b → ℤ) : Measurable (modelBand K k) :=
  Finset.measurable_sum _ fun i _ => (measurable_shellFieldScalarRestriction K).comp
    ((measurable_pi_apply (k i)).comp measurable_subtype_coe)

/-- Pulling back a finite independent family along an exact law-preserving map. -/
theorem iIndepFun_of_map {ι Ω Ω' E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (ν : Measure Ω') (g : Ω → Ω') (hg : Measurable g)
    (hmap : ρ.map g = ν) (X : ι → Ω' → E) (hX : ∀ i, Measurable (X i))
    (hi : iIndepFun X ν) : iIndepFun (fun i => X i ∘ g) ρ := by
  have hh := hi.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)
  rw [← hmap, Measure.map_map (measurable_pi_iff.mpr hX) hg] at hh
  simp_rw [Measure.map_map (hX _) hg] at hh
  exact (iIndepFun_iff_map_fun_eq_pi_map (fun i => ((hX i).comp hg).aemeasurable)).mpr hh

/-- The actual shell restrictions retain their joint independence. -/
theorem iIndepFun_shellRestrictions {b : ℕ} (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (k : Fin b → ℤ) (hk : Function.Injective k) :
    iIndepFun (fun i => fun ω : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction K (ω.1 (k i))) (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hi := ((Model.shellLevels_independent M).precomp hk).comp
    (fun _ => shellFieldScalarRestriction K) (fun _ => measurable_shellFieldScalarRestriction K)
  exact iIndepFun_of_map _ _ Subtype.val measurable_subtype_coe
    (Cutoff.map_cutoffSampleLaw_val M) _
    (fun i => (measurable_shellFieldScalarRestriction K).comp (measurable_pi_apply (k i))) hi

/-- A fresh finite band is independent of the entire completed older field. -/
theorem indepFun_olderField_band {b : ℕ} (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell))
    (k : Fin b → ℤ) (hk : ∀ i, m < k i) :
    IndepFun (olderField K m) (modelBand K k) (Cutoff.cutoffSampleLaw M).toMeasure := by
  let X : Cutoff.ShellSeq 2 → C(K, ℝ) := fun ω =>
    ∑' r : ℕ, shellFieldScalarRestriction K (ω (m - (r : ℤ)))
  let Y : Cutoff.ShellSeq 2 → C(K, ℝ) := fun ω =>
    ∑ i, shellFieldScalarRestriction K (ω (k i))
  have hX : @Measurable _ _ (Cutoff.shellIndexSigma (Iic m)) _ X := by
    let : MeasurableSpace (Cutoff.ShellSeq 2) := Cutoff.shellIndexSigma (Iic m)
    exact Measurable.tsum fun r => (measurable_shellFieldScalarRestriction K).comp
      (Cutoff.measurable_shellCoordinate_shellIndexSigma (by change m - (r : ℤ) ≤ m; omega))
  have hY : @Measurable _ _ (Cutoff.shellIndexSigma (Set.range k)) _ Y := by
    let : MeasurableSpace (Cutoff.ShellSeq 2) := Cutoff.shellIndexSigma (Set.range k)
    exact Finset.measurable_sum _ fun i _ => (measurable_shellFieldScalarRestriction K).comp
      (Cutoff.measurable_shellCoordinate_shellIndexSigma ⟨i, rfl⟩)
  have hXb := hX.mono (Cutoff.shellIndexSigma_le_borel _) le_rfl
  have hYb := hY.mono (Cutoff.shellIndexSigma_le_borel _) le_rfl
  have hind := Cutoff.indepFun_of_measurable_shellIndexSigma_of_disjoint M
    (Set.disjoint_left.mpr (fun z hz hz' => by obtain ⟨i, rfl⟩ := hz'; exact (hk i).not_ge hz)) hX hY
  have hpair := hind.map_prod_eq_prod_map_map hXb.aemeasurable hYb.aemeasurable
  rw [← Cutoff.map_cutoffSampleLaw_val M,
    Measure.map_map (hXb.prodMk hYb) measurable_subtype_coe,
    Measure.map_map hXb measurable_subtype_coe,
    Measure.map_map hYb measurable_subtype_coe] at hpair
  exact (indepFun_iff_map_prod_eq_prod_map_map (measurable_olderField K ell m hK).aemeasurable
    (measurable_modelBand K k).aemeasurable).mpr hpair

/-- Every actual finite band has one Hilbert-series realization. This discharges the band
law premise of the heat calculus; no replacement by independent spatial centers occurs. -/
theorem exists_modelBand_realization {b : ℕ} [NeZero b]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : Fin b → ℤ) (hk : Function.Injective k) :
    ∃ (T : BandHilbert b →L[ℝ] C(K, ℝ))
      (v : ℕ → BandHilbert b) (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand K k) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) := by
  classical
  have hex (i : Fin b) := freshShell_map_scalarRestriction_eq_gaussianSeries M h hM (k i - 1) (K := K)
  choose T v hv hlaw using hex
  simp only [sub_add_cancel] at hlaw
  let A := bandFactor T
  let w := bandDirections v
  have hw : Summable (fun j => ‖w j‖ ^ 2) := bandDirections_summable v hv
  refine ⟨A, w, hw, ?_⟩
  apply measure_eq_of_continuousMap_eval_linearCombination
  intro ι _ x t
  let L : C(K, ℝ) →L[ℝ] ℝ := ∑ i, t i • ContinuousMap.evalCLM ℝ (x i)
  have hL : (continuousMapEvalLinearCombination ι x t) = L := by
    funext f
    simp only [continuousMapEvalLinearCombination, L, sum_apply, smul_apply, smul_eq_mul,
      ContinuousMap.evalCLM_apply]
  rw [hL, Measure.map_map L.continuous.measurable (measurable_modelBand K k),
    Measure.map_map L.continuous.measurable (stronglyMeasurable_gaussianSeriesLimitE hw A).measurable]
  have hi := (iIndepFun_shellRestrictions K M k hk).comp
    (fun _ => L) (fun _ => L.continuous.measurable)
  let s : Fin b → ℝ≥0 := fun i => Real.toNNReal (∑' j, (L (T i (v i j))) ^ 2)
  have hs (i : Fin b) : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω => L (shellFieldScalarRestriction K (ω.1 (k i)))) = gaussianReal 0 (s i) := by
    have hm : Measurable (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction K (ω.1 (k i))) :=
      (measurable_shellFieldScalarRestriction K).comp
        ((measurable_pi_apply (k i)).comp measurable_subtype_coe)
    have hh := congrArg (fun ν : Measure C(K, ℝ) => ν.map L) (hlaw i)
    rw [Measure.map_map L.continuous.measurable hm,
      Measure.map_map L.continuous.measurable (stronglyMeasurable_gaussianSeriesLimitE (hv i) (T i)).measurable] at hh
    exact hh.trans (map_gaussianSeriesLimitE_linear (hv i) (T i) L)
  have hsum := independent_gaussian_sum_law (Cutoff.cutoffSampleLaw M).toMeasure
    (fun i ω => L (shellFieldScalarRestriction K (ω.1 (k i)))) s
    (fun i => L.continuous.measurable.comp ((measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (k i)).comp measurable_subtype_coe))) hi hs
  have he : (fun ω => L (modelBand K k ω)) =
      fun ω => ∑ i, L (shellFieldScalarRestriction K (ω.1 (k i))) := by
    funext ω
    exact map_sum L _ _
  simp only [Function.comp_def]
  rw [he, hsum]
  have hseries := map_gaussianSeriesLimitE_linear hw A L
  rw [hseries]
  congr 2
  dsimp only [s, A, w]
  rw [bandFactor_covariance v hv T L, Real.toNNReal_sum_of_nonneg (fun i _ => tsum_nonneg fun j => sq_nonneg _)]

end ASDExplicitGamma.Gaussian

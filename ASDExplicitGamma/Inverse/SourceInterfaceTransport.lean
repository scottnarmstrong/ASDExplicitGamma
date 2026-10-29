module

public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Inverse.SourceQ3CovarianceLaw
public import ASDExplicitGamma.Gaussian.ModelHeatTrace
public import ASDExplicitGamma.Main.PanelComparison
public import ASDExplicitGamma.Main.HeatIdentity
public import ASDExplicitGamma.Native.SourceSmallerGammaInterface
public import ASDExplicitGamma.Cold.NativeTrace

/-! Actual-law one-shell source transport in the completed OLD frame. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Set Filter Algsuperdiff.Section3 Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Native
open scoped ENNReal

noncomputable section

/-- The actual cutoff-law source mean during insertion of shell `m+1`,
observed at source depth `r` and kept in the true OLD frame `sigmaBar M m`. -/
noncomputable def inSourceMeanActual (M : ABKModel 2) (m : ℤ) (r : ℕ) (t : ℝ) : ℝ :=
  modelTraceHeatAverage (m - (r : ℤ)) M m t

/-- The actual expected source-energy generator for that same insertion and
frame. The q3 directions are the physical shell at `m+1`. -/
noncomputable def inSourceMeanRateActual (M : ABKModel 2) (h : ℝ)
    (m : ℤ) (r : ℕ) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * modelHeatTraceAverage
    (closure (cubeSet (originCube 2 (m - (r : ℤ))))) M m
    (modelTraceObservable (m - (r : ℤ)) M.nu (Annealed.sigmaBar M m : ℝ))
    (pureFluxMainCubeQ3Directions (m - (r : ℤ))
      (q3ModelAmplitude M h (m + 1)) (q3ModelLength (m + 1))) t

/-- A nonnegative uniform source-energy slope, defined from the actual-law
generator over the complete one-shell heat panel. -/
noncomputable def inSourceMeanSlopeActual (M : ABKModel 2) (h : ℝ)
    (m : ℤ) (r : ℕ) : ℝ :=
  max 0 (sSup (inSourceMeanRateActual M h m r '' Set.Icc 0 1))

/-- The zero-time source mean is the actual completed OLD mean, converted
from its extended expectation to `ℝ`. Both observables use the same cutoff
sample law and the same true frame `sigmaBar M m`. -/
theorem in_source_mean_old_endpoint
    (M : ABKModel 2) (m : ℤ) (r : ℕ) :
    inSourceMeanActual M m r 0 = (nativeCompletedSourceMean M m r).toReal := by
  let q : ℤ := m - (r : ℤ)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hpath (ω : Cutoff.CutoffSample 2) :
      traceDefect (cubeSet (originCube 2 q))
          (Model.partialInsertedCoefficient M m 0 ω).toFun
          (Annealed.sigmaBar M m : ℝ) = cutoffTraceDefect M m q ω := by
    have hcoeff : (Model.partialInsertedCoefficient M m 0 ω).toFun =
        (Cutoff.coefficientCutoff M.nu m ω).toFun := by
      ext x i j
      simp [Model.partialInsertedCoefficient]
    rw [cutoffTraceDefect, hcoeff]
  have hreal : modelTraceHeatAverage q M m 0 =
      ∫ ω, cutoffTraceDefect M m q ω ∂μ := by
    rw [modelTraceHeatAverage]
    exact integral_congr_ae (Filter.Eventually.of_forall hpath)
  have hint : Integrable (cutoffTraceDefect M m q) μ :=
    ASDExplicitGamma.Cold.integrable_cutoffTraceDefect M m q
  have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ cutoffTraceDefect M m q ω :=
    Filter.Eventually.of_forall (Variational.cutoffTraceDefect_nonneg M m q)
  have hconvert :
      (∫ ω, cutoffTraceDefect M m q ω ∂μ) =
        (nativeCompletedSourceMean M m r).toReal := by
    simpa only [nativeCompletedSourceMean, q, μ] using
      (integral_eq_lintegral_of_nonneg_ae hnonneg hint.aestronglyMeasurable)
  simpa only [inSourceMeanActual, q] using hreal.trans hconvert

theorem in_source_actual_heat_panel
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (r : ℕ) :
    mainHeatPanelIdentity (inSourceMeanActual M m r)
      (inSourceMeanRateActual M h m r) ∧
      ContinuousOn (inSourceMeanRateActual M h m r) (Set.Icc 0 1) := by
  let q : ℤ := m - (r : ℤ)
  let K := closure (cubeSet (originCube 2 q))
  let σ : ℝ := Annealed.sigmaBar M m
  let Φ := modelTraceObservable q M.nu σ
  let b := q3ModelAmplitude M h (m + 1)
  let L := q3ModelLength (m + 1)
  let H := pureFluxMainCubeQ3Directions q b L
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hΦ : HasPolynomiallyBoundedC2Derivatives Φ :=
    modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu σ M.nu_pos hσ
  obtain ⟨T, v, hA, hlaw, _, _, hheatCont, hderiv, hzero, _⟩ :=
    exists_modelTrace_heat_and_moment_identities q M h hM m
  have hqs : q + ((r + 1 : ℕ) : ℤ) = m + 1 := by
    dsimp [q]
    omega
  have hlaw' : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K
        (ω.1 (q + ((r + 1 : ℕ) : ℤ)))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) := by
    rw [hqs]
    exact hlaw
  have hcov (x : C(K, ℝ)) :
      modelCovarianceTrace Φ (fun j => T (v j)) x =
        modelCovarianceTrace Φ H x := by
    simpa [H, b, L, ← hqs] using
      source_q3_test_covariance_trace_eq_of_fresh_law q M h hM (r + 1)
        T v hA hlaw' Φ hΦ x
  have hrate : ∀ t : ℝ,
      (1 / 2 : ℝ) * modelHeatTraceAverage K M m Φ (fun j => T (v j)) t =
        inSourceMeanRateActual M h m r t := by
    intro t
    dsimp only [inSourceMeanRateActual, K, Φ, H, b, L, q, σ]
    unfold modelHeatTraceAverage modelHeatAverage
    apply congrArg (fun z : ℝ => (1 / 2 : ℝ) * z)
    apply integral_congr_ae
    filter_upwards [] with ω
    exact hcov (modelInsertedScalar
      (closure (cubeSet (originCube 2 (m - (r : ℤ))))) m t ω)
  have hrateCont : ContinuousOn (inSourceMeanRateActual M h m r) (Set.Ici 0) := by
    exact hheatCont.congr (fun t _ => (hrate t).symm)
  have hpanel : mainHeatPanelIdentity (inSourceMeanActual M m r)
      (inSourceMeanRateActual M h m r) := by
    apply mainHeatPanelIdentity_of_C1 hrateCont
    · intro t ht
      have hh := hderiv t ht
      rw [hrate t] at hh
      change HasDerivAt (modelTraceHeatAverage (m - (r : ℤ)) M m)
        (inSourceMeanRateActual M h m r t) t
      simpa [q] using hh
    · rw [← hrate 0]
      change HasDerivWithinAt (modelTraceHeatAverage (m - (r : ℤ)) M m)
        (1 / 2 * modelHeatTraceAverage K M m Φ (fun j => T (v j)) 0) (Set.Ici 0) 0
      simpa [q] using hzero
  exact ⟨hpanel, hrateCont.mono Set.Icc_subset_Ici_self⟩

theorem in_source_linear_transport_of_panel
    {f d : ℝ → ℝ} (hpanel : mainHeatPanelIdentity f d)
    (L : ℝ) (hL : ∀ t ∈ Set.Icc (0 : ℝ) 1, d t ≤ L)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    f τ ≤ f 0 + τ * L := by
  let g : ℝ → ℝ := fun t => f t - L * t
  have hlin : AbsolutelyContinuousOnInterval (fun t => L * t) 0 1 := by
    exact (contDiff_const.mul contDiff_id).contDiffOn.absolutelyContinuousOnInterval
  have hg : AbsolutelyContinuousOnInterval g 0 1 := by
    have hg' : AbsolutelyContinuousOnInterval (f - (fun t => L * t)) 0 1 :=
      hpanel.1.sub hlin
    have heq : g = f - (fun t => L * t) := by
      funext t
      rfl
    rw [heq]
    exact hg'
  have hsubset : Set.uIcc 0 τ ⊆ Set.uIcc 0 1 := by
    rw [uIcc_of_le hτ.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc (by norm_num) hτ.2
  have hgτ : AbsolutelyContinuousOnInterval g 0 τ := hg.mono hsubset
  have hderiv : ∀ᵐ t : ℝ, t ∈ Set.Icc 0 τ → deriv g t ≤ 0 := by
    filter_upwards [hpanel.2.1] with t hsource
    intro ht
    have ht' : t ∈ Set.uIcc (0 : ℝ) τ := by
      simpa only [uIcc_of_le hτ.1] using ht
    have ht01' : t ∈ Set.uIcc (0 : ℝ) 1 := hsubset ht'
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht01'
    have hft := hsource ht01
    have hsub := hft.sub ((hasDerivAt_id t).const_mul L)
    have hsub' : HasDerivAt g (d t - L) t := by
      convert hsub using 1
      · funext s
        simp [g]
      · ring
    rw [hsub'.deriv]
    exact sub_nonpos.mpr (hL t ht01)
  have hend := panel_endpoint_le_of_deriv_nonpos hτ.1 hgτ hderiv
  dsimp [g] at hend
  linarith

/-- Actual-law one-shell transport with its own nonnegative panel-supremum
slope. This form is independent of the source-row producer and can be summed
against OLD history weights before the producer rows are instantiated. -/
theorem in_source_actual_mean_transport_by_slope
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (r : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    inSourceMeanActual M m r t ≤
      inSourceMeanActual M m r 0 + t * inSourceMeanSlopeActual M h m r := by
  obtain ⟨hpanel, hcont⟩ := in_source_actual_heat_panel M h hM m r
  have hbdd : BddAbove
      (inSourceMeanRateActual M h m r '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.bddAbove_image hcont
  have hrate : inSourceMeanRateActual M h m r t ≤
      inSourceMeanSlopeActual M h m r := by
    unfold inSourceMeanSlopeActual
    exact le_max_of_le_right (le_csSup hbdd ⟨t, ht, rfl⟩)
  exact in_source_linear_transport_of_panel hpanel _
    (fun s hs => by
      unfold inSourceMeanSlopeActual
      exact le_trans (le_csSup hbdd ⟨s, hs, rfl⟩) (le_max_right _ _)) ht

/-- IN-SOURCE-TRANSPORT as an actual-law expectation statement. The panel
mean is always `Cutoff.cutoffSampleLaw M`, with coefficient `M.nu` and the
single OLD true frame `sigmaBar M m`; its slope is the supremum of the actual
positive source-energy generator on that panel. The exact source-row input is
retained as the companion endpoint output, including its actual-law L20 tail. -/
theorem in_source_transport_source
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (hSmall : NativeSourceSmallerGammaBounds M m)
    :
    (∀ r : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      inSourceMeanActual M m r t ≤
        inSourceMeanActual M m r 0 + t * inSourceMeanSlopeActual M h m r) ∧
      (∀ r : ℕ,
        inSourceMeanActual M m r 0 = (nativeCompletedSourceMean M m r).toReal) ∧
      nativeCompletedSourceMean M m 5 ≤
        ENNReal.ofReal (theta M * (inSourceA5 : ℝ)) ∧
      nativeCompletedSourceWeak M m 5 ≤
        ENNReal.ofReal (theta M * (inSourceXi5Pre : ℝ)) := by
  have hRows := in_source_rows_source M m hSmall
  refine ⟨?_, ?_, hRows.2.2.1, hRows.2.2.2.1⟩
  · intro r t ht
    obtain ⟨hpanel, hcont⟩ := in_source_actual_heat_panel M h hM m r
    have hbdd : BddAbove
        (inSourceMeanRateActual M h m r '' Set.Icc (0 : ℝ) 1) :=
      isCompact_Icc.bddAbove_image hcont
    have hrate : inSourceMeanRateActual M h m r t ≤
        inSourceMeanSlopeActual M h m r := by
      unfold inSourceMeanSlopeActual
      exact (le_max_of_le_right (le_csSup hbdd ⟨t, ht, rfl⟩))
    exact in_source_linear_transport_of_panel hpanel _
      (fun s hs => by
        unfold inSourceMeanSlopeActual
        exact le_trans (le_csSup hbdd ⟨s, hs, rfl⟩) (le_max_right _ _)) ht
  · intro r
    exact in_source_mean_old_endpoint M m r

end
end ASDExplicitGamma.Inverse


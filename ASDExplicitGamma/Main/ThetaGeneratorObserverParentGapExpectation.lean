module

public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeA
public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Inverse.MixedBridgeConclusion
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeLocalWeightedTheta
public import ASDExplicitGamma.Inverse.MixedBridgeSharpSlope
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Numerics.Native.Source5
public import ASDExplicitGamma.Main.ObserverParentGapTheta
public import ASDExplicitGamma.Inverse.MixedBridgeObsCellTheta
public import ASDExplicitGamma.Main.ThetaGeneratorELinearCellExpectation

/-! Observer-root parent-gap row: expectation of the reference-subtracted tiled
parent primal error, `E sqrt(avg V^2) <= mainV xi f`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
  ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.MainReturn ASDExplicitGamma.Numerics.Native
  ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Cutoff ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped ENNReal
open ASDExplicitGamma.Numerics.MainReturn ASDExplicitGamma.Numerics.Native
  ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Cutoff ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Local OLD-Theta row on an arbitrary scale-`m-5` cell against the explicit
`mainEnvelopeXi`. -/
theorem main_envelope_xi_obscell_row_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) (hU : U.scale = m - ((5 : ℕ) : ℤ)) :
    Integrable (fun ω => mixedOldTheta M m U t ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, mixedOldTheta M m U t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) /
        (Annealed.sigmaBar M m : ℝ)) ^ 2)
        M.gamma (theta M * mainSourceInversePrefix) (theta M) t := by
  let v := (q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)) ^ 2
  have hlocal := mixed_bridge_obscell_old_theta_local_xi5
    M h hM hγ N hpast m hm t ht U hU
  have htheta0 : 0 ≤ theta M := (ASDExplicitGamma.Cold.cold_theta_pos M).le
  have htheta1 : theta M ≤ 1 := ASDExplicitGamma.Cold.cold_theta_le_one M hγ
  have hxi0 : 0 ≤ (inSourceXi5Pre : ℝ) := by
    norm_num [inSourceXi5Pre,
      ASDExplicitGamma.Numerics.Native.nativeSource5Result]
  have hxiCapQ : inSourceXi5Pre ≤
      (140120486781 / 1000000000000 : ℚ) := by
    exact nativeSource5_caps.2.2.1.le
  have hxiCap : (inSourceXi5Pre : ℝ) ≤
      (140120486781 / 1000000000000 : ℝ) := by
    have hxiCapR := (Rat.cast_le (K := ℝ)).2 hxiCapQ
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow,
      Rat.cast_one] using hxiCapR
  have hprefixQ : (140120486781 / 1000000000000 : ℚ) ≤
      observer1Panel0Data.initialInverseMean - (1 / 10 ^ 12 : ℚ) := by
    decide +kernel
  have hprefix : (140120486781 / 1000000000000 : ℝ) ≤
      mainSourceInversePrefix := by
    change (140120486781 / 1000000000000 : ℝ) ≤
      (observer1Panel0Data.initialInverseMean : ℝ) - (1 / 10 ^ 12 : ℝ)
    have hprefixR := (Rat.cast_le (K := ℝ)).2 hprefixQ
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_one] using hprefixR
  have hpreCap : mixedXiPreCap M ≤ theta M * mainSourceInversePrefix := by
    rw [mixedXiPreCap]
    exact mul_le_mul_of_nonneg_left (hxiCap.trans hprefix) htheta0
  have hslope := mixed_bridge_local_slope_main_chi
    M h hM hγ N hpast m hm
  have htimeSlope : t * mixedBridgeLocalSlope M h m ≤
      t * mainChi v M.gamma :=
    mul_le_mul_of_nonneg_left hslope ht.1
  refine ⟨hlocal.1, hlocal.2.trans ?_⟩
  unfold mixedBridgeLocalXi5
  have hres : (1 / (13 * 10 ^ 12 : ℝ)) * theta M ≤ (1 / 10 ^ 12 : ℝ) * theta M := by
    nlinarith
  calc
    _ ≤ theta M * mainSourceInversePrefix + (1 / 10 ^ 12 : ℝ) * theta M +
          t * mainChi v M.gamma :=
        add_le_add (add_le_add hpreCap hres) htimeSlope
    _ = mainEnvelopeXi v M.gamma (theta M * mainSourceInversePrefix) (theta M) t := rfl

theorem observer_cell_scale_Th (m : ℤ) (hobs : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (5 + hobs)) :
    U.scale = m - ((5 : ℕ) : ℤ) := by
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
  rw [hs]
  simp only [originCube]
  push_cast
  omega

/-- The observer trace term `A = traceDefect Q a 1` is nonnegative, integrable and
has mean `modelTraceHeatAverage (m+hobs) M m t`. -/
theorem observer_anchor_integrable_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hobs : ℕ) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    Integrable (fun ω => rawCubeFourLoadTrace M m (originCube 2 (m + hobs)) t ω) μ ∧
    (∫ ω, rawCubeFourLoadTrace M m (originCube 2 (m + hobs)) t ω ∂μ) =
      modelTraceHeatAverage (m + hobs) M m t := by
  intro μ
  refine ⟨?_, rfl⟩
  classical
  set Q : TriadicCube 2 := originCube 2 (m + hobs) with hQ
  set d : ℕ := 5 + hobs with hd
  have hkey : ∀ ω : CutoffSample 2, 0 ≤ rawCubeFourLoadTrace M m Q t ω ∧
      rawCubeFourLoadTrace M m Q t ω ≤ descendantsAverage Q d
        (fun U => rawWeakTraceSequence M m U t ω 0) := by
    intro ω
    set σ : ℝ := (Annealed.sigmaBar M m : ℝ) with hσdef
    have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
    set k := mainELinearObsCoefficient Q m t ω with hk
    set a : CoeffField 2 := responseFramePlanarCoefficientField M.nu σ k with ha
    have hEll := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) M.nu σ M.nu_pos hσ k
    have hfieldQ : ∀ x ∈ openCubeSet Q,
        a x = σ⁻¹ • (Model.partialInsertedCoefficient M m t ω).toFun x := fun x hx =>
      old_signed_obs_frame_eq_scaled_partial M Q m t ω x hx
    have hQ0 : Q ∈ descendantsAtDepth Q 0 := by simp
    have hA : traceDefect (openCubeSet Q) a 1 = rawCubeFourLoadTrace M m Q t ω :=
      obs_partial_trace_cell_eq_raw M m t ht ω Q a hfieldQ Q 0 hQ0
    rw [← hA]
    refine ⟨Cold.coarse_square_traceDefect_nonneg Q hEll, ?_⟩
    have hle := old_signed_parent_trace_le_child Q d M.nu σ M.nu_pos hσ k
    refine hle.trans (le_of_eq ?_)
    have htower := descendantsAverage_add_eq_descendantsAverage_descendantsAverage Q d 0
      (fun U => traceDefect (openCubeSet U) a 1)
    have h0 : ∀ (U : TriadicCube 2) (F : TriadicCube 2 → ℝ), descendantsAverage U 0 F = F U := by
      intro U F
      simp [descendantsAverage]
    change descendantsAverage Q (d + 0) _ = _ at htower
    show descendantsAverage Q d _ = _
    rw [show d = d + 0 from rfl, htower]
    unfold descendantsAverage
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro U hU
    have hfieldU : ∀ x ∈ openCubeSet U,
        a x = σ⁻¹ • (Model.partialInsertedCoefficient M m t ω).toFun x :=
      fun x hx => hfieldQ x (openCubeSet_subset_of_mem_descendantsAtDepth hU hx)
    exact obs_source_trace_average_eq M m t ht ω U a hfieldU 0
  have hcellInt : ∀ U ∈ descendantsAtDepth Q d,
      Integrable (fun ω => rawWeakTraceSequence M m U t ω 0) μ := by
    intro U hU
    exact (mixed_bridge_obscell_trace_mean M h hM hγ N hpast m hm t ht 5 (by omega) U
      (observer_cell_scale_Th m hobs U hU) 0).1
  have hbound : Integrable (fun ω => descendantsAverage Q d
      (fun U => rawWeakTraceSequence M m U t ω 0)) μ := by
    unfold descendantsAverage
    exact (integrable_finsetSum _ hcellInt).const_mul _
  have hmeas : AEStronglyMeasurable (fun ω => rawCubeFourLoadTrace M m Q t ω) μ :=
    mixed_bridge_obscell_raw_depth_aestronglyMeasurable M m (m + hobs) t
  refine hbound.mono' hmeas (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (hkey ω).1]
  exact (hkey ω).2

/-- Observer-root parent-gap row: the tiled parent primal error size on the
depth-`5+hobs` cells of `originCube 2 (m+hobs)` has a majorant with expectation
at most `mainV xi f = sqrt (xi - betaOld f)`, `f` the observer mean. -/
theorem observer_parent_gap_row_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ) (h40 : hobs ≤ 40) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    ∃ Vbar : CutoffSample 2 → ℝ, Integrable Vbar μ ∧ (∀ ω, 0 ≤ Vbar ω) ∧
      (∀ ω, Real.sqrt (descendantsAverage (originCube 2 (m + hobs)) (5 + hobs)
        (fun U => oldSignedPrimalErrorSize (originCube 2 (m + hobs)) U M.nu
          (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1
          (mainELinearObsCoefficient (originCube 2 (m + hobs)) m t ω) ^ 2)) ≤
        Vbar ω) ∧
      (∫ ω, Vbar ω ∂μ) ≤
        mainV (mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) /
          (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) t)
          (modelTraceHeatAverage (m + hobs) M m t) := by
  intro μ
  classical
  set Q : TriadicCube 2 := originCube 2 (m + hobs) with hQ
  set d : ℕ := 5 + hobs with hd
  set ξ : ℝ := mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) t with hξ
  set f : ℝ := modelTraceHeatAverage (m + hobs) M m t with hf
  set C : ℝ := 3683 / 2500 with hC
  have hrow := fun U (hU : U ∈ descendantsAtDepth Q d) =>
    main_envelope_xi_obscell_row_Th M h hM hγ N hpast m hm t ht U
      (observer_cell_scale_Th m hobs U hU)
  have hanchor := observer_anchor_integrable_Th M h hM hγ N hpast m hm t ht hobs
  let avgΘ : CutoffSample 2 → ℝ := fun ω => descendantsAverage Q d
    (fun U => mixedOldTheta M m U t ω)
  have hΘint : Integrable avgΘ μ := by
    unfold avgΘ descendantsAverage
    exact (integrable_finsetSum _ (fun U hU => (hrow U hU).1)).const_mul _
  have hcardpos : 0 < ((descendantsAtDepth Q d).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q d)
  have hΘle : (∫ ω, avgΘ ω ∂μ) ≤ ξ := by
    have h1 : (∫ ω, avgΘ ω ∂μ) = ((descendantsAtDepth Q d).card : ℝ)⁻¹ *
        ∑ U ∈ descendantsAtDepth Q d, ∫ ω, mixedOldTheta M m U t ω ∂μ := by
      unfold avgΘ descendantsAverage
      rw [integral_const_mul, integral_finsetSum _ (fun U hU => (hrow U hU).1)]
    rw [h1]
    have h2 : (∑ U ∈ descendantsAtDepth Q d, ∫ ω, mixedOldTheta M m U t ω ∂μ) ≤
        ∑ U ∈ descendantsAtDepth Q d, ξ :=
      Finset.sum_le_sum (fun U hU => (hrow U hU).2)
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    calc _ ≤ ((descendantsAtDepth Q d).card : ℝ)⁻¹ *
          (((descendantsAtDepth Q d).card : ℝ) * ξ) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hcardpos.le)
      _ = ξ := by field_simp
  let A : CutoffSample 2 → ℝ := fun ω => rawCubeFourLoadTrace M m Q t ω
  have hAint : Integrable A μ := hanchor.1
  have hAmean : (∫ ω, A ω ∂μ) = f := hanchor.2
  let X : CutoffSample 2 → ℝ := fun ω => avgΘ ω - C * A ω
  have hXint : Integrable X μ := hΘint.sub (hAint.const_mul C)
  have hXle : (∫ ω, X ω ∂μ) ≤ ξ - C * f := by
    have : (∫ ω, X ω ∂μ) = (∫ ω, avgΘ ω ∂μ) - C * ∫ ω, A ω ∂μ := by
      unfold X
      rw [integral_sub hΘint (hAint.const_mul C), integral_const_mul]
    rw [this, hAmean]
    linarith
  have hpath : ∀ ω, descendantsAverage Q d (fun U =>
      oldSignedPrimalErrorSize Q U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1
        (mainELinearObsCoefficient Q m t ω) ^ 2) ≤ X ω := by
    intro ω
    have hp := observer_parent_primal_le_avg_theta M hγ m t ht hobs h40 ω
    have hAeq : traceDefect (openCubeSet Q)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainELinearObsCoefficient Q m t ω)) 1 = A ω := by
      have hQ0 : Q ∈ descendantsAtDepth Q 0 := by simp
      exact obs_partial_trace_cell_eq_raw M m t ht ω Q _
        (fun x hx => old_signed_obs_frame_eq_scaled_partial M Q m t ω x hx) Q 0 hQ0
    unfold X avgΘ
    rw [← hAeq]
    exact hp
  have hnn : ∀ ω, 0 ≤ X ω := by
    intro ω
    refine le_trans ?_ (hpath ω)
    unfold descendantsAverage
    exact mul_nonneg (inv_nonneg.mpr hcardpos.le)
      (Finset.sum_nonneg (fun U _ => sq_nonneg _))
  obtain ⟨hVint, hVle⟩ := main_sqrt_expectation_ae_Th μ X hXint
    (Filter.Eventually.of_forall hnn)
  refine ⟨fun ω => Real.sqrt (X ω), hVint, fun ω => Real.sqrt_nonneg _,
    fun ω => Real.sqrt_le_sqrt (hpath ω), ?_⟩
  refine hVle.trans ?_
  exact Real.sqrt_le_sqrt hXle

end ASDExplicitGamma.Main

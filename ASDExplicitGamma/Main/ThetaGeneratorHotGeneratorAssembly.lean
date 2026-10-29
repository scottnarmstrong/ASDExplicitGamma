module

public import ASDExplicitGamma.Main.EnvelopeHTheta
public import ASDExplicitGamma.Main.ThetaGeneratorEBottomCovarianceActualLaw
public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeHSharpHist
public import ASDExplicitGamma.Main.ThetaGeneratorEParentGapActualLaw
public import ASDExplicitGamma.Main.ThetaGeneratorHotGeneratorPathwise
public import ASDExplicitGamma.Main.ThetaGeneratorAffine
public import ASDExplicitGamma.Main.ThetaGeneratorHotGeneratorIntegrated
public import ASDExplicitGamma.Main.ThetaGeneratorHotRowMajorants
public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeHSharpOfHist

/-! The observer generator inequality (per time and differential form) with the
history envelope `mainEnvelopeH35Theta (theta M) (b²) M.gamma` in place of `mainEnvelopeH (theta M)`; the
inputs of the E steps are their versions with this history envelope. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Model ASDExplicitGamma.Native ASDExplicitGamma.Response
  ASDExplicitGamma.Triadic ASDExplicitGamma.Scalar
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Generator inequality at one observer root and time, in the `_of_inverse_deficit` form:
the mean of the trace term `-b² (tr D - 2)` is bounded by the named quantity `Iabs`
(the inverse-deficit bound, discharged by MA-INVERSE-DEFICIT at observer cubes). -/
theorem main_generator_hot_of_inverse_deficit_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (Iabs : ℝ) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let σ : ℝ := Annealed.sigmaBar M m
    let amp := q3ModelAmplitude M h (m + 1)
    let b := amp / σ
    let L := q3ModelLength (m + 1)
    let Q := originCube 2 (m + (hobs : ℤ))
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    let xi := mainEnvelopeXi (b ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) t
    let a := inSourceMeanActual M m 5 t
    let f := modelTraceHeatAverage (m + hobs) M m t
    let H := mainEnvelopeH35Theta (theta M) (b ^ 2) M.gamma t
    let τ : CutoffSample 2 → ℝ := fun ω => Matrix.trace (coarseBlockMatrix (openCubeSet Q)
      (responseFramePlanarCoefficientField M.nu σ (mainELinearObsCoefficient Q m t ω))).lowerRight
    Integrable τ μ →
    -b ^ 2 * ((∫ ω, τ ω ∂μ) - 2) ≤ Iabs →
    (1 / 2 : ℝ) * modelHeatTraceAverage (closure (cubeSet Q)) M m
        (modelTraceObservable (m + (hobs : ℤ)) M.nu σ)
        (fun j => mainCubeH3Value (m + (hobs : ℤ)) amp L
          (mainCubeQ3Directions (m + (hobs : ℤ)) amp L j)) t ≤
      b ^ 2 * q + mainAffineTerm_Th M b q t + mainSourceError' (b ^ 2) a f H xi q + Iabs := by
  classical
  dsimp only
  intro hτ hInv
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar_characterization M m).1
  have hamp : 0 < q3ModelAmplitude M h (m + 1) :=
    mul_pos hM.1 (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _)
  have hb : 0 < q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ) := div_pos hamp hσ
  have hmul : (Annealed.sigmaBar M m : ℝ) *
      (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) =
      q3ModelAmplitude M h (m + 1) := by field_simp
  obtain ⟨hΨint, hEq⟩ := hot_generator_trace_average M h hM m (m + (hobs : ℤ)) t
  obtain ⟨Lg, hLgi, hLgae, hLgint⟩ :=
    main_e_linear_actual_law_Th M h hM hγ N hpast m hm t ht hobs h1 h40
  obtain ⟨Gc, hGci, hGcle, -, hGcint⟩ :=
    main_e_covariance_node_Th M h hM hγ N hpast m hm hobs h1 h40 t ht
  obtain ⟨Gt, hGti, hGtle, hGtint⟩ :=
    main_e_parent_gap_actual_law_Th M h hM hγ N hpast m hm t ht hobs h1 h40
  obtain ⟨Gb, hGbi, hGble, hGbint⟩ :=
    main_e_bottom_covariance_actual_law_Th M h hM hγ N hpast m hm t ht hobs h1 h40
  obtain ⟨Gs, hGsi, hGsle, hGsint⟩ :=
    main_hot_e_source_square_majorant_ofHist_Th (Hfun := (fun s => mainEnvelopeH35Theta (theta M) ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N_Th M h hM hγ N hpast m hm) M h hM hγ N hpast m hm hobs h1 h40 t ht
      (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ))
  obtain ⟨Go, hGoi, hGoae, hGoint⟩ :=
    main_hot_e_oscillation_majorant_ofHist_Th (Hfun := (fun s => mainEnvelopeH35Theta (theta M) ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N_Th M h hM hγ N hpast m hm) M h hM hγ N hpast m hm hobs h1 h40 t ht
      (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) hb
  obtain ⟨Gf, hGfi, hGfle, hGfint⟩ :=
    main_hot_e_remainder_feedback_majorant_ofHist_Th (Hfun := (fun s => mainEnvelopeH35Theta (theta M) ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N_Th M h hM hγ N hpast m hm) M h hM hγ N hpast m hm hobs h1 h40 t ht
      (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ))
  have hAffI := main_affine_observer_affine_integrable M h hM m hobs t
    (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) (q3ModelLength (m + 1))
  have hAffB := main_affine_actual_law_Th M h hM hγ N hpast m hm ht hobs h1 h40
  have hBn := main_affine_flat_boundary_cap M h hM m hobs h1 h40
  have hrows := main_generator_error_inventory_bound_of_rows
    ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
    (inSourceMeanActual M m 5 t) (modelTraceHeatAverage (m + hobs) M m t)
    (mainEnvelopeH35Theta (theta M) ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t)
    (mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma
      (theta M * mainSourceInversePrefix) (theta M) t)
    (mainAffineFlatBoundaryCapQ (hobs - 1))
    (∫ ω, Lg ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)
    (∫ ω, Gs ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)
    (∫ ω, Gc ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)
    (∫ ω, Go ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)
    (∫ ω, Gt ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)
    (∫ ω, Gb ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)
    (∫ ω, Gf ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)
    hLgint hGsint hGcint
    (by unfold mainEOscillationSourceProfile at hGoint; exact hGoint) hGtint hGbint hGfint
  refine le_trans (le_of_eq hEq) (le_trans (hotGen_combine_Th
    (oldSignedFlatBoundaryEnergy (originCube 2 (m + (hobs : ℤ)))
      (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) (q3ModelLength (m + 1)))
    (((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ))) ^ 2)
    hΨint hLgi hAffI hGsi hGci hGoi hGfi hGti hGbi hτ ?_) ?_)
  · filter_upwards [hLgae, hGoae] with ω hlg hgo
    have hpw := hot_generator_pathwise_Th M m hobs t
      (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ω
    dsimp only at hpw
    rw [hmul] at hpw
    have hAffω : oldSignedFlatAffineContribution (originCube 2 (m + (hobs : ℤ))) (hobs + 5)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainELinearObsCoefficient (originCube 2 (m + (hobs : ℤ))) m t ω))
        (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) (q3ModelLength (m + 1)) =
        oldSignedFlatAffineContribution (originCube 2 (m + (hobs : ℤ))) (hobs + 5)
          (oldSignedPartialFrameFieldAt M (originCube 2 (m + (hobs : ℤ))) m t ω)
          (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ))
          (q3ModelLength (m + 1)) := rfl
    have hTop := (le_abs_self _).trans (hGtle ω)
    have hBot := hGble ω
    have hSrc := hGsle ω
    have hCov := hGcle ω
    have hFb := hGfle ω
    linarith [hpw, hAffω, hTop, hBot, hSrc, hCov, hFb, hlg, hgo]
  · have hAff2 : (∫ ω, oldSignedFlatAffineContribution (originCube 2 (m + (hobs : ℤ))) (hobs + 5)
        (oldSignedPartialFrameFieldAt M (originCube 2 (m + (hobs : ℤ))) m t ω)
        (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ))
        (q3ModelLength (m + 1)) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        mainAffineTerm_Th M (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ))
          (mainAffineFlatBoundaryCapQ (hobs - 1)) t := hAffB
    linarith [hrows, hBn, hAff2, hInv]

/-- MA-GENERATOR-HYPOTHESES at an observer root, `_of_inverse_deficit` form: the observer mean
`f(t) = E tr D_{Q_{m+hobs}}` is absolutely continuous and a.e.
`f' ≤ B₀ + aff + E_corrected(f) + Iabs`, where `Iabs s` is any bound for the mean of
`-b² (tr D - 2)`, here the named hypothesis `hInv` (MA-INVERSE-DEFICIT at observer cubes). -/
theorem main_generator_hypotheses_hot_of_inverse_deficit_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (Iabs : ℝ → ℝ)
    (hInv : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Integrable (hotInverseTrace_Th M m hobs s) (Cutoff.cutoffSampleLaw M).toMeasure ∧
        -(q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2 *
          ((∫ ω, hotInverseTrace_Th M m hobs s ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) - 2) ≤
          Iabs s) :
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    AbsolutelyContinuousOnInterval (modelTraceHeatAverage (m + (hobs : ℤ)) M m) 0 1 ∧
      ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        deriv (modelTraceHeatAverage (m + (hobs : ℤ)) M m) s ≤
          b ^ 2 * q + mainAffineTerm_Th M b q s +
            mainSourceError' (b ^ 2) (inSourceMeanActual M m 5 s)
              (modelTraceHeatAverage (m + (hobs : ℤ)) M m s) (mainEnvelopeH35Theta (theta M) (b ^ 2) M.gamma s)
              (mainEnvelopeXi (b ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) s) q + Iabs s := by
  intro b q
  have hHeat := (main_actual_q3_heat_identities (m + (hobs : ℤ)) M h hM m).1
  refine ⟨hHeat.1, ?_⟩
  filter_upwards [hHeat.2.1] with s hs hs01
  have hd := (hs hs01).deriv
  rw [hd]
  have := main_generator_hot_of_inverse_deficit_Th M h hM hγ N hpast m hm hobs h1 h40 s hs01
    (Iabs s)
  dsimp only at this
  exact this (hInv s hs01).1 (hInv s hs01).2

end

end ASDExplicitGamma.Main

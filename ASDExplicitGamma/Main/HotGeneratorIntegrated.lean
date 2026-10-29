module

public import ASDExplicitGamma.Main.HotGeneratorIntegral
public import ASDExplicitGamma.Main.HotNodeMajorants
public import ASDExplicitGamma.Main.AffineObserverIntegrable
public import ASDExplicitGamma.Main.GeneratorErrorInventoryAssembly
public import ASDExplicitGamma.Main.ELinearActualLaw
public import ASDExplicitGamma.Main.EParentGapActualLaw
public import ASDExplicitGamma.Main.EBottomCovarianceActualLaw
public import ASDExplicitGamma.Main.HotCovNodeFinal
public import ASDExplicitGamma.Main.AffineStationary

/-! Generator assembly, step 4: the integrated generator bound at the observer root in
the `_of_inverse_deficit` form. The inverse-deficit input is the explicit bound on the mean of
the actual trace term `-b² (tr D - 2)` of the bottom covariance row. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Model ASDExplicitGamma.Native ASDExplicitGamma.Response
  ASDExplicitGamma.Triadic ASDExplicitGamma.Scalar
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- The stationary affine term of the generator inequality (MA-AFFINE). -/
def mainAffineTerm (M : ABKModel 2) (b q t : ℝ) : ℝ :=
  (b ^ 2 / 2) * mainEnvelopeA (b ^ 2) M.gamma mainSourceMeanPrefix t +
    (b ^ 2 * q) * (mainBeta - 1) + (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * mainA2 (b ^ 2) / 9

/-- Integral of a left-associated sum of ten integrable functions. -/
theorem hotGen_integral_sum10 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : Ω → ℝ}
    (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (h3 : Integrable f3 μ)
    (h4 : Integrable f4 μ) (h5 : Integrable f5 μ) (h6 : Integrable f6 μ)
    (h7 : Integrable f7 μ) (h8 : Integrable f8 μ) (h9 : Integrable f9 μ)
    (h10 : Integrable f10 μ) :
    (∫ ω, (f1 ω + f2 ω + f3 ω + f4 ω + f5 ω + f6 ω + f7 ω + f8 ω + f9 ω + f10 ω) ∂μ) =
      (∫ ω, f1 ω ∂μ) + (∫ ω, f2 ω ∂μ) + (∫ ω, f3 ω ∂μ) + (∫ ω, f4 ω ∂μ) + (∫ ω, f5 ω ∂μ) +
        (∫ ω, f6 ω ∂μ) + (∫ ω, f7 ω ∂μ) + (∫ ω, f8 ω ∂μ) + (∫ ω, f9 ω ∂μ) +
        ∫ ω, f10 ω ∂μ := by
  have i2 : Integrable (fun ω => f1 ω + f2 ω) μ := h1.add h2
  have i3 : Integrable (fun ω => f1 ω + f2 ω + f3 ω) μ := i2.add h3
  have i4 : Integrable (fun ω => f1 ω + f2 ω + f3 ω + f4 ω) μ := i3.add h4
  have i5 : Integrable (fun ω => f1 ω + f2 ω + f3 ω + f4 ω + f5 ω) μ := i4.add h5
  have i6 : Integrable (fun ω => f1 ω + f2 ω + f3 ω + f4 ω + f5 ω + f6 ω) μ := i5.add h6
  have i7 : Integrable (fun ω => f1 ω + f2 ω + f3 ω + f4 ω + f5 ω + f6 ω + f7 ω) μ := i6.add h7
  have i8 : Integrable (fun ω => f1 ω + f2 ω + f3 ω + f4 ω + f5 ω + f6 ω + f7 ω + f8 ω) μ :=
    i7.add h8
  have i9 : Integrable (fun ω => f1 ω + f2 ω + f3 ω + f4 ω + f5 ω + f6 ω + f7 ω + f8 ω + f9 ω) μ :=
    i8.add h9
  rw [integral_add i9 h10, integral_add i8 h9, integral_add i7 h8, integral_add i6 h7,
    integral_add i5 h6, integral_add i4 h5, integral_add i3 h4, integral_add i2 h3,
    integral_add h1 h2]

/-- Integration of the pathwise generator bound against the ten integrable pieces. -/
theorem hotGen_combine {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F Lg Aff Gs Gc Go Gf Gt Gb τ : Ω → ℝ} (Bn c : ℝ)
    (hF : Integrable F μ) (hLg : Integrable Lg μ) (hAff : Integrable Aff μ)
    (hGs : Integrable Gs μ) (hGc : Integrable Gc μ) (hGo : Integrable Go μ)
    (hGf : Integrable Gf μ) (hGt : Integrable Gt μ) (hGb : Integrable Gb μ)
    (hτ : Integrable τ μ)
    (hae : ∀ᵐ ω ∂μ, F ω ≤ Lg ω + Bn + Aff ω + Gs ω + Gc ω + Go ω + Gf ω + Gt ω +
      (-c * (τ ω - 2)) + Gb ω) :
    (∫ ω, F ω ∂μ) ≤ (∫ ω, Lg ω ∂μ) + Bn + (∫ ω, Aff ω ∂μ) + (∫ ω, Gs ω ∂μ) +
      (∫ ω, Gc ω ∂μ) + (∫ ω, Go ω ∂μ) + (∫ ω, Gf ω ∂μ) + (∫ ω, Gt ω ∂μ) +
      (-c * ((∫ ω, τ ω ∂μ) - 2)) + ∫ ω, Gb ω ∂μ := by
  have hT : Integrable (fun ω => -c * (τ ω - 2)) μ :=
    (hτ.sub (integrable_const (2 : ℝ))).const_mul (-c)
  have hB : Integrable (fun _ : Ω => Bn) μ := integrable_const Bn
  have hsum := hotGen_integral_sum10 hLg hB hAff hGs hGc hGo hGf hGt hT hGb
  have hint : Integrable (fun ω => Lg ω + Bn + Aff ω + Gs ω + Gc ω + Go ω + Gf ω + Gt ω +
      (-c * (τ ω - 2)) + Gb ω) μ :=
    (((((((((hLg.add hB).add hAff).add hGs).add hGc).add hGo).add hGf).add hGt).add hT).add hGb)
  have hmono := integral_mono_ae hF hint hae
  refine hmono.trans (le_of_eq ?_)
  rw [hsum, integral_const, integral_const_mul, integral_sub hτ (integrable_const _),
    integral_const]
  simp

/-- Generator inequality at one observer root and time, in the `_of_inverse_deficit` form:
the mean of the trace term `-b² (tr D - 2)` is bounded by the named quantity `Iabs`
(the inverse-deficit bound, discharged by MA-INVERSE-DEFICIT at observer cubes). -/
theorem main_generator_hot_of_inverse_deficit'
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
    let xi := mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t
    let a := inSourceMeanActual M m 5 t
    let f := modelTraceHeatAverage (m + hobs) M m t
    let H := mainEnvelopeH (theta M) M.gamma t
    let τ : CutoffSample 2 → ℝ := fun ω => Matrix.trace (coarseBlockMatrix (openCubeSet Q)
      (responseFramePlanarCoefficientField M.nu σ (mainELinearObsCoefficient Q m t ω))).lowerRight
    Integrable τ μ →
    -b ^ 2 * ((∫ ω, τ ω ∂μ) - 2) ≤ Iabs →
    (1 / 2 : ℝ) * modelHeatTraceAverage (closure (cubeSet Q)) M m
        (modelTraceObservable (m + (hobs : ℤ)) M.nu σ)
        (fun j => mainCubeH3Value (m + (hobs : ℤ)) amp L
          (mainCubeQ3Directions (m + (hobs : ℤ)) amp L j)) t ≤
      b ^ 2 * q + mainAffineTerm M b q t + mainSourceError' (b ^ 2) a f H xi q + Iabs := by
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
    main_e_linear_actual_law M h hM hγ N hpast m hm t ht hobs h1 h40
  obtain ⟨Gc, hGci, hGcle, -, hGcint⟩ :=
    main_e_covariance_node M h hM hγ N hpast m hm hobs h1 h40 t ht
  obtain ⟨Gt, hGti, hGtle, hGtint⟩ :=
    main_e_parent_gap_actual_law M h hM hγ N hpast m hm t ht hobs h1 h40
  obtain ⟨Gb, hGbi, hGble, hGbint⟩ :=
    main_e_bottom_covariance_actual_law M h hM hγ N hpast m hm t ht hobs h1 h40
  obtain ⟨Gs, hGsi, hGsle, hGsint⟩ :=
    main_hot_e_source_square_majorant M h hM hγ N hpast m hm hobs h1 h40 t ht
      (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ))
  obtain ⟨Go, hGoi, hGoae, hGoint⟩ :=
    main_hot_e_oscillation_majorant M h hM hγ N hpast m hm hobs h1 h40 t ht
      (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) hb
  obtain ⟨Gf, hGfi, hGfle, hGfint⟩ :=
    main_hot_e_remainder_feedback_majorant M h hM hγ N hpast m hm hobs h1 h40 t ht
      (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ))
  have hAffI := main_affine_observer_affine_integrable M h hM m hobs t
    (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) (q3ModelLength (m + 1))
  have hAffB := main_affine_actual_law M h hM hγ N hpast m hm ht hobs h1 h40
  have hBn := main_affine_flat_boundary_cap M h hM m hobs h1 h40
  have hrows := main_generator_error_inventory_bound_of_rows
    ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
    (inSourceMeanActual M m 5 t) (modelTraceHeatAverage (m + hobs) M m t)
    (mainEnvelopeH (theta M) M.gamma t)
    (mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma
      mainSourceInversePrefix (theta M) t)
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
  refine le_trans (le_of_eq hEq) (le_trans (hotGen_combine
    (oldSignedFlatBoundaryEnergy (originCube 2 (m + (hobs : ℤ)))
      (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) (q3ModelLength (m + 1)))
    (((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ))) ^ 2)
    hΨint hLgi hAffI hGsi hGci hGoi hGfi hGti hGbi hτ ?_) ?_)
  · filter_upwards [hLgae, hGoae] with ω hlg hgo
    have hpw := hot_generator_pathwise M m hobs t
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
        mainAffineTerm M (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ))
          (mainAffineFlatBoundaryCapQ (hobs - 1)) t := hAffB
    linarith [hrows, hBn, hAff2, hInv]

/-- The actual inverse-trace term `tr D` of the bottom covariance row on the observer root. -/
def hotInverseTrace (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ) (ω : CutoffSample 2) : ℝ :=
  Matrix.trace (coarseBlockMatrix (openCubeSet (originCube 2 (m + (hobs : ℤ))))
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
      (mainELinearObsCoefficient (originCube 2 (m + (hobs : ℤ))) m t ω))).lowerRight

/-- MA-GENERATOR-HYPOTHESES at an observer root, `_of_inverse_deficit` form: the observer mean
`f(t) = E tr D_{Q_{m+hobs}}` is absolutely continuous and a.e.
`f' ≤ B₀ + aff + E_corrected(f) + Iabs`, where `Iabs s` is any bound for the mean of
`-b² (tr D - 2)`, here the named hypothesis `hInv` (MA-INVERSE-DEFICIT at observer cubes). -/
theorem main_generator_hypotheses_hot_of_inverse_deficit'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (Iabs : ℝ → ℝ)
    (hInv : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Integrable (hotInverseTrace M m hobs s) (Cutoff.cutoffSampleLaw M).toMeasure ∧
        -(q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2 *
          ((∫ ω, hotInverseTrace M m hobs s ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) - 2) ≤
          Iabs s) :
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    AbsolutelyContinuousOnInterval (modelTraceHeatAverage (m + (hobs : ℤ)) M m) 0 1 ∧
      ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        deriv (modelTraceHeatAverage (m + (hobs : ℤ)) M m) s ≤
          b ^ 2 * q + mainAffineTerm M b q s +
            mainSourceError' (b ^ 2) (inSourceMeanActual M m 5 s)
              (modelTraceHeatAverage (m + (hobs : ℤ)) M m s) (mainEnvelopeH (theta M) M.gamma s)
              (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) s) q + Iabs s := by
  intro b q
  have hHeat := (main_actual_q3_heat_identities (m + (hobs : ℤ)) M h hM m).1
  refine ⟨hHeat.1, ?_⟩
  filter_upwards [hHeat.2.1] with s hs hs01
  have hd := (hs hs01).deriv
  rw [hd]
  have := main_generator_hot_of_inverse_deficit' M h hM hγ N hpast m hm hobs h1 h40 s hs01
    (Iabs s)
  dsimp only at this
  exact this (hInv s hs01).1 (hInv s hs01).2

end

end ASDExplicitGamma.Main

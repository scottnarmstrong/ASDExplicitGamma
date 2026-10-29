module

public import ASDExplicitGamma.Inverse.RawShellBandGenerator
public import ASDExplicitGamma.Inverse.RawShellBankMoment
public import ASDExplicitGamma.Inverse.RawShellQ3Drift
public import ASDExplicitGamma.Inverse.RawShellQ3FullBracket
public import ASDExplicitGamma.Inverse.RawShellQ3Law
public import ASDExplicitGamma.Native.VanishingBracket
public import ASDExplicitGamma.Gaussian.ModelHeatPower

/-! The bank-backed p=20 generator row for an arbitrary weighted shell-band
coordinate step. -/

@[expose] public section

open MeasureTheory Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open Algsuperdiff.Section3.Cutoff
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Native
open ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational
open scoped ENNReal

namespace ASDExplicitGamma.Inverse

/-- At every coordinate step of an arbitrary finite attenuation band, the
actual p=20 generator integral obeys the bank row. The local history is
for the current prefix; the full-response cap is for the complete band. -/
theorem raw_shell_band_step_p20_generator_integral_bank_row
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (N i : ℕ) (hi : i < N)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (N : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1)
    (hpastLocal : ∀ j < n, nativeInductionState M h j)
    (hpastFull : ∀ j ≤ n + (N : ℤ) - 303, nativeInductionState M h j)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let Q := originCube 2 n
    let K := closure (cubeSet Q)
    let σ : ℝ := Annealed.sigmaBar M n
    let s := i + 1
    let J := n + (s : ℤ)
    let W := rawShellBandStepWeights n i weights t
    let X := rawShellBandScalarFromWeights M n s W
    let Φ := modelTraceObservable n M.nu σ
    let H := pureFluxMainCubeQ3Directions n
      (q3ModelAmplitude M h J) (q3ModelLength J)
    let T := fun ω => Φ (X ω)
    let F := fun ω => T ω + 4
    let P := rawShellWeightedLocalHistory M n J W
    let D := fun ω => bankInverseTraceObservable n M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (X ω)
    let L := fun ω => (1 / 2 : ℝ) * modelCovarianceTrace Φ H (X ω)
    let Γ := fun ω => modelGradientSquareTrace Φ H (X ω)
    let κ := lemmaVH2kn
      (cubeScaleFactor Q / (q3ModelLength J).1)
      (diagMeshRadius Q (pureFluxBankSourceDepth s) / (q3ModelLength J).1)
    let κB := lemmaVH2Bn
      (cubeScaleFactor Q / (q3ModelLength J).1)
      (diagMeshRadius Q (pureFluxBankSourceDepth s) / (q3ModelLength J).1)
    let μR := pureFluxCovarianceMu (pureFluxCovarianceA 0 i)
      (pureFluxCovarianceB 0 i)
    let v := (q3ModelAmplitude M h J) ^ 2 / σ ^ 2
    (∫ ω, 20 * T ω ^ (19 : ℝ) * L ω +
      190 * T ω ^ (18 : ℝ) * Γ ω ∂μ) ≤
      20 * (∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) *
        (v * ((78 + 76 * κ) * (3683 / 2500 : ℝ) +
          2 * κ * (3683 / 2500 : ℝ) * rawTraceFullResponseCap M.gamma N +
          (μR + 38 * (κB ^ 2 + κ)) *
            (3683 / 2500 : ℝ) ^ 2 * rawTraceFullResponseCap M.gamma N)) := by
  classical
  dsimp only
  let Q := originCube 2 n
  let K := closure (cubeSet Q)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M n
  let s := i + 1
  let J := n + (s : ℤ)
  let W := rawShellBandStepWeights n i weights t
  let X := fun ω : Cutoff.CutoffSample 2 =>
    rawShellBandScalarFromWeights M n s W ω
  let Φ : C(K, ℝ) → ℝ := modelTraceObservable n M.nu σ
  let H := pureFluxMainCubeQ3Directions n
    (q3ModelAmplitude M h J) (q3ModelLength J)
  let T : Cutoff.CutoffSample 2 → ℝ := fun ω => Φ (X ω)
  let F : Cutoff.CutoffSample 2 → ℝ := fun ω => T ω + 4
  let P := rawShellWeightedLocalHistory M n J W
  let D : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    bankInverseTraceObservable n M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (X ω)
  let L : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    (1 / 2 : ℝ) * modelCovarianceTrace Φ H (X ω)
  let Γ : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    modelGradientSquareTrace Φ H (X ω)
  let κ := lemmaVH2kn
    (cubeScaleFactor Q / (q3ModelLength J).1)
    (diagMeshRadius Q (pureFluxBankSourceDepth s) / (q3ModelLength J).1)
  let κB := lemmaVH2Bn
    (cubeScaleFactor Q / (q3ModelLength J).1)
    (diagMeshRadius Q (pureFluxBankSourceDepth s) / (q3ModelLength J).1)
  let μR := pureFluxCovarianceMu (pureFluxCovarianceA 0 i)
    (pureFluxCovarianceB 0 i)
  let b := q3ModelAmplitude M h J
  let v := b ^ 2 / σ ^ 2
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hν : 0 < M.nu := M.nu_pos
  have hΦ : HasPolynomiallyBoundedC2Derivatives Φ :=
    modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu σ hν hσ
  have hΦ0 : ∀ x, 0 ≤ Φ x := modelTraceObservable_nonneg n M.nu σ hν hσ
  have hstepBounds := raw_shell_band_step_weights_bounds n N i hi weights hw t ht
  have hW : ∀ k ∈ Finset.Ioc n J, 0 ≤ W k ∧ W k ≤ 1 := by
    intro k hk
    apply hstepBounds k
    simp only [Finset.mem_Ioc] at hk ⊢
    exact ⟨hk.1, by dsimp [J, s] at hk ⊢; omega⟩
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hXmeas : Measurable X := measurable_raw_shell_weighted_prefix M n s W
  have hTmeas : Measurable T := hΦ.1.continuous.measurable.comp hXmeas
  have hFmeas : Measurable F := hTmeas.add measurable_const
  have hPmeas : Measurable P := raw_shell_weighted_local_history_measurable M n J W
  have hDmeas : Measurable D :=
    (bank_inverse_trace_observable_C2 n M.nu σ M.nu_pos hσ).1.continuous.measurable.comp hXmeas
  have hT0 : ∀ ω, 0 ≤ T ω := fun ω => hΦ0 (X ω)
  have hF0 : ∀ ω, 0 ≤ F ω := by
    intro ω
    dsimp [F]
    exact add_nonneg (hT0 ω) (by norm_num)
  have hP0 : ∀ ω, 0 ≤ P ω := fun ω => ENNReal.toReal_nonneg
  have hDframe (ω : CutoffSample 2) : D ω = Matrix.trace
      ((frameMatrix σ (coarseBlockMatrix (cubeSet Q)
        (responsePlanarCoefficientField M.nu
          (ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ (X ω))))).lowerRight) := by
    simpa [D, Q, K, σ, X] using
      raw_shell_band_bank_inverse_trace_eq_frame_trace M n (X ω)
  have hD0 : ∀ ω, 0 ≤ D ω := by
    intro ω
    let k := ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ (X ω)
    have hrows := nativeTraceShearDefectRows Q M.nu σ hν hσ k
    have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
    have hmul := mul_pos hrows.2.1 hσ2
    have heq : (Matrix.trace (frameMatrix σ
        (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu k))).lowerRight /
          σ ^ 2) * σ ^ 2 = Matrix.trace (frameMatrix σ
        (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu k))).lowerRight :=
      div_mul_cancel₀ _ hσ2.ne'
    rw [heq] at hmul
    rw [hDframe ω]
    exact hmul.le
  have hTF : ∀ᵐ ω ∂μ, T ω ≤ F ω :=
    Filter.Eventually.of_forall fun ω => by dsimp [F]; linarith
  have hDle : ∀ᵐ ω ∂μ, D ω ≤ 2 * P ω := by
    exact raw_shell_band_step_inverse_trace_le_local_history M h hM hg n N i hi
      weights hw hpastLocal t ht
  have hP128 := raw_shell_weighted_local_history_L128 M h hM hg n J (by omega)
    W hW hpastLocal
  have hFcap := raw_shell_weighted_full_response_L128 M h hM hg n N W hstepBounds hpastFull
  have hF_eq : F = fun ω => rootTraceObservable M Q n
      (n + (N : ℤ)) n W ω := by
    funext ω
    change T ω + 4 = _
    exact (raw_shell_band_step_trace_eq M n N i hi weights t ω).symm
  have hF128 : eLpNorm F (128 : ℝ≥0∞) μ ≤
      ENNReal.ofReal (rawTraceFullResponseCap M.gamma N) := by
    rw [hF_eq, show (128 : ℝ≥0∞) = ENNReal.ofReal (128 : ℝ) by norm_num]
    exact hFcap
  have hP128' : eLpNorm P (128 : ℝ≥0∞) μ ≤ ENNReal.ofReal (3683 / 2500 : ℝ) := by
    simpa only [μ] using hP128
  have hF128' : eLpNorm F (128 : ℝ≥0∞) μ ≤
      ENNReal.ofReal (rawTraceFullResponseCap M.gamma N) := by
    simpa only [μ] using hF128
  have hcaps := raw_trace_p20_bank_holder_caps μ P F T D M.gamma N
    M.shellPrefix.gamma_pos.le hP0 hF0 hT0 hD0 hTF hDle
    hPmeas.aestronglyMeasurable hFmeas.aestronglyMeasurable
    hTmeas.aestronglyMeasurable hDmeas.aestronglyMeasurable hP128' hF128'
  rcases hcaps with ⟨hTmem, hDmem, hPFmem, hP2Fmem,
    hTnorm, hDnorm, hPFnorm, hP2Fnorm⟩
  have hsource := raw_shell_weighted_source_history_ae_le_local_history
    M h hM hg n s hs W hW hpastLocal
  have hL : ∀ᵐ ω ∂μ,
      L ω ≤ v * D ω + 2 * v * κ * (P ω * F ω) +
        v * μR * (P ω ^ 2 * F ω) := by
    filter_upwards [hsource] with ω hsourceω
    have hrow := raw_trace_model_q3_positive_generator_row_tight n s hs
      M.nu σ b hν hσ (X ω)
    dsimp only [] at hrow
    have hD := hDframe ω
    rw [← hD] at hrow
    let Bsrc := rawShellWeightedSourceHistory M n s W ω
    have hBnonneg : 0 ≤ Bsrc := by
      dsimp [Bsrc, rawShellWeightedSourceHistory]
      exact le_max_of_le_left
        (lemmaVTileHistory_nonneg Q (pureFluxBankSourceDepth s)
          (responseFramePlanarCoefficientField M.nu σ
            (pureFluxOpenResponseRestriction n (X ω))))
    have hB : Bsrc ≤ P ω := by simpa [Bsrc, P, J] using hsourceω
    have hBsq : Bsrc ^ 2 ≤ P ω ^ 2 := by nlinarith [hB, hBnonneg, hP0 ω]
    have hκ : 0 ≤ κ := by
      dsimp [κ]
      unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
      have hρ : 0 ≤ cubeScaleFactor Q / (q3ModelLength J).1 :=
        div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
          (q3ModelLength J).2.le
      have hδ : 0 ≤ diagMeshRadius Q (pureFluxBankSourceDepth s) /
          (q3ModelLength J).1 :=
        div_nonneg (diagMeshRadius_pos Q (pureFluxBankSourceDepth s)).le
          (q3ModelLength J).2.le
      positivity
    have hμ : 0 ≤ μR := by
      dsimp [μR]
      exact (pureFlux_covariance_mu_lower
        (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i)).1
    have hbase : L ω ≤ v * D ω +
        (2 * v * κ * Bsrc + v * μR * Bsrc ^ 2) * F ω := by
      simpa [L, D, X, Φ, H, F, P, κ, μR, v, b, Bsrc,
        Q, J, s, rawShellWeightedSourceHistory, pureFluxBankSourceDepth] using hrow
    have hproducts : (2 * v * κ * Bsrc + v * μR * Bsrc ^ 2) * F ω ≤
        2 * v * κ * (P ω * F ω) + v * μR * (P ω ^ 2 * F ω) := by
      calc
        _ = (2 * v * κ) * (Bsrc * F ω) + (v * μR) * (Bsrc ^ 2 * F ω) := by ring
        _ ≤ (2 * v * κ) * (P ω * F ω) + (v * μR) * (P ω ^ 2 * F ω) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hB (hF0 ω)) (by positivity))
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hBsq (hF0 ω)) (by positivity))
        _ = _ := by ring
    calc
      L ω ≤ v * D ω + (2 * v * κ * Bsrc + v * μR * Bsrc ^ 2) * F ω := hbase
      _ ≤ v * D ω + 2 * v * κ * (P ω * F ω) +
          v * μR * (P ω ^ 2 * F ω) := by nlinarith only [hproducts]
  have hΓ : ∀ᵐ ω ∂μ,
      Γ ω ≤ 4 * v * T ω *
        ((1 + κ) * D ω + (κB ^ 2 + κ) * (P ω ^ 2 * F ω)) := by
    filter_upwards [hsource] with ω hsourceω
    have hrow := raw_trace_model_q3_full_bracket_row_tight n s M.nu σ b hν hσ (X ω)
    dsimp only [] at hrow
    have hD := hDframe ω
    rw [← hD] at hrow
    let Bsrc := rawShellWeightedSourceHistory M n s W ω
    have hBnonneg : 0 ≤ Bsrc := by
      dsimp [Bsrc, rawShellWeightedSourceHistory]
      exact le_max_of_le_left
        (lemmaVTileHistory_nonneg Q (pureFluxBankSourceDepth s)
          (responseFramePlanarCoefficientField M.nu σ
            (pureFluxOpenResponseRestriction n (X ω))))
    have hB : Bsrc ≤ P ω := by simpa [Bsrc, P, J] using hsourceω
    have hBsq : Bsrc ^ 2 ≤ P ω ^ 2 := by nlinarith [hB, hBnonneg, hP0 ω]
    have hκ : 0 ≤ κ := by
      dsimp [κ]
      unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
      have hρ : 0 ≤ cubeScaleFactor Q / (q3ModelLength J).1 :=
        div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
          (q3ModelLength J).2.le
      have hδ : 0 ≤ diagMeshRadius Q (pureFluxBankSourceDepth s) /
          (q3ModelLength J).1 :=
        div_nonneg (diagMeshRadius_pos Q (pureFluxBankSourceDepth s)).le
          (q3ModelLength J).2.le
      positivity
    have hκB : 0 ≤ κB := by
      dsimp [κB]
      unfold lemmaVH2Bn lemmaVH2R1 lemmaVH2A2 lemmaVH2C1 lemmaVH2C2
      have hρ : 0 ≤ cubeScaleFactor Q / (q3ModelLength J).1 :=
        div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
          (q3ModelLength J).2.le
      have hδ : 0 ≤ diagMeshRadius Q (pureFluxBankSourceDepth s) /
          (q3ModelLength J).1 :=
        div_nonneg (diagMeshRadius_pos Q (pureFluxBankSourceDepth s)).le
          (q3ModelLength J).2.le
      positivity
    have hv : 0 ≤ v := by dsimp [v]; positivity
    have hbase : Γ ω ≤ 4 * v * T ω *
        ((1 + κ) * D ω + (κB ^ 2 + κ) * Bsrc ^ 2 * F ω) := by
      simpa [Γ, D, X, Φ, H, F, P, κ, κB, v, b, Bsrc,
        Q, J, s, rawShellWeightedSourceHistory, pureFluxBankSourceDepth] using hrow
    have hinner : (1 + κ) * D ω + (κB ^ 2 + κ) * Bsrc ^ 2 * F ω ≤
        (1 + κ) * D ω + (κB ^ 2 + κ) * (P ω ^ 2 * F ω) := by
      calc
        _ = (1 + κ) * D ω + (κB ^ 2 + κ) * (Bsrc ^ 2 * F ω) := by ring
        _ ≤ _ := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hBsq (hF0 ω))
            (add_nonneg (sq_nonneg κB) hκ))
    have houter : 0 ≤ 4 * v * T ω :=
      mul_nonneg (mul_nonneg (by norm_num) hv) (hT0 ω)
    exact hbase.trans (mul_le_mul_of_nonneg_left hinner houter)
  have hΦpow := hasPolynomiallyBoundedC2Derivatives_rpow hΦ hΦ0
    (by norm_num : (2 : ℝ) ≤ 20)
  obtain ⟨ell, hKell⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet Q).isCompact_closure
  obtain ⟨Treal, vreal, hAreal, hlaw⟩ :=
    freshShell_map_scalarRestriction_eq_gaussianSeries M h hM
      (n + (s : ℤ) - 1) (K := K)
  let Hreal : ℕ → C(K, ℝ) := fun j => Treal (vreal j)
  have hHreal : Summable (fun j => ‖Hreal j‖ ^ 2) :=
    summable_sq_norm_gaussianDirections hAreal Treal
  have hGenMeas := measurable_modelCovarianceTrace
    (fun x : C(K, ℝ) => Φ x ^ (20 : ℝ)) hΦpow.1 Hreal
  have hGenGrowth := polynomial_modelCovarianceTrace Hreal hHreal
    (fun x : C(K, ℝ) => Φ x ^ (20 : ℝ)) hΦpow
  have hXmapMom := raw_shell_weighted_prefix_polynomial_moments M n s W hW
  have hGenIntegrableMap : Integrable
      (modelCovarianceTrace (fun x : C(K, ℝ) => Φ x ^ (20 : ℝ)) Hreal)
      ((Cutoff.cutoffSampleLaw M).toMeasure.map X) := by
    obtain ⟨Cgen, hCgen, dgen, hbound⟩ := hGenGrowth
    have hmajor := (hXmapMom dgen).const_mul Cgen
    apply hmajor.mono' hGenMeas.aestronglyMeasurable
    filter_upwards with x
    change ‖modelCovarianceTrace (fun x : C(K, ℝ) => Φ x ^ (20 : ℝ)) Hreal x‖ ≤ _
    exact hbound x
  have hGenIntegrable : Integrable
      (fun ω => modelCovarianceTrace
        (fun x : C(K, ℝ) => Φ x ^ (20 : ℝ)) Hreal (X ω)) μ := by
    exact (integrable_map_measure hGenMeas.aestronglyMeasurable
      hXmeas.aemeasurable).mp hGenIntegrableMap
  have hGeneratorInt : Integrable
      (fun ω => 20 * T ω ^ (19 : ℝ) * L ω +
        190 * T ω ^ (18 : ℝ) * Γ ω) μ := by
    have hEq : (fun ω => 20 * T ω ^ (19 : ℝ) * L ω +
        190 * T ω ^ (18 : ℝ) * Γ ω) =
        fun ω => (1 / 2 : ℝ) * modelCovarianceTrace
          (fun x : C(K, ℝ) => Φ x ^ (20 : ℝ)) Hreal (X ω) := by
      funext ω
      have hpow := modelCovarianceTrace_rpow hAreal Treal
        (fun x : C(K, ℝ) => Φ x) hΦ hΦ0
        (p := 20) (by norm_num : (2 : ℝ) ≤ 20) (X ω)
      have htime : n + (s : ℤ) - 1 + 1 = n + (s : ℤ) := by omega
      have hlaw' : (Cutoff.cutoffSampleLaw M).toMeasure.map
          (fun ω : CutoffSample 2 => shellFieldScalarRestriction K
            (ω.1 (n + (s : ℤ)))) =
          standardGaussianInfinitePi.map (gaussianSeriesLimitE hAreal Treal) := by
        simpa only [htime] using hlaw
      have hgen := raw_trace_model_q3_power_generator_eq_of_fresh_law
        n M h hM s σ hσ Treal vreal hAreal hlaw' (X ω)
      have hpoint : 20 * (Φ (X ω)) ^ (19 : ℝ) *
          ((1 / 2 : ℝ) * modelCovarianceTrace Φ H (X ω)) +
          190 * (Φ (X ω)) ^ (18 : ℝ) *
            modelGradientSquareTrace Φ H (X ω) =
          modelPowerHeatGenerator Φ H 20 (X ω) := by
        rw [modelPowerHeatGenerator]
        norm_num
      rw [hpoint]
      calc
        modelPowerHeatGenerator Φ H 20 (X ω) =
            modelPowerHeatGenerator Φ Hreal 20 (X ω) := hgen.symm
        _ = (1 / 2 : ℝ) * modelCovarianceTrace
            (fun x : C(K, ℝ) => Φ x ^ (20 : ℝ)) Hreal (X ω) := hpow.symm
    rw [hEq]
    exact (hGenIntegrable.const_mul (1 / 2 : ℝ))
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hκnonneg : 0 ≤ κ := by
    dsimp [κ]
    unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
    have hρ : 0 ≤ cubeScaleFactor Q / (q3ModelLength J).1 :=
      div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
        (q3ModelLength J).2.le
    have hδ : 0 ≤ diagMeshRadius Q (pureFluxBankSourceDepth s) /
        (q3ModelLength J).1 :=
      div_nonneg (diagMeshRadius_pos Q (pureFluxBankSourceDepth s)).le
        (q3ModelLength J).2.le
    positivity
  have hμnonneg : 0 ≤ μR := by
    dsimp [μR]
    exact (pureFlux_covariance_mu_lower
      (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i)).1
  have hrow := raw_trace_p20_generator_integral_bank_row μ P F T D L Γ
    M.gamma N v κ κB μR hv hκnonneg hμnonneg M.shellPrefix.gamma_pos.le
    hP0 hF0 hT0 hD0 hTF hDle hPmeas.aestronglyMeasurable
    hFmeas.aestronglyMeasurable hTmeas.aestronglyMeasurable
    hDmeas.aestronglyMeasurable hP128' hF128' hL hΓ hGeneratorInt
  simpa only [P, F, T, D, L, Γ, κ, κB, μR, v, μ] using hrow

end ASDExplicitGamma.Inverse

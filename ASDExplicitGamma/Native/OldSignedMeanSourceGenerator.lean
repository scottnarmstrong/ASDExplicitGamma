module

public import ASDExplicitGamma.Inverse.SourceInterfaceEnergy
public import ASDExplicitGamma.Native.OldSignedFull64Generator

/-! Actual OLD mean transport with the sharp pure-source covariance rows.
Adapted from the actual SourceInterfaceEnergy generator proof; the local
inverse bank is unchanged and the full-response factor needs only L60. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory Set Filter Homogenization Algsuperdiff.Section3
open Gaussian Main Response Triadic Variational Inverse
open scoped ENNReal
noncomputable section

/-- Physical one-shell mean source coefficient, with source covariance
constants and the proved full64 bank. -/
noncomputable def oldSignedMeanSourceCap
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (r : ℕ) : ℝ := by
  let q : ℤ := m - (r : ℤ)
  let s : ℕ := r + 1
  let Q := originCube 2 q
  let σ : ℝ := Annealed.sigmaBar M m
  let κ := lemmaVH2kn
    (cubeScaleFactor Q / (q3ModelLength (q + (s : ℤ))).1)
    (diagMeshRadius Q (pureFluxBankSourceDepth s) /
      (q3ModelLength (q + (s : ℤ))).1)
  let A := pureFluxCovarianceA 0 (s - 1)
  let A' := pureFluxCovarianceB 0 (s - 1)
  let μR := pureFluxCovarianceMu A A'
  let v := (q3ModelAmplitude M h (q + (s : ℤ))) ^ 2 / σ ^ 2
  let C := rawTraceOldFrameP20LocalClock M.gamma s
  let fCap := oldSignedP20Full64Cap M.gamma s
  exact v * C * (2 * (3683 / 2500 : ℝ) +
    2 * κ * (3683 / 2500 : ℝ) * fCap +
    C * μR * (3683 / 2500 : ℝ) ^ 2 * fCap)

private theorem old_signed_mean_integral_le_positiveLpNorm
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf0 : ∀ ω, 0 ≤ f ω) (hf : MemLp f (ENNReal.ofReal 20) μ) :
    (∫ ω, f ω ∂μ) ≤ positiveLpNorm μ 20 f := by
  have hmono := eLpNorm_le_eLpNorm_of_exponent_le (f := f) (μ := μ)
    (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal 20 by norm_num)
  have hnorm := ENNReal.toReal_mono hf.eLpNorm_ne_top hmono
  change lpNorm f 1 μ ≤ (eLpNorm f (ENNReal.ofReal 20) μ).toReal at hnorm
  rw [lpNorm_one_eq_integral_norm hf.aestronglyMeasurable] at hnorm
  simp only [Real.norm_of_nonneg (hf0 _)] at hnorm
  rw [positiveLpNorm_eq_eLpNorm_toReal μ (by norm_num) f hf0 hf]
  exact hnorm

/-- The expected one-shell q3 generator in the true OLD frame is bounded by
the explicit positive-energy coefficient. The only history hypotheses are
the native states strictly before `m`; all random quantities are the actual
cutoff-law source history and trace. -/
theorem old_signed_actual_mean_source_generator
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j)
    (r : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    inSourceMeanRateActual M h m r t ≤ oldSignedMeanSourceCap M h m r ∧
      0 ≤ oldSignedMeanSourceCap M h m r := by
  classical
  let q : ℤ := m - (r : ℤ)
  let s : ℕ := r + 1
  let i : ℕ := s - 1
  let Q := originCube 2 q
  let K := closure (cubeSet Q)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M m
  let σq : ℝ := Annealed.sigmaBar M q
  let Φ : C(K, ℝ) → ℝ := modelTraceObservable q M.nu σ
  let b := q3ModelAmplitude M h (q + (s : ℤ))
  let H := pureFluxMainCubeQ3Directions q b (q3ModelLength (q + (s : ℤ)))
  let W := rawShellBandStepWeights q i (fun _ => (1 : ℝ)) t
  let X := rawShellBandScalarFromWeights M q s W
  let T : Cutoff.CutoffSample 2 → ℝ := fun ω => Φ (X ω)
  let F : Cutoff.CutoffSample 2 → ℝ := fun ω => T ω + 4
  let P := rawShellWeightedLocalHistory M q (q + (s : ℤ)) W
  let D : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    bankInverseTraceObservable q M.nu σq M.nu_pos
      (Annealed.sigmaBar_characterization M q).1 (X ω)
  let L : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    (1 / 2 : ℝ) * modelCovarianceTrace Φ H (X ω)
  let ρ := σ / σq
  let C := rawTraceOldFrameP20LocalClock M.gamma s
  let κ := lemmaVH2kn
    (cubeScaleFactor Q / (q3ModelLength (q + (s : ℤ))).1)
    (diagMeshRadius Q (pureFluxBankSourceDepth s) /
      (q3ModelLength (q + (s : ℤ))).1)
  let A := pureFluxCovarianceA 0 (s - 1)
  let A' := pureFluxCovarianceB 0 (s - 1)
  let μR := pureFluxCovarianceMu A A'
  let v := b ^ 2 / σ ^ 2
  let v' := v * C
  let μR' := C * μR
  let fCap := oldSignedP20Full64Cap M.gamma s
  have hqle : q ≤ m := by dsimp [q]; omega
  have hstateLocal : ∀ j < q, nativeInductionState M h j := by
    intro j hj
    exact hpast j (lt_of_lt_of_le hj hqle)
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hi : i < s := by dsimp [i]; omega
  have hiadd : i + 1 = s := by dsimp [i]; omega
  have hqs : q + (s : ℤ) = m + 1 := by dsimp [q, s]; omega
  have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ht
  have hunit : ∀ k ∈ Finset.Ioc q (q + (s : ℤ)),
      0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 := by intros; norm_num
  have hW : ∀ k ∈ Finset.Ioc q (q + (s : ℤ)),
      0 ≤ W k ∧ W k ≤ 1 := by
    intro k hk
    have hh := raw_shell_band_step_weights_bounds q s i hi
      (fun _ => (1 : ℝ)) hunit t htcc k hk
    simpa [W, i, hiadd] using hh
  have hWm : ∀ k ∈ Finset.Ioc m (m + 1),
      0 ≤ (Real.sqrt t) ∧ (Real.sqrt t) ≤ 1 := by
    intro k hk
    have hk' : k = m + 1 := by
      simp only [Finset.mem_Ioc] at hk
      omega
    subst k
    exact ⟨Real.sqrt_nonneg t, Real.sqrt_le_one.mpr ht.2⟩
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hσq : 0 < σq := (Annealed.sigmaBar_characterization M q).1
  have hν : 0 < M.nu := M.nu_pos
  have hX : ∀ ω, X ω = modelInsertedScalar K m t ω := by
    intro ω
    obtain ⟨ell, hKell⟩ := exists_originCube_containing_compact K
      (isBounded_cubeSet Q).isCompact_closure
    have hcoeff : attenuatedCoefficient M q (q + (s : ℤ)) W ω =
        (Model.partialInsertedCoefficient M m t ω).toFun := by
      have hWpartial (k : ℤ) (hk : k ∈ Finset.Ioc q (q + (s : ℤ))) :
          W k = bankPartialInsertionWeights q s t k := by
        have hcur : q + (i : ℤ) + 1 = q + (s : ℤ) := by omega
        by_cases htop : k = q + (s : ℤ)
        · subst k
          simp [W, rawShellBandStepWeights, bankPartialInsertionWeights, hcur]
        · have hlt : k < q + (s : ℤ) := by
            have hle := (Finset.mem_Ioc.mp hk).2
            omega
          have hprev : k ∈ Finset.Ioc q (q + (i : ℤ)) := by
            simp only [Finset.mem_Ioc]
            constructor
            · exact (Finset.mem_Ioc.mp hk).1
            · dsimp [i]
              omega
          simp [W, rawShellBandStepWeights, bankPartialInsertionWeights,
            htop, hlt, hprev, hcur]
      have hweights : attenuatedCoefficient M q (q + (s : ℤ)) W ω =
          attenuatedCoefficient M q (q + (s : ℤ))
            (bankPartialInsertionWeights q s t) ω := by
        funext x
        unfold attenuatedCoefficient
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [hWpartial k hk]
      rw [hweights]
      funext x
      calc
        attenuatedCoefficient M q (q + (s : ℤ))
            (bankPartialInsertionWeights q s t) ω x =
            Cutoff.coefficientCutoff M.nu (q + (s : ℤ) - 1) ω x +
              Real.sqrt t • (ω.val (q + (s : ℤ))).forgetShell x :=
          raw_shell_partial_coefficient_any M q s hs t ω x
        _ = (Model.partialInsertedCoefficient M m t ω).toFun x := by
          rw [show q + (s : ℤ) - 1 = m by omega,
            show q + (s : ℤ) = m + 1 by omega]
          simp [Model.partialInsertedCoefficient]
    have hscal : X ω = modelInsertedScalar K m t ω := by
      ext x
      calc
        X ω x = attenuatedCoefficient M q (q + (s : ℤ)) W ω x.1 1 0 :=
          raw_shell_weighted_scalar_eq_coefficient_entry M q s W ω ell hKell x
        _ = (Model.partialInsertedCoefficient M m t ω).toFun x.1 1 0 := by
          rw [hcoeff]
        _ = modelInsertedScalar K m t ω x := by
          symm
          exact modelInsertedScalar_apply K M ell m hKell t ω x
    exact hscal
  have hPmeas : Measurable P := raw_shell_weighted_local_history_measurable M q
    (q + (s : ℤ)) W
  have hTmeas : Measurable T := (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives
    q M.nu σ hν hσ).1.continuous.measurable.comp
      (measurable_raw_shell_weighted_prefix M q s W)
  have hFmeas : Measurable F := hTmeas.add measurable_const
  have hDmeas : Measurable D := (bank_inverse_trace_observable_C2 q M.nu σq
    M.nu_pos hσq).1.continuous.measurable.comp
      (measurable_raw_shell_weighted_prefix M q s W)
  have hT0 : ∀ ω, 0 ≤ T ω := fun ω => modelTraceObservable_nonneg q M.nu σ hν hσ (X ω)
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => add_nonneg (hT0 ω) (by norm_num)
  have hP0 : ∀ ω, 0 ≤ P ω := fun ω => ENNReal.toReal_nonneg
  have hD0 : ∀ ω, 0 ≤ D ω := fun ω =>
    native_source_model_inverse_trace_nonneg q M.nu σq M.nu_pos hσq (X ω)
  have hDframe (ω : Cutoff.CutoffSample 2) :
      ρ * D ω = Matrix.trace ((frameMatrix σ
        (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu
          (ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ (X ω))))).lowerRight) := by
    rw [show D ω = bankInverseTraceObservable q M.nu σq M.nu_pos hσq (X ω) by rfl]
    rw [native_source_model_inverse_trace_eq_frame_trace q M.nu σq M.nu_pos hσq (X ω)]
    simp only [frameMatrix, Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply,
      Matrix.smul_apply, smul_eq_mul, Q, K]
    dsimp [ρ]
    field_simp [hσq.ne']
  have hDle : ∀ᵐ ω ∂μ, D ω ≤ 2 * P ω := by
    have hh := raw_shell_band_step_inverse_trace_le_local_history M h hM hg q s i hi
      (fun _ => (1 : ℝ)) hunit hstateLocal t htcc
    filter_upwards [hh] with ω hω
    simpa [D, P, X, W, i, hiadd] using hω
  have hP128 : eLpNorm P (128 : ℝ≥0∞) μ ≤ ENNReal.ofReal (3683 / 2500 : ℝ) := by
    simpa [P] using raw_shell_weighted_local_history_L128 M h hM hg q
      (q + (s : ℤ)) (by omega) W hW hstateLocal
  have hBsource := raw_shell_weighted_source_history_ae_le_local_history_at_frame
    M h hM hg q s hs W hW hstateLocal σ hσ
  have hratio : ρ ≤ C := by
    have hr := true_frame_ratio_le M m q
    have hgap : m - q = (s : ℤ) - 1 := by dsimp [q, s]; omega
    have hgapR : ((m - q : ℤ) : ℝ) = (s : ℝ) - 1 := by exact_mod_cast hgap
    have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have habs : |((m - q : ℤ) : ℝ)| = (s : ℝ) - 1 := by
      rw [hgapR]
      apply abs_of_nonneg
      linarith
    rw [habs] at hr
    simpa [ρ, C, rawTraceOldFrameP20LocalClock] using hr
  have hC0 : 0 ≤ C := by dsimp [C, rawTraceOldFrameP20LocalClock]; positivity
  have hBcap : ∀ᵐ ω ∂μ,
      max (lemmaVTileHistory Q (pureFluxBankSourceDepth s)
          (responseFramePlanarCoefficientField M.nu σ
            (pureFluxOpenResponseRestriction q (X ω))))
        (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
          (responseFramePlanarCoefficientField M.nu σ
            (pureFluxOpenResponseRestriction q (X ω)))) ≤ C * P ω := by
    filter_upwards [hBsource] with ω hω
    exact hω.trans (mul_le_mul_of_nonneg_right hratio (hP0 ω))
  have hF64 : eLpNorm F (64 : ℝ≥0∞) μ ≤ ENNReal.ofReal fCap := by
    let G := fun ω : Cutoff.CutoffSample 2 =>
      rootTraceObservable M Q m (m + 1) m (fun _ => Real.sqrt t) ω
    have hstateFull : ∀ j ≤ (m + 1) - 303, nativeInductionState M h j := by
      intro j hj
      apply hpast j
      omega
    have hfull := full_response_completed_bank64 M h hM hg Q (m + 1) m m
      (by change q - 1 ≤ m + 1; dsimp [q]; omega)
      (by change q - 342 ≤ m; dsimp [q]; omega)
      (by omega) hstateFull (fun _ => Real.sqrt t) hWm
    have hGcap : eLpNorm (fun ω => G ω / 4) (ENNReal.ofReal 64) μ ≤ ENNReal.ofReal
        (((2018618 : ℝ) / 1000000 + M.gamma *
          ((16684 : ℝ) * ((s + 1 : ℕ) : ℝ) + 5899542)) *
          (3 : ℝ) ^ (2 * M.gamma * ((s + 1 : ℕ) : ℝ) +
            2 * M.gamma * (s : ℝ))) := by
      have hDint : (m + 1 : ℤ) - q + 1 = (s + 1 : ℕ) := by dsimp [q, s]; omega
      have hD : ((m + 1 : ℤ) : ℝ) - (Q.scale : ℝ) + 1 = ((s + 1 : ℕ) : ℝ) := by
        rw [show Q.scale = q by rfl]
        exact_mod_cast hDint
      have hgapInt : m - q + 1 = (s : ℤ) := by dsimp [q, s]; omega
      have hgap : ((m - q + 1 : ℤ) : ℝ) = (s : ℝ) := by exact_mod_cast hgapInt
      have habs : |((m - q + 1 : ℤ) : ℝ)| = (s : ℝ) := by
        rw [hgap]
        exact abs_of_nonneg (by positivity)
      have hh := hfull
      have hQscale : Q.scale = q := by rfl
      rw [hQscale] at hh
      dsimp only at hh
      have hDq : ((m + 1 : ℤ) : ℝ) - (q : ℝ) + 1 = ((s + 1 : ℕ) : ℝ) := by
        rw [← hQscale]
        exact hD
      rw [hDq, habs] at hh
      simpa only [G, μ] using hh
    have hGeq : F = G := by
      funext ω
      dsimp only [G]
      obtain ⟨ell, hKell⟩ := exists_originCube_containing_compact K
        (isBounded_cubeSet Q).isCompact_closure
      have htrace := modelTraceObservable_inserted_eq_traceDefect q M ell m hKell σ t ω
      have hcoeff := full_response_coefficient_partial M (m + 1) t ω
      have hcoeff' : attenuatedCoefficient M m (m + 1) (fun _ => Real.sqrt t) ω =
          fun x => Cutoff.coefficientCutoff M.nu m ω x +
            Real.sqrt t • (ω.val (m + 1)).forgetShell x := by
        simpa only [show m + 1 - 1 = m by omega] using hcoeff
      have hcoeffModel : attenuatedCoefficient M m (m + 1)
          (fun _ => Real.sqrt t) ω = (Model.partialInsertedCoefficient M m t ω).toFun := by
        funext x
        rw [hcoeff']
        simp [Model.partialInsertedCoefficient]
      rw [root_trace_observable_eq_trace_defect]
      rw [hcoeffModel]
      rw [← htrace]
      simp only [F, T, Φ]
      rw [hX ω]
    rw [hGeq, show (64 : ℝ≥0∞) = ENNReal.ofReal (64 : ℝ) by norm_num]
    have hscale : G = (4 : ℝ) • (fun ω => G ω / 4) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hscale, eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 4)]
    have hfour : ENNReal.ofReal 4 * ENNReal.ofReal
        (((2018618 : ℝ) / 1000000 + M.gamma *
          ((16684 : ℝ) * ((s + 1 : ℕ) : ℝ) + 5899542)) *
          (3 : ℝ) ^ (2 * M.gamma * ((s + 1 : ℕ) : ℝ) +
            2 * M.gamma * (s : ℝ))) = ENNReal.ofReal fCap := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      dsimp [fCap, oldSignedP20Full64Cap]
      congr 1
      ring
    calc
      _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal
          (((2018618 : ℝ) / 1000000 + M.gamma *
            ((16684 : ℝ) * ((s + 1 : ℕ) : ℝ) + 5899542)) *
            (3 : ℝ) ^ (2 * M.gamma * ((s + 1 : ℕ) : ℝ) +
              2 * M.gamma * (s : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hGcap (by norm_num)
      _ = ENNReal.ofReal fCap := hfour
  have hTmeas' : AEStronglyMeasurable T μ := hTmeas.aestronglyMeasurable
  have hFmeas' : AEStronglyMeasurable F μ := hFmeas.aestronglyMeasurable
  have hPmeas' : AEStronglyMeasurable P μ := hPmeas.aestronglyMeasurable
  have hDmeas' : AEStronglyMeasurable D μ := hDmeas.aestronglyMeasurable
  have hfCap0 : 0 ≤ fCap := by
      have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
      have hpoly : 0 ≤ (2018618 : ℝ) / 1000000 + M.gamma *
          ((16684 : ℝ) * ((s + 1 : ℕ) : ℝ) + 5899542) := by positivity
      dsimp [fCap, oldSignedP20Full64Cap]
      exact mul_nonneg (mul_nonneg (by norm_num) hpoly) (by positivity)
  have hF60 : eLpNorm F (60:ℝ≥0∞) μ ≤ ENNReal.ofReal fCap :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (60:ℝ≥0∞)≤64)).trans hF64
  have hcaps := old_signed_p20_holder_caps_of_full_L60 μ P F T D fCap hfCap0
    hP0 hF0 hT0 (fun ω => by exact hD0 ω)
    (Filter.Eventually.of_forall fun ω => by dsimp [F, T]; linarith [hT0 ω])
    hDle hPmeas' hFmeas' hTmeas' hDmeas' hP128 hF60
  rcases hcaps with ⟨hTmem, hDmem, hPFmem, hP2Fmem,
    hTnorm, hDnorm, hPFnorm, hP2Fnorm⟩
  have hB0 : ∀ ω, 0 ≤ max
      (lemmaVTileHistory Q (pureFluxBankSourceDepth s)
        (responseFramePlanarCoefficientField M.nu σ
          (pureFluxOpenResponseRestriction q (X ω))))
      (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
        (responseFramePlanarCoefficientField M.nu σ
          (pureFluxOpenResponseRestriction q (X ω)))) := by
    intro ω
    exact le_max_of_le_left (lemmaVTileHistory_nonneg Q (pureFluxBankSourceDepth s) _)
  have hκ : 0 ≤ κ := by
    have hrho : 0 ≤ cubeScaleFactor Q /
        (q3ModelLength (q + (s : ℤ))).1 :=
      div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le (q3ModelLength (q + (s : ℤ))).2.le
    have hdelta : 0 ≤ diagMeshRadius Q (pureFluxBankSourceDepth s) /
        (q3ModelLength (q + (s : ℤ))).1 :=
      div_nonneg (diagMeshRadius_pos Q (pureFluxBankSourceDepth s)).le
        (q3ModelLength (q + (s : ℤ))).2.le
    dsimp [κ]
    unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
    positivity
  have hμ : 0 ≤ μR := (pureFlux_covariance_mu_lower A A').1
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hv' : 0 ≤ v' := mul_nonneg hv hC0
  have hμ' : 0 ≤ μR' := mul_nonneg hC0 hμ
  have hLbound : ∀ᵐ ω ∂μ,
      L ω ≤ v' * D ω + 2 * v' * κ * (P ω * F ω) +
        v' * μR' * (P ω ^ 2 * F ω) := by
    filter_upwards [hBcap] with ω hBω
    let Bsrc := max (lemmaVTileHistory Q (pureFluxBankSourceDepth s)
        (responseFramePlanarCoefficientField M.nu σ
          (pureFluxOpenResponseRestriction q (X ω))))
      (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
        (responseFramePlanarCoefficientField M.nu σ
          (pureFluxOpenResponseRestriction q (X ω))))
    have hBsrc0 : 0 ≤ Bsrc := by dsimp [Bsrc]; exact hB0 ω
    have hBsrc : Bsrc ≤ C * P ω := by simpa [Bsrc] using hBω
    have hBsrcsq : Bsrc ^ 2 ≤ C ^ 2 * P ω ^ 2 := by
      nlinarith [hBsrc, hP0 ω, hC0]
    have hrow := source_model_q3_positive_generator_row q s hs
      M.nu σ b hν hσ (X ω)
    dsimp only [] at hrow
    rw [← hDframe ω] at hrow
    have hrow' : L ω ≤ v * (ρ * D ω) +
        (2 * v * κ * Bsrc + v * μR * Bsrc ^ 2) * F ω := by
      change (1 / 2 : ℝ) * modelCovarianceTrace Φ H (X ω) ≤
        v * (ρ * D ω) +
          (2 * v * κ * Bsrc + v * μR * Bsrc ^ 2) * (T ω + 4)
      exact hrow
    have hDterm : v * (ρ * D ω) ≤ v' * D ω := by
      calc
        v * (ρ * D ω) = (v * ρ) * D ω := by ring
        _ ≤ (v * C) * D ω := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio hv) (hD0 ω)
        _ = v' * D ω := by simp [v']
    have hBF : Bsrc * F ω ≤ C * (P ω * F ω) := by
      calc
        _ ≤ (C * P ω) * F ω := mul_le_mul_of_nonneg_right hBsrc (hF0 ω)
        _ = C * (P ω * F ω) := by ring
    have hB2F : Bsrc ^ 2 * F ω ≤ C ^ 2 * (P ω ^ 2 * F ω) := by
      calc
        _ ≤ (C ^ 2 * P ω ^ 2) * F ω := mul_le_mul_of_nonneg_right hBsrcsq (hF0 ω)
        _ = C ^ 2 * (P ω ^ 2 * F ω) := by ring
    have hterms : (2 * v * κ * Bsrc + v * μR * Bsrc ^ 2) * F ω ≤
        2 * v' * κ * (P ω * F ω) + v' * μR' * (P ω ^ 2 * F ω) := by
      calc
        _ = (2 * v * κ) * (Bsrc * F ω) + (v * μR) * (Bsrc ^ 2 * F ω) := by ring
        _ ≤ (2 * v * κ) * (C * (P ω * F ω)) +
            (v * μR) * (C ^ 2 * (P ω ^ 2 * F ω)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hBF (by positivity))
            (mul_le_mul_of_nonneg_left hB2F (by positivity))
        _ = 2 * v' * κ * (P ω * F ω) +
            v' * μR' * (P ω ^ 2 * F ω) := by dsimp [v', μR']; ring
    calc
      L ω ≤ v * (ρ * D ω) +
          (2 * v * κ * Bsrc + v * μR * Bsrc ^ 2) * F ω := hrow'
      _ ≤ v' * D ω +
          (2 * v' * κ * (P ω * F ω) + v' * μR' * (P ω ^ 2 * F ω)) :=
        add_le_add hDterm hterms
      _ = _ := by ring
  have hLintegrable : Integrable L μ := by
    have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu σ hν hσ
    have hregular := source_q3_covariance_trace_regular q b
      (q3ModelLength (q + (s : ℤ))) Φ hΦ
    obtain ⟨ell, hKell⟩ := exists_originCube_containing_compact K
      (isBounded_cubeSet Q).isCompact_closure
    have hGen := bank_model_heat_integrable K M h hM ell m hKell
      (modelCovarianceTrace Φ H) hregular.1 hregular.2 t
    have heq : L = fun ω => (1 / 2 : ℝ) *
        modelCovarianceTrace Φ H (modelInsertedScalar K m t ω) := by
      funext ω
      simp [L, H, Φ, X, hX ω]
    rw [heq]
    exact hGen.const_mul (1 / 2 : ℝ)
  have hRightIntegrable : Integrable (fun ω =>
      v' * D ω + 2 * v' * κ * (P ω * F ω) +
        v' * μR' * (P ω ^ 2 * F ω)) μ := by
    have hDint : Integrable (fun ω => v' * D ω) μ :=
      (hDmem.integrable (by norm_num : (1:ℝ≥0∞) ≤ ENNReal.ofReal 20)).const_mul v'
    have hPFint : Integrable (fun ω => (2 * v' * κ) * (P ω * F ω)) μ :=
      (hPFmem.integrable (by norm_num : (1:ℝ≥0∞) ≤ ENNReal.ofReal 20)).const_mul
        (2 * v' * κ)
    have hP2int : Integrable (fun ω => (v' * μR') * (P ω ^ 2 * F ω)) μ :=
      (hP2Fmem.integrable (by norm_num : (1:ℝ≥0∞) ≤ ENNReal.ofReal 20)).const_mul
        (v' * μR')
    have hfun : (fun ω => v' * D ω + 2 * v' * κ * (P ω * F ω) +
          v' * μR' * (P ω ^ 2 * F ω)) =
        ((fun ω => v' * D ω) +
          (fun ω => (2 * v' * κ) * (P ω * F ω))) +
          (fun ω => (v' * μR') * (P ω ^ 2 * F ω)) := by
      funext ω
      simp only [Pi.add_apply]
    rw [hfun]
    exact (hDint.add hPFint).add hP2int
  have hint := integral_mono_ae hLintegrable hRightIntegrable hLbound
  have hDmean := old_signed_mean_integral_le_positiveLpNorm μ D hD0 hDmem
  have hPFmean := old_signed_mean_integral_le_positiveLpNorm μ (fun ω => P ω * F ω)
    (fun ω => mul_nonneg (hP0 ω) (hF0 ω)) hPFmem
  have hP2mean := old_signed_mean_integral_le_positiveLpNorm μ
    (fun ω => P ω ^ 2 * F ω)
    (fun ω => mul_nonneg (sq_nonneg (P ω)) (hF0 ω)) hP2Fmem
  have hfinal : (∫ ω, L ω ∂μ) ≤
      v' * (2 * (3683 / 2500 : ℝ)) +
        2 * v' * κ * ((3683 / 2500 : ℝ) * fCap) +
        v' * μR' * ((3683 / 2500 : ℝ) ^ 2 * fCap) := by
    calc
      _ ≤ ∫ ω, v' * D ω + 2 * v' * κ * (P ω * F ω) +
            v' * μR' * (P ω ^ 2 * F ω) ∂μ := hint
      _ = v' * (∫ ω, D ω ∂μ) +
            2 * v' * κ * (∫ ω, P ω * F ω ∂μ) +
            v' * μR' * (∫ ω, P ω ^ 2 * F ω ∂μ) := by
        have hpoint : (fun ω =>
            v' * D ω + 2 * v' * κ * (P ω * F ω) +
              v' * μR' * (P ω ^ 2 * F ω)) =
            (fun ω => v' * D ω) +
              (fun ω => (2 * v' * κ) * (P ω * F ω)) +
              (fun ω => (v' * μR') * (P ω ^ 2 * F ω)) := by
          funext ω
          simp only [Pi.add_apply]
        rw [hpoint]
        have hDint : Integrable (fun ω => v' * D ω) μ :=
          (hDmem.integrable (by norm_num)).const_mul v'
        have hPFint : Integrable (fun ω => (2 * v' * κ) * (P ω * F ω)) μ :=
          (hPFmem.integrable (by norm_num)).const_mul (2 * v' * κ)
        have hP2int : Integrable (fun ω => (v' * μR') * (P ω ^ 2 * F ω)) μ :=
          (hP2Fmem.integrable (by norm_num)).const_mul (v' * μR')
        change (∫ ω, (((fun ω => v' * D ω) +
          (fun ω => (2 * v' * κ) * (P ω * F ω))) ω) +
          (v' * μR') * (P ω ^ 2 * F ω) ∂μ) = _
        rw [integral_add (hDint.add hPFint) hP2int]
        change (∫ ω, v' * D ω + (2 * v' * κ) * (P ω * F ω) ∂μ) +
          ∫ ω, (v' * μR') * (P ω ^ 2 * F ω) ∂μ = _
        rw [integral_add hDint hPFint]
        rw [integral_const_mul, integral_const_mul, integral_const_mul]
      _ ≤ v' * (2 * (3683 / 2500 : ℝ)) +
          2 * v' * κ * ((3683 / 2500 : ℝ) * fCap) +
          v' * μR' * ((3683 / 2500 : ℝ) ^ 2 * fCap) := by
        have hcoeffD : 0 ≤ v' := hv'
        have hcoeffPF : 0 ≤ 2 * v' * κ := by positivity
        have hcoeffP2 : 0 ≤ v' * μR' := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hDmean hcoeffD,
          mul_le_mul_of_nonneg_left hPFmean hcoeffPF,
          mul_le_mul_of_nonneg_left hP2mean hcoeffP2,
          hDnorm, hPFnorm, hP2Fnorm]
  have hrate : inSourceMeanRateActual M h m r t = ∫ ω, L ω ∂μ := by
    dsimp only [inSourceMeanRateActual]
    unfold modelHeatTraceAverage modelHeatAverage
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp only [L, Φ, H]
    rw [hX ω]
    dsimp only [b]
    rw [hqs]
  have hvEq : v' = v * C := by rfl
  have hmuEq : μR' = C * μR := by rfl
  have hcapEq : oldSignedMeanSourceCap M h m r =
      v * C * (2 * (3683 / 2500 : ℝ) +
        2 * κ * (3683 / 2500 : ℝ) * fCap +
        C * μR * (3683 / 2500 : ℝ) ^ 2 * fCap) := by rfl
  have hfinalCap : (∫ ω, L ω ∂μ) ≤
      v * C * (2 * (3683 / 2500 : ℝ) +
        2 * κ * (3683 / 2500 : ℝ) * fCap +
        C * μR * (3683 / 2500 : ℝ) ^ 2 * fCap) := by
    calc
      _ ≤ v' * (2 * (3683 / 2500 : ℝ)) +
            2 * v' * κ * ((3683 / 2500 : ℝ) * fCap) +
            v' * μR' * ((3683 / 2500 : ℝ) ^ 2 * fCap) := hfinal
      _ = _ := by rw [hvEq, hmuEq]; ring
  constructor
  · rw [hrate, hcapEq]
    exact hfinalCap
  · rw [hcapEq]
    have hvC : 0 ≤ v * C := mul_nonneg hv hC0
    positivity


end
end ASDExplicitGamma.Native

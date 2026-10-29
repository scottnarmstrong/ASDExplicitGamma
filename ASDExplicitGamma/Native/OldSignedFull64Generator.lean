module

public import ASDExplicitGamma.Inverse.RawShellBandBankInputs
public import ASDExplicitGamma.Inverse.RawShellBandGenerator
public import ASDExplicitGamma.Inverse.RawShellBankMoment
public import ASDExplicitGamma.Inverse.RawShellQ3Law
public import ASDExplicitGamma.Inverse.OrderBandBounds
public import ASDExplicitGamma.Inverse.FullResponseExports
public import ASDExplicitGamma.Gaussian.ModelHeatTrace
public import ASDExplicitGamma.Gaussian.ModelHeatPower
public import ASDExplicitGamma.Native.VanishingBracket
public import ASDExplicitGamma.Native.OldSignedFullSixtyHolder
public import ASDExplicitGamma.Inverse.RawShellFixedFrameGeneralP20

/-! The actual fixed-OLD-frame p20 generator using the smaller full64 bank.
Adapted from Inverse.RawShellFixedFrameGeneralP20; the original export is unchanged. -/

@[expose] public section

namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Inverse

open MeasureTheory Set Filter
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open Algsuperdiff.Section3.Cutoff
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Response
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open ASDExplicitGamma.Native
open scoped ENNReal

noncomputable def oldSignedP20Full64Cap (gamma : ℝ) (s : ℕ) : ℝ :=
  4 * ((2018618 : ℝ) / 1000000 + gamma *
      ((16684 : ℝ) * ((s + 1 : ℕ) : ℝ) + 5899542)) *
    (3 : ℝ) ^ (2 * gamma * ((s + 1 : ℕ) : ℝ) + 2 * gamma * (s : ℝ))

/-- The finite-p generator row for cell scale `q` in the fixed OLD
frame `sigmaBar M m`. The shell is inserted at `q+s=m+1`; all local and full
response inputs are derived from the native state prefix through `m`. -/
theorem old_signed_p20_generator_full64
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (q m : ℤ) (s : ℕ)
    (hqs : q + (s : ℤ) = m + 1) (hs : 6 ≤ s)
    (hpast : ∀ j ≤ m, nativeInductionState M h j) :
    let Q := originCube 2 q
    let σ := (Annealed.sigmaBar M m : ℝ)
    let κ := rawTraceRemainderKappaF
      (cubeScaleFactor Q / (q3ModelLength (q + (s : ℤ))).1)
      (diagMeshRadius Q (pureFluxBankSourceDepth s) /
        (q3ModelLength (q + (s : ℤ))).1)
    let κB := rawTraceRemainderB
      (cubeScaleFactor Q / (q3ModelLength (q + (s : ℤ))).1)
      (diagMeshRadius Q (pureFluxBankSourceDepth s) /
        (q3ModelLength (q + (s : ℤ))).1)
    let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
      (rawTraceRemainderA (pureFluxCovarianceRho 0 (s - 1))
        (pureFluxCovarianceDelta 0 (s - 1)))
      (rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
        (pureFluxCovarianceDelta 0 (s - 1)))
    let v := (q3ModelAmplitude M h (q + (s : ℤ))) ^ 2 / σ ^ 2
    let C := rawTraceOldFrameP20LocalClock M.gamma s
    let fCap := oldSignedP20Full64Cap M.gamma s
    let U : ℝ → ℝ := fun _ =>
      v * ((78 + 76 * κ) * (C * (3683 / 2500 : ℝ)) +
        2 * κ * (C * (3683 / 2500 : ℝ)) * fCap +
        (μR + 38 * (κB ^ 2 + κ)) * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap)
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      deriv (modelTracePowerHeatAverage q M m 20) t ≤
        20 * modelTracePowerHeatAverage q M m 20 t ^ ((19 : ℝ) / 20) * U t := by
  classical
  dsimp only
  intro t ht
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Q := originCube 2 q
  let K := closure (cubeSet Q)
  let σ : ℝ := Annealed.sigmaBar M m
  let σq : ℝ := Annealed.sigmaBar M q
  let J := q + (s : ℤ)
  let i := s - 1
  let W := rawShellBandStepWeights q i (fun _ => (1 : ℝ)) t
  let X := fun ω : Cutoff.CutoffSample 2 =>
    rawShellBandScalarFromWeights M q s W ω
  let Φ := modelTraceObservable q M.nu σ
  let b := q3ModelAmplitude M h J
  let H := pureFluxMainCubeQ3Directions q b (q3ModelLength J)
  let T := fun ω => Φ (X ω)
  let F := fun ω => T ω + 4
  let P := rawShellWeightedLocalHistory M q J W
  let D := fun ω => bankInverseTraceObservable q M.nu σq
    M.nu_pos (Annealed.sigmaBar_characterization M q).1 (X ω)
  let L := fun ω => (1 / 2 : ℝ) * modelCovarianceTrace Φ H (X ω)
  let Γ := fun ω => modelGradientSquareTrace Φ H (X ω)
  let κ := rawTraceRemainderKappaF
    (cubeScaleFactor Q / (q3ModelLength J).1)
    (diagMeshRadius Q (pureFluxBankSourceDepth s) / (q3ModelLength J).1)
  let κB := rawTraceRemainderB
    (cubeScaleFactor Q / (q3ModelLength J).1)
    (diagMeshRadius Q (pureFluxBankSourceDepth s) / (q3ModelLength J).1)
  let A := rawTraceRemainderA (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let A' := rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0 A A'
  let v := b ^ 2 / σ ^ 2
  let R := σ / σq
  let C := rawTraceOldFrameP20LocalClock M.gamma s
  let fCap := oldSignedP20Full64Cap M.gamma s
  let qCap := C * (κB ^ 2 + κ) - κ

  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hσq : 0 < σq := (Annealed.sigmaBar_characterization M q).1
  have hν : 0 < M.nu := M.nu_pos
  have hstateLocal : ∀ j < q, nativeInductionState M h j := by
    intro j hj
    exact hpast j (by omega)
  have hstateFull : ∀ j ≤ J - 303, nativeInductionState M h j := by
    intro j hj
    have hJ : J = m + 1 := by dsimp [J]; omega
    rw [hJ] at hj
    exact hpast j (by omega)
  have hi : i < s := by dsimp [i]; omega
  have hiadd : i + 1 = s := by dsimp [i]; omega
  have hs1 : 1 ≤ s := by omega
  have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hunit : ∀ k ∈ Finset.Ioc q (q + (s : ℤ)),
      0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 := by intros; norm_num
  have hW : ∀ k ∈ Finset.Ioc q J, 0 ≤ W k ∧ W k ≤ 1 := by
    intro k hk
    have hstep := raw_shell_band_step_weights_bounds q s i hi (fun _ => (1 : ℝ))
      hunit t htcc k (by simpa [J] using hk)
    simpa [W, J, hiadd] using hstep
  have hWpartial (k : ℤ) (hk : k ∈ Finset.Ioc q J) :
      W k = bankPartialInsertionWeights q s t k := by
    have hcur : q + (i : ℤ) + 1 = q + (s : ℤ) := by
      dsimp [i]
      omega
    by_cases htop : k = q + (s : ℤ)
    · subst k
      change rawShellBandStepWeights q i (fun _ => (1 : ℝ)) t (q + (s : ℤ)) = _
      simp [rawShellBandStepWeights, bankPartialInsertionWeights, hcur]
    · have hlt : k < q + (s : ℤ) := by
        have hk' := Finset.mem_Ioc.mp hk
        dsimp [J] at hk'
        omega
      have hprev : k ∈ Finset.Ioc q (q + (i : ℤ)) := by
        simp only [Finset.mem_Ioc]
        have hk' := Finset.mem_Ioc.mp hk
        dsimp [J] at hk'
        constructor
        · exact hk'.1
        · dsimp [i]
          omega
      change rawShellBandStepWeights q i (fun _ => (1 : ℝ)) t k = _
      simp [rawShellBandStepWeights, bankPartialInsertionWeights,
        htop, hlt, hprev, hcur]

  have hcoeff (ω : Cutoff.CutoffSample 2) :
      attenuatedCoefficient M q J W ω =
        (Model.partialInsertedCoefficient M m t ω).toFun := by
    have hweights : attenuatedCoefficient M q J W ω =
        attenuatedCoefficient M q J (bankPartialInsertionWeights q s t) ω := by
      funext x
      unfold attenuatedCoefficient
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [hWpartial k hk]
    rw [hweights]
    funext x
    calc
      attenuatedCoefficient M q J (bankPartialInsertionWeights q s t) ω x =
          Cutoff.coefficientCutoff M.nu (q + (s : ℤ) - 1) ω x +
            Real.sqrt t • (ω.val (q + (s : ℤ))).forgetShell x :=
        raw_shell_partial_coefficient_any M q s hs1 t ω x
      _ = (Model.partialInsertedCoefficient M m t ω).toFun x := by
        have htime : q + (s : ℤ) - 1 = m := by omega
        have hendpoint : q + (s : ℤ) = m + 1 := by omega
        rw [htime, hendpoint]
        change (Cutoff.coefficientCutoff M.nu m ω).toFun x +
          Real.sqrt t • (ω.val (m + 1)).forgetShell.toFun x =
          (Model.partialInsertedCoefficient M m t ω).toFun x
        simp [Model.partialInsertedCoefficient]

  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet Q).isCompact_closure
  have hX (ω : Cutoff.CutoffSample 2) :
      X ω = modelInsertedScalar K m t ω := by
    ext x
    calc
      X ω x = attenuatedCoefficient M q J W ω x.1 1 0 :=
        raw_shell_weighted_scalar_eq_coefficient_entry M q s W ω ell hK x
      _ = Model.partialInsertedCoefficient M m t ω x.1 1 0 := by
        rw [hcoeff ω]
      _ = modelInsertedScalar K m t ω x := by
        symm
        exact modelInsertedScalar_apply K M ell m hK t ω x

  have hΦ : HasPolynomiallyBoundedC2Derivatives Φ :=
    modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu σ hν hσ
  have hΦ0 : ∀ x, 0 ≤ Φ x := modelTraceObservable_nonneg q M.nu σ hν hσ
  have hXmeas : Measurable X := measurable_raw_shell_weighted_prefix M q s W
  have hTmeas : Measurable T := hΦ.1.continuous.measurable.comp hXmeas
  have hFmeas : Measurable F := hTmeas.add measurable_const
  have hPmeas : Measurable P := raw_shell_weighted_local_history_measurable M q J W
  have hDmeas : Measurable D :=
    (bank_inverse_trace_observable_C2 q M.nu σq M.nu_pos hσq).1.continuous.measurable.comp hXmeas
  have hT0 : ∀ ω, 0 ≤ T ω := fun ω => hΦ0 (X ω)
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => add_nonneg (hT0 ω) (by norm_num)
  have hP0 : ∀ ω, 0 ≤ P ω := fun ω => ENNReal.toReal_nonneg
  have hDframeq (ω : Cutoff.CutoffSample 2) :
      D ω = Matrix.trace
        ((frameMatrix σq (coarseBlockMatrix (cubeSet Q)
          (responsePlanarCoefficientField M.nu
            (ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ (X ω))))).lowerRight) := by
    change bankInverseTraceObservable q M.nu σq M.nu_pos hσq (X ω) = _
    rw [bank_inverse_trace_observable_eq q M.nu σq M.nu_pos hσq (X ω)]
    simp [Q, K, bankInverseTrace, frameMatrix, Matrix.trace,
      Fin.sum_univ_two, Matrix.diag_apply, Matrix.smul_apply, smul_eq_mul]
  have hDframe (ω : Cutoff.CutoffSample 2) :
      R * D ω = Matrix.trace
        ((frameMatrix σ (coarseBlockMatrix (cubeSet Q)
          (responsePlanarCoefficientField M.nu
            (ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ (X ω))))).lowerRight) := by
    rw [hDframeq ω]
    simp [R, frameMatrix, Matrix.trace, Fin.sum_univ_two,
      Matrix.diag_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp [hσq.ne']
  have hD0 : ∀ ω, 0 ≤ D ω := by
    intro ω
    let k := ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ (X ω)
    have hrows := nativeTraceShearDefectRows Q M.nu σq hν hσq k
    have hσq2 : 0 < σq ^ 2 := sq_pos_of_pos hσq
    have hmul := mul_pos hrows.2.1 hσq2
    have heq :
        (Matrix.trace (frameMatrix σq
          (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu k))).lowerRight /
          σq ^ 2) * σq ^ 2 =
        Matrix.trace (frameMatrix σq
          (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu k))).lowerRight :=
      div_mul_cancel₀ _ hσq2.ne'
    rw [heq] at hmul
    rw [hDframeq ω]
    exact hmul.le

  have hDstep := raw_shell_band_step_inverse_trace_le_local_history M h hM hg q s i hi
    (fun _ => (1 : ℝ)) hunit hstateLocal t htcc
  have hDle : ∀ᵐ ω ∂μ, D ω ≤ 2 * P ω := by
    filter_upwards [hDstep] with ω hω
    simpa [D, P, X, J, hiadd] using hω
  have hP128 := raw_shell_weighted_local_history_L128 M h hM hg q J
    (by dsimp [J]; omega) W hW hstateLocal
  have hP128' : eLpNorm P (128 : ℝ≥0∞) μ ≤ ENNReal.ofReal (3683 / 2500 : ℝ) := by
    simpa only [P, μ] using hP128

  have hsource := raw_shell_weighted_source_history_ae_le_local_history_at_frame
    M h hM hg q s hs1 W hW hstateLocal σ hσ
  have hRle : R ≤ C := by
    have hratio := true_frame_ratio_le M m q
    have hgap : m - q = (s : ℤ) - 1 := by omega
    have hgapR : ((m - q : ℤ) : ℝ) = (s : ℝ) - 1 := by exact_mod_cast hgap
    have hs1R : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
    have hs0R : 0 ≤ (s : ℝ) - 1 := by linarith
    have habs : |((m - q : ℤ) : ℝ)| = (s : ℝ) - 1 := by
      rw [hgapR, abs_of_nonneg hs0R]
    rw [habs] at hratio
    simpa [C, rawTraceOldFrameP20LocalClock] using hratio
  have hR0 : 0 ≤ R := div_nonneg hσ.le hσq.le
  have hC1 : 1 ≤ C := by
    apply Real.one_le_rpow (by norm_num)
    have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
    have hs0 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
    have harg : 0 ≤ 2 * M.gamma * ((s : ℝ) - 1) := by nlinarith
    exact harg
  have hC0 : 0 ≤ C := by linarith
  have hBsource : ∀ᵐ ω ∂μ,
      max (lemmaVTileHistory Q (pureFluxBankSourceDepth s)
            (responseFramePlanarCoefficientField M.nu σ
              (pureFluxOpenResponseRestriction q (X ω))))
          (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
            (responseFramePlanarCoefficientField M.nu σ
              (pureFluxOpenResponseRestriction q (X ω)))) ≤ C * P ω := by
    filter_upwards [hsource] with ω hω
    have hω' :
        max (lemmaVTileHistory Q (pureFluxBankSourceDepth s)
              (responseFramePlanarCoefficientField M.nu σ
                (pureFluxOpenResponseRestriction q (X ω))))
            (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
              (responseFramePlanarCoefficientField M.nu σ
                (pureFluxOpenResponseRestriction q (X ω)))) ≤ R * P ω := by
      simpa [Q, P] using hω
    exact hω'.trans (mul_le_mul_of_nonneg_right hRle (hP0 ω))

  have hFcap : eLpNorm F (64 : ℝ≥0∞) μ ≤ ENNReal.ofReal fCap := by
    have hQscale : Q.scale = q := by rfl
    have hfull := full_response_completed_bank64 M h hM hg Q (m + 1) m m
      (by rw [hQscale]; omega) (by rw [hQscale]; omega) (by omega)
      (fun j hj => hpast j (by omega)) (fun _ => Real.sqrt t)
      (by
        intro j hj
        have hj' : j = m + 1 := by simp only [Finset.mem_Ioc] at hj; omega
        subst j
        exact ⟨Real.sqrt_nonneg t, (Real.sqrt_le_one).mpr htcc.2⟩)
    have hDint : (m + 1 : ℤ) - q + 1 = (s + 1 : ℕ) := by omega
    have hD : ((m + 1 : ℤ) : ℝ) - (Q.scale : ℝ) + 1 = ((s + 1 : ℕ) : ℝ) := by
      rw [hQscale]
      exact_mod_cast hDint
    have hgapInt : m - q + 1 = (s : ℤ) := by omega
    have hgap : ((m - q + 1 : ℤ) : ℝ) = (s : ℝ) := by exact_mod_cast hgapInt
    have habs : |((m - q + 1 : ℤ) : ℝ)| = (s : ℝ) := by
      rw [hgap]
      exact abs_of_nonneg (by positivity)
    rw [hQscale] at hfull
    have hfullProfile : eLpNorm
        (fun ω => rootTraceObservable M Q m (m + 1) m (fun _ => Real.sqrt t) ω / 4)
        (ENNReal.ofReal 64) μ ≤ ENNReal.ofReal
          (((2018618 : ℝ) / 1000000 + M.gamma *
              ((16684 : ℝ) * ((s + 1 : ℕ) : ℝ) + 5899542)) *
            (3 : ℝ) ^ (2 * M.gamma * ((s + 1 : ℕ) : ℝ) + 2 * M.gamma * (s : ℝ))) := by
      dsimp only at hfull
      have hDq : ((m + 1 : ℤ) : ℝ) - (q : ℝ) + 1 = ((s + 1 : ℕ) : ℝ) := by
        exact_mod_cast hDint
      rw [hDq, habs] at hfull
      simpa only [μ] using hfull
    have hF_eq : F = fun ω =>
        rootTraceObservable M Q m (m + 1) m (fun _ => Real.sqrt t) ω := by
      funext ω
      have hmodel := modelTraceObservable_inserted_eq_traceDefect q M ell m hK σ t ω
      have hcoeff := full_response_coefficient_partial M (m + 1) t ω
      have hcoeff' : attenuatedCoefficient M m (m + 1) (fun _ => Real.sqrt t) ω =
          fun x => Cutoff.coefficientCutoff M.nu m ω x +
            Real.sqrt t • (ω.val (m + 1)).forgetShell x := by
        simpa only [show m + 1 - 1 = m by omega] using hcoeff
      have hcoeffModel : attenuatedCoefficient M m (m + 1) (fun _ => Real.sqrt t) ω =
          (Model.partialInsertedCoefficient M m t ω).toFun := by
        funext x
        rw [hcoeff']
        simp [Model.partialInsertedCoefficient]
      rw [root_trace_observable_eq_trace_defect]
      rw [hcoeffModel]
      rw [← hmodel]
      simp only [F, T]
      rw [← hX ω]
    rw [hF_eq, show (64 : ℝ≥0∞) = ENNReal.ofReal (64 : ℝ) by norm_num]
    have hscale :
        (fun ω => rootTraceObservable M Q m (m + 1) m (fun _ => Real.sqrt t) ω) =
          (4 : ℝ) • (fun ω =>
            rootTraceObservable M Q m (m + 1) m (fun _ => Real.sqrt t) ω / 4) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hscale, eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 4)]
    calc
      ENNReal.ofReal 4 * eLpNorm
          (fun ω => rootTraceObservable M Q m (m + 1) m (fun _ => Real.sqrt t) ω / 4)
          (ENNReal.ofReal 64) μ ≤
          ENNReal.ofReal 4 * ENNReal.ofReal
            (((2018618 : ℝ) / 1000000 + M.gamma *
                ((16684 : ℝ) * ((s + 1 : ℕ) : ℝ) + 5899542)) *
              (3 : ℝ) ^ (2 * M.gamma * ((s + 1 : ℕ) : ℝ) + 2 * M.gamma * (s : ℝ))) := by
        gcongr
      _ = ENNReal.ofReal fCap := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        dsimp [fCap, oldSignedP20Full64Cap]
        congr 1
        ring

  have hPcap0 : 0 ≤ (3683 / 2500 : ℝ) := by positivity
  have hfCap0 : 0 ≤ fCap := by
    dsimp [fCap, oldSignedP20Full64Cap]
    have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
    positivity
  have hcaps := old_signed_p20_holder_caps_of_full_L60 μ P F T D fCap hfCap0
    hP0 hF0 hT0 hD0
    (Filter.Eventually.of_forall fun ω => by dsimp [F, T]; linarith [hT0 ω])
    hDle hPmeas.aestronglyMeasurable hFmeas.aestronglyMeasurable
    hTmeas.aestronglyMeasurable hDmeas.aestronglyMeasurable hP128' ((eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (60:ℝ≥0∞)≤64)).trans hFcap)
  rcases hcaps with ⟨hTmem, hDmem, hPFmem, hP2Fmem,
    hTnorm, hDnorm, hPFnorm, hP2Fnorm⟩

  have hBnonneg : ∀ ω, 0 ≤
      max (lemmaVTileHistory Q (pureFluxBankSourceDepth s)
            (responseFramePlanarCoefficientField M.nu σ
              (pureFluxOpenResponseRestriction q (X ω))))
          (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
            (responseFramePlanarCoefficientField M.nu σ
              (pureFluxOpenResponseRestriction q (X ω)))) := by
    intro ω
    exact le_max_of_le_left (lemmaVTileHistory_nonneg Q (pureFluxBankSourceDepth s) _)
  have hB : ∀ᵐ ω ∂μ,
      max (lemmaVTileHistory Q (pureFluxBankSourceDepth s)
            (responseFramePlanarCoefficientField M.nu σ
              (pureFluxOpenResponseRestriction q (X ω))))
          (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
            (responseFramePlanarCoefficientField M.nu σ
              (pureFluxOpenResponseRestriction q (X ω)))) ≤ C * P ω := hBsource
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hκ : 0 ≤ κ := by
    dsimp [κ]
    unfold rawTraceRemainderKappaF
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
    unfold rawTraceRemainderB
    have hρ : 0 ≤ cubeScaleFactor Q / (q3ModelLength J).1 :=
      div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
        (q3ModelLength J).2.le
    have hδ : 0 ≤ diagMeshRadius Q (pureFluxBankSourceDepth s) /
        (q3ModelLength J).1 :=
      div_nonneg (diagMeshRadius_pos Q (pureFluxBankSourceDepth s)).le
        (q3ModelLength J).2.le
    positivity
  have hμR : 0 ≤ μR := by
    dsimp [μR]
    unfold rawTraceRemainderMu
    apply div_nonneg
    · have hH0 : 0 ≤ rawTraceRemainderH0 := by norm_num [rawTraceRemainderH0]
      positivity
    · norm_num
  have hqCap : 0 ≤ qCap := by
    dsimp [qCap]
    have hC1 : 1 ≤ C := hC1
    nlinarith [sq_nonneg κB]
  let v' := v * C
  let muR' := C * μR
  have hv' : 0 ≤ v' := mul_nonneg hv hC0
  have hmuR' : 0 ≤ muR' := mul_nonneg hC0 hμR
  have hL : ∀ᵐ ω ∂μ,
      L ω ≤ v' * D ω + 2 * v' * κ * (P ω * F ω) +
        v' * muR' * (P ω ^ 2 * F ω) := by
    have hq3 := hBsource
    filter_upwards [hq3] with ω hBω
    have hrow := raw_trace_model_q3_positive_generator_row q s hs1 M.nu σ b hν hσ (X ω)
    dsimp only [] at hrow
    rw [← hDframe ω] at hrow
    let Bsrc := max (lemmaVTileHistory Q (pureFluxBankSourceDepth s)
        (responseFramePlanarCoefficientField M.nu σ
          (pureFluxOpenResponseRestriction q (X ω))))
      (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
        (responseFramePlanarCoefficientField M.nu σ
          (pureFluxOpenResponseRestriction q (X ω))))
    have hBnonneg' : 0 ≤ Bsrc := by dsimp [Bsrc]; exact hBnonneg ω
    have hB' : Bsrc ≤ C * P ω := by simpa [Bsrc] using hBω
    have hBsq : Bsrc ^ 2 ≤ C ^ 2 * P ω ^ 2 := by
      nlinarith [hB', hBnonneg', hP0 ω, hC0]
    have hB2F : Bsrc ^ 2 * F ω ≤ C ^ 2 * (P ω ^ 2 * F ω) := by
      calc
        _ ≤ (C ^ 2 * P ω ^ 2) * F ω := mul_le_mul_of_nonneg_right hBsq (hF0 ω)
        _ = C ^ 2 * (P ω ^ 2 * F ω) := by ring
    have hbase : L ω ≤ v * (R * D ω) +
        (2 * v * κ * Bsrc + v * μR * Bsrc ^ 2) * F ω := by
      simpa [Q, J, L, D, X, Φ, H, T, F, κ, A, A', μR, v, b, Bsrc,
        rawShellWeightedSourceHistory, pureFluxBankSourceDepth, cubeScaleFactor,
        originCube] using hrow
    have hDterm : v * (R * D ω) ≤ v' * D ω := by
      calc
        v * (R * D ω) = (v * R) * D ω := by ring
        _ ≤ (v * C) * D ω := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRle hv) (hD0 ω)
        _ = v' * D ω := by simp [v']
    have hBF : Bsrc * F ω ≤ C * (P ω * F ω) := by
      calc
        _ ≤ (C * P ω) * F ω := mul_le_mul_of_nonneg_right hB' (hF0 ω)
        _ = C * (P ω * F ω) := by ring
    have hB2F : Bsrc ^ 2 * F ω ≤ C ^ 2 * (P ω ^ 2 * F ω) := by
      calc
        _ ≤ (C ^ 2 * P ω ^ 2) * F ω := mul_le_mul_of_nonneg_right hBsq (hF0 ω)
        _ = C ^ 2 * (P ω ^ 2 * F ω) := by ring
    have hsourceTerms :
        (2 * v * κ * Bsrc + v * μR * Bsrc ^ 2) * F ω ≤
          2 * v' * κ * (P ω * F ω) + v' * muR' * (P ω ^ 2 * F ω) := by
      calc
        _ = (2 * v * κ) * (Bsrc * F ω) + (v * μR) * (Bsrc ^ 2 * F ω) := by ring
        _ ≤ (2 * v * κ) * (C * (P ω * F ω)) +
            (v * μR) * (C ^ 2 * (P ω ^ 2 * F ω)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hBF (by positivity))
            (mul_le_mul_of_nonneg_left hB2F (by positivity))
        _ = 2 * v' * κ * (P ω * F ω) +
            v' * muR' * (P ω ^ 2 * F ω) := by
          dsimp [v', muR']
          ring
    calc
      L ω ≤ v * (R * D ω) +
          (2 * v * κ * Bsrc + v * μR * Bsrc ^ 2) * F ω := hbase
      _ ≤ v' * D ω +
          (2 * v' * κ * (P ω * F ω) + v' * muR' * (P ω ^ 2 * F ω)) :=
        add_le_add hDterm hsourceTerms
      _ = v' * D ω + 2 * v' * κ * (P ω * F ω) +
          v' * muR' * (P ω ^ 2 * F ω) := by ring
  have hΓ : ∀ᵐ ω ∂μ,
      Γ ω ≤ 4 * v' * T ω * ((1 + κ) * D ω + (qCap + κ) * (P ω ^ 2 * F ω)) := by
    filter_upwards [hBsource] with ω hBω
    have hrow := raw_trace_model_q3_full_bracket_row q s M.nu σ b hν hσ (X ω)
    dsimp only [] at hrow
    rw [← hDframe ω] at hrow
    let Bsrc := max (lemmaVTileHistory Q (pureFluxBankSourceDepth s)
        (responseFramePlanarCoefficientField M.nu σ
          (pureFluxOpenResponseRestriction q (X ω))))
      (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
        (responseFramePlanarCoefficientField M.nu σ
          (pureFluxOpenResponseRestriction q (X ω))))
    have hBnonneg' : 0 ≤ Bsrc := by dsimp [Bsrc]; exact hBnonneg ω
    have hB' : Bsrc ≤ C * P ω := by simpa [Bsrc] using hBω
    have hBsq : Bsrc ^ 2 ≤ C ^ 2 * P ω ^ 2 := by
      nlinarith [hB', hBnonneg', hP0 ω, hC0]
    have hbase : Γ ω ≤ 4 * v * T ω *
        ((1 + κ) * (R * D ω) + (κB ^ 2 + κ) * Bsrc ^ 2 * F ω) := by
      simpa [Q, J, Γ, D, X, Φ, H, T, F, κ, κB, v, b, Bsrc,
        rawShellWeightedSourceHistory, pureFluxBankSourceDepth, cubeScaleFactor,
        originCube] using hrow
    have hB2F : Bsrc ^ 2 * F ω ≤ C ^ 2 * (P ω ^ 2 * F ω) := by
      calc
        _ ≤ (C ^ 2 * P ω ^ 2) * F ω := mul_le_mul_of_nonneg_right hBsq (hF0 ω)
        _ = C ^ 2 * (P ω ^ 2 * F ω) := by ring
    have hinner :
        (1 + κ) * (R * D ω) + (κB ^ 2 + κ) * Bsrc ^ 2 * F ω ≤
          C * ((1 + κ) * D ω + (κB ^ 2 + κ) * C * (P ω ^ 2 * F ω)) := by
      have hDterm : (1 + κ) * (R * D ω) ≤ C * ((1 + κ) * D ω) := by
        have hRD : R * D ω ≤ C * D ω :=
          mul_le_mul_of_nonneg_right hRle (hD0 ω)
        calc
          _ ≤ (1 + κ) * (C * D ω) :=
            mul_le_mul_of_nonneg_left hRD (by positivity)
          _ = C * ((1 + κ) * D ω) := by ring
      have hBterm : (κB ^ 2 + κ) * (Bsrc ^ 2 * F ω) ≤
          C * ((κB ^ 2 + κ) * C * (P ω ^ 2 * F ω)) := by
        calc
          _ ≤ (κB ^ 2 + κ) * (C ^ 2 * (P ω ^ 2 * F ω)) :=
            mul_le_mul_of_nonneg_left hB2F (add_nonneg (sq_nonneg κB) hκ)
          _ = C * ((κB ^ 2 + κ) * C * (P ω ^ 2 * F ω)) := by ring
      calc
        _ = (1 + κ) * (R * D ω) +
            (κB ^ 2 + κ) * (Bsrc ^ 2 * F ω) := by ring
        _ ≤ C * ((1 + κ) * D ω) +
            C * ((κB ^ 2 + κ) * C * (P ω ^ 2 * F ω)) :=
              add_le_add hDterm hBterm
        _ = _ := by ring
    have houter : 0 ≤ 4 * v * T ω :=
      mul_nonneg (mul_nonneg (by norm_num) hv) (hT0 ω)
    have hbase' := mul_le_mul_of_nonneg_left hinner houter
    have houter' : 4 * v * T ω *
        (C * ((1 + κ) * D ω + (κB ^ 2 + κ) * C * (P ω ^ 2 * F ω))) =
      4 * v' * T ω * ((1 + κ) * D ω + (qCap + κ) * (P ω ^ 2 * F ω)) := by
      dsimp [v', qCap]
      ring
    calc
      Γ ω ≤ 4 * v * T ω *
          ((1 + κ) * (R * D ω) + (κB ^ 2 + κ) * Bsrc ^ 2 * F ω) := hbase
      _ ≤ _ := hbase'
      _ = _ := houter'

  have hΦpow := hasPolynomiallyBoundedC2Derivatives_rpow hΦ hΦ0
    (by norm_num : (2 : ℝ) ≤ 20)
  obtain ⟨ellHeat, hKHeat⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet Q).isCompact_closure
  obtain ⟨Treal, vreal, hAreal, hlaw, _hΦregular, _htraceCont,
      _htraceHeatCont, _htraceDeriv, _htraceDeriv0, hpowers⟩ :=
    exists_modelTrace_heat_and_moment_identities q M h hM m
  let Hreal : ℕ → C(K, ℝ) := fun j => Treal (vreal j)
  have hHreal : Summable (fun j => ‖Hreal j‖ ^ 2) :=
    summable_sq_norm_gaussianDirections hAreal Treal
  have hGenMeas := measurable_modelCovarianceTrace
    (fun x : C(K, ℝ) => Φ x ^ (20 : ℝ)) hΦpow.1 Hreal
  have hGenGrowth := polynomial_modelCovarianceTrace Hreal hHreal
    (fun x : C(K, ℝ) => Φ x ^ (20 : ℝ)) hΦpow
  have hGenIntegrable := bank_model_heat_integrable K M h hM ellHeat m hKHeat
    (modelCovarianceTrace (fun x => Φ x ^ (20 : ℝ)) Hreal)
    hGenMeas hGenGrowth t
  have hGeneratorInt : Integrable
      (fun ω => 20 * T ω ^ (19 : ℝ) * L ω + 190 * T ω ^ (18 : ℝ) * Γ ω) μ := by
    have hEq : (fun ω => 20 * T ω ^ (19 : ℝ) * L ω +
        190 * T ω ^ (18 : ℝ) * Γ ω) =
        fun ω => (1 / 2 : ℝ) * modelCovarianceTrace
          (fun x : C(K, ℝ) => Φ x ^ (20 : ℝ)) Hreal
          (modelInsertedScalar K m t ω) := by
      funext ω
      have hpow := modelCovarianceTrace_rpow hAreal Treal
        (fun x : C(K, ℝ) => Φ x) hΦ hΦ0
        (p := 20) (by norm_num : (2 : ℝ) ≤ 20) (X ω)
      have htime : q + (s : ℤ) = m + 1 := hqs
      have hlaw' : (Cutoff.cutoffSampleLaw M).toMeasure.map
          (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K
            (ω.1 (q + (s : ℤ)))) =
          standardGaussianInfinitePi.map (gaussianSeriesLimitE hAreal Treal) := by
        simpa only [htime] using hlaw
      have hgen := raw_trace_model_q3_power_generator_eq_of_fresh_law
        q M h hM s σ hσ Treal vreal hAreal hlaw' (X ω)
      have hpoint : 20 * (Φ (X ω)) ^ (19 : ℝ) *
          ((1 / 2 : ℝ) * modelCovarianceTrace Φ H (X ω)) +
          190 * (Φ (X ω)) ^ (18 : ℝ) * modelGradientSquareTrace Φ H (X ω) =
          modelPowerHeatGenerator Φ H 20 (X ω) := by
        rw [modelPowerHeatGenerator]
        norm_num
      rw [← hX ω]
      rw [hpoint]
      calc
        modelPowerHeatGenerator Φ H 20 (X ω) =
            modelPowerHeatGenerator Φ Hreal 20 (X ω) := hgen.symm
        _ = (1 / 2 : ℝ) * modelCovarianceTrace
            (fun x : C(K, ℝ) => Φ x ^ (20 : ℝ)) Hreal (X ω) := hpow.symm
    rw [hEq]
    exact (hGenIntegrable.const_mul (1 / 2 : ℝ))

  have hrow := raw_trace_p20_generator_integral_bound μ T D
    (fun ω => P ω * F ω) (fun ω => P ω ^ 2 * F ω) L Γ v' κ muR' qCap
    hv' hκ hmuR' hqCap hT0 hD0
    (fun ω => mul_nonneg (hP0 ω) (hF0 ω))
    (fun ω => mul_nonneg (sq_nonneg (P ω)) (hF0 ω))
    hTmem hDmem hPFmem hP2Fmem hL hΓ hGeneratorInt
  have hcoeff :
      v' * (39 + 38 * κ) * positiveLpNorm μ 20 D +
        2 * v' * κ * positiveLpNorm μ 20 (fun ω => P ω * F ω) +
        v' * (muR' + 38 * (qCap + κ)) *
          positiveLpNorm μ 20 (fun ω => P ω ^ 2 * F ω) ≤
      v * ((78 + 76 * κ) * (C * (3683 / 2500 : ℝ)) +
        2 * κ * (C * (3683 / 2500 : ℝ)) * fCap +
        (μR + 38 * (κB ^ 2 + κ)) * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap) := by
    have hDcoef : 0 ≤ v' * (39 + 38 * κ) := by positivity
    have hPFcoef : 0 ≤ 2 * v' * κ := by positivity
    have hP2coef : 0 ≤ v' * (muR' + 38 * (qCap + κ)) := by positivity
    have hqeq : qCap + κ = C * (κB ^ 2 + κ) := by dsimp [qCap]; ring
    calc
      _ ≤ v' * (39 + 38 * κ) * (2 * (3683 / 2500 : ℝ)) +
          2 * v' * κ * ((3683 / 2500 : ℝ) * fCap) +
          v' * (muR' + 38 * (qCap + κ)) *
            ((3683 / 2500 : ℝ) ^ 2 * fCap) := by
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hDnorm hDcoef)
          (mul_le_mul_of_nonneg_left hPFnorm hPFcoef))
          (mul_le_mul_of_nonneg_left hP2Fnorm hP2coef)
      _ = _ := by
        dsimp [v', muR']
        rw [hqeq]
        ring
  have hmoment0 : 0 ≤ ∫ ω, T ω ^ (20 : ℝ) ∂μ := by
    apply integral_nonneg
    intro ω
    exact Real.rpow_nonneg (hT0 ω) _
  have hscale : 0 ≤ 20 * (∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) := by
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hmoment0 _)
  have hrow' :
      (∫ ω, 20 * T ω ^ (19 : ℝ) * L ω +
        190 * T ω ^ (18 : ℝ) * Γ ω ∂μ) ≤
      20 * (∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) *
        (v * ((78 + 76 * κ) * (C * (3683 / 2500 : ℝ)) +
          2 * κ * (C * (3683 / 2500 : ℝ)) * fCap +
          (μR + 38 * (κB ^ 2 + κ)) * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap)) := by
    calc
      _ ≤ 20 * (∫ ω, T ω ^ (20 : ℝ) ∂μ) ^ ((19 : ℝ) / 20) *
          (v' * (39 + 38 * κ) * positiveLpNorm μ 20 D +
            2 * v' * κ * positiveLpNorm μ 20 (fun ω => P ω * F ω) +
            v' * (muR' + 38 * (qCap + κ)) *
              positiveLpNorm μ 20 (fun ω => P ω ^ 2 * F ω)) := hrow
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoeff hscale

  have hmoment := hpowers 20 (by norm_num : (2 : ℝ) ≤ 20)
  have hderiv := hmoment.2.2.1 t ht.1
  have hderiv_eq : deriv (modelTracePowerHeatAverage q M m 20) t =
      modelHeatAverage K M m
        (modelPowerHeatGenerator Φ (fun j => Treal (vreal j)) 20) t := by
    exact hderiv.deriv
  have hderivInt : deriv (modelTracePowerHeatAverage q M m 20) t =
      ∫ ω, 20 * T ω ^ (19 : ℝ) * L ω +
        190 * T ω ^ (18 : ℝ) * Γ ω ∂μ := by
    rw [hderiv_eq]
    unfold modelHeatAverage
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      have hpow := modelCovarianceTrace_rpow hAreal Treal
        (fun x : C(K, ℝ) => Φ x) hΦ hΦ0
        (p := 20) (by norm_num : (2 : ℝ) ≤ 20) (X ω)
      have htime : q + (s : ℤ) = m + 1 := hqs
      have hlaw'' : (Cutoff.cutoffSampleLaw M).toMeasure.map
          (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K
            (ω.1 (q + (s : ℤ)))) =
          standardGaussianInfinitePi.map (gaussianSeriesLimitE hAreal Treal) := by
        simpa only [htime] using hlaw
      have hgen := raw_trace_model_q3_power_generator_eq_of_fresh_law
        q M h hM s σ hσ Treal vreal hAreal hlaw'' (X ω)
      have hpoint : 20 * T ω ^ (19 : ℝ) * L ω +
          190 * T ω ^ (18 : ℝ) * Γ ω = modelPowerHeatGenerator Φ H 20 (X ω) := by
        rw [modelPowerHeatGenerator]
        norm_num [L, Γ, T]
      change modelPowerHeatGenerator Φ Hreal 20 (modelInsertedScalar K m t ω) =
        20 * T ω ^ (19 : ℝ) * L ω + 190 * T ω ^ (18 : ℝ) * Γ ω
      rw [← hX ω]
      calc
        modelPowerHeatGenerator Φ Hreal 20 (X ω) =
            modelPowerHeatGenerator Φ H 20 (X ω) := hgen
        _ = 20 * T ω ^ (19 : ℝ) * L ω +
            190 * T ω ^ (18 : ℝ) * Γ ω := hpoint.symm
  rw [hderivInt]
  have hmomentEq : modelTracePowerHeatAverage q M m 20 t =
      ∫ ω, T ω ^ (20 : ℝ) ∂μ := by
    rw [modelTracePowerHeatAverage_eq]
    unfold modelHeatAverage
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      change modelTraceObservable q M.nu σ
          (modelInsertedScalar K m t ω) ^ (20 : ℝ) = T ω ^ (20 : ℝ)
      rw [← hX ω]
  rw [hmomentEq]
  exact hrow'

end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Main.ObsInverseDeficitBounds
public import ASDExplicitGamma.Main.InverseDeficitHeatAdapter
public import ASDExplicitGamma.Main.InverseDeficitODE
public import ASDExplicitGamma.Main.HotGeneratorIntegral
public import ASDExplicitGamma.Inverse.BankHeatIntegrability
public import ASDExplicitGamma.Main.HotGeneratorHypotheses
public import ASDExplicitGamma.Inverse.BridgeGlobalBank

/-! MA-INVERSE-DEFICIT at observer cubes, step 2: the global bank moment bound for the observer
history `B*`, and the absolute inverse-deficit branch from the pathwise lower generator (A) at
`Q = originCube 2 (m+hobs)`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
  ASDExplicitGamma.Native ASDExplicitGamma.Model ASDExplicitGamma.Scalar
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- The pathwise lower generator (A) at the observer root: the exact interface shape fixed by the
observer lower generator (frame `σ̄_m`, shell `m+1`, `v = (amp/σ̄_m)²`, global history
`B* = mixedBridgeBstar`). -/
def ObsInverseLowerGen (M : ABKModel 2) (h : ℝ) (m : ℤ) (hobs : ℕ) (t : ℝ) : Prop :=
  ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
    (1 / 2 : ℝ) * modelCovarianceTrace
        (mainInverseObservable (m + (hobs : ℤ)) M.nu (Annealed.sigmaBar M m : ℝ))
        (pureFluxMainCubeQ3Directions (m + (hobs : ℤ)) (q3ModelAmplitude M h (m + 1))
          (q3ModelLength (m + 1)))
        (modelInsertedScalar (closure (cubeSet (originCube 2 (m + (hobs : ℤ))))) m t ω) ≥
      -(mainInverseMuMinusSource
          ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) *
        (max 1 (mixedBridgeBstar M m t ω)) ^ 2 *
        mainInverseObservable (m + (hobs : ℤ)) M.nu (Annealed.sigmaBar M m : ℝ)
          (modelInsertedScalar (closure (cubeSet (originCube 2 (m + (hobs : ℤ))))) m t ω))

theorem obs_inverse_observable_measurable (M : ABKModel 2) (n m : ℤ) (t : ℝ) :
    Measurable (fun ω : CutoffSample 2 =>
      mainInverseObservable n M.nu (Annealed.sigmaBar M m : ℝ)
        (modelInsertedScalar (closure (cubeSet (originCube 2 n))) m t ω)) := by
  let K := closure (cubeSet (originCube 2 n))
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hscalar : Measurable (modelInsertedScalar K m t) := by
    change Measurable (fun ω => olderField K m ω +
      Real.sqrt t • shellFieldScalarRestriction K (ω.1 (m + 1)))
    exact (measurable_olderField K ell m hK).add
      (((measurable_shellFieldScalarRestriction K).comp
        ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)).const_smul (Real.sqrt t))
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar_characterization M m).1
  exact (mainInverseObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ).1.continuous.measurable.comp hscalar

/-- Bank moment bound for the observer history `B*`: integrability and the cubic estimate. -/
theorem obs_inverse_cubic_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ))) :
    let n := m + (hobs : ℤ)
    let σ : ℝ := Annealed.sigmaBar M m
    let x := modelInsertedScalar (closure (cubeSet (originCube 2 n))) m t
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let d : CutoffSample 2 → ℝ := fun ω => mainInverseObservable n M.nu σ (x ω)
    Integrable d μ ∧
      Integrable (fun ω => (max 1 (mixedBridgeBstar M m t ω)) ^ 2 * d ω) μ ∧
      ∫ ω, (max 1 (mixedBridgeBstar M m t ω)) ^ 2 * d ω ∂μ ≤
        mainBeta ^ 2 * (∫ ω, d ω ∂μ) +
          2 * (2 * mainBeta ^ 2 * mainEpsNew + 3 * mainBeta * mainEpsNew ^ 2 +
            mainEpsNew ^ 3) := by
  intro n σ x μ d
  let Y : CutoffSample 2 → ENNReal :=
    bankFiniteRootHistoryMax (mixedBridgeObserverSourceRoots m) M m (m + 40)
      (bankPartialInsertionWeights m 1 t)
  let B : CutoffSample 2 → ℝ := fun ω => mixedBridgeBstar M m t ω
  let Bstar : CutoffSample 2 → ℝ := fun ω => max 1 (B ω)
  let R : CutoffSample 2 → ℝ :=
    inverseBankPopulationRemainder .globalInverse (mixedBridgeObserverSourceRoots m) M m
      (m + 40) (bankPartialInsertionWeights m 1 t)
  let β : ℝ := inverseBankCap .globalInverse
  let ε : ℝ := inverseBankReserve .globalInverse
  have hBank := mixed_bridge_global_bank_inputs M h hM hγ m t ht hstate
  have hB0 : ∀ ω, 0 ≤ B ω := fun ω => mixed_bridge_bstar_nonneg M m t ω
  have hBY : ∀ ω, B ω = (Y ω).toReal := by
    intro ω
    have := mixed_bridge_bstar_eq_bank_finite_history M m t ht ω
    simp only [Y, B]
    rw [← this, ENNReal.toReal_ofReal (hB0 ω)]
  have hYmeas : Measurable Y := history_finite_max_measurable _ _
    (fun Q' => bank_root_inverse_history_measurable Q'.1 M m (m + 40)
      (bankPartialInsertionWeights m 1 t))
  have hBmeas : Measurable B := by
    have : B = fun ω => (Y ω).toReal := funext hBY
    rw [this]
    exact ENNReal.measurable_toReal.comp hYmeas
  have hBstarMeas : Measurable Bstar := measurable_const.max hBmeas
  have hβ : 1 ≤ β := by norm_num [β, inverseBankCap, inverseBankA, inverseBankE]
  have hβ0 : 0 ≤ β := le_trans (by norm_num) hβ
  have hε : 0 ≤ ε := by norm_num [ε, inverseBankReserve]
  have hBank' := hBank
  have hBmem := main_inverse_deficit_toReal_memLp_lp128_of_ennreal
    Y β hβ0 hBank.history_finite hBank.total_L128
  have hBmem' : MemLp B 128 μ := by
    have : B = fun ω => (Y ω).toReal := funext hBY
    rw [this]; exact hBmem.1
  have hsource : ∀ ω, 0 ≤ d ω ∧ d ω ≤ 2 * B ω := fun ω =>
    obs_inverse_trace_bounds M m hobs h40 t ht ω
  have hBstar0 : ∀ᵐ ω ∂μ, 0 ≤ Bstar ω :=
    Filter.Eventually.of_forall fun ω => (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 (B ω))
  have hBstarMem : MemLp Bstar 128 μ := by
    apply MemLp.mono' ((memLp_const (1 : ℝ)).add hBmem') hBstarMeas.aestronglyMeasurable
    filter_upwards with ω
    change ‖max 1 (B ω)‖ ≤ 1 + B ω
    rw [Real.norm_of_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 (B ω)))]
    exact max_le (by linarith [hB0 ω]) (by norm_num)
  have hR0 : ∀ ω, 0 ≤ R ω := hBank.remainder_nonneg
  have hBsplit : ∀ᵐ ω ∂μ, Bstar ω ≤ β + R ω := by
    filter_upwards [hBank.history_le] with ω hω
    have hsplit : Y ω ≤ ENNReal.ofReal (β + R ω) := by
      rw [← ENNReal.ofReal_add hβ0 (hR0 ω)] at hω
      simpa [Y, β, R] using hω
    have hreal : B ω ≤ β + R ω := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsplit
      rw [hBY ω]
      simpa [ENNReal.toReal_ofReal (add_nonneg hβ0 (hR0 ω))] using this
    have hpad : 1 ≤ β + R ω := by nlinarith [hβ, hR0 ω]
    exact max_le hpad hreal
  have hdmeas : Measurable d := obs_inverse_observable_measurable M n m t
  have hdB : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω ≤ 2 * Bstar ω :=
    Filter.Eventually.of_forall fun ω =>
      ⟨(hsource ω).1, (hsource ω).2.trans
        (mul_le_mul_of_nonneg_left (le_max_right 1 (B ω)) (by norm_num))⟩
  have hRmem : MemLp R 128 μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hBank.remainder_L128 ENNReal.ofReal_lt_top
  have hRcap : lpNorm R 128 μ ≤ ε := by
    change (eLpNorm R 128 μ).toReal ≤ ε
    calc
      _ ≤ (ENNReal.ofReal ε).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBank.remainder_L128
      _ = ε := ENNReal.toReal_ofReal hε
  have hIntegrable := main_inverse_deficit_trace_integrability_of_lp128
    Bstar d hdmeas hBstarMem hBstar0 hdB
  have hbound := main_inverse_deficit_cubic_integral_bound_of_lp128
    β ε Bstar d R hβ0 (Filter.Eventually.of_forall hR0) hBsplit hdB
    hIntegrable.2 hIntegrable.1 hRmem hRcap
  refine ⟨hIntegrable.1, hIntegrable.2, ?_⟩
  have hbound' : ∫ ω, Bstar ω ^ 2 * d ω ∂μ ≤ β ^ 2 * (∫ ω, d ω ∂μ) +
      2 * (2 * β ^ 2 * ε + 3 * β * ε ^ 2 + ε ^ 3) := hbound
  have hβe : β = mainBeta := by norm_num [β, inverseBankCap, inverseBankA, inverseBankE, mainBeta]
  have hεe : ε = mainEpsNew := by norm_num [ε, inverseBankReserve, mainEpsNew]
  rw [hβe, hεe] at hbound'
  exact hbound'

/-- Integrability and heat-average identity of the half covariance trace of the inverse trace. -/
theorem obs_inverse_trace_average (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (n : ℤ) (t : ℝ) :
    let K := closure (cubeSet (originCube 2 n))
    let σ : ℝ := Annealed.sigmaBar M m
    let b := q3ModelAmplitude M h (m + 1)
    let L := q3ModelLength (m + 1)
    let Ψ : C(K, ℝ) → ℝ := modelCovarianceTrace (mainInverseObservable n M.nu σ)
      (pureFluxMainCubeQ3Directions n b L)
    Integrable (fun ω => (1 / 2 : ℝ) * Ψ (modelInsertedScalar K m t ω))
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (1 / 2 : ℝ) * modelHeatTraceAverage K M m (mainInverseObservable n M.nu σ)
      (fun j => mainCubeH3Value n b L (mainCubeQ3Directions n b L j)) t =
      ∫ ω, (1 / 2 : ℝ) * Ψ (modelInsertedScalar K m t ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  intro K σ b L Ψ
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let H : ℕ → C(K, ℝ) := pureFluxMainCubeQ3Directions n b L
  have hΦ : HasPolynomiallyBoundedC2Derivatives (mainInverseObservable n M.nu σ) :=
    mainInverseObservable_hasPolynomiallyBoundedC2Derivatives n M.nu σ M.nu_pos hσ
  have hH : Summable (fun j => ‖H j‖ ^ 2) := by
    exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(K, ℝ) inferInstance (mainCubeH3InnerProductSpace n b L).toNormedSpace
      inferInstance inferInstance (mainCubeQ3Directions n b L)
      (mainCubeQ3Directions_summable n b L) (mainCubeH3Value n b L)
  have hΨmeas : Measurable Ψ :=
    measurable_modelCovarianceTrace (mainInverseObservable n M.nu σ) hΦ.1 H
  have hΨgrowth : HasPolynomialGrowth Ψ :=
    polynomial_modelCovarianceTrace H hH (mainInverseObservable n M.nu σ) hΦ
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hint : Integrable (fun ω => Ψ (modelInsertedScalar K m t ω))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    bank_model_heat_integrable K M h hM ell m hK Ψ hΨmeas hΨgrowth t
  refine ⟨hint.const_mul (1 / 2 : ℝ), ?_⟩
  unfold modelHeatTraceAverage modelHeatAverage Ψ
  rw [← integral_const_mul]
  rfl

/-- The averaged lower generator row at one time, from (A) and the bank moment bound. -/
theorem obs_inverse_generator_row
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)))
    (hA : ObsInverseLowerGen M h m hobs s) :
    let n := m + (hobs : ℤ)
    let σ : ℝ := Annealed.sigmaBar M m
    let amp := q3ModelAmplitude M h (m + 1)
    let L := q3ModelLength (m + 1)
    let μminus := mainInverseMuMinusSource ((amp / σ) ^ 2)
    (-mainKappa μminus * mainInverseHeatAverage n M m s - mainKappa μminus * mainRho ≤
      (1 / 2 : ℝ) * modelHeatTraceAverage (closure (cubeSet (originCube 2 n))) M m
        (mainInverseObservable n M.nu σ)
        (fun j => mainCubeH3Value n amp L (mainCubeQ3Directions n amp L j)) s) := by
  intro n σ amp L μminus
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hamp : 0 < amp := mul_pos hM.1 (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _)
  have hv : 0 < (amp / σ) ^ 2 := sq_pos_of_pos (div_pos hamp hσ)
  have hmu : 0 < μminus := by
    have hkb : 0 < mainInverseKB ((amp / σ) ^ 2) := by
      unfold mainInverseKB mainInverseA2 mainInverseA4
      positivity
    unfold μminus mainInverseMuMinusSource mainInverseMuMinus
    have hrad : 0 < mainInverseKB ((amp / σ) ^ 2) ^ 4 +
        4 * (63 / 50 : ℝ) ^ 2 * mainInverseKA ((amp / σ) ^ 2) ^ 2 *
          mainInverseKB ((amp / σ) ^ 2) ^ 2 := by positivity
    have hroot := Real.sqrt_pos.2 hrad
    positivity
  obtain ⟨hint, heq⟩ := obs_inverse_trace_average M h hM m n s
  obtain ⟨hdInt, hBdInt, hbound⟩ := obs_inverse_cubic_bound M h hM hγ m hobs h40 s hs hstate
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hleft : Integrable (fun ω => -(μminus * (max 1 (mixedBridgeBstar M m s ω)) ^ 2 *
      mainInverseObservable n M.nu σ
        (modelInsertedScalar (closure (cubeSet (originCube 2 n))) m s ω))) μ := by
    refine (hBdInt.const_mul (-μminus)).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only []
    ring
  have hrowInt := integral_mono_ae hleft hint hA
  have hmean : (∫ ω, mainInverseObservable n M.nu σ
      (modelInsertedScalar (closure (cubeSet (originCube 2 n))) m s ω) ∂μ) =
      mainInverseHeatAverage n M m s := by
    unfold mainInverseHeatAverage
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact mainInverseObservable_inserted M m n s ω
  have hmomentScale := mul_le_mul_of_nonneg_left hbound hmu.le
  have hrem : mainBeta ^ 2 * mainRho =
      2 * (2 * mainBeta ^ 2 * mainEpsNew + 3 * mainBeta * mainEpsNew ^ 2 + mainEpsNew ^ 3) := by
    norm_num [mainBeta, mainEpsNew, mainRho]
  have hscale : mainKappa μminus * (mainInverseHeatAverage n M m s + mainRho) =
      μminus * (mainBeta ^ 2 * (∫ ω, mainInverseObservable n M.nu σ
        (modelInsertedScalar (closure (cubeSet (originCube 2 n))) m s ω) ∂μ) +
        2 * (2 * mainBeta ^ 2 * mainEpsNew + 3 * mainBeta * mainEpsNew ^ 2 + mainEpsNew ^ 3)) := by
    rw [hmean, ← hrem]
    unfold mainKappa
    ring
  have hint2 : (∫ ω, -(μminus * (max 1 (mixedBridgeBstar M m s ω)) ^ 2 *
      mainInverseObservable n M.nu σ
        (modelInsertedScalar (closure (cubeSet (originCube 2 n))) m s ω)) ∂μ) =
      -μminus * ∫ ω, (max 1 (mixedBridgeBstar M m s ω)) ^ 2 *
        mainInverseObservable n M.nu σ
          (modelInsertedScalar (closure (cubeSet (originCube 2 n))) m s ω) ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only []
    ring
  rw [← heq] at hrowInt
  rw [hint2] at hrowInt
  calc -mainKappa μminus * mainInverseHeatAverage n M m s - mainKappa μminus * mainRho
      = -(mainKappa μminus * (mainInverseHeatAverage n M m s + mainRho)) := by ring
    _ = -(μminus * (mainBeta ^ 2 * (∫ ω, mainInverseObservable n M.nu σ
        (modelInsertedScalar (closure (cubeSet (originCube 2 n))) m s ω) ∂μ) +
        2 * (2 * mainBeta ^ 2 * mainEpsNew + 3 * mainBeta * mainEpsNew ^ 2 +
          mainEpsNew ^ 3))) := by rw [hscale]
    _ ≤ -μminus * ∫ ω, (max 1 (mixedBridgeBstar M m s ω)) ^ 2 *
        mainInverseObservable n M.nu σ
          (modelInsertedScalar (closure (cubeSet (originCube 2 n))) m s ω) ∂μ := by
      nlinarith [hmomentScale]
    _ ≤ _ := hrowInt

/-- MA-INVERSE-DEFICIT at an observer cube: `-v (u(t) - 2) ≤ I_abs(t)` with `v = (amp/σ̄_m)²`,
from the pathwise lower generator (A) at every time. -/
theorem obs_inverse_deficit_absolute_branch
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (N : ℤ) (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h40 : hobs ≤ 40)
    (hA : ∀ s ∈ Set.Icc (0 : ℝ) 1, ObsInverseLowerGen M h m hobs s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    -((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) *
        (mainInverseHeatAverage (m + (hobs : ℤ)) M m t - 2) ≤
      mainInverseAbs ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
        (mainInverseMuMinusSource
          ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)) t := by
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar_characterization M m).1
  have hamp : 0 < q3ModelAmplitude M h (m + 1) :=
    mul_pos hM.1 (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _)
  have hv : 0 < (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2 :=
    sq_pos_of_pos (div_pos hamp hσ)
  have hmu : 0 < mainInverseMuMinusSource
      ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) := by
    have hkb : 0 < mainInverseKB
        ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) := by
      unfold mainInverseKB mainInverseA2 mainInverseA4
      positivity
    unfold mainInverseMuMinusSource mainInverseMuMinus
    have hrad : 0 < mainInverseKB
          ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) ^ 4 +
        4 * (63 / 50 : ℝ) ^ 2 * mainInverseKA
          ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) ^ 2 *
          mainInverseKB
            ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) ^ 2 := by
      positivity
    have hroot := Real.sqrt_pos.2 hrad
    positivity
  have hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)) := fun j =>
    hpast (m - (j : ℤ)) (by omega)
  have hgen : ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      -mainKappa (mainInverseMuMinusSource
          ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)) *
        mainInverseHeatAverage (m + (hobs : ℤ)) M m s -
        mainKappa (mainInverseMuMinusSource
          ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)) * mainRho ≤
      (1 / 2 : ℝ) * modelHeatTraceAverage
        (closure (cubeSet (originCube 2 (m + (hobs : ℤ))))) M m
        (mainInverseObservable (m + (hobs : ℤ)) M.nu (Annealed.sigmaBar M m : ℝ))
        (fun j => mainCubeH3Value (m + (hobs : ℤ)) (q3ModelAmplitude M h (m + 1))
          (q3ModelLength (m + 1))
          (mainCubeQ3Directions (m + (hobs : ℤ)) (q3ModelAmplitude M h (m + 1))
            (q3ModelLength (m + 1)) j)) s :=
    Filter.Eventually.of_forall fun s hs =>
      obs_inverse_generator_row M h hM hγ m hobs h40 s hs hstate (hA s hs)
  exact main_inverse_heat_absolute_branch_of_generator_bound (m + (hobs : ℤ)) M h hM m _ t hmu
    hv.le ht hgen

end

end ASDExplicitGamma.Main

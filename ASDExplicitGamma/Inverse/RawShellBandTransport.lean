module

public import ASDExplicitGamma.Inverse.RawShellBandP20Row
public import ASDExplicitGamma.Inverse.RawMomentRoot
public import ASDExplicitGamma.Inverse.RawShellBudget
public import ASDExplicitGamma.Native.GenericSourceInitialRoot
public import ASDExplicitGamma.Inverse.SourceCovarianceBudget
public import ASDExplicitGamma.Gaussian.ModelHeatAverage

/-! The finite weighted raw-trace shell telescope in the fixed base frame. -/

@[expose] public section

open MeasureTheory Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open Algsuperdiff.Section3.Cutoff
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Native ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational
open scoped ENNReal

namespace ASDExplicitGamma.Inverse

/-- The actual p=20 moment of the finite weighted raw shell prefix. -/
@[irreducible] noncomputable def rawShellBandP20Moment (M : ABKModel 2) (n : ℤ)
    (s : ℕ) (weights : ℤ → ℝ) : ℝ :=
  ∫ ω : CutoffSample 2,
    (modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
      (rawShellBandScalarFromWeights M n s weights ω)) ^ (20 : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure

private theorem raw_shell_band_power_generator_eq_heat_trace
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (i : ℕ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (i : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1)
    (Treal : GaussianFactorL2 ℕ →L[ℝ]
      C(closure (cubeSet (originCube 2 n)), ℝ))
    (vreal : ℕ → GaussianFactorL2 ℕ)
    (hAreal : Summable (fun j => ‖vreal j‖ ^ 2))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : CutoffSample 2 => shellFieldScalarRestriction
        (closure (cubeSet (originCube 2 n))) (ω.1 (n + (i : ℤ) + 1))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hAreal Treal))
    (t : ℝ) :
    let K := closure (cubeSet (originCube 2 n))
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let X := rawShellBandScalarFromWeights M n i weights
    let Y := fun ω : CutoffSample 2 => shellFieldScalarRestriction K
      (ω.1 (n + (i : ℤ) + 1))
    let Φ := modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
    let Ψ := fun x : C(K, ℝ) => Φ x ^ (20 : ℝ)
    let H := pureFluxMainCubeQ3Directions n
      (q3ModelAmplitude M h (n + ((i + 1 : ℕ) : ℤ)))
      (q3ModelLength (n + ((i + 1 : ℕ) : ℤ)))
    (∫ ω, modelPowerHeatGenerator Φ H 20 (X ω + Real.sqrt t • Y ω) ∂μ) =
      (1 / 2 : ℝ) * randomBaseHeatTraceAverage hAreal Treal (μ.map X) Ψ t := by
  classical
  dsimp only
  let K := closure (cubeSet (originCube 2 n))
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := rawShellBandScalarFromWeights M n i weights
  let Y : CutoffSample 2 → C(K, ℝ) := fun ω =>
    shellFieldScalarRestriction K (ω.1 (n + (i : ℤ) + 1))
  let Φ : C(K, ℝ) → ℝ := modelTraceObservable n M.nu (Annealed.sigmaBar M n)
  let Ψ : C(K, ℝ) → ℝ := fun x => Φ x ^ (20 : ℝ)
  let H := pureFluxMainCubeQ3Directions n
    (q3ModelAmplitude M h (n + ((i + 1 : ℕ) : ℤ)))
    (q3ModelLength (n + ((i + 1 : ℕ) : ℤ)))
  let Hreal : ℕ → C(K, ℝ) := fun j => Treal (vreal j)
  let C : C(K, ℝ) → ℝ := modelCovarianceTrace Ψ Hreal
  have hν : 0 < M.nu := M.nu_pos
  have hσ : 0 < (Annealed.sigmaBar M n : ℝ) :=
    (Annealed.sigmaBar_characterization M n).1
  have hΦderiv : HasPolynomiallyBoundedC2Derivatives Φ :=
    modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
      (Annealed.sigmaBar M n) hν hσ
  have hΦ0 : ∀ x, 0 ≤ Φ x :=
    modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n) hν hσ
  have hΨderiv := hasPolynomiallyBoundedC2Derivatives_rpow hΦderiv hΦ0
    (by norm_num : (2 : ℝ) ≤ 20)
  have hX : Measurable X := measurable_raw_shell_weighted_prefix M n i weights
  have hY : Measurable Y := (measurable_shellFieldScalarRestriction K).comp
    ((measurable_pi_apply (n + (i : ℤ) + 1)).comp measurable_subtype_coe)
  have hind := indepFun_raw_shell_weighted_prefix_fresh M n i weights
  have hMom := raw_shell_weighted_prefix_polynomial_moments M n i weights hw
  have hHreal : Summable (fun j => ‖Hreal j‖ ^ 2) :=
    summable_sq_norm_gaussianDirections hAreal Treal
  have hCmeas := measurable_modelCovarianceTrace Ψ hΨderiv.1 Hreal
  have hCgrowth := polynomial_modelCovarianceTrace Hreal hHreal Ψ hΨderiv
  have hins := integral_independent_insertion μ X Y hX hY hind
    hAreal Treal hlaw hMom C hCmeas hCgrowth t
  have hprodInt := integrable_randomBaseHeatIntegrand hAreal Treal (μ.map X)
    hMom C hCmeas hCgrowth t
  have hprod : (∫ p : C(K, ℝ) × (ℕ → ℝ),
      C (p.1 + Real.sqrt t • gaussianSeriesLimitE hAreal Treal p.2)
        ∂((μ.map X).prod standardGaussianInfinitePi)) =
      randomBaseHeatTraceAverage hAreal Treal (μ.map X) Ψ t := by
    rw [integral_prod _ hprodInt]
    simp only [randomBaseHeatTraceAverage, gaussianSeriesHeatTraceAverage,
      gaussianSeriesHeatTrace, gaussianSeriesHeatArgument, modelCovarianceTrace,
      C, Hreal, Ψ]
  have hgenEq (x : C(K, ℝ)) :
      modelPowerHeatGenerator Φ H 20 x = (1 / 2 : ℝ) * C x := by
    have htime : n + (i : ℤ) + 1 = n + ((i + 1 : ℕ) : ℤ) := by
      simp only [Nat.cast_add, Nat.cast_one]
      omega
    have hlawQ3 : (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : CutoffSample 2 => shellFieldScalarRestriction K
          (ω.1 (n + ((i + 1 : ℕ) : ℤ)))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hAreal Treal) := by
      simpa only [htime] using hlaw
    have hmodel := raw_trace_model_q3_power_generator_eq_of_fresh_law
      n M h hM (i + 1) (Annealed.sigmaBar M n) hσ
      Treal vreal hAreal hlawQ3 x
    have hpow := modelCovarianceTrace_rpow hAreal Treal Φ hΦderiv hΦ0
      (p := 20) (by norm_num : (2 : ℝ) ≤ 20) x
    calc
      modelPowerHeatGenerator Φ H 20 x =
          modelPowerHeatGenerator Φ (fun j => Treal (vreal j)) 20 x := by
        simpa [Φ, H] using hmodel.symm
      _ = (1 / 2 : ℝ) * C x := by
        simpa only [C, Hreal, Ψ] using hpow.symm
  have hpoint (ω : CutoffSample 2) :
      modelPowerHeatGenerator Φ H 20 (X ω + Real.sqrt t • Y ω) =
        (1 / 2 : ℝ) * C (X ω + Real.sqrt t • Y ω) :=
    hgenEq (X ω + Real.sqrt t • Y ω)
  calc
    _ = ∫ ω, (1 / 2 : ℝ) * C (X ω + Real.sqrt t • Y ω) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (1 / 2 : ℝ) * ∫ ω, C (X ω + Real.sqrt t • Y ω) ∂μ := by
      rw [integral_const_mul]
    _ = (1 / 2 : ℝ) * ∫ p : C(K, ℝ) × (ℕ → ℝ),
          C (p.1 + Real.sqrt t • gaussianSeriesLimitE hAreal Treal p.2)
          ∂((μ.map X).prod standardGaussianInfinitePi) := by
      rw [hins.2]
    _ = _ := by
      simpa [μ, X, Ψ] using congrArg (fun z => (1 / 2 : ℝ) * z) hprod

private theorem raw_shell_band_profile_succ_scalar
    (M : ABKModel 2) (n : ℤ) (i : ℕ) (weights : ℤ → ℝ)
    (ω : CutoffSample 2) :
    rawShellBandScalarFromWeights M n (i + 1) weights ω =
      rawShellBandScalarFromWeights M n i weights ω +
        weights (n + (i : ℤ) + 1) •
          shellFieldScalarRestriction (closure (cubeSet (originCube 2 n)))
            (ω.1 (n + (i : ℤ) + 1)) := by
  classical
  let W := rawShellBandStepWeights n i weights 1
  have hW (k : ℤ) (hk : k ∈ Finset.Ioc n (n + ((i + 1 : ℕ) : ℤ))) :
      W k = weights k := by
    by_cases htop : k = n + (i : ℤ) + 1
    · subst k
      simp [W, rawShellBandStepWeights, Real.sqrt_one]
    · have hprev : k ∈ Finset.Ioc n (n + (i : ℤ)) := by
        simp only [Finset.mem_Ioc] at hk ⊢
        omega
      simp [W, rawShellBandStepWeights, htop, hprev]
  have hprofile : rawShellBandScalarFromWeights M n (i + 1) W ω =
      rawShellBandScalarFromWeights M n (i + 1) weights ω := by
    ext x
    simp only [rawShellBandScalarFromWeights, ContinuousMap.add_apply,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hW k hk]
  calc
    rawShellBandScalarFromWeights M n (i + 1) weights ω =
        rawShellBandScalarFromWeights M n (i + 1) W ω := hprofile.symm
    _ = rawShellBandScalarFromWeights M n i weights ω +
        (Real.sqrt (1 : ℝ) * weights (n + (i : ℤ) + 1)) •
          shellFieldScalarRestriction (closure (cubeSet (originCube 2 n)))
            (ω.1 (n + (i : ℤ) + 1)) := by
      exact raw_shell_band_step_scalar_eq M n i weights 1 ω
    _ = _ := by simp [Real.sqrt_one]

private theorem raw_shell_band_step_generator_integral_eq
    (M : ABKModel 2) (n : ℤ) (i : ℕ) (weights : ℤ → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hweight : 0 ≤ weights (n + (i : ℤ) + 1))
    (Φ : C(closure (cubeSet (originCube 2 n)), ℝ) → ℝ)
    (H : ℕ → C(closure (cubeSet (originCube 2 n)), ℝ)) :
    (∫ ω : CutoffSample 2,
      modelPowerHeatGenerator Φ H 20
        (rawShellBandScalarFromWeights M n (i + 1)
          (rawShellBandStepWeights n i weights t) ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω : CutoffSample 2,
        modelPowerHeatGenerator Φ H 20
          (rawShellBandScalarFromWeights M n i weights ω +
            Real.sqrt (t * weights (n + (i : ℤ) + 1) ^ 2) •
              shellFieldScalarRestriction (closure (cubeSet (originCube 2 n)))
                (ω.1 (n + (i : ℤ) + 1)))
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    have hsqrt : Real.sqrt (t * weights (n + (i : ℤ) + 1) ^ 2) =
        Real.sqrt t * weights (n + (i : ℤ) + 1) := by
      rw [Real.sqrt_mul ht, Real.sqrt_sq_eq_abs,
        abs_of_nonneg hweight]
    have harg := raw_shell_band_step_scalar_eq M n i weights t ω
    rw [← hsqrt] at harg
    exact congrArg (modelPowerHeatGenerator Φ H 20) harg


/-- The variance, sharp shear coefficients, and exact source mass of the
`i`th coordinate step in a fixed completed frame. -/
noncomputable def rawShellBandStepVariance (M : ABKModel 2) (h : ℝ)
    (n : ℤ) (i : ℕ) : ℝ :=
  (q3ModelAmplitude M h (n + ((i + 1 : ℕ) : ℤ))) ^ 2 /
    (Annealed.sigmaBar M n : ℝ) ^ 2

noncomputable def rawShellBandStepKappa (n : ℤ) (i : ℕ) : ℝ :=
  lemmaVH2kn
    (cubeScaleFactor (originCube 2 n) /
      (q3ModelLength (n + ((i + 1 : ℕ) : ℤ))).1)
    (diagMeshRadius (originCube 2 n) (pureFluxBankSourceDepth (i + 1)) /
      (q3ModelLength (n + ((i + 1 : ℕ) : ℤ))).1)

noncomputable def rawShellBandStepKappaB (n : ℤ) (i : ℕ) : ℝ :=
  lemmaVH2Bn
    (cubeScaleFactor (originCube 2 n) /
      (q3ModelLength (n + ((i + 1 : ℕ) : ℤ))).1)
    (diagMeshRadius (originCube 2 n) (pureFluxBankSourceDepth (i + 1)) /
      (q3ModelLength (n + ((i + 1 : ℕ) : ℤ))).1)

noncomputable def rawShellBandStepMu (i : ℕ) : ℝ :=
  pureFluxCovarianceMu (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i)

noncomputable def rawShellBandStepCoefficient (M : ABKModel 2) (h : ℝ)
    (n : ℤ) (N i : ℕ) : ℝ :=
  let v := rawShellBandStepVariance M h n i
  let κ := rawShellBandStepKappa n i
  let κB := rawShellBandStepKappaB n i
  let μR := rawShellBandStepMu i
  let b := (3683 / 2500 : ℝ)
  let f := rawTraceFullResponseCap M.gamma N
  v * ((78 + 76 * κ) * b + 2 * κ * b * f +
    (μR + 38 * (κB ^ 2 + κ)) * b ^ 2 * f)

/-- One weighted coordinate step obeys the actual p=20 root increment bound.
The heat parameter is rescaled by the squared deterministic weight; its
chain-rule factor is at most one. -/
theorem raw_shell_band_step_root_increment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (N i : ℕ) (hi : i < N)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (N : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1)
    (hpastLocal : ∀ j < n, nativeInductionState M h j)
    (hpastFull : ∀ j ≤ n + (N : ℤ) - 303, nativeInductionState M h j) :
    (rawShellBandP20Moment M n (i + 1) weights) ^ ((20 : ℝ)⁻¹) -
      (rawShellBandP20Moment M n i weights) ^ ((20 : ℝ)⁻¹) ≤
        rawShellBandStepCoefficient M h n N i := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M n
  let Φ : C(K, ℝ) → ℝ := modelTraceObservable n M.nu σ
  let Ψ : C(K, ℝ) → ℝ := fun x => Φ x ^ (20 : ℝ)
  let X := rawShellBandScalarFromWeights M n i weights
  let wi := weights (n + (i : ℤ) + 1)
  let J := n + ((i + 1 : ℕ) : ℤ)
  let H := pureFluxMainCubeQ3Directions n
    (q3ModelAmplitude M h J) (q3ModelLength J)
  have hbandTop : n + (i : ℤ) + 1 ∈ Finset.Ioc n (n + (N : ℤ)) := by
    simp only [Finset.mem_Ioc]
    omega
  have hwi := hw (n + (i : ℤ) + 1) hbandTop
  have hwiSq0 : 0 ≤ wi ^ 2 := sq_nonneg wi
  have hwiSq1 : wi ^ 2 ≤ 1 := by nlinarith [hwi.1, hwi.2]
  have hprefix : ∀ k ∈ Finset.Ioc n (n + (i : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1 := by
    intro k hk
    apply hw k
    simp only [Finset.mem_Ioc] at hk ⊢
    omega
  have hν : 0 < M.nu := M.nu_pos
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hΦderiv : HasPolynomiallyBoundedC2Derivatives Φ :=
    modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu σ hν hσ
  have hΦ0 : ∀ x, 0 ≤ Φ x := modelTraceObservable_nonneg n M.nu σ hν hσ
  have hΨderiv := hasPolynomiallyBoundedC2Derivatives_rpow hΦderiv hΦ0
    (by norm_num : (2 : ℝ) ≤ 20)
  have hΨmeas : Measurable Ψ := hΨderiv.1.continuous.measurable
  have hΨgrowth : HasPolynomialGrowth Ψ := by
    rcases hΨderiv with ⟨_, C, hC, d, hvalue, _, _⟩
    exact ⟨C, hC, d, hvalue⟩
  obtain ⟨Treal, vreal, hAreal, hlaw, htransfer⟩ :=
    raw_shell_band_prefix_heat_transfer M h hM n i weights hprefix
      Ψ hΨmeas hΨgrowth
  let moment : ℝ → ℝ :=
    randomBaseHeatAverage hAreal Treal (μ.map X) Ψ ∘ (fun t : ℝ => t * wi ^ 2)
  have hMom := raw_shell_weighted_prefix_polynomial_moments M n i weights hprefix
  have hheat := c1On_randomBaseHeatAverage hAreal Treal (μ.map X) hMom Ψ hΨderiv
  have hmoment_cont : ContinuousOn moment (Icc (0 : ℝ) 1) := by
    have harg : ContinuousOn (fun t : ℝ => t * wi ^ 2) (Icc (0 : ℝ) 1) :=
      (continuous_id.mul continuous_const).continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => t * wi ^ 2)
        (Icc (0 : ℝ) 1) (Ici (0 : ℝ)) := by
      intro t ht
      exact mul_nonneg ht.1 hwiSq0
    exact hheat.1.comp harg hmaps
  have hmomentEq (t : ℝ) (ht : 0 ≤ t) :
      moment t = rawShellBandP20Moment M n (i + 1)
        (rawShellBandStepWeights n i weights t) := by
    have htrans := htransfer (t * wi ^ 2)
    have hsqrt : Real.sqrt (t * wi ^ 2) = Real.sqrt t * wi := by
      rw [Real.sqrt_mul ht, Real.sqrt_sq_eq_abs, abs_of_nonneg hwi.1]
    have harg (ω : CutoffSample 2) :
        rawShellBandScalarFromWeights M n (i + 1)
            (rawShellBandStepWeights n i weights t) ω =
          X ω + Real.sqrt (t * wi ^ 2) •
            shellFieldScalarRestriction K (ω.1 (n + (i : ℤ) + 1)) := by
      rw [raw_shell_band_step_scalar_eq]
      simp only [X]
      rw [← hsqrt]
    calc
      moment t = randomBaseHeatAverage hAreal Treal (μ.map X) Ψ (t * wi ^ 2) := rfl
      _ = rawShellBandPrefixHeatAverage M n i weights Ψ (t * wi ^ 2) := (htrans).symm
      _ = ∫ ω, Ψ (X ω + Real.sqrt (t * wi ^ 2) •
            shellFieldScalarRestriction K (ω.1 (n + (i : ℤ) + 1))) ∂μ := rfl
      _ = ∫ ω, Ψ (rawShellBandScalarFromWeights M n (i + 1)
            (rawShellBandStepWeights n i weights t) ω) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => congrArg Ψ (harg ω).symm
      _ = rawShellBandP20Moment M n (i + 1)
            (rawShellBandStepWeights n i weights t) := by
        unfold rawShellBandP20Moment
        rfl
  have hmoment0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ moment t := by
    intro t ht
    rw [hmomentEq t ht.1]
    unfold rawShellBandP20Moment
    apply integral_nonneg
    intro ω
    exact Real.rpow_nonneg (hΦ0 _) _
  have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hf : 0 ≤ rawTraceFullResponseCap M.gamma N := by
    unfold rawTraceFullResponseCap
    positivity
  have hcoeff_nonneg : 0 ≤ rawShellBandStepCoefficient M h n N i := by
    dsimp [rawShellBandStepCoefficient, rawShellBandStepVariance,
      rawShellBandStepKappa, rawShellBandStepKappaB, rawShellBandStepMu]
    have hv : 0 ≤ (q3ModelAmplitude M h (n + ((i + 1 : ℕ) : ℤ))) ^ 2 /
        (Annealed.sigmaBar M n : ℝ) ^ 2 := by positivity
    have hκ : 0 ≤ lemmaVH2kn
        (cubeScaleFactor (originCube 2 n) /
          (q3ModelLength (n + ((i + 1 : ℕ) : ℤ))).1)
        (diagMeshRadius (originCube 2 n) (pureFluxBankSourceDepth (i + 1)) /
          (q3ModelLength (n + ((i + 1 : ℕ) : ℤ))).1) := by
      have hρ : 0 ≤ cubeScaleFactor (originCube 2 n) /
          (q3ModelLength J).1 :=
        div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' (originCube 2 n)).le
          (q3ModelLength J).2.le
      have hδ : 0 ≤ diagMeshRadius (originCube 2 n) (pureFluxBankSourceDepth (i + 1)) /
          (q3ModelLength J).1 :=
        div_nonneg (diagMeshRadius_pos (originCube 2 n)
          (pureFluxBankSourceDepth (i + 1))).le (q3ModelLength J).2.le
      unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
      positivity
    have hκB : 0 ≤ lemmaVH2Bn
        (cubeScaleFactor (originCube 2 n) /
          (q3ModelLength (n + ((i + 1 : ℕ) : ℤ))).1)
        (diagMeshRadius (originCube 2 n) (pureFluxBankSourceDepth (i + 1)) /
          (q3ModelLength (n + ((i + 1 : ℕ) : ℤ))).1) := by
      have hρ : 0 ≤ cubeScaleFactor (originCube 2 n) /
          (q3ModelLength J).1 :=
        div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' (originCube 2 n)).le
          (q3ModelLength J).2.le
      have hδ : 0 ≤ diagMeshRadius (originCube 2 n) (pureFluxBankSourceDepth (i + 1)) /
          (q3ModelLength J).1 :=
        div_nonneg (diagMeshRadius_pos (originCube 2 n)
          (pureFluxBankSourceDepth (i + 1))).le (q3ModelLength J).2.le
      unfold lemmaVH2Bn lemmaVH2R1 lemmaVH2A2 lemmaVH2C1 lemmaVH2C2
      positivity
    have hμ : 0 ≤ pureFluxCovarianceMu
        (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i) :=
      (pureFlux_covariance_mu_lower _ _).1
    positivity
  have hderiv_heat : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt moment (deriv moment t) t ∧
        deriv moment t ≤
          20 * moment t ^ ((19 : ℝ) / 20) *
            rawShellBandStepCoefficient M h n N i := by
    intro t ht
    by_cases hwi0 : wi = 0
    · have heq : moment = fun _ : ℝ =>
          randomBaseHeatAverage hAreal Treal (μ.map X) Ψ 0 := by
        funext u
        simp [moment, hwi0]
      have hderiv0 : deriv moment t = 0 := by
        rw [heq]
        simp
      constructor
      · rw [heq]
        simpa [heq] using hasDerivAt_const t
          (randomBaseHeatAverage hAreal Treal (μ.map X) Ψ 0)
      · rw [hderiv0]
        have hmt : 0 ≤ moment t := hmoment0 t ⟨ht.1.le, ht.2.le⟩
        have hpow : 0 ≤ moment t ^ ((19 : ℝ) / 20) :=
          Real.rpow_nonneg hmt _
        positivity
    · have hwiPos : 0 < wi := lt_of_le_of_ne hwi.1 (Ne.symm hwi0)
      have hu : 0 < t * wi ^ 2 := mul_pos ht.1 (sq_pos_of_pos hwiPos)
      have hargDeriv : HasDerivAt (fun u : ℝ => u * wi ^ 2) (wi ^ 2) t := by
        simpa only [id_eq, one_mul] using (hasDerivAt_id t).mul_const (wi ^ 2)
      have hchain := (hheat.2.2.1 (t * wi ^ 2) hu).comp t hargDeriv
      have hchain' : HasDerivAt moment
          (wi ^ 2 * ((1 / 2 : ℝ) *
            randomBaseHeatTraceAverage hAreal Treal (μ.map X) Ψ (t * wi ^ 2))) t := by
        have hchain'' : HasDerivAt moment
            (((1 / 2 : ℝ) * randomBaseHeatTraceAverage hAreal Treal
              (μ.map X) Ψ (t * wi ^ 2)) * wi ^ 2) t := by
          simpa only [moment] using hchain
        exact hchain''.congr_deriv (by ring)
      have htrace := raw_shell_band_power_generator_eq_heat_trace
        M h hM n i weights hprefix Treal vreal hAreal hlaw
        (t * wi ^ 2)
      have hgenEq :
          (∫ ω, modelPowerHeatGenerator Φ
          H 20
              (X ω + Real.sqrt (t * wi ^ 2) •
                shellFieldScalarRestriction K (ω.1 (n + (i : ℤ) + 1))) ∂μ) =
            (1 / 2 : ℝ) * randomBaseHeatTraceAverage hAreal Treal
              (μ.map X) Ψ (t * wi ^ 2) := htrace
      have hrow := raw_shell_band_step_p20_generator_integral_bank_row
        M h hM hg n N i hi weights hw hpastLocal hpastFull t ⟨ht.1.le, ht.2.le⟩
      have hrowPower :
          (∫ ω, modelPowerHeatGenerator Φ
            H 20
              (rawShellBandScalarFromWeights M n (i + 1)
                (rawShellBandStepWeights n i weights t) ω) ∂μ) ≤
            20 * moment t ^ ((19 : ℝ) / 20) *
              rawShellBandStepCoefficient M h n N i := by
        rw [hmomentEq t ht.1.le]
        dsimp only [modelPowerHeatGenerator, Φ, H, μ, σ, J]
        have hrow' := hrow
        dsimp only [] at hrow'
        have hpow19 : (20 : ℝ) - 1 = 19 := by norm_num
        have hpow18 : (20 : ℝ) - 2 = 18 := by norm_num
        simp only [hpow19, hpow18]
        have hnum : (20 : ℝ) * 19 / 2 = 190 := by norm_num
        rw [hnum]
        simpa [rawShellBandStepCoefficient, rawShellBandStepVariance,
          rawShellBandStepKappa, rawShellBandStepKappaB, rawShellBandStepMu,
          rawShellBandP20Moment] using hrow'
      have hstepGenEq :=
        (raw_shell_band_step_generator_integral_eq M n i weights t ht.1.le hwi.1 Φ H).symm
      have hGenUpper :
          (∫ ω, modelPowerHeatGenerator Φ H 20
            (X ω + Real.sqrt (t * wi ^ 2) •
              shellFieldScalarRestriction K (ω.1 (n + (i : ℤ) + 1))) ∂μ) ≤
            20 * moment t ^ ((19 : ℝ) / 20) *
              rawShellBandStepCoefficient M h n N i := by
        rw [hstepGenEq]
        exact hrowPower
      have hGnonpos_or_pos := le_total 0
        (∫ ω, modelPowerHeatGenerator Φ
          H 20
            (X ω + Real.sqrt (t * wi ^ 2) •
              shellFieldScalarRestriction K (ω.1 (n + (i : ℤ) + 1))) ∂μ)
      have hscaled : wi ^ 2 *
          (∫ ω, modelPowerHeatGenerator Φ
              H 20
              (X ω + Real.sqrt (t * wi ^ 2) •
                shellFieldScalarRestriction K (ω.1 (n + (i : ℤ) + 1))) ∂μ) ≤
            20 * moment t ^ ((19 : ℝ) / 20) *
              rawShellBandStepCoefficient M h n N i := by
        rcases hGnonpos_or_pos with hG | hG
        · calc
            wi ^ 2 *
                (∫ ω, modelPowerHeatGenerator Φ
                  H 20
                    (X ω + Real.sqrt (t * wi ^ 2) •
                      shellFieldScalarRestriction K (ω.1 (n + (i : ℤ) + 1))) ∂μ) ≤
                1 * (∫ ω, modelPowerHeatGenerator Φ
                  H 20
                    (X ω + Real.sqrt (t * wi ^ 2) •
                      shellFieldScalarRestriction K (ω.1 (n + (i : ℤ) + 1))) ∂μ) := by
              exact mul_le_mul_of_nonneg_right hwiSq1 hG
            _ = ∫ ω, modelPowerHeatGenerator Φ
                  H 20
                    (X ω + Real.sqrt (t * wi ^ 2) •
                      shellFieldScalarRestriction K (ω.1 (n + (i : ℤ) + 1))) ∂μ := by ring
            _ ≤ 20 * moment t ^ ((19 : ℝ) / 20) *
                  rawShellBandStepCoefficient M h n N i := hGenUpper
        · have hleft : wi ^ 2 *
              (∫ ω, modelPowerHeatGenerator Φ
                H 20
                  (X ω + Real.sqrt (t * wi ^ 2) •
                    shellFieldScalarRestriction K (ω.1 (n + (i : ℤ) + 1))) ∂μ) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hwiSq0 hG
          have hmt : 0 ≤ moment t :=
            hmoment0 t ⟨ht.1.le, ht.2.le⟩
          have hright : 0 ≤ 20 * moment t ^ ((19 : ℝ) / 20) *
              rawShellBandStepCoefficient M h n N i := by positivity
          linarith
      have hderivEq := hchain'.deriv
      have hchainFinal : HasDerivAt moment (deriv moment t) t :=
        hchain'.congr_deriv hderivEq.symm
      have hbound : deriv moment t ≤
          20 * moment t ^ ((19 : ℝ) / 20) *
            rawShellBandStepCoefficient M h n N i := by
        rw [hderivEq, ← htrace]
        exact hscaled
      exact ⟨hchainFinal, hbound⟩
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt moment (deriv moment t) t :=
    fun t ht => (hderiv_heat t ht).1
  have hheatBound : ∀ t ∈ Ioo (0 : ℝ) 1,
      deriv moment t ≤ 20 * moment t ^ ((19 : ℝ) / 20) *
        rawShellBandStepCoefficient M h n N i :=
    fun t ht => (hderiv_heat t ht).2
  have hU0 : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ rawShellBandStepCoefficient M h n N i :=
    fun _ _ => hcoeff_nonneg
  have hUInt : IntegrableOn (fun _ : ℝ => rawShellBandStepCoefficient M h n N i)
      (Icc (0 : ℝ) 1) := by
    exact integrableOn_const (C := rawShellBandStepCoefficient M h n N i) (by
      rw [Real.volume_Icc]
      norm_num)
  have hroot := raw_p20_moment_root_sub_le_integral
    (f := moment) (df := fun t => deriv moment t)
    (U := fun _ => rawShellBandStepCoefficient M h n N i)
    hmoment_cont hmoment0 hderiv hU0 hUInt hheatBound (s := 0) (t := 1)
    (by norm_num) (by norm_num) (by norm_num)
  have hstep0 : rawShellBandScalarFromWeights M n (i + 1)
      (rawShellBandStepWeights n i weights 0) =
      rawShellBandScalarFromWeights M n i weights := by
    funext ω
    ext x
    rw [raw_shell_band_step_scalar_eq]
    simp [Real.sqrt_zero]
  have hstart : moment 0 = rawShellBandP20Moment M n i weights := by
    rw [hmomentEq 0 (by norm_num)]
    unfold rawShellBandP20Moment
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by rw [hstep0]
  have hend : moment 1 = rawShellBandP20Moment M n (i + 1) weights := by
    rw [hmomentEq 1 (by norm_num)]
    unfold rawShellBandP20Moment
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      change (modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
          (rawShellBandScalarFromWeights M n (i + 1)
            (rawShellBandStepWeights n i weights 1) ω)) ^ (20 : ℝ) =
        (modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
          (rawShellBandScalarFromWeights M n (i + 1) weights ω)) ^ (20 : ℝ)
      have hprofile : rawShellBandScalarFromWeights M n (i + 1)
          (rawShellBandStepWeights n i weights 1) ω =
          rawShellBandScalarFromWeights M n (i + 1) weights ω := by
        calc
          _ = rawShellBandScalarFromWeights M n i weights ω +
              (Real.sqrt 1 * weights (n + (i : ℤ) + 1)) •
                shellFieldScalarRestriction (closure (cubeSet (originCube 2 n)))
                  (ω.1 (n + (i : ℤ) + 1)) :=
            raw_shell_band_step_scalar_eq M n i weights 1 ω
          _ = rawShellBandScalarFromWeights M n i weights ω +
              weights (n + (i : ℤ) + 1) •
                shellFieldScalarRestriction (closure (cubeSet (originCube 2 n)))
                  (ω.1 (n + (i : ℤ) + 1)) := by simp
          _ = rawShellBandScalarFromWeights M n (i + 1) weights ω :=
            (raw_shell_band_profile_succ_scalar M n i weights ω).symm
      rw [hprofile]
  rw [hend, hstart] at hroot
  simpa only [show (∫ t in (0 : ℝ)..1,
      rawShellBandStepCoefficient M h n N i) =
        rawShellBandStepCoefficient M h n N i by simp] using hroot

private theorem raw_shell_band_step_kappa_eq_source (n : ℤ) (i : ℕ) :
    rawShellBandStepKappa n i =
      lemmaVH2kn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i) := by
  unfold rawShellBandStepKappa
  rw [pureFlux_bank_source_rho n (i + 1) (by omega),
    pureFlux_bank_source_delta n (i + 1) (by omega)]
  simp

private theorem raw_shell_band_step_kappaB_eq_source (n : ℤ) (i : ℕ) :
    rawShellBandStepKappaB n i =
      pureFluxCovarianceB 0 i := by
  unfold rawShellBandStepKappaB
  rw [pureFlux_bank_source_rho n (i + 1) (by omega),
    pureFlux_bank_source_delta n (i + 1) (by omega)]
  exact source_lemmaV_B_eq_covariance_B i

private theorem raw_shell_band_root_increment_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (N : ℕ)
    (hstate : nativeInductionState M h n)
    (hpastLocal : ∀ j < n, nativeInductionState M h j)
    (hpastFull : ∀ j ≤ n + (N : ℤ) - 303, nativeInductionState M h j)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (N : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1) :
    (rawShellBandP20Moment M n N weights) ^ ((20 : ℝ)⁻¹) -
        (rawShellBandP20Moment M n 0 weights) ^ ((20 : ℝ)⁻¹) ≤
      ((9 / 2 : ℝ) * M.gamma * 3 ^ (2 * M.gamma * (N : ℝ))) *
        (((78 * (N : ℝ) + 76 * (521 / 1000 : ℝ)) * (3683 / 2500 : ℝ)) +
          2 * (521 / 1000 : ℝ) * (3683 / 2500 : ℝ) *
            rawTraceFullResponseCap M.gamma N +
          ((1975 / 1000 : ℝ) + 38 * (1565 / 1000 : ℝ)) *
            (3683 / 2500 : ℝ) ^ 2 * rawTraceFullResponseCap M.gamma N) := by
  classical
  let e : ℝ := (9 / 2 : ℝ) * M.gamma * 3 ^ (2 * M.gamma * (N : ℝ))
  let b : ℝ := 3683 / 2500
  let f : ℝ := rawTraceFullResponseCap M.gamma N
  let v : ℕ → ℝ := rawShellBandStepVariance M h n
  let κ : ℕ → ℝ := rawShellBandStepKappa n
  let κB : ℕ → ℝ := rawShellBandStepKappaB n
  let μR : ℕ → ℝ := fun i => v i * rawShellBandStepMu i
  let q : ℕ → ℝ := fun i => κB i ^ 2 + κ i
  let d : ℕ → ℝ := rawShellBandStepCoefficient M h n N
  have he : e = nativeSourceShellClock M.gamma N := by
    simp [e, ASDExplicitGamma.Native.nativeSourceShellClock]
  have he0 : 0 ≤ e := by
    rw [he]
    dsimp [ASDExplicitGamma.Native.nativeSourceShellClock]
    have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
    exact mul_nonneg (mul_nonneg (by norm_num) hγ)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
  have hf : 0 ≤ f := by
    dsimp [f]
    unfold rawTraceFullResponseCap
    have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
    apply mul_nonneg
    · apply mul_nonneg (by norm_num)
      exact add_nonneg (by norm_num) (mul_nonneg hγ (by positivity))
    · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hv (i : ℕ) (hi : i ∈ Finset.range N) : v i ≤ e := by
    rw [he]
    exact native_source_shell_variance_le_clock M h n N (i + 1) hstate (by
      have hi' := Finset.mem_range.mp hi
      omega)
  have hcov := source_covariance_weighted_partial_sums (Finset.range N) v e he0 hv
  have hV : ∑ i ∈ Finset.range N, v i ≤ (N : ℝ) * e := by
    calc
      _ ≤ ∑ _i ∈ Finset.range N, e := Finset.sum_le_sum fun i hi => hv i hi
      _ = (N : ℝ) * e := by simp
  have hK : ∑ i ∈ Finset.range N, v i * κ i ≤ (521 / 1000 : ℝ) * e := by
    simpa only [v, κ, rawShellBandStepVariance,
      raw_shell_band_step_kappa_eq_source] using hcov.1
  have hMu : ∑ i ∈ Finset.range N, μR i ≤ (1975 / 1000 : ℝ) * e := by
    simpa only [v, μR, rawShellBandStepVariance, rawShellBandStepMu] using hcov.2.1
  have hQ : ∑ i ∈ Finset.range N, v i * q i ≤ (1565 / 1000 : ℝ) * e := by
    simpa only [v, q, κ, κB, rawShellBandStepVariance,
      rawShellBandStepKappa, rawShellBandStepKappaB,
      raw_shell_band_step_kappa_eq_source,
      raw_shell_band_step_kappaB_eq_source] using hcov.2.2
  have hcoeff (i : ℕ) (hi : i ∈ Finset.range N) :
      d i ≤ v i * (78 * b) + (v i * κ i) * (76 * b + 2 * b * f) +
        μR i * (b ^ 2 * f) + (v i * q i) * (38 * b ^ 2 * f) := by
    dsimp [d, rawShellBandStepCoefficient, v, κ, κB, μR, q, b, f,
      rawShellBandStepVariance, rawShellBandStepKappa,
      rawShellBandStepKappaB, rawShellBandStepMu]
    apply le_of_eq
    ring
  have hroot :
      (∑ i ∈ Finset.range N,
        ((rawShellBandP20Moment M n (i + 1) weights) ^ ((20 : ℝ)⁻¹) -
          (rawShellBandP20Moment M n i weights) ^ ((20 : ℝ)⁻¹))) ≤
        ∑ i ∈ Finset.range N, d i := by
    apply Finset.sum_le_sum
    intro i hi
    exact raw_shell_band_step_root_increment M h hM hg n N i
      (by have hi' := Finset.mem_range.mp hi; omega) weights hw hpastLocal hpastFull
  have htelescope (r : ℕ) :
      ∑ i ∈ Finset.range r,
        ((rawShellBandP20Moment M n (i + 1) weights) ^ ((20 : ℝ)⁻¹) -
          (rawShellBandP20Moment M n i weights) ^ ((20 : ℝ)⁻¹)) =
        (rawShellBandP20Moment M n r weights) ^ ((20 : ℝ)⁻¹) -
          (rawShellBandP20Moment M n 0 weights) ^ ((20 : ℝ)⁻¹) := by
    induction r with
    | zero => simp
    | succ r ihr =>
        rw [Finset.sum_range_succ, ihr]
        ring
  have hsum := raw_trace_p20_shell_sum_budget N e b f v κ μR q d
    (by norm_num [b]) hf hV hK hMu hQ (by
      intro i hi
      have hrow := hcoeff i hi
      simpa only [d, v, κ, μR, q, b, f, Finset.mem_range] using hrow)
  rw [htelescope N] at hroot
  simpa [e, b, f] using hroot.trans hsum

private theorem raw_shell_band_trace_memLp20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (N : ℕ) (hN : 1 ≤ N)
    (hpastFull : ∀ j ≤ n + (N : ℤ) - 303, nativeInductionState M h j)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (N : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1) :
    let T := fun ω : CutoffSample 2 =>
      modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
        (rawShellBandScalarFromWeights M n N weights ω)
    AEStronglyMeasurable T ((Cutoff.cutoffSampleLaw M).toMeasure) ∧
      MemLp T (ENNReal.ofReal 20) ((Cutoff.cutoffSampleLaw M).toMeasure) := by
  classical
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let K := closure (cubeSet (originCube 2 n))
  let T : CutoffSample 2 → ℝ := fun ω =>
    modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
      (rawShellBandScalarFromWeights M n N weights ω)
  let F : CutoffSample 2 → ℝ := fun ω => T ω + 4
  have hT0 (ω : CutoffSample 2) : 0 ≤ T ω :=
    modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n : ℝ)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1 _
  have hF0 (ω : CutoffSample 2) : 0 ≤ F ω := add_nonneg (hT0 ω) (by norm_num)
  have hcap := raw_shell_weighted_full_response_L128 M h hM hg n N weights hw hpastFull
  let W := rawShellBandStepWeights n (N - 1) weights 1
  have hW (k : ℤ) (hk : k ∈ Finset.Ioc n (n + (N : ℤ))) : W k = weights k := by
    by_cases htop : k = n + ((N - 1 : ℕ) : ℤ) + 1
    · subst k
      simp [W, rawShellBandStepWeights, Real.sqrt_one]
    · have hprev : k ∈ Finset.Ioc n (n + ((N - 1 : ℕ) : ℤ)) := by
        simp only [Finset.mem_Ioc] at hk ⊢
        omega
      simp [W, rawShellBandStepWeights, htop, hprev]
  have hcoef : attenuatedCoefficient M n (n + (N : ℤ)) W =
      attenuatedCoefficient M n (n + (N : ℤ)) weights := by
    funext ω x a b
    simp only [attenuatedCoefficient, Matrix.add_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hW k hk]
  have hFcap : eLpNorm F (ENNReal.ofReal 128) μ ≤
      ENNReal.ofReal (rawTraceFullResponseCap M.gamma N) := by
    have hEq (ω : CutoffSample 2) :
        rootTraceObservable M (originCube 2 n) n (n + (N : ℤ)) n weights ω = F ω := by
      have hstep := raw_shell_band_step_trace_eq M n N (N - 1)
        (by omega) weights 1 ω
      unfold rootTraceObservable at hstep ⊢
      rw [← hcoef]
      have hNcast : (N - 1 + 1 : ℕ) = N := Nat.sub_add_cancel hN
      rw [hNcast] at hstep
      have hprof : rawShellBandScalarFromWeights M n N W ω =
          rawShellBandScalarFromWeights M n N weights ω := by
        unfold rawShellBandScalarFromWeights
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [hW k hk]
      have hprof' : rawShellBandScalarFromWeights M n N
          (rawShellBandStepWeights n (N - 1) weights 1) ω =
          rawShellBandScalarFromWeights M n N weights ω := by
        simpa only [W] using hprof
      rw [hprof'] at hstep
      simpa [F, T] using hstep
    have hEqFun :
        rootTraceObservable M (originCube 2 n) n (n + (N : ℤ)) n weights = F :=
      funext hEq
    rw [← hEqFun]
    exact hcap
  have hFtop : eLpNorm F (ENNReal.ofReal 128) μ < ⊤ :=
    hFcap.trans_lt ENNReal.ofReal_lt_top
  have hFm : AEStronglyMeasurable F μ := aestronglyMeasurable_of_eLpNorm_ne_top hFtop.ne
  have hTm : AEStronglyMeasurable T μ := by
    have hsub : AEStronglyMeasurable (fun ω => F ω - 4) μ :=
      hFm.sub (aestronglyMeasurable_const (b := (4 : ℝ)))
    have heq : (fun ω => F ω - 4) = T := by
      funext ω
      dsimp [F]
      ring
    rw [heq] at hsub
    exact hsub
  have hcmp : eLpNorm T (ENNReal.ofReal 20) μ ≤ eLpNorm F (ENNReal.ofReal 20) μ := by
    apply eLpNorm_mono_ae hTm
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (hT0 ω), Real.norm_of_nonneg (hF0 ω)]
    dsimp [F]
    linarith
  have hmono := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := F) (μ := μ)
    (show ENNReal.ofReal (20 : ℝ) ≤ ENNReal.ofReal (128 : ℝ) by norm_num) hFm
  have hF20 : eLpNorm F (ENNReal.ofReal 20) μ ≤
      eLpNorm F (ENNReal.ofReal 128) μ := by
    simpa only [measure_univ, ENNReal.one_rpow, mul_one] using hmono
  have hmem : MemLp T (ENNReal.ofReal 20) μ :=
    memLp_iff.mpr (hcmp.trans_lt (hF20.trans_lt hFtop))
  exact ⟨hTm, hmem⟩

/-- The finite weighted-band theorem on the actual cutoff law. The
local past and full-response state ranges are exactly the inputs used by the
two source banks; no bank-norm cap is an extra premise. -/
theorem raw_shell_band_transport_p20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (N : ℕ) (hN : 1 ≤ N)
    (hstate : nativeInductionState M h n)
    (hpastLocal : ∀ j < n, nativeInductionState M h j)
    (hpastFull : ∀ j ≤ n + (N : ℤ) - 303, nativeInductionState M h j)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (N : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let T_N := fun ω : CutoffSample 2 =>
      modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
        (rawShellBandScalarFromWeights M n N weights ω)
    let T_0 := fun ω : CutoffSample 2 =>
      modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
        (olderField (closure (cubeSet (originCube 2 n))) n ω)
    eLpNorm T_N (ENNReal.ofReal 20) μ ≤
        eLpNorm T_0 (ENNReal.ofReal 20) μ + ENNReal.ofReal (
          ((9 / 2 : ℝ) * M.gamma * 3 ^ (2 * M.gamma * (N : ℝ))) *
            (((78 * (N : ℝ) + 76 * (521 / 1000 : ℝ)) * (3683 / 2500 : ℝ)) +
              2 * (521 / 1000 : ℝ) * (3683 / 2500 : ℝ) *
                rawTraceFullResponseCap M.gamma N +
              ((1975 / 1000 : ℝ) + 38 * (1565 / 1000 : ℝ)) *
                (3683 / 2500 : ℝ) ^ 2 * rawTraceFullResponseCap M.gamma N)) ∧
      eLpNorm T_0 (ENNReal.ofReal 20) μ ≤
        ENNReal.ofReal ((21 / 100 : ℝ) * (M.gamma / gammaZero)) := by
  classical
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let T_N : CutoffSample 2 → ℝ := fun ω =>
    modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
      (rawShellBandScalarFromWeights M n N weights ω)
  let T_0 : CutoffSample 2 → ℝ := fun ω =>
    modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
      (olderField (closure (cubeSet (originCube 2 n))) n ω)
  let rN := (rawShellBandP20Moment M n N weights) ^ ((20 : ℝ)⁻¹)
  let r0 := (rawShellBandP20Moment M n 0 weights) ^ ((20 : ℝ)⁻¹)
  let C : ℝ := ((9 / 2 : ℝ) * M.gamma * 3 ^ (2 * M.gamma * (N : ℝ))) *
    (((78 * (N : ℝ) + 76 * (521 / 1000 : ℝ)) * (3683 / 2500 : ℝ)) +
      2 * (521 / 1000 : ℝ) * (3683 / 2500 : ℝ) *
        rawTraceFullResponseCap M.gamma N +
      ((1975 / 1000 : ℝ) + 38 * (1565 / 1000 : ℝ)) *
        (3683 / 2500 : ℝ) ^ 2 * rawTraceFullResponseCap M.gamma N)
  have hNnonneg (ω : CutoffSample 2) : 0 ≤ T_N ω :=
    modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n : ℝ)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1 _
  have h0nonneg (ω : CutoffSample 2) : 0 ≤ T_0 ω :=
    modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n : ℝ)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1 _
  have hNmem := raw_shell_band_trace_memLp20 M h hM hg n N hN hpastFull weights hw
  have h0eq : T_0 = cutoffTraceDefect M n n := by
    funext ω
    exact native_source_model_trace_older_eq M n ω
  have h0mem : MemLp T_0 (ENNReal.ofReal 20) μ := by
    rw [h0eq]
    have hcap : root20 M n < ⊤ := hstate.2.2.1.trans_lt ENNReal.ofReal_lt_top
    have hcap' : eLpNorm (cutoffTraceDefect M n n) (ENNReal.ofReal 20) μ < ⊤ := by
      simpa [root20, μ] using hcap
    exact memLp_iff.mpr hcap'
  have hrN : rN = (eLpNorm T_N (ENNReal.ofReal 20) μ).toReal := by
    have hEq : rawShellBandP20Moment M n N weights ^ ((20 : ℝ)⁻¹) =
        positiveLpNorm μ 20 T_N := by
      simp only [rawShellBandP20Moment, positiveLpNorm, T_N, μ]
    dsimp [rN]
    rw [hEq]
    exact positiveLpNorm_eq_eLpNorm_toReal μ (p := 20) (by norm_num)
      T_N hNnonneg hNmem.2
  have hr0 : r0 = (eLpNorm T_0 (ENNReal.ofReal 20) μ).toReal := by
    have hzero : rawShellBandScalarFromWeights M n 0 weights =
        olderField (closure (cubeSet (originCube 2 n))) n := by
      funext ω
      ext x
      simp [rawShellBandScalarFromWeights]
    have hEq : rawShellBandP20Moment M n 0 weights ^ ((20 : ℝ)⁻¹) =
        positiveLpNorm μ 20 T_0 := by
      simp only [rawShellBandP20Moment, positiveLpNorm, T_0, μ]
      rw [hzero]
    dsimp [r0]
    rw [hEq]
    exact positiveLpNorm_eq_eLpNorm_toReal μ (p := 20) (by norm_num)
      T_0 h0nonneg h0mem
  have hroot := raw_shell_band_root_increment_bound M h hM hg n N hstate
    hpastLocal hpastFull weights hw
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
    unfold rawTraceFullResponseCap
    positivity
  have hroots : rN - r0 ≤ C := by
    simpa [rN, r0, C] using hroot
  have hNtop : eLpNorm T_N (ENNReal.ofReal 20) μ ≠ ⊤ := hNmem.2.eLpNorm_ne_top
  have h0top : eLpNorm T_0 (ENNReal.ofReal 20) μ ≠ ⊤ := h0mem.eLpNorm_ne_top
  have hreal : (eLpNorm T_N (ENNReal.ofReal 20) μ).toReal ≤
      (eLpNorm T_0 (ENNReal.ofReal 20) μ).toReal + C := by
    rw [hrN, hr0] at hroots
    linarith
  have hband : eLpNorm T_N (ENNReal.ofReal 20) μ ≤
      eLpNorm T_0 (ENNReal.ofReal 20) μ + ENNReal.ofReal C := by
    calc
      _ = ENNReal.ofReal (eLpNorm T_N (ENNReal.ofReal 20) μ).toReal :=
        (ENNReal.ofReal_toReal hNtop).symm
      _ ≤ ENNReal.ofReal ((eLpNorm T_0 (ENNReal.ofReal 20) μ).toReal + C) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hC0]
        rw [ENNReal.ofReal_toReal h0top]
  have hstart : eLpNorm T_0 (ENNReal.ofReal 20) μ ≤
      ENNReal.ofReal ((21 / 100 : ℝ) * (M.gamma / gammaZero)) := by
    have hstateCap : eLpNorm T_0 (ENNReal.ofReal 20) μ ≤
        ENNReal.ofReal ((2013 / 10000 : ℝ) * theta M) := by
      rw [h0eq]
      simpa [root20, μ] using hstate.2.2.1
    have hθ : 0 ≤ theta M := by
      unfold theta
      exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
    have hcoef : ((2013 / 10000 : ℝ) * theta M) ≤
        (21 / 100 : ℝ) * (M.gamma / gammaZero) := by
      have hθeq : theta M = M.gamma / gammaZero := rfl
      rw [hθeq]
      nlinarith [mul_nonneg (show 0 ≤ (21 / 100 : ℝ) - 2013 / 10000 by norm_num) hθ]
    exact hstateCap.trans (ENNReal.ofReal_le_ofReal hcoef)
  exact ⟨by simpa [C] using hband, hstart⟩

end ASDExplicitGamma.Inverse

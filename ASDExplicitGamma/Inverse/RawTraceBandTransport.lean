module

public import ASDExplicitGamma.Inverse.RawTraceBand
public import ASDExplicitGamma.Inverse.RawShellBandTransport
public import ASDExplicitGamma.Inverse.RawShellBandBankInputs
public import ASDExplicitGamma.Inverse.RawTraceFrameMap
public import ASDExplicitGamma.Inverse.AnchorAdapter
public import ASDExplicitGamma.Inverse.RawShellBankCaps
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Statements.Root20
public import ASDExplicitGamma.Gaussian.ModelHeatResponse
public import ASDExplicitGamma.Response.ResponseRealization
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! The exact finite-band p=20 output feeds the audited h*=134 raw-trace
profile. This module exposes a
distinct-name helper whose only transport premise is that exact shell output. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal

noncomputable section

/-- The exact increment in the p=20 shell conclusion. -/
def rawTraceBandShellIncrement (γ : ℝ) (H : ℕ) : ℝ :=
  ((9 / 2 : ℝ) * γ * (3 : ℝ) ^ (2 * γ * (H : ℝ))) *
    (((78 * (H : ℝ) + 76 * (521 / 1000 : ℝ)) * (3683 / 2500 : ℝ)) +
      2 * (521 / 1000 : ℝ) * (3683 / 2500 : ℝ) * rawTraceFullResponseCap γ H +
      ((1975 / 1000 : ℝ) + 38 * (1565 / 1000 : ℝ)) *
        (3683 / 2500 : ℝ) ^ 2 * rawTraceFullResponseCap γ H)

/-- Transport a finite-band p=20 shell conclusion to the true-frame L²
depth profile. `hShell` is the conclusion, quantified over the
allowed weights; the starting point is derived from the native state. -/
theorem raw_trace_band_depth_profile_of_shell_transport_helper
    (M : ABKModel 2) (h : ℝ)
    (hγ : M.gamma ≤ gammaZero) (n m : ℤ) (d : ℕ) (hnm : n ≤ m)
    (hdepth : ((m - n : ℤ) : ℝ) + 1 ≤ 134 + (d : ℝ))
    (hstate : nativeInductionState M h n) (weights : ℤ → ℝ)
    (_hweights : ∀ k ∈ Finset.Ioc n (n + ((134 + d : ℕ) : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1)
    (hShell :
      eLpNorm
          (fun ω => modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
            (rawShellBandScalarFromWeights M n (134 + d) weights ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        eLpNorm
          (fun ω => modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
            (olderField (closure (cubeSet (originCube 2 n))) n ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure +
        ENNReal.ofReal (rawTraceBandShellIncrement M.gamma (134 + d))) :
    eLpNorm
        (fun ω => modelTraceObservable n M.nu (Annealed.sigmaBar M m : ℝ)
          (rawShellBandScalarFromWeights M n (134 + d) weights ω))
        (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal
        (theta M * (invTraceM : ℚ) * (1 + (d : ℝ)) ^ 2 *
          (3 : ℝ) ^ (6 * gammaZero * d)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let K := closure (cubeSet (originCube 2 n))
  let T₀ : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ) (olderField K n ω)
  let Tₐ : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
      (rawShellBandScalarFromWeights M n (134 + d) weights ω)
  let Tₘ : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    modelTraceObservable n M.nu (Annealed.sigmaBar M m : ℝ)
      (rawShellBandScalarFromWeights M n (134 + d) weights ω)
  let γ := M.gamma
  let H : ℝ := 134 + (d : ℝ)
  let η : ℝ := 1 / 1000
  let frameError : ℝ :=
    8 * (1 + 1 / η) * ((11 / 10 : ℝ) * γ * H) ^ 2
  let shellIncrement : ℝ :=
    ((9 / 2 : ℝ) * γ * (3 : ℝ) ^ (2 * γ * H)) *
      (((78 * H + 76 * (521 / 1000 : ℝ)) * (3683 / 2500 : ℝ)) +
        2 * (521 / 1000 : ℝ) * (3683 / 2500 : ℝ) *
          rawTraceFullResponseCap γ (134 + d) +
        ((1975 / 1000 : ℝ) + 38 * (1565 / 1000 : ℝ)) *
          (3683 / 2500 : ℝ) ^ 2 * rawTraceFullResponseCap γ (134 + d))
  have hγpos : 0 < γ := M.shellPrefix.gamma_pos
  have hγ0pos : 0 < gammaZero := by norm_num [gammaZero]
  have hθ0 : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg hγpos.le hγ0pos.le
  have hStartEq : T₀ = cutoffTraceDefect M n n := by
    funext ω
    have hcut := cutoff_response_true_frame M n n ω
    simpa [T₀, K, modelInsertedScalar] using hcut
  have hStartFrozen : eLpNorm T₀ (ENNReal.ofReal 20) μ ≤
      ENNReal.ofReal (2013 / 10000 * theta M) := by
    rw [hStartEq]
    simpa [root20] using hstate.2.2.1
  have hStartCoeff : (2013 / 10000 : ℝ) * theta M ≤
      (21 / 100 : ℝ) * theta M := by
    have hgap : 0 ≤ (21 / 100 : ℝ) - 2013 / 10000 := by norm_num
    nlinarith [mul_nonneg hgap hθ0]
  have hStart : eLpNorm T₀ (ENNReal.ofReal 20) μ ≤
      ENNReal.ofReal ((21 / 100 : ℝ) * theta M) :=
    hStartFrozen.trans (ENNReal.ofReal_le_ofReal hStartCoeff)
  have hBand := hShell
  have hIncEq : rawTraceBandIncrement γ H = shellIncrement := by
    dsimp [shellIncrement, H, γ]
    unfold rawTraceBandIncrement rawTraceBandClock rawTraceBandFullCap
      rawTraceFullResponseCap
    push_cast
    ring_nf
  have hSourceIncEq : rawTraceBandShellIncrement γ (134 + d) = shellIncrement := by
    simp [rawTraceBandShellIncrement, shellIncrement, γ, H]
  have hInc0 : 0 ≤ shellIncrement := by
    dsimp [shellIncrement, H, γ]
    unfold rawTraceFullResponseCap
    positivity
  have hBand' : eLpNorm Tₐ (ENNReal.ofReal 20) μ ≤
      ENNReal.ofReal ((21 / 100 : ℝ) * theta M + shellIncrement) := by
    have hStart0 : 0 ≤ (21 / 100 : ℝ) * theta M := mul_nonneg (by norm_num) hθ0
    calc
      eLpNorm Tₐ (ENNReal.ofReal 20) μ ≤
          eLpNorm T₀ (ENNReal.ofReal 20) μ + ENNReal.ofReal shellIncrement := by
        simpa [Tₐ, T₀, μ, γ, hSourceIncEq] using hBand
      _ ≤ ENNReal.ofReal ((21 / 100 : ℝ) * theta M) +
          ENNReal.ofReal shellIncrement := add_le_add hStart le_rfl
      _ = ENNReal.ofReal ((21 / 100 : ℝ) * theta M + shellIncrement) := by
        rw [ENNReal.ofReal_add hStart0 hInc0]
  have hBand2 : eLpNorm Tₐ (ENNReal.ofReal 2) μ ≤
      ENNReal.ofReal ((21 / 100 : ℝ) * theta M + shellIncrement) := by
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num :
      ENNReal.ofReal 2 ≤ ENNReal.ofReal 20)).trans hBand'
  let ρ := (Annealed.sigmaBar M m : ℝ) / (Annealed.sigmaBar M n : ℝ)
  have hmap (ω : Cutoff.CutoffSample 2) : Tₘ ω ≤
      ρ * ((1 + η) * Tₐ ω + frameError) := by
    let φω := rawShellBandScalarFromWeights M n (134 + d) weights ω
    let cω := responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ φω)
    let Λω := (M.nu ^ 2 + ‖ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ φω‖ ^ 2) / M.nu
    have hcω : IsEllipticFieldOn M.nu Λω (cubeSet (originCube 2 n)) cω := by
      exact responsePlanarCoefficientField_isElliptic
        (measurableSet_cubeSet (originCube 2 n)) M.nu M.nu_pos _
    have hm := raw_trace_defect_frame_map M n m (originCube 2 n) cω Λω hcω hnm η
      (by norm_num [η])
    have hdist : 0 ≤ ((m - n : ℤ) : ℝ) + 1 := by
      have hi : 0 ≤ (m - n : ℤ) := sub_nonneg.mpr hnm
      exact add_nonneg (by exact_mod_cast hi) (by norm_num)
    have hdepth' : ((m - n : ℤ) : ℝ) + 1 ≤ H := by
      simpa [H] using hdepth
    have harg : 0 ≤ (11 / 10 : ℝ) * γ * (((m - n : ℤ) : ℝ) + 1) := by
      positivity
    have hargle : (11 / 10 : ℝ) * γ * (((m - n : ℤ) : ℝ) + 1) ≤
        (11 / 10 : ℝ) * γ * H :=
      mul_le_mul_of_nonneg_left hdepth' (by positivity)
    have harg2 := (sq_le_sq₀ harg (by positivity :
      0 ≤ (11 / 10 : ℝ) * γ * H)).2 hargle
    have hErr : 8 * (1 + 1 / η) *
        ((11 / 10 : ℝ) * γ * (((m - n : ℤ) : ℝ) + 1)) ^ 2 ≤ frameError := by
      dsimp [frameError]
      exact mul_le_mul_of_nonneg_left harg2 (by positivity)
    have hbracket : (1 + η) *
        traceDefect (cubeSet (originCube 2 n)) cω
          (Annealed.sigmaBar M n : ℝ) +
        8 * (1 + 1 / η) *
          ((11 / 10 : ℝ) * γ * (((m - n : ℤ) : ℝ) + 1)) ^ 2 ≤
        (1 + η) * traceDefect (cubeSet (originCube 2 n)) cω
          (Annealed.sigmaBar M n : ℝ) + frameError := by
      exact add_le_add_right hErr _
    have hρloc : 0 ≤
        (Annealed.sigmaBar M m : ℝ) / (Annealed.sigmaBar M n : ℝ) :=
      div_nonneg (Annealed.sigmaBar_characterization M m).1.le
        (Annealed.sigmaBar_characterization M n).1.le
    have hbracket' : (1 + η) *
        traceDefect (cubeSet (originCube 2 n)) cω
          (Annealed.sigmaBar M n : ℝ) +
        8 * (1 + 1 / η) *
          ((11 / 10 : ℝ) * M.gamma * ((m : ℝ) - (n : ℝ) + 1)) ^ 2 ≤
        (1 + η) * traceDefect (cubeSet (originCube 2 n)) cω
          (Annealed.sigmaBar M n : ℝ) + frameError := by
      simpa [γ, Int.cast_sub] using hbracket
    have hm' := hm.trans (mul_le_mul_of_nonneg_left hbracket' hρloc)
    simpa [Tₘ, Tₐ, φω, cω, Λω, ρ, η, frameError, modelTraceObservable,
      Int.cast_sub] using hm'
  have hρ0 : 0 ≤ ρ := by
    exact div_nonneg (Annealed.sigmaBar_characterization M m).1.le
      (Annealed.sigmaBar_characterization M n).1.le
  have hTₐ0 (ω : Cutoff.CutoffSample 2) : 0 ≤ Tₐ ω := by
    simpa [Tₐ] using modelTraceObservable_nonneg n M.nu
      (Annealed.sigmaBar M n : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 _
  have hTₘ0 (ω : Cutoff.CutoffSample 2) : 0 ≤ Tₘ ω := by
    simpa [Tₘ] using modelTraceObservable_nonneg n M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 _
  have hFrame0 : 0 ≤ frameError := by positivity
  have hScalarMeas : Measurable
      (fun ω => rawShellBandScalarFromWeights M n (134 + d) weights ω) := by
    obtain ⟨ell, hK⟩ :=
      Gaussian.exists_originCube_containing_compact K
        (isBounded_cubeSet (originCube 2 n)).isCompact_closure
    change Measurable (fun ω => olderField K n ω +
      ∑ k ∈ Finset.Ioc n (n + ((134 + d : ℕ) : ℤ)),
        weights k • shellFieldScalarRestriction K (ω.1 k))
    apply (measurable_olderField K ell n hK).add
    apply Finset.measurable_sum
    intro k hk
    have hcoord : Measurable (fun ω : Cutoff.CutoffSample 2 => ω.1 k) :=
      (measurable_pi_apply k).comp measurable_subtype_coe
    have hterm : Measurable (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction K (ω.1 k)) :=
      (measurable_shellFieldScalarRestriction K).comp hcoord
    exact hterm.const_smul (weights k)
  have hObsCont := (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1).1.continuous
  have hTmMeas : Measurable Tₘ := by
    exact hObsCont.measurable.comp hScalarMeas
  let F : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ρ * ((1 + η) * Tₐ ω + frameError)
  have hF0 (ω : Cutoff.CutoffSample 2) : 0 ≤ F ω := by
    dsimp [F]
    exact mul_nonneg hρ0 (add_nonneg
      (mul_nonneg (by norm_num [η]) (hTₐ0 ω)) hFrame0)
  have hNormMap (ω : Cutoff.CutoffSample 2) : ‖Tₘ ω‖ₑ ≤ ‖F ω‖ₑ := by
    rw [Real.enorm_eq_ofReal (hTₘ0 ω), Real.enorm_eq_ofReal (hF0 ω)]
    exact ENNReal.ofReal_le_ofReal (hmap ω)
  have hFrameLp : eLpNorm Tₘ (ENNReal.ofReal 2) μ ≤
      eLpNorm F (ENNReal.ofReal 2) μ :=
    eLpNorm_mono_enorm (p := ENNReal.ofReal 2) (μ := μ)
      hTmMeas.aestronglyMeasurable hNormMap
  have hρbound : ρ ≤ (3 : ℝ) ^ (2 * γ * (134 + (d : ℝ))) := by
    have hratio := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity M n (m - n)
      (sub_nonneg.mpr hnm)
    have hraw : ρ ≤ Real.rpow 3 (2 * γ * ((m - n : ℤ) : ℝ)) := by
      dsimp [ρ, γ] at *
      simpa [Int.add_sub_cancel] using hratio.2
    apply hraw.trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    nlinarith [hdepth, hγpos.le]
  have hFrameLpBound : eLpNorm F (ENNReal.ofReal 2) μ ≤
      ENNReal.ofReal ((3 : ℝ) ^ (2 * γ * (134 + (d : ℝ))) *
        ((1 + η) * ((21 / 100 : ℝ) * theta M + shellIncrement) + frameError)) := by
    let A : Cutoff.CutoffSample 2 → ℝ := fun ω => (1 + η) * Tₐ ω
    let C : Cutoff.CutoffSample 2 → ℝ := fun _ => frameError
    have hAeq : eLpNorm A (ENNReal.ofReal 2) μ =
        ENNReal.ofReal (1 + η) * eLpNorm Tₐ (ENNReal.ofReal 2) μ := by
      have hfun : A = (1 + η) • Tₐ := by
        funext ω
        simp [A, smul_eq_mul]
      rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num [η])]
    have hCeq : eLpNorm C (ENNReal.ofReal 2) μ = ENNReal.ofReal frameError := by
      rw [eLpNorm_const _ (by norm_num) (NeZero.ne μ)]
      simp [Real.enorm_eq_ofReal hFrame0, measure_univ]
    have hAdd : eLpNorm (fun ω => A ω + C ω) (ENNReal.ofReal 2) μ ≤
        eLpNorm A (ENNReal.ofReal 2) μ + eLpNorm C (ENNReal.ofReal 2) μ := by
      exact eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)
    have hsum : eLpNorm (fun ω => A ω + C ω) (ENNReal.ofReal 2) μ ≤
        ENNReal.ofReal ((1 + η) * ((21 / 100 : ℝ) * theta M + shellIncrement) +
          frameError) := by
      have hAupper : eLpNorm A (ENNReal.ofReal 2) μ ≤
          ENNReal.ofReal ((1 + η) * ((21 / 100 : ℝ) * theta M + shellIncrement)) := by
        rw [hAeq]
        calc
          _ ≤ ENNReal.ofReal (1 + η) *
              ENNReal.ofReal ((21 / 100 : ℝ) * theta M + shellIncrement) :=
            mul_le_mul_of_nonneg_left hBand2 bot_le
          _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num [η])]
      calc
        _ ≤ eLpNorm A (ENNReal.ofReal 2) μ + eLpNorm C (ENNReal.ofReal 2) μ := hAdd
        _ ≤ ENNReal.ofReal ((1 + η) * ((21 / 100 : ℝ) * theta M + shellIncrement)) +
              ENNReal.ofReal frameError := add_le_add hAupper (le_of_eq hCeq)
        _ = _ := by rw [ENNReal.ofReal_add (by positivity) hFrame0]
    have hFfun : F = ρ • (fun ω => A ω + C ω) := by
      funext ω
      simp [F, A, C, η, smul_eq_mul]
    have hBracket0 : 0 ≤
        (1 + η) * ((21 / 100 : ℝ) * theta M + shellIncrement) + frameError := by
      positivity
    calc
      eLpNorm F (ENNReal.ofReal 2) μ =
          ENNReal.ofReal ρ * eLpNorm (fun ω => A ω + C ω)
            (ENNReal.ofReal 2) μ := by
        rw [hFfun, eLpNorm_const_smul, Real.enorm_eq_ofReal hρ0]
      _ ≤ ENNReal.ofReal ρ * ENNReal.ofReal
          ((1 + η) * ((21 / 100 : ℝ) * theta M + shellIncrement) + frameError) :=
        mul_le_mul_of_nonneg_left hsum bot_le
      _ = ENNReal.ofReal (ρ *
          ((1 + η) * ((21 / 100 : ℝ) * theta M + shellIncrement) + frameError)) := by
        rw [← ENNReal.ofReal_mul hρ0]
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (2 * γ * (134 + (d : ℝ))) *
          ((1 + η) * ((21 / 100 : ℝ) * theta M + shellIncrement) + frameError)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right hρbound hBracket0
  have hLambda :
      (3 : ℝ) ^ (2 * γ * (134 + (d : ℝ))) *
          ((1 + η) * ((21 / 100 : ℝ) * theta M + shellIncrement) + frameError) =
        rawTraceBandLambda γ (134 + (d : ℝ)) := by
    unfold rawTraceBandLambda theta
    simp only [η, frameError, shellIncrement, H, γ]
    rw [hIncEq]
  have hProfile := raw_trace_band_depth_profile γ d hγpos hγ
  calc
    eLpNorm Tₘ (ENNReal.ofReal 2) μ ≤ eLpNorm F (ENNReal.ofReal 2) μ := hFrameLp
    _ ≤ ENNReal.ofReal (rawTraceBandLambda γ (134 + (d : ℝ))) := by
      rw [← hLambda]
      exact hFrameLpBound
    _ ≤ ENNReal.ofReal
        (theta M * (invTraceM : ℚ) * (1 + (d : ℝ)) ^ 2 *
          (3 : ℝ) ^ (6 * gammaZero * d)) := by
      apply ENNReal.ofReal_le_ofReal
      simpa [theta, gammaZero] using hProfile

end

end ASDExplicitGamma.Inverse

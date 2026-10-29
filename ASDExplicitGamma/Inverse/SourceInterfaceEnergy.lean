module

public import ASDExplicitGamma.Inverse.SourceInterfaceTransport
public import ASDExplicitGamma.Inverse.RawShellFixedFrameGeneralP20
public import ASDExplicitGamma.Inverse.RawShellL20Caps
public import ASDExplicitGamma.Inverse.RawMomentChain
public import ASDExplicitGamma.Inverse.FullResponseExports
public import ASDExplicitGamma.Inverse.SourceQ3Drift
public import ASDExplicitGamma.Inverse.SourceQ3TraceRegularity
public import ASDExplicitGamma.Native.GenericSourceActualInverse
public import ASDExplicitGamma.Scalar.InverseHistory

/-! Quantitative one-shell OLD source-energy control in the completed frame. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Set Filter Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Native
open ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped ENNReal

noncomputable section

/-- The actual OLD-frame first-moment generator bound obtained from the
order-128 local history and full-response rows. The shell is `m+1`; `r` is
the source depth, so the source cell is `m-r`. -/
noncomputable def inSourceOldEnergyCap
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (r : ℕ) : ℝ := by
  let q : ℤ := m - (r : ℤ)
  let s : ℕ := r + 1
  let Q := originCube 2 q
  let σ : ℝ := Annealed.sigmaBar M m
  let κ := rawTraceRemainderKappaF
    (cubeScaleFactor Q / (q3ModelLength (q + (s : ℤ))).1)
    (diagMeshRadius Q (pureFluxBankSourceDepth s) /
      (q3ModelLength (q + (s : ℤ))).1)
  let A := rawTraceRemainderA (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let A' := rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0 A A'
  let v := (q3ModelAmplitude M h (q + (s : ℤ))) ^ 2 / σ ^ 2
  let C := rawTraceOldFrameP20LocalClock M.gamma s
  let fCap := rawTraceOldFrameP20FullResponseCap M.gamma s
  exact v * C * (2 * (3683 / 2500 : ℝ) +
    2 * κ * (3683 / 2500 : ℝ) * fCap +
    C * μR * (3683 / 2500 : ℝ) ^ 2 * fCap)

private theorem in_source_sqrt_le {x c : ℝ}
    (hc : 0 ≤ c) (hxc : x ≤ c ^ 2) : Real.sqrt x ≤ c := by
  exact Real.sqrt_le_iff.mpr ⟨hc, hxc⟩

/-- Uniform coarse bounds for the exact SHEAR remainder coefficients when its
two scale ratios lie in the unit interval. These deliberately only majorize
the covariance rows; no source-law estimate is hidden in this algebraic
lemma. -/
private theorem in_source_remainder_coarse_bounds
    {rho delta : ℝ} (hrho : 0 ≤ rho ∧ rho ≤ 1)
    (hdelta : 0 ≤ delta ∧ delta ≤ 1) :
    rawTraceRemainderKappaF rho delta ≤ 64 ∧
      rawTraceRemainderB rho delta ≤ 32 ∧
      rawTraceRemainderA rho delta ≤ 43 ∧
      rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
        (rawTraceRemainderA rho delta) (rawTraceRemainderB rho delta) ≤ 13000 := by
  have hρsq : rho ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - rho)]
  have hδsq : delta ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - delta)]
  have hρδ : rho * delta ≤ 1 := by
    calc
      rho * delta ≤ rho * 1 := mul_le_mul_of_nonneg_left hdelta.2 hrho.1
      _ ≤ 1 := by simpa using hrho.2
  have hs78 : Real.sqrt (78 / 10 : ℝ) ≤ 3 :=
    in_source_sqrt_le (by norm_num) (by norm_num)
  have hs156 : Real.sqrt (156 / 5 : ℝ) ≤ 6 :=
    in_source_sqrt_le (by norm_num) (by norm_num)
  have hs46488 : Real.sqrt (46488 / 25 : ℝ) ≤ 44 :=
    in_source_sqrt_le (by norm_num) (by norm_num)
  have hs78b : Real.sqrt (78 / 5 : ℝ) ≤ 4 :=
    in_source_sqrt_le (by norm_num) (by norm_num)
  have hs23244 : Real.sqrt (23244 / 25 : ℝ) ≤ 31 :=
    in_source_sqrt_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2 : ℝ) ≤ 2 :=
    in_source_sqrt_le (by norm_num) (by norm_num)
  have hρbase : Real.sqrt (78 / 10 : ℝ) * rho ≤ 3 := by
    calc
      _ ≤ 3 * rho := mul_le_mul_of_nonneg_right hs78 hrho.1
      _ ≤ 3 := by nlinarith [hrho.2]
  have hδlinearA : Real.sqrt (156 / 5 : ℝ) * delta ≤ 6 := by
    calc
      _ ≤ 6 * delta := mul_le_mul_of_nonneg_right hs156 hdelta.1
      _ ≤ 6 := by nlinarith [hdelta.2]
  have hδquadA : Real.sqrt (46488 / 25 : ℝ) * delta ^ 2 ≤ 44 := by
    calc
      _ ≤ 44 * delta ^ 2 := mul_le_mul_of_nonneg_right hs46488 (sq_nonneg delta)
      _ ≤ 44 := by nlinarith [hδsq]
  have hδlinearB : Real.sqrt (78 / 5 : ℝ) * delta ≤ 4 := by
    calc
      _ ≤ 4 * delta := mul_le_mul_of_nonneg_right hs78b hdelta.1
      _ ≤ 4 := by nlinarith [hdelta.2]
  have hδquadB : Real.sqrt (23244 / 25 : ℝ) * delta ^ 2 ≤ 31 := by
    calc
      _ ≤ 31 * delta ^ 2 := mul_le_mul_of_nonneg_right hs23244 (sq_nonneg delta)
      _ ≤ 31 := by nlinarith [hδsq]
  have hA : rawTraceRemainderA rho delta ≤ 43 := by
    unfold rawTraceRemainderA
    have hfirst : 1.860 * (Real.sqrt (78 / 10 : ℝ) * rho) ≤ 1.860 * 3 :=
      mul_le_mul_of_nonneg_left hρbase (by norm_num)
    have hsecond : 2.36412 * (Real.sqrt (156 / 5 : ℝ) * delta) ≤ 2.36412 * 6 :=
      mul_le_mul_of_nonneg_left hδlinearA (by norm_num)
    have hthird : 0.52288 * (Real.sqrt (46488 / 25 : ℝ) * delta ^ 2) ≤ 0.52288 * 44 :=
      mul_le_mul_of_nonneg_left hδquadA (by norm_num)
    nlinarith only [hfirst, hsecond, hthird]
  have hB : rawTraceRemainderB rho delta ≤ 32 := by
    unfold rawTraceRemainderB
    have hfirst : 1.860 * (Real.sqrt (78 / 10 : ℝ) * rho) ≤ 1.860 * 3 :=
      mul_le_mul_of_nonneg_left hρbase (by norm_num)
    have hsecond : 2.36412 * (Real.sqrt (78 / 5 : ℝ) * delta) ≤ 2.36412 * 4 :=
      mul_le_mul_of_nonneg_left hδlinearB (by norm_num)
    have hthird : 0.52288 * (Real.sqrt (23244 / 25 : ℝ) * delta ^ 2) ≤ 0.52288 * 31 :=
      mul_le_mul_of_nonneg_left hδquadB (by norm_num)
    nlinarith only [hfirst, hsecond, hthird]
  have hκ : rawTraceRemainderKappaF rho delta ≤ 64 := by
    unfold rawTraceRemainderKappaF
    have hsqrt2pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have hsqrt2lower : 1 ≤ Real.sqrt (2 : ℝ) :=
      Real.le_sqrt_of_sq_le (by norm_num)
    have hdiv : (78 / 5 : ℝ) / Real.sqrt 2 ≤ 78 / 5 := by
      rw [div_le_iff₀ hsqrt2pos]
      nlinarith [hsqrt2lower]
    have hfirst :
        1.860 * ((78 / 5 : ℝ) / 4) * rho ^ 2 ≤
          1.860 * ((78 / 5 : ℝ) / 4) := by
      calc
        _ ≤ 1.860 * ((78 / 5 : ℝ) / 4) * 1 :=
          mul_le_mul_of_nonneg_left hρsq
            (by norm_num : (0 : ℝ) ≤ 1.860 * ((78 / 5 : ℝ) / 4))
        _ = 1.860 * ((78 / 5 : ℝ) / 4) := by ring
    have hsecond :
        2.36412 * ((78 / 5 : ℝ) / Real.sqrt 2) * (rho * delta) ≤
          2.36412 * (78 / 5 : ℝ) := by
      calc
        _ ≤ 2.36412 * ((78 / 5 : ℝ) / Real.sqrt 2) * 1 := by
          exact mul_le_mul_of_nonneg_left hρδ
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2.36412)
              (div_nonneg (by norm_num : (0 : ℝ) ≤ 78 / 5) hsqrt2pos.le))
        _ = 2.36412 * ((78 / 5 : ℝ) / Real.sqrt 2) := by ring
        _ ≤ 2.36412 * (78 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_left hdiv (by norm_num)
    have hthird :
        0.52288 * Real.sqrt 2 * (78 / 5 : ℝ) * delta ^ 2 ≤
          0.52288 * 2 * (78 / 5 : ℝ) := by
      have hcoeff : 0 ≤ 0.52288 * (78 / 5 : ℝ) := by positivity
      calc
        _ = (0.52288 * (78 / 5 : ℝ)) * (Real.sqrt 2 * delta ^ 2) := by ring
        _ ≤ (0.52288 * (78 / 5 : ℝ)) * 2 := by
          exact mul_le_mul_of_nonneg_left
            (calc
              Real.sqrt 2 * delta ^ 2 ≤ 2 * delta ^ 2 :=
                mul_le_mul_of_nonneg_right hs2 (sq_nonneg delta)
              _ ≤ 2 := by nlinarith [hδsq]) hcoeff
        _ = 0.52288 * 2 * (78 / 5 : ℝ) := by ring
    nlinarith only [hfirst, hsecond, hthird]
  have hA0 : 0 ≤ rawTraceRemainderA rho delta := by
    unfold rawTraceRemainderA
    positivity [hrho.1, hdelta.1]
  have hB0 : 0 ≤ rawTraceRemainderB rho delta := by
    unfold rawTraceRemainderB
    positivity [hrho.1, hdelta.1]
  have hH0 : 0 ≤ rawTraceRemainderH0 := by norm_num [rawTraceRemainderH0]
  have hH03 : rawTraceRemainderH0 ≤ 3 := by norm_num [rawTraceRemainderH0]
  have hD00 : 0 ≤ rawTraceRemainderD0 := by
    unfold rawTraceRemainderD0
    positivity
  have hD05 : rawTraceRemainderD0 ≤ 5 := by
    unfold rawTraceRemainderD0
    have hsqrt : Real.sqrt rawTraceRemainderH0 ≤ 2 :=
      in_source_sqrt_le (by norm_num) (by norm_num [rawTraceRemainderH0])
    nlinarith [hsqrt]
  have hA2 : (rawTraceRemainderA rho delta) ^ 2 ≤ 43 ^ 2 := by
    nlinarith [hA0, hA]
  have hAB : rawTraceRemainderA rho delta * rawTraceRemainderB rho delta ≤ 43 * 32 := by
    calc
      _ ≤ 43 * rawTraceRemainderB rho delta :=
        mul_le_mul_of_nonneg_right hA hB0
      _ ≤ 43 * 32 := mul_le_mul_of_nonneg_left hB (by norm_num)
  have hroot :
      Real.sqrt (rawTraceRemainderH0 ^ 2 * (rawTraceRemainderA rho delta) ^ 4 +
        4 * rawTraceRemainderD0 ^ 2 * (rawTraceRemainderA rho delta) ^ 2 *
          (rawTraceRemainderB rho delta) ^ 2) ≤
        rawTraceRemainderH0 * (rawTraceRemainderA rho delta) ^ 2 +
          2 * rawTraceRemainderD0 * rawTraceRemainderA rho delta *
            rawTraceRemainderB rho delta := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hx := mul_nonneg hH0 (sq_nonneg (rawTraceRemainderA rho delta))
      have hy := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD00)
        (mul_nonneg hA0 hB0)
      nlinarith [sq_nonneg
        (rawTraceRemainderH0 * (rawTraceRemainderA rho delta) ^ 2),
        sq_nonneg (2 * rawTraceRemainderD0 * rawTraceRemainderA rho delta *
          rawTraceRemainderB rho delta)]
  have hmu : rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
      (rawTraceRemainderA rho delta) (rawTraceRemainderB rho delta) ≤ 13000 := by
    unfold rawTraceRemainderMu
    calc
      _ ≤ (rawTraceRemainderH0 * (rawTraceRemainderA rho delta) ^ 2 +
            (rawTraceRemainderH0 * (rawTraceRemainderA rho delta) ^ 2 +
              2 * rawTraceRemainderD0 * rawTraceRemainderA rho delta *
                rawTraceRemainderB rho delta)) / 2 := by
          gcongr
      _ ≤ 13000 := by nlinarith [hH03, hD05, hA2, hAB]
  exact ⟨hκ, hB, hA, hmu⟩

private theorem in_source_integral_le_positiveLpNorm
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
theorem in_source_actual_generator_old_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j)
    (r : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    inSourceMeanRateActual M h m r t ≤ inSourceOldEnergyCap M h m r ∧
      0 ≤ inSourceOldEnergyCap M h m r := by
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
  let κ := rawTraceRemainderKappaF
    (cubeScaleFactor Q / (q3ModelLength (q + (s : ℤ))).1)
    (diagMeshRadius Q (pureFluxBankSourceDepth s) /
      (q3ModelLength (q + (s : ℤ))).1)
  let κB := rawTraceRemainderB
    (cubeScaleFactor Q / (q3ModelLength (q + (s : ℤ))).1)
    (diagMeshRadius Q (pureFluxBankSourceDepth s) /
      (q3ModelLength (q + (s : ℤ))).1)
  let A := rawTraceRemainderA (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let A' := rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0 A A'
  let v := b ^ 2 / σ ^ 2
  let qCap := C * (κB ^ 2 + κ) - κ
  let v' := v * C
  let μR' := C * μR
  let fCap := rawTraceOldFrameP20FullResponseCap M.gamma s
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
  have hC1 : 1 ≤ C := by
    dsimp [C, rawTraceOldFrameP20LocalClock]
    apply Real.one_le_rpow (by norm_num)
    have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
    have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have : 0 ≤ 2 * M.gamma * ((s : ℝ) - 1) := by nlinarith
    exact this
  have hBcap : ∀ᵐ ω ∂μ,
      max (lemmaVTileHistory Q (pureFluxBankSourceDepth s)
          (responseFramePlanarCoefficientField M.nu σ
            (pureFluxOpenResponseRestriction q (X ω))))
        (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
          (responseFramePlanarCoefficientField M.nu σ
            (pureFluxOpenResponseRestriction q (X ω)))) ≤ C * P ω := by
    filter_upwards [hBsource] with ω hω
    exact hω.trans (mul_le_mul_of_nonneg_right hratio (hP0 ω))
  have hF128 : eLpNorm F (128 : ℝ≥0∞) μ ≤ ENNReal.ofReal fCap := by
    let G := fun ω : Cutoff.CutoffSample 2 =>
      rootTraceObservable M Q m (m + 1) m (fun _ => Real.sqrt t) ω
    have hstateFull : ∀ j ≤ (m + 1) - 303, nativeInductionState M h j := by
      intro j hj
      apply hpast j
      omega
    have hfull := full_response_completed_bank128 M h hM hg Q (m + 1) m m
      (by change q - 1 ≤ m + 1; dsimp [q]; omega)
      (by change q - 342 ≤ m; dsimp [q]; omega)
      (by omega) hstateFull (fun _ => Real.sqrt t) hWm
    have hGcap : eLpNorm (fun ω => G ω / 4) (ENNReal.ofReal 128) μ ≤ ENNReal.ofReal
        (((2018618 : ℝ) / 1000000 + M.gamma *
          ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216)) *
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
    rw [hGeq, show (128 : ℝ≥0∞) = ENNReal.ofReal (128 : ℝ) by norm_num]
    have hscale : G = (4 : ℝ) • (fun ω => G ω / 4) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hscale, eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 4)]
    have hfour : ENNReal.ofReal 4 * ENNReal.ofReal
        (((2018618 : ℝ) / 1000000 + M.gamma *
          ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216)) *
          (3 : ℝ) ^ (2 * M.gamma * ((s + 1 : ℕ) : ℝ) +
            2 * M.gamma * (s : ℝ))) = ENNReal.ofReal fCap := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      dsimp [fCap, rawTraceOldFrameP20FullResponseCap]
      congr 1
      ring
    calc
      _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal
          (((2018618 : ℝ) / 1000000 + M.gamma *
            ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216)) *
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
          ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216) := by positivity
      dsimp [fCap, rawTraceOldFrameP20FullResponseCap]
      exact mul_nonneg (mul_nonneg (by norm_num) hpoly) (by positivity)
  have hcaps := raw_trace_p20_bank_holder_caps_of_cap μ P F T D fCap hfCap0
    hP0 hF0 hT0 (fun ω => by exact hD0 ω)
    (Filter.Eventually.of_forall fun ω => by dsimp [F, T]; linarith [hT0 ω])
    hDle hPmeas' hFmeas' hTmeas' hDmeas' hP128 hF128
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
      div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
        (q3ModelLength (q + (s : ℤ))).2.le
    have hdelta : 0 ≤ diagMeshRadius Q (pureFluxBankSourceDepth s) /
        (q3ModelLength (q + (s : ℤ))).1 :=
      div_nonneg (diagMeshRadius_pos Q (pureFluxBankSourceDepth s)).le
        (q3ModelLength (q + (s : ℤ))).2.le
    dsimp [κ]
    unfold rawTraceRemainderKappaF
    positivity
  have hκB : 0 ≤ κB := by
    have hrho : 0 ≤ cubeScaleFactor Q /
        (q3ModelLength (q + (s : ℤ))).1 :=
      div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
        (q3ModelLength (q + (s : ℤ))).2.le
    have hdelta : 0 ≤ diagMeshRadius Q (pureFluxBankSourceDepth s) /
        (q3ModelLength (q + (s : ℤ))).1 :=
      div_nonneg (diagMeshRadius_pos Q (pureFluxBankSourceDepth s)).le
        (q3ModelLength (q + (s : ℤ))).2.le
    dsimp [κB]
    unfold rawTraceRemainderB
    positivity
  have hμ : 0 ≤ μR := by
    dsimp [μR]
    unfold rawTraceRemainderMu
    have hH0 : 0 ≤ rawTraceRemainderH0 := by norm_num [rawTraceRemainderH0]
    have hD0' : 0 ≤ rawTraceRemainderD0 := by
      unfold rawTraceRemainderD0
      positivity
    have hA0 : 0 ≤ A := by
      have hrho := (pureFlux_covariance_rho_pos 0 (s - 1)).le
      have hdelta := (pureFlux_covariance_delta_bounds 0 (s - 1)).1
      dsimp [A]
      unfold rawTraceRemainderA
      positivity
    have hA'0 : 0 ≤ A' := by
      have hrho := (pureFlux_covariance_rho_pos 0 (s - 1)).le
      have hdelta := (pureFlux_covariance_delta_bounds 0 (s - 1)).1
      dsimp [A']
      unfold rawTraceRemainderB
      positivity
    positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hv' : 0 ≤ v' := mul_nonneg hv hC0
  have hμ' : 0 ≤ μR' := mul_nonneg hC0 hμ
  have hqCap : 0 ≤ qCap := by
    dsimp [qCap]
    nlinarith [sq_nonneg κB, mul_nonneg hC0 (add_nonneg (sq_nonneg κB) hκ)]
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
    have hrow := raw_trace_model_q3_positive_generator_row q s hs
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
  have hDmean := in_source_integral_le_positiveLpNorm μ D hD0 hDmem
  have hPFmean := in_source_integral_le_positiveLpNorm μ (fun ω => P ω * F ω)
    (fun ω => mul_nonneg (hP0 ω) (hF0 ω)) hPFmem
  have hP2mean := in_source_integral_le_positiveLpNorm μ
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
  have hcapEq : inSourceOldEnergyCap M h m r =
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

/-- The actual-law OLD source slope is bounded by the energy cap whenever
the required native states lie strictly before the completed label. -/
theorem in_source_actual_slope_old_energy_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j) (r : ℕ) :
    inSourceMeanSlopeActual M h m r ≤ inSourceOldEnergyCap M h m r := by
  let S := inSourceMeanRateActual M h m r '' Set.Icc (0 : ℝ) 1
  have henergy := in_source_actual_generator_old_energy M h hM hg m hpast r 0
    ⟨le_rfl, by norm_num⟩
  have hS_nonempty : S.Nonempty := by
    refine ⟨inSourceMeanRateActual M h m r 0, ?_⟩
    exact ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩
  have hsup : sSup S ≤ inSourceOldEnergyCap M h m r := by
    apply csSup_le hS_nonempty
    rintro x ⟨t, ht, rfl⟩
    exact (in_source_actual_generator_old_energy M h hM hg m hpast r t ht).1
  unfold inSourceMeanSlopeActual
  exact max_le henergy.2 hsup

/-- The weight of the depth-`r` OLD source-energy slope in the completed
history. This keeps the prescribed inverse-history discount, the OLD bank
constant, and the source growth factor separate and visible. -/
noncomputable def inSourceOldEnergyHistoryWeight
    (M : ABKModel 2) (r : ℕ) : ℝ :=
  (1 - Scalar.inverseHistoryDiscount ^ 2) *
    Scalar.inverseHistoryDiscount ^ (2 * r) *
      (3683 / 2500 : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (r : ℝ))

private theorem in_source_old_energy_history_weight_nonneg'
    (M : ABKModel 2) (r : ℕ) :
    0 ≤ inSourceOldEnergyHistoryWeight M r := by
  have hα := Scalar.inverse_history_discount_range
  have hpref : 0 ≤ 1 - Scalar.inverseHistoryDiscount ^ 2 := by
    have hprod := mul_nonneg
      (sub_nonneg.mpr hα.2.le)
      (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hα.1.le)
    nlinarith
  unfold inSourceOldEnergyHistoryWeight
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg hpref
      exact pow_nonneg hα.1.le _
    · norm_num
  · exact Real.rpow_nonneg (by norm_num) _

/-- On every finite initial segment, the weighted sum of the actual OLD
source-energy slopes is bounded by the corresponding sum of explicit
actual-law generator caps. The law in each slope is the true cutoff sample
law and all generator bounds use the completed OLD frame. -/
theorem in_source_actual_finite_old_energy_sum
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j) (N : ℕ) :
    (∑ r ∈ Finset.range N,
      inSourceOldEnergyHistoryWeight M r * inSourceMeanSlopeActual M h m r) ≤
    ∑ r ∈ Finset.range N,
      inSourceOldEnergyHistoryWeight M r * inSourceOldEnergyCap M h m r := by
  apply Finset.sum_le_sum
  intro r hr
  exact mul_le_mul_of_nonneg_left
    (in_source_actual_slope_old_energy_bound M h hM hg m hpast r)
    (in_source_old_energy_history_weight_nonneg' M r)

private theorem in_source_full_response_cap_depth_envelope
    (gamma : ℝ) (r : ℕ) (hgamma0 : 0 ≤ gamma)
    (hgamma : gamma ≤ (17 / 50000 : ℝ)) :
    rawTraceOldFrameP20FullResponseCap gamma (r + 1) ≤
      50000 * ((r : ℝ) + 1) * (3 : ℝ) ^ (4 * gamma * (r : ℝ)) := by
  let s : ℕ := r + 1
  have hsCast : (s : ℝ) = (r : ℝ) + 1 := by simp [s]
  have hsp1Cast : ((s + 1 : ℕ) : ℝ) = (r : ℝ) + 2 := by
    simp [s]
    ring
  have hr1 : 1 ≤ (r : ℝ) + 1 := by
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.zero_le r
    linarith
  have hdepth :
      (32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216 ≤
        11580638 * ((r : ℝ) + 1) := by
    rw [hsp1Cast]
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.zero_le r
    nlinarith [hr0]
  have hgammaDepth :
      gamma * ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216) ≤
        4000 * ((r : ℝ) + 1) := by
    calc
      _ ≤ gamma * (11580638 * ((r : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hdepth hgamma0
      _ ≤ (17 / 50000 : ℝ) * (11580638 * ((r : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hgamma (by positivity)
      _ ≤ 4000 * ((r : ℝ) + 1) := by
        have hconst : (17 / 50000 : ℝ) * 11580638 ≤ 4000 := by norm_num
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
        nlinarith [hconst, hr0]
  have hrawInner :
      (2018618 : ℝ) / 1000000 +
          gamma * ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216) ≤
        4003 * ((r : ℝ) + 1) := by
    calc
      _ ≤ 3 + 4000 * ((r : ℝ) + 1) :=
        add_le_add (by norm_num : (2018618 : ℝ) / 1000000 ≤ 3) hgammaDepth
      _ ≤ 4003 * ((r : ℝ) + 1) := by nlinarith [hr1]
  have hsmallGamma : 6 * gamma ≤ 1 := by nlinarith [hgamma]
  have hpowSmall : (3 : ℝ) ^ (6 * gamma) ≤ 3 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hsmallGamma
  have hpowDepth :
      (3 : ℝ) ^ (2 * gamma * ((s + 1 : ℕ) : ℝ) +
          2 * gamma * (s : ℝ)) =
        (3 : ℝ) ^ (4 * gamma * (r : ℝ) + 6 * gamma) := by
    congr 1
    rw [hsp1Cast, hsCast]
    ring
  have hpowR0 : 0 ≤ (3 : ℝ) ^ (4 * gamma * (r : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  unfold rawTraceOldFrameP20FullResponseCap
  rw [hpowDepth, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  calc
    _ ≤ 4 * (4003 * ((r : ℝ) + 1)) *
        ((3 : ℝ) ^ (4 * gamma * (r : ℝ)) * 3) := by gcongr
    _ = 48036 * ((r : ℝ) + 1) *
        (3 : ℝ) ^ (4 * gamma * (r : ℝ)) := by ring
    _ ≤ 50000 * ((r : ℝ) + 1) *
        (3 : ℝ) ^ (4 * gamma * (r : ℝ)) := by
      have hrplus0 : 0 ≤ (r : ℝ) + 1 := le_trans (by norm_num) hr1
      have hfactor : 0 ≤ ((r : ℝ) + 1) *
          (3 : ℝ) ^ (4 * gamma * (r : ℝ)) := mul_nonneg hrplus0 hpowR0
      calc
        _ = 48036 * (((r : ℝ) + 1) * (3 : ℝ) ^ (4 * gamma * (r : ℝ))) := by ring
        _ ≤ 50000 * (((r : ℝ) + 1) * (3 : ℝ) ^ (4 * gamma * (r : ℝ))) :=
          mul_le_mul_of_nonneg_right (by norm_num) hfactor
        _ = _ := by ring

private theorem in_source_old_energy_cap_depth_envelope
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (r : ℕ)
    (hg : M.gamma ≤ gammaZero) :
    inSourceOldEnergyCap M h m r ≤
      3000000000 *
        ((q3ModelAmplitude M h (m + 1)) ^ 2 /
          (Annealed.sigmaBar M m : ℝ) ^ 2) *
        ((r : ℝ) + 1) * (3 : ℝ) ^ (8 * M.gamma * (r : ℝ)) := by
  classical
  let q : ℤ := m - (r : ℤ)
  let s : ℕ := r + 1
  let Q := originCube 2 q
  let rho := pureFluxCovarianceRho 0 (s - 1)
  let delta := pureFluxCovarianceDelta 0 (s - 1)
  let len := (q3ModelLength (q + (s : ℤ))).1
  let mesh := diagMeshRadius Q (pureFluxBankSourceDepth s)
  let kappa := rawTraceRemainderKappaF (cubeScaleFactor Q / len) (mesh / len)
  let kappaB := rawTraceRemainderB (cubeScaleFactor Q / len) (mesh / len)
  let A := rawTraceRemainderA rho delta
  let A' := rawTraceRemainderB rho delta
  let muR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0 A A'
  let v := (q3ModelAmplitude M h (q + (s : ℤ))) ^ 2 /
    (Annealed.sigmaBar M m : ℝ) ^ 2
  let C := rawTraceOldFrameP20LocalClock M.gamma s
  let fCap := rawTraceOldFrameP20FullResponseCap M.gamma s
  let b : ℝ := 3683 / 2500
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hsr : s - 1 = r := by omega
  have hρgeom : cubeScaleFactor Q / len = rho := by
    simpa [Q, len, rho, q, s] using pureFlux_bank_source_rho q s hs
  have hδgeom : mesh / len = delta := by
    simpa [Q, len, mesh, delta, q, s] using pureFlux_bank_source_delta q s hs
  have hρ0 : 0 ≤ rho := by
    dsimp [rho]
    exact (pureFlux_covariance_rho_pos 0 (s - 1)).le
  have hρ1 : rho ≤ 1 := by
    dsimp [rho]
    rw [hsr]
    unfold pureFluxCovarianceRho
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hδ0 : 0 ≤ delta := by
    dsimp [delta]
    exact (pureFlux_covariance_delta_bounds 0 (s - 1)).1
  have hδ1 : delta ≤ 1 := by
    dsimp [delta]
    rw [hsr]
    exact ((pureFlux_covariance_delta_bounds 0 r).2).trans hρ1
  have hcoarse := in_source_remainder_coarse_bounds
    ⟨hρ0, hρ1⟩ ⟨hδ0, hδ1⟩
  have hkappa0 : 0 ≤ kappa := by
    dsimp [kappa]
    rw [hρgeom, hδgeom]
    unfold rawTraceRemainderKappaF
    positivity
  have hkappa : kappa ≤ 64 := by
    dsimp [kappa]
    rw [hρgeom, hδgeom]
    exact hcoarse.1
  have hkappaB : kappaB ≤ 32 := by
    dsimp [kappaB]
    rw [hρgeom, hδgeom]
    exact hcoarse.2.1
  have hA0 : 0 ≤ A := by
    dsimp [A]
    unfold rawTraceRemainderA
    positivity [hρ0, hδ0]
  have hA : A ≤ 43 := by dsimp [A]; exact hcoarse.2.2.1
  have hA'0 : 0 ≤ A' := by
    dsimp [A']
    unfold rawTraceRemainderB
    positivity [hρ0, hδ0]
  have hA' : A' ≤ 32 := by dsimp [A']; exact hcoarse.2.1
  have hmu0 : 0 ≤ muR := by
    dsimp [muR]
    unfold rawTraceRemainderMu
    have hH0 : 0 ≤ rawTraceRemainderH0 := by norm_num [rawTraceRemainderH0]
    apply div_nonneg
    · apply add_nonneg
      · exact mul_nonneg hH0 (sq_nonneg _)
      · exact Real.sqrt_nonneg _
    · norm_num
  have hmu : muR ≤ 13000 := by dsimp [muR, A, A']; exact hcoarse.2.2.2
  have hgamma0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hgamma' : M.gamma ≤ (17 / 50000 : ℝ) := by
    simpa [gammaZero] using hg
  have hC0 : 0 ≤ C := by
    dsimp [C, rawTraceOldFrameP20LocalClock]
    exact Real.rpow_nonneg (by norm_num) _
  have hC1 : 1 ≤ C := by
    dsimp [C, rawTraceOldFrameP20LocalClock]
    apply Real.one_le_rpow (by norm_num)
    apply mul_nonneg
    · exact mul_nonneg (by norm_num) hgamma0
    · nlinarith [show (1 : ℝ) ≤ (s : ℝ) by exact_mod_cast hs]
  have hr1 : 1 ≤ (r : ℝ) + 1 := by
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.zero_le r
    linarith
  have hfCap := in_source_full_response_cap_depth_envelope
    M.gamma r hgamma0 hgamma'
  have hv0 : 0 ≤ v := by
    dsimp [v]
    positivity
  have hb0 : 0 ≤ b := by norm_num [b]
  have hb2 : b ≤ 2 := by norm_num [b]
  have htermK : 2 * kappa * b * fCap ≤ 256 * fCap := by
    have hcoeff : 2 * kappa * b ≤ 256 := by
      calc
        _ ≤ 2 * 64 * b := by gcongr
        _ ≤ 2 * 64 * 2 := by gcongr
        _ = 256 := by norm_num
    exact mul_le_mul_of_nonneg_right hcoeff (by
      dsimp [fCap, rawTraceOldFrameP20FullResponseCap]
      positivity [hgamma0])
  have htermMu : C * muR * b ^ 2 * fCap ≤ 52000 * C * fCap := by
    have hcoeff : muR * b ^ 2 ≤ 52000 := by
      calc
        _ ≤ 13000 * b ^ 2 := mul_le_mul_of_nonneg_right hmu (sq_nonneg b)
        _ ≤ 13000 * 4 := by nlinarith [hb2, hb0]
        _ = 52000 := by norm_num
    have hf0 : 0 ≤ fCap := by
      dsimp [fCap, rawTraceOldFrameP20FullResponseCap]
      positivity [hgamma0]
    calc
      _ = (muR * b ^ 2) * (C * fCap) := by ring
      _ ≤ 52000 * (C * fCap) := mul_le_mul_of_nonneg_right hcoeff
          (mul_nonneg hC0 hf0)
      _ = 52000 * C * fCap := by ring
  have htermBase : 2 * b ≤ 4 := by nlinarith [hb2]
  have hinner :
      2 * b + 2 * kappa * b * fCap + C * muR * b ^ 2 * fCap ≤
        52260 * C * (fCap + 1) := by
    have hf0 : 0 ≤ fCap := by
      dsimp [fCap, rawTraceOldFrameP20FullResponseCap]
      positivity [hgamma0]
    have hcf : fCap ≤ C * fCap := by
      calc
        fCap = 1 * fCap := by ring
        _ ≤ C * fCap := mul_le_mul_of_nonneg_right hC1 hf0
    have hpre :
        2 * b + 2 * kappa * b * fCap + C * muR * b ^ 2 * fCap ≤
          4 + 256 * fCap + 52000 * C * fCap := by
      linarith [htermBase, htermK, htermMu]
    have hpost :
        4 + 256 * fCap + 52000 * C * fCap ≤ 52260 * C * (fCap + 1) := by
      nlinarith [hcf, hC1, hf0]
    exact hpre.trans hpost
  have hfplus : fCap + 1 ≤
      50001 * ((r : ℝ) + 1) * (3 : ℝ) ^ (4 * M.gamma * (r : ℝ)) := by
    have hpowR1 : 1 ≤ (3 : ℝ) ^ (4 * M.gamma * (r : ℝ)) := by
      apply Real.one_le_rpow (by norm_num)
      exact mul_nonneg (mul_nonneg (by norm_num) hgamma0) (Nat.cast_nonneg _)
    have hX : 1 ≤ ((r : ℝ) + 1) *
        (3 : ℝ) ^ (4 * M.gamma * (r : ℝ)) := by
      calc
        1 = 1 * 1 := by ring
        _ ≤ ((r : ℝ) + 1) * 1 := mul_le_mul_of_nonneg_right hr1 (by norm_num)
        _ ≤ ((r : ℝ) + 1) *
            (3 : ℝ) ^ (4 * M.gamma * (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hpowR1 (by positivity)
    calc
      _ ≤ 50000 * ((r : ℝ) + 1) *
          (3 : ℝ) ^ (4 * M.gamma * (r : ℝ)) + 1 := by
        linarith [hfCap]
      _ ≤ 50000 * ((r : ℝ) + 1) *
          (3 : ℝ) ^ (4 * M.gamma * (r : ℝ)) +
            ((r : ℝ) + 1) * (3 : ℝ) ^ (4 * M.gamma * (r : ℝ)) :=
        by linarith [hX]
      _ = 50001 * ((r : ℝ) + 1) *
          (3 : ℝ) ^ (4 * M.gamma * (r : ℝ)) := by ring
  have hC2f : C ^ 2 * (3 : ℝ) ^ (4 * M.gamma * (r : ℝ)) =
      (3 : ℝ) ^ (8 * M.gamma * (r : ℝ)) := by
    change ((3 : ℝ) ^ (2 * M.gamma * ((s : ℝ) - 1))) ^ 2 *
      (3 : ℝ) ^ (4 * M.gamma * (r : ℝ)) = _
    rw [show (s : ℝ) - 1 = (r : ℝ) by exact_mod_cast hsr]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)
      (2 * M.gamma * (r : ℝ)) 2]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hcapFormula : inSourceOldEnergyCap M h m r =
      v * C * (2 * b + 2 * kappa * b * fCap + C * muR * b ^ 2 * fCap) := by
    rfl
  calc
    inSourceOldEnergyCap M h m r =
        v * C * (2 * b + 2 * kappa * b * fCap + C * muR * b ^ 2 * fCap) :=
      hcapFormula
    _ ≤ v * C * (52260 * C * (fCap + 1)) :=
      mul_le_mul_of_nonneg_left hinner (mul_nonneg hv0 hC0)
    _ ≤ v * C * (52260 * C *
          (50001 * ((r : ℝ) + 1) * (3 : ℝ) ^ (4 * M.gamma * (r : ℝ)))) := by
      gcongr
    _ = 2613052260 * v * ((r : ℝ) + 1) *
          (C ^ 2 * (3 : ℝ) ^ (4 * M.gamma * (r : ℝ))) := by ring
    _ = 2613052260 * v * ((r : ℝ) + 1) *
          (3 : ℝ) ^ (8 * M.gamma * (r : ℝ)) := by rw [hC2f]
    _ ≤ 3000000000 * v * ((r : ℝ) + 1) *
          (3 : ℝ) ^ (8 * M.gamma * (r : ℝ)) := by
      have hrnonneg : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.zero_le r
      have hrplus0 : 0 ≤ (r : ℝ) + 1 := add_nonneg hrnonneg (by norm_num)
      have hpow0 : 0 ≤ (3 : ℝ) ^ (8 * M.gamma * (r : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      have hfactor : 0 ≤ v * ((r : ℝ) + 1) *
          (3 : ℝ) ^ (8 * M.gamma * (r : ℝ)) :=
        mul_nonneg (mul_nonneg hv0 hrplus0) hpow0
      calc
        _ = 2613052260 *
            (v * ((r : ℝ) + 1) * (3 : ℝ) ^ (8 * M.gamma * (r : ℝ))) := by ring
        _ ≤ 3000000000 *
            (v * ((r : ℝ) + 1) * (3 : ℝ) ^ (8 * M.gamma * (r : ℝ))) :=
          mul_le_mul_of_nonneg_right (by norm_num) hfactor
        _ = _ := by ring
    _ = 3000000000 *
          ((q3ModelAmplitude M h (m + 1)) ^ 2 /
            (Annealed.sigmaBar M m : ℝ) ^ 2) *
          ((r : ℝ) + 1) * (3 : ℝ) ^ (8 * M.gamma * (r : ℝ)) := by
      have hqs : q + (s : ℤ) = m + 1 := by dsimp [q, s]; omega
      simp only [v, hqs]

private theorem in_source_poly_geometric_summable
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun r : ℕ => ((r : ℝ) + 1) * q ^ r) := by
  have hqnorm : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq0]; exact hq1
  have hpoly : Summable (fun r : ℕ => (r : ℝ) * q ^ r) := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hqnorm :
        Summable (fun r : ℕ => (r : ℝ) ^ 1 * q ^ r))
  have hgeo : Summable (fun r : ℕ => q ^ r) :=
    summable_geometric_of_lt_one hq0 hq1
  have hsplit : (fun r : ℕ => ((r : ℝ) + 1) * q ^ r) =
      fun (r : ℕ) => (r : ℝ) * q ^ r + q ^ r := by
    funext r
    ring
  rw [hsplit]
  exact hpoly.add hgeo

theorem in_source_actual_weighted_old_energy_cap_summable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j) :
    Summable (fun r : ℕ =>
      inSourceOldEnergyHistoryWeight M r * inSourceOldEnergyCap M h m r) := by
  let q : ℝ := (Scalar.inverseHistoryDiscount ^ 2) *
    (3 : ℝ) ^ (10 * M.gamma)
  let A : ℝ := (1 - Scalar.inverseHistoryDiscount ^ 2) *
    (3683 / 2500 : ℝ) * 3000000000 *
      ((q3ModelAmplitude M h (m + 1)) ^ 2 /
        (Annealed.sigmaBar M m : ℝ) ^ 2)
  have hα := Scalar.inverse_history_discount_range
  have hαsq : Scalar.inverseHistoryDiscount ^ 2 ≤ 1 := by
    have hmul := mul_le_mul hα.2.le hα.2.le hα.1.le (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hγsmall : M.gamma ≤ (17 / 50000 : ℝ) := by
    simpa [gammaZero] using hg
  have h10γ : 10 * M.gamma ≤ (1 / 4 : ℝ) := by nlinarith
  have hpow : (3 : ℝ) ^ (10 * M.gamma) ≤ (3 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h10γ
  have hαproduct : Scalar.inverseHistoryDiscount ^ 2 *
      (3 : ℝ) ^ (1 / 4 : ℝ) = Scalar.inverseHistoryDiscount := by
    rw [Scalar.inverse_history_discount_eq]
    have hb : (3 : ℝ) ^ (1 / 4 : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos (by norm_num) _).ne'
    field_simp [hb]
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    calc
      q ≤ Scalar.inverseHistoryDiscount := by
        dsimp [q]
        exact le_trans
          (mul_le_mul_of_nonneg_left hpow (sq_nonneg Scalar.inverseHistoryDiscount))
          (le_of_eq hαproduct)
      _ < 1 := hα.2
  have hseries := in_source_poly_geometric_summable hq0 hq1
  have hmajorant : Summable (fun r : ℕ => A * ((r : ℝ) + 1) * q ^ r) := by
    simpa [mul_assoc] using hseries.mul_left A
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have hrem0 : 0 ≤ 1 - Scalar.inverseHistoryDiscount ^ 2 := by linarith
    have hσ : 0 < (Annealed.sigmaBar M m : ℝ) :=
      (Annealed.sigmaBar_characterization M m).1
    positivity
  have hcapNonneg : ∀ r : ℕ, 0 ≤ inSourceOldEnergyCap M h m r := by
    intro r
    exact (in_source_actual_generator_old_energy M h hM hg m hpast r 0
      ⟨le_rfl, by norm_num⟩).2
  have hfactor (r : ℕ) :
      Scalar.inverseHistoryDiscount ^ (2 * r) *
        (3 : ℝ) ^ (2 * M.gamma * (r : ℝ)) *
          (3 : ℝ) ^ (8 * M.gamma * (r : ℝ)) = q ^ r := by
    have h2 := Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)
      (2 * M.gamma) r
    have h8 := Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)
      (8 * M.gamma) r
    have hprod : ((3 : ℝ) ^ (2 * M.gamma)) ^ r *
        ((3 : ℝ) ^ (8 * M.gamma)) ^ r =
          ((3 : ℝ) ^ (10 * M.gamma)) ^ r := by
      rw [← mul_pow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      rw [show 2 * M.gamma + 8 * M.gamma = 10 * M.gamma by ring]
    dsimp [q]
    rw [pow_mul, h2, h8, mul_assoc, hprod, ← mul_pow]
  have hmajorize (r : ℕ) :
      inSourceOldEnergyHistoryWeight M r * inSourceOldEnergyCap M h m r ≤
        A * ((r : ℝ) + 1) * q ^ r := by
    have hw := in_source_old_energy_history_weight_nonneg' M r
    have hdepth := in_source_old_energy_cap_depth_envelope M h m r hg
    calc
      _ ≤ inSourceOldEnergyHistoryWeight M r *
          (3000000000 * ((q3ModelAmplitude M h (m + 1)) ^ 2 /
            (Annealed.sigmaBar M m : ℝ) ^ 2) * ((r : ℝ) + 1) *
            (3 : ℝ) ^ (8 * M.gamma * (r : ℝ))) :=
        mul_le_mul_of_nonneg_left hdepth hw
      _ = A * ((r : ℝ) + 1) * q ^ r := by
        change ((1 - Scalar.inverseHistoryDiscount ^ 2) *
            Scalar.inverseHistoryDiscount ^ (2 * r) * (3683 / 2500 : ℝ) *
            (3 : ℝ) ^ (2 * M.gamma * (r : ℝ))) *
          (3000000000 * ((q3ModelAmplitude M h (m + 1)) ^ 2 /
            (Annealed.sigmaBar M m : ℝ) ^ 2) * ((r : ℝ) + 1) *
            (3 : ℝ) ^ (8 * M.gamma * (r : ℝ))) = _
        calc
          _ = (1 - Scalar.inverseHistoryDiscount ^ 2) * (3683 / 2500 : ℝ) *
              3000000000 *
              ((q3ModelAmplitude M h (m + 1)) ^ 2 /
                (Annealed.sigmaBar M m : ℝ) ^ 2) * ((r : ℝ) + 1) *
              (Scalar.inverseHistoryDiscount ^ (2 * r) *
                (3 : ℝ) ^ (2 * M.gamma * (r : ℝ)) *
                (3 : ℝ) ^ (8 * M.gamma * (r : ℝ))) := by ring
          _ = A * ((r : ℝ) + 1) * q ^ r := by
            rw [hfactor]
  have hcapSummable : Summable (fun r : ℕ =>
      inSourceOldEnergyHistoryWeight M r * inSourceOldEnergyCap M h m r) :=
    Summable.of_nonneg_of_le
      (fun r => mul_nonneg (in_source_old_energy_history_weight_nonneg' M r)
        (hcapNonneg r)) hmajorize hmajorant
  exact hcapSummable

/-- The complete discounted OLD source-energy slope series is summable in the
actual cutoff law and true frame, and its sum is bounded by the corresponding
sum of the explicit per-depth generator caps. This is the monotone-series
passage from the finite-depth energy estimates. -/
theorem in_source_actual_complete_old_energy_sum
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j) :
    Summable (fun r : ℕ =>
      inSourceOldEnergyHistoryWeight M r * inSourceMeanSlopeActual M h m r) ∧
      (∑' r : ℕ, inSourceOldEnergyHistoryWeight M r *
        inSourceMeanSlopeActual M h m r) ≤
      ∑' r : ℕ, inSourceOldEnergyHistoryWeight M r *
        inSourceOldEnergyCap M h m r := by
  have hcap := in_source_actual_weighted_old_energy_cap_summable M h hM hg m hpast
  have hterm (r : ℕ) :
      inSourceOldEnergyHistoryWeight M r * inSourceMeanSlopeActual M h m r ≤
        inSourceOldEnergyHistoryWeight M r * inSourceOldEnergyCap M h m r :=
    mul_le_mul_of_nonneg_left
      (in_source_actual_slope_old_energy_bound M h hM hg m hpast r)
      (in_source_old_energy_history_weight_nonneg' M r)
  have hactual := Summable.of_nonneg_of_le
    (fun r => mul_nonneg (in_source_old_energy_history_weight_nonneg' M r)
      (by
        change 0 ≤ inSourceMeanSlopeActual M h m r
        unfold inSourceMeanSlopeActual
        exact le_max_left 0 _)) hterm hcap
  exact ⟨hactual, hactual.tsum_le_tsum hterm hcap⟩

/-- The actual cutoff-law source mean has a quantitative one-shell transport
bound from its completed OLD endpoint. The slope is the explicit OLD energy
cap proved from strict-past states, rather than an assumed cap or a panel
supremum premise. The observable keeps coefficient `M.nu` and the fixed true
frame `sigmaBar M m` throughout. -/
theorem in_source_actual_mean_transport_old_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j)
    (r : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    inSourceMeanActual M m r t ≤
      (nativeCompletedSourceMean M m r).toReal +
        t * inSourceOldEnergyCap M h m r ∧
      0 ≤ inSourceOldEnergyCap M h m r := by
  obtain ⟨hpanel, _⟩ := in_source_actual_heat_panel M h hM m r
  have htransport : inSourceMeanActual M m r t ≤
      inSourceMeanActual M m r 0 + t * inSourceOldEnergyCap M h m r :=
    in_source_linear_transport_of_panel hpanel _
      (fun s hs => (in_source_actual_generator_old_energy
        M h hM hg m hpast r s hs).1) ht
  have hendpoint := in_source_mean_old_endpoint M m r
  have hcap := (in_source_actual_generator_old_energy
    M h hM hg m hpast r 0 (by norm_num)).2
  refine ⟨?_, hcap⟩
  rw [hendpoint] at htransport
  exact htransport

end

end ASDExplicitGamma.Inverse

end

module

public import ASDExplicitGamma.Main.EnvelopeHProfileArithmetic
public import ASDExplicitGamma.Inverse.RawShellFixedFrameGeneralP20
public import ASDExplicitGamma.Inverse.SourceVarianceClock
public import ASDExplicitGamma.Cold.NativeCellTrace
public import ASDExplicitGamma.Cold.NativeStrongHistory
public import ASDExplicitGamma.Cold.NativeThetaScaling

/-! The fixed-OLD-frame raw-shell p=20 generator discharges the exact
depthwise generator premise in the MA-ENVELOPE-H profile assembly. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Cold

/-- The exact deterministic coefficient in the fixed-old-frame p=20 row,
at cell depth `j` below the five-level OLD parent. -/
noncomputable def mainRawShellOldFrameP20Control
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (j : ℕ) : ℝ :=
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let s : ℕ := 6 + j
  let Q := originCube 2 q
  let σ : ℝ := Annealed.sigmaBar M m
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
  let fCap := rawTraceOldFrameP20FullResponseCap M.gamma s
  v * ((78 + 76 * κ) * (C * (3683 / 2500 : ℝ)) +
    2 * κ * (C * (3683 / 2500 : ℝ)) * fCap +
    (μR + 38 * (κB ^ 2 + κ)) * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap)

/-- For every cell depth `q=m-5-j`, the p=20 derivative row is supplied by
the actual raw-shell producer, with the frame held at `sigmaBar M m` and
the inserted shell at `m+1`. No abstract generator estimate is assumed. -/
theorem main_rawShell_fixed_old_frame_p20_hGenerator
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) (j : ℕ) :
    ∀ t ∈ Ioo (0 : ℝ) 1,
      deriv (modelTracePowerHeatAverage
        (m - ((5 + j : ℕ) : ℤ)) M m 20) t ≤
        20 * modelTracePowerHeatAverage
          (m - ((5 + j : ℕ) : ℤ)) M m 20 t ^ ((19 : ℝ) / 20) *
          mainRawShellOldFrameP20Control M h m j := by
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let s : ℕ := 6 + j
  have hqs : q + (s : ℤ) = m + 1 := by
    dsimp [q, s]
    omega
  have hs : 6 ≤ s := by dsimp [s]; omega
  have hrow := raw_shell_q3_p20_generator_derivative_fixed_old_frame
    M h hM hg q m s hqs hs hpast
  intro t ht
  simpa [mainRawShellOldFrameP20Control, q, s, hqs] using hrow t ht

/-- The actual OLD-frame four-load trace at every depth has finite twentieth
moment at every insertion time. The fixed-frame completed-response bank gives
an order-128 cap, which embeds into L20 on the probability law. -/
theorem main_rawDepthFourLoadTrace_memLp_twenty_fixed_old_frame
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (j : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    MemLp
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) t)
      20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  classical
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let s : ℕ := 6 + j
  let Q := originCube 2 q
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let T : Cutoff.CutoffSample 2 → ℝ :=
    rawDepthFourLoadTrace M m q t
  let F : Cutoff.CutoffSample 2 → ℝ := fun ω => T ω + 4
  have hqs : q + (s : ℤ) = m + 1 := by dsimp [q, s]; omega
  have hs : 6 ≤ s := by dsimp [s]; omega
  have hcoeffModel (ω : Cutoff.CutoffSample 2) :
      attenuatedCoefficient M m (m + 1) (fun _ => Real.sqrt t) ω =
        (Model.partialInsertedCoefficient M m t ω).toFun := by
    have hcoeff := full_response_coefficient_partial M (m + 1) t ω
    have hcoeff' : attenuatedCoefficient M m (m + 1)
        (fun _ => Real.sqrt t) ω = fun x =>
          Cutoff.coefficientCutoff M.nu m ω x +
            Real.sqrt t • (ω.val (m + 1)).forgetShell x := by
      simpa only [show m + 1 - 1 = m by omega] using hcoeff
    funext x
    rw [hcoeff']
    simp [Model.partialInsertedCoefficient]
  have hF_eq : F = fun ω =>
      rootTraceObservable M Q m (m + 1) m (fun _ => Real.sqrt t) ω := by
    funext ω
    rw [root_trace_observable_eq_trace_defect]
    change traceDefect (cubeSet Q)
        (Model.partialInsertedCoefficient M m t ω).toFun
        (Annealed.sigmaBar M m : ℝ) + 4 =
      traceDefect (cubeSet Q)
        (attenuatedCoefficient M m (m + 1) (fun _ => Real.sqrt t) ω)
        (Annealed.sigmaBar M m : ℝ) + 4
    rw [← hcoeffModel ω]
  have hQ : Q.scale = q := by rfl
  have hN : Q.scale - 1 ≤ (m + 1 : ℤ) := by
    rw [hQ]
    dsimp [q]
    omega
  have hm : Q.scale - 342 ≤ m := by
    rw [hQ]
    dsimp [q]
    omega
  have hmN : m ≤ m + 1 := by omega
  have hbank := full_response_completed_bank128 M h hM hg Q
    (m + 1) m m hN hm hmN
    (fun n hn => hpast n (by omega)) (fun _ => Real.sqrt t)
    (by
      intro k hk
      have hk' := Finset.mem_Ioc.mp hk
      have htop : k = m + 1 := by omega
      subst k
      exact ⟨Real.sqrt_nonneg t, (Real.sqrt_le_one).mpr ht.2⟩)
  have hDInt : m + 1 - q + 1 = ((s + 1 : ℕ) : ℤ) := by
    dsimp [q, s]
    omega
  have hD : ((m + 1 : ℤ) : ℝ) - (Q.scale : ℝ) + 1 =
      ((s + 1 : ℕ) : ℝ) := by
    rw [hQ]
    exact_mod_cast hDInt
  have hgapInt : m - q + 1 = (s : ℤ) := by
    dsimp [q, s]
    omega
  have hgap : |((m - q + 1 : ℤ) : ℝ)| = (s : ℝ) := by
    rw [show ((m - q + 1 : ℤ) : ℝ) = (s : ℝ) by exact_mod_cast hgapInt]
    exact abs_of_nonneg (by positivity)
  have hgapQ : |((m - Q.scale + 1 : ℤ) : ℝ)| = (s : ℝ) := by
    rw [hQ]
    exact hgap
  let capBase : ℝ :=
    ((2018618 : ℝ) / 1000000 + M.gamma *
      (32474 * ((s + 1 : ℕ) : ℝ) + 11483216)) *
        (3 : ℝ) ^ (2 * M.gamma * ((s + 1 : ℕ) : ℝ) + 2 * M.gamma * (s : ℝ))
  dsimp only at hbank
  rw [hD, hgapQ] at hbank
  have hbank' : eLpNorm
      (fun ω => rootTraceObservable M Q m (m + 1) m
        (fun _ => Real.sqrt t) ω / 4)
      (ENNReal.ofReal 128) μ ≤ ENNReal.ofReal capBase := by
    simpa only [capBase] using hbank
  have hFdiv_eq : (fun ω => F ω / 4) = fun ω =>
      rootTraceObservable M Q m (m + 1) m (fun _ => Real.sqrt t) ω / 4 := by
    funext ω
    rw [hF_eq]
  rw [← hFdiv_eq] at hbank'
  have hscale : F = (4 : ℝ) • (fun ω => F ω / 4) := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hnorm_eq : eLpNorm F (ENNReal.ofReal 128) μ =
      ENNReal.ofReal 4 * eLpNorm (fun ω => F ω / 4)
        (ENNReal.ofReal 128) μ := by
    calc
      eLpNorm F (ENNReal.ofReal 128) μ =
          eLpNorm ((4 : ℝ) • (fun ω => F ω / 4))
            (ENNReal.ofReal 128) μ :=
        congrArg (fun G => eLpNorm G (ENNReal.ofReal 128) μ) hscale
      _ = ENNReal.ofReal 4 * eLpNorm (fun ω => F ω / 4)
          (ENNReal.ofReal 128) μ := by
        rw [eLpNorm_const_smul,
          Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 4)]
  have hFtop : eLpNorm F (ENNReal.ofReal 128) μ < ⊤ := by
    calc
      eLpNorm F (ENNReal.ofReal 128) μ =
          ENNReal.ofReal 4 * eLpNorm (fun ω => F ω / 4)
            (ENNReal.ofReal 128) μ := hnorm_eq
      _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal capBase :=
        by gcongr
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hFmeas : AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top hFtop.ne
  have hF20mono := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := F) (μ := μ)
    (show ENNReal.ofReal (20 : ℝ) ≤ ENNReal.ofReal (128 : ℝ) by norm_num)
    hFmeas
  have hF20 : eLpNorm F (ENNReal.ofReal 20) μ ≤
      eLpNorm F (ENNReal.ofReal 128) μ := by
    simpa only [measure_univ, ENNReal.one_rpow, mul_one] using hF20mono
  have hFmem : MemLp F (ENNReal.ofReal 20) μ :=
    memLp_iff.mpr (hF20.trans_lt hFtop)
  have hsub : MemLp (fun ω => F ω - 4) (ENNReal.ofReal 20) μ :=
    hFmem.sub (memLp_const (μ := μ) (p := ENNReal.ofReal 20) (4 : ℝ))
  have hsubEq : (fun ω => F ω - 4) = T := by
    funext ω
    simp [F]
  rw [hsubEq] at hsub
  rw [show (20 : ENNReal) = ENNReal.ofReal (20 : ℝ) by norm_num]
  simpa only [T, q] using hsub

/-- At the source cell scale, the two geometric ratios are exactly the
covariance rows used by the deterministic p=20 control. -/
theorem main_rawShell_fixed_old_frame_p20_source_scales
    (q : ℤ) (s : ℕ) (hs : 6 ≤ s) :
    cubeScaleFactor (originCube 2 q) / (q3ModelLength (q + (s : ℤ))).1 =
        pureFluxCovarianceRho 0 (s - 1) ∧
      diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth s) /
        (q3ModelLength (q + (s : ℤ))).1 =
        pureFluxCovarianceDelta 0 (s - 1) := by
  have hs1 : 1 ≤ s := by omega
  exact ⟨pureFlux_bank_source_rho q s hs1,
    pureFlux_bank_source_delta q s hs1⟩

/-- The fixed-old-frame p=20 coefficients stay uniformly inside the source
caps on the actual six-generation-and-deeper mesh. -/
theorem main_rawShell_fixed_old_frame_p20_remainder_caps
    (q : ℤ) (s : ℕ) (hs : 6 ≤ s) :
    let ρ := cubeScaleFactor (originCube 2 q) /
      (q3ModelLength (q + (s : ℤ))).1
    let δ := diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth s) /
      (q3ModelLength (q + (s : ℤ))).1
    let A := rawTraceRemainderA (pureFluxCovarianceRho 0 (s - 1))
      (pureFluxCovarianceDelta 0 (s - 1))
    let B := rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
      (pureFluxCovarianceDelta 0 (s - 1))
    let κ := rawTraceRemainderKappaF ρ δ
    let κB := rawTraceRemainderB ρ δ
    let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0 A B
    0 ≤ ρ ∧ ρ ≤ 1 / 243 ∧ 0 ≤ δ ∧ δ ≤ 1 / 243 ∧
      0 ≤ A ∧ A ≤ 1 ∧ 0 ≤ B ∧ B ≤ 1 ∧
      0 ≤ κ ∧ κ ≤ 1 ∧ 0 ≤ κB ∧ κB ≤ 1 ∧ 0 ≤ μR ∧ μR ≤ 10 := by
  dsimp only
  let ρ := cubeScaleFactor (originCube 2 q) /
    (q3ModelLength (q + (s : ℤ))).1
  let δ := diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth s) /
    (q3ModelLength (q + (s : ℤ))).1
  let A := rawTraceRemainderA (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let B := rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let κ := rawTraceRemainderKappaF ρ δ
  let κB := rawTraceRemainderB ρ δ
  let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0 A B
  have hscale := main_rawShell_fixed_old_frame_p20_source_scales q s hs
  have hρeq : ρ = pureFluxCovarianceRho 0 (s - 1) := by
    simpa only [ρ] using hscale.1
  have hδeq : δ = pureFluxCovarianceDelta 0 (s - 1) := by
    simpa only [δ] using hscale.2
  have hρbank : 0 ≤ pureFluxCovarianceRho 0 (s - 1) :=
    (pureFlux_covariance_rho_pos 0 (s - 1)).le
  have hδbank := pureFlux_covariance_delta_bounds 0 (s - 1)
  have hpow : (1 / 3 : ℝ) ^ s ≤ (1 / 3 : ℝ) ^ 6 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  have hρbankEq : pureFluxCovarianceRho 0 (s - 1) = (1 / 3 : ℝ) ^ s := by
    unfold pureFluxCovarianceRho
    congr 1
    omega
  have hρ : 0 ≤ ρ := by rw [hρeq]; exact hρbank
  have hρbankle : pureFluxCovarianceRho 0 (s - 1) ≤ 1 / 243 := by
    rw [hρbankEq]
    calc
      _ ≤ (1 / 3 : ℝ) ^ 6 := hpow
      _ = 1 / 729 := by norm_num
      _ ≤ 1 / 243 := by norm_num
  have hρle : ρ ≤ 1 / 243 := by rw [hρeq]; exact hρbankle
  have hδ : 0 ≤ δ := by rw [hδeq]; exact hδbank.1
  have hδle : δ ≤ 1 / 243 := by
    rw [hδeq]
    exact hδbank.2.trans hρbankle
  have hρA : 0 ≤ pureFluxCovarianceRho 0 (s - 1) := hρbank
  have hδA : 0 ≤ pureFluxCovarianceDelta 0 (s - 1) := hδbank.1
  have hsqrtA0 : Real.sqrt (78 / 10 : ℝ) ≤ 3 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrtA1 : Real.sqrt (156 / 5 : ℝ) ≤ 6 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrtA2 : Real.sqrt (46488 / 25 : ℝ) ≤ 44 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrtB1 : Real.sqrt (78 / 5 : ℝ) ≤ 4 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrtB2 : Real.sqrt (23244 / 25 : ℝ) ≤ 31 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hA : 0 ≤ A ∧ A ≤ 1 := by
    constructor
    · dsimp [A]
      unfold rawTraceRemainderA
      positivity
    · dsimp [A]
      unfold rawTraceRemainderA
      have hρ' : pureFluxCovarianceRho 0 (s - 1) ≤ 1 / 243 := hρbankle
      have hδ' : pureFluxCovarianceDelta 0 (s - 1) ≤ 1 / 243 := hδbank.2.trans hρ'
      have hρsq : (pureFluxCovarianceRho 0 (s - 1)) ^ 2 ≤ (1 / 243 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hρA hρ' 2
      have hδsq : (pureFluxCovarianceDelta 0 (s - 1)) ^ 2 ≤ (1 / 243 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hδA hδ' 2
      calc
        _ ≤ 1.860 * 3 * (1 / 243) + 2.36412 * 6 * (1 / 243) +
            0.52288 * 44 * (1 / 243 : ℝ) ^ 2 := by
              gcongr
        _ ≤ 1 := by norm_num
  have hB : 0 ≤ B ∧ B ≤ 1 := by
    constructor
    · dsimp [B]
      unfold rawTraceRemainderB
      positivity
    · dsimp [B]
      unfold rawTraceRemainderB
      have hρ' : pureFluxCovarianceRho 0 (s - 1) ≤ 1 / 243 := hρbankle
      have hδ' : pureFluxCovarianceDelta 0 (s - 1) ≤ 1 / 243 := hδbank.2.trans hρ'
      have hρsq : (pureFluxCovarianceRho 0 (s - 1)) ^ 2 ≤ (1 / 243 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hρA hρ' 2
      have hδsq : (pureFluxCovarianceDelta 0 (s - 1)) ^ 2 ≤ (1 / 243 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hδA hδ' 2
      calc
        _ ≤ 1.860 * 3 * (1 / 243) + 2.36412 * 4 * (1 / 243) +
            0.52288 * 31 * (1 / 243 : ℝ) ^ 2 := by
              gcongr
        _ ≤ 1 := by norm_num
  have hsqrt2 : 1 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 2 := by
    constructor
    · nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    · exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hκ : 0 ≤ κ ∧ κ ≤ 1 := by
    constructor
    · dsimp [κ]
      unfold rawTraceRemainderKappaF
      positivity
    · dsimp [κ]
      unfold rawTraceRemainderKappaF
      have hρsq : ρ ^ 2 ≤ (1 / 243 : ℝ) ^ 2 := pow_le_pow_left₀ hρ hρle 2
      have hδsq : δ ^ 2 ≤ (1 / 243 : ℝ) ^ 2 := pow_le_pow_left₀ hδ hδle 2
      have hρδ : ρ * δ ≤ (1 / 243 : ℝ) ^ 2 := by
        calc
          ρ * δ ≤ (1 / 243 : ℝ) * δ := by
            exact mul_le_mul_of_nonneg_right hρle hδ
          _ ≤ (1 / 243 : ℝ) * (1 / 243 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hδle (by norm_num)
          _ = (1 / 243 : ℝ) ^ 2 := by ring
      have hInv : (Real.sqrt 2)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (by positivity : 0 < Real.sqrt 2)]
        exact hsqrt2.1
      have hcoef2 : (78 / 5 : ℝ) / Real.sqrt 2 ≤ 78 / 5 := by
        apply (div_le_iff₀ (by positivity : 0 < Real.sqrt 2)).2
        nlinarith [hsqrt2.1]
      have hterm1 : 1.860 * ((78 / 5 : ℝ) / 4) * ρ ^ 2 ≤
          1.860 * ((78 / 5 : ℝ) / 4) * (1 / 243 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hρsq (by positivity)
      have hterm2 : 2.36412 * ((78 / 5 : ℝ) / Real.sqrt 2) * ρ * δ ≤
          2.36412 * (78 / 5) * (1 / 243 : ℝ) ^ 2 := by
        calc
          _ = (2.36412 * ((78 / 5 : ℝ) / Real.sqrt 2)) * (ρ * δ) := by ring
          _ ≤ (2.36412 * ((78 / 5 : ℝ) / Real.sqrt 2)) *
              ((1 / 243 : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_left hρδ (by positivity)
          _ ≤ (2.36412 * (78 / 5)) * (1 / 243 : ℝ) ^ 2 := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hcoef2 (by norm_num)) (by positivity)
          _ = 2.36412 * (78 / 5) * (1 / 243 : ℝ) ^ 2 := by ring
      have hterm3 : 0.52288 * Real.sqrt 2 * (78 / 5 : ℝ) * δ ^ 2 ≤
          0.52288 * 2 * (78 / 5) * (1 / 243 : ℝ) ^ 2 := by
        calc
          _ = (0.52288 * Real.sqrt 2 * (78 / 5 : ℝ)) * δ ^ 2 := by ring
          _ ≤ (0.52288 * Real.sqrt 2 * (78 / 5 : ℝ)) *
              (1 / 243 : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_left hδsq (by positivity)
          _ ≤ (0.52288 * 2 * (78 / 5 : ℝ)) * (1 / 243 : ℝ) ^ 2 := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hsqrt2.2 (by norm_num))
                    (by norm_num : 0 ≤ (78 / 5 : ℝ))) (by positivity)
          _ = 0.52288 * 2 * (78 / 5) * (1 / 243 : ℝ) ^ 2 := by ring
      calc
        _ = 1.860 * ((78 / 5 : ℝ) / 4) * ρ ^ 2 +
            2.36412 * ((78 / 5 : ℝ) / Real.sqrt 2) * ρ * δ +
            0.52288 * Real.sqrt 2 * (78 / 5) * δ ^ 2 := by rfl
        _ ≤ 1.860 * ((78 / 5 : ℝ) / 4) * (1 / 243 : ℝ) ^ 2 +
            2.36412 * (78 / 5) * (1 / 243 : ℝ) ^ 2 +
            0.52288 * 2 * (78 / 5) * (1 / 243 : ℝ) ^ 2 := by linarith [hterm1, hterm2, hterm3]
        _ ≤ 1 := by norm_num
  have hκB : 0 ≤ κB ∧ κB ≤ 1 := by
    constructor
    · dsimp [κB]
      unfold rawTraceRemainderB
      positivity
    · dsimp [κB]
      unfold rawTraceRemainderB
      have hρ' : ρ ≤ 1 / 243 := hρle
      have hδ' : δ ≤ 1 / 243 := hδle
      have hρsq : ρ ^ 2 ≤ (1 / 243 : ℝ) ^ 2 := pow_le_pow_left₀ hρ hρ' 2
      have hδsq : δ ^ 2 ≤ (1 / 243 : ℝ) ^ 2 := pow_le_pow_left₀ hδ hδ' 2
      calc
        _ ≤ 1.860 * 3 * (1 / 243) + 2.36412 * 4 * (1 / 243) +
            0.52288 * 31 * (1 / 243 : ℝ) ^ 2 := by
              gcongr
        _ ≤ 1 := by norm_num
  have hmu : 0 ≤ μR ∧ μR ≤ 10 := by
    constructor
    · dsimp [μR]
      unfold rawTraceRemainderMu
      apply div_nonneg
      · have hH0 : 0 ≤ rawTraceRemainderH0 := by norm_num [rawTraceRemainderH0]
        have hD0 : 0 ≤ rawTraceRemainderD0 := by
          unfold rawTraceRemainderD0
          positivity
        positivity
      · norm_num
    · dsimp [μR]
      unfold rawTraceRemainderMu
      have hH0 : 0 ≤ rawTraceRemainderH0 ∧ rawTraceRemainderH0 ≤ 12 / 5 := by
        norm_num [rawTraceRemainderH0]
      have hD0 : 0 ≤ rawTraceRemainderD0 ∧ rawTraceRemainderD0 ≤ 4 := by
        constructor
        · unfold rawTraceRemainderD0
          unfold rawTraceRemainderH0
          positivity
        · unfold rawTraceRemainderD0
          have hsH : Real.sqrt rawTraceRemainderH0 ≤ 8 / 5 := by
            exact (Real.sqrt_le_iff).2 ⟨by norm_num [rawTraceRemainderH0],
              by norm_num [rawTraceRemainderH0]⟩
          nlinarith [hH0.2, hsH]
      have hrad : rawTraceRemainderH0 ^ 2 * A ^ 4 +
          4 * rawTraceRemainderD0 ^ 2 * A ^ 2 * B ^ 2 ≤ 81 := by
        have hA2 : A ^ 2 ≤ 1 :=
          (pow_le_pow_left₀ hA.1 hA.2 2).trans_eq (by norm_num)
        have hB2 : B ^ 2 ≤ 1 := by
          exact (pow_le_pow_left₀ hB.1 hB.2 2).trans_eq (by norm_num)
        have hA4 : A ^ 4 ≤ 1 := by
          exact (pow_le_pow_left₀ hA.1 hA.2 4).trans_eq (by norm_num)
        have hAB : A ^ 2 * B ^ 2 ≤ 1 := by
          calc
            _ ≤ 1 * B ^ 2 := mul_le_mul_of_nonneg_right hA2 (sq_nonneg B)
            _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hB2 (by norm_num)
            _ = 1 := by ring
        have hH02 : rawTraceRemainderH0 ^ 2 ≤ (12 / 5 : ℝ) ^ 2 :=
          pow_le_pow_left₀ hH0.1 hH0.2 2
        have hD02 : rawTraceRemainderD0 ^ 2 ≤ (4 : ℝ) ^ 2 :=
          pow_le_pow_left₀ hD0.1 hD0.2 2
        have hfirst : rawTraceRemainderH0 ^ 2 * A ^ 4 ≤ (12 / 5 : ℝ) ^ 2 := by
          calc
            _ ≤ rawTraceRemainderH0 ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hA4 (sq_nonneg rawTraceRemainderH0)
            _ = rawTraceRemainderH0 ^ 2 := by ring
            _ ≤ (12 / 5 : ℝ) ^ 2 := hH02
        have hsecond : 4 * rawTraceRemainderD0 ^ 2 * A ^ 2 * B ^ 2 ≤
            4 * (4 : ℝ) ^ 2 := by
          calc
            _ = (4 * rawTraceRemainderD0 ^ 2) * (A ^ 2 * B ^ 2) := by ring
            _ ≤ (4 * rawTraceRemainderD0 ^ 2) * 1 :=
              mul_le_mul_of_nonneg_left hAB (by positivity)
            _ = 4 * rawTraceRemainderD0 ^ 2 := by ring
            _ ≤ 4 * (4 : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left hD02 (by norm_num)
        calc
          _ ≤ (12 / 5 : ℝ) ^ 2 + 4 * (4 : ℝ) ^ 2 := add_le_add hfirst hsecond
          _ ≤ 81 := by norm_num
      have hsqrt : Real.sqrt (rawTraceRemainderH0 ^ 2 * A ^ 4 +
          4 * rawTraceRemainderD0 ^ 2 * A ^ 2 * B ^ 2) ≤ 9 := by
        exact (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith [hrad]⟩
      have hA2 : A ^ 2 ≤ 1 :=
        (pow_le_pow_left₀ hA.1 hA.2 2).trans_eq (by norm_num)
      have hdiag : rawTraceRemainderH0 * A ^ 2 ≤ 12 / 5 := by
        calc
          _ ≤ rawTraceRemainderH0 * 1 :=
            mul_le_mul_of_nonneg_left hA2 hH0.1
          _ ≤ 12 / 5 := by simpa only [mul_one] using hH0.2
      nlinarith [hdiag, hsqrt]
  refine ⟨hρ, hρle, hδ, hδle, hA.1, hA.2, hB.1, hB.2,
    hκ.1, hκ.2, hκB.1, hκB.2, hmu.1, hmu.2⟩

/-- The exact fixed-frame control is bounded by one product of its local clock
and full-response cap. The factor `428` follows from the proved source
remainder caps, and is used only to establish summability. -/
theorem main_rawShell_fixed_old_frame_p20_control_coarse_bound
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (j : ℕ) :
    let q : ℤ := m - ((5 + j : ℕ) : ℤ)
    let s : ℕ := 6 + j
    let J := q + (s : ℤ)
    let κ := rawTraceRemainderKappaF
      (cubeScaleFactor (originCube 2 q) / (q3ModelLength J).1)
      (diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth s) /
        (q3ModelLength J).1)
    let κB := rawTraceRemainderB
      (cubeScaleFactor (originCube 2 q) / (q3ModelLength J).1)
      (diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth s) /
        (q3ModelLength J).1)
    let A := rawTraceRemainderA (pureFluxCovarianceRho 0 (s - 1))
      (pureFluxCovarianceDelta 0 (s - 1))
    let B := rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
      (pureFluxCovarianceDelta 0 (s - 1))
    let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0 A B
    let v := (q3ModelAmplitude M h J) ^ 2 /
      (Annealed.sigmaBar M m : ℝ) ^ 2
    let C := rawTraceOldFrameP20LocalClock M.gamma s
    let fCap := rawTraceOldFrameP20FullResponseCap M.gamma s
    mainRawShellOldFrameP20Control M h m j ≤ 428 * v * C ^ 2 * fCap := by
  dsimp only
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let s : ℕ := 6 + j
  let J := q + (s : ℤ)
  let ρ := cubeScaleFactor (originCube 2 q) / (q3ModelLength J).1
  let δ := diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth s) /
    (q3ModelLength J).1
  let κ := rawTraceRemainderKappaF ρ δ
  let κB := rawTraceRemainderB ρ δ
  let A := rawTraceRemainderA (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let B := rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0 A B
  let v := (q3ModelAmplitude M h J) ^ 2 /
    (Annealed.sigmaBar M m : ℝ) ^ 2
  let C := rawTraceOldFrameP20LocalClock M.gamma s
  let fCap := rawTraceOldFrameP20FullResponseCap M.gamma s
  have hs : 6 ≤ s := by dsimp [s]; omega
  have hcaps := main_rawShell_fixed_old_frame_p20_remainder_caps q s hs
  rcases hcaps with ⟨_, _, _, _, _, _, _, _, hκ0, hκ1,
    hκB0, hκB1, hμR0, hμR1⟩
  have hκnonneg : 0 ≤ κ := by simpa [κ, ρ, δ, J] using hκ0
  have hκcap : κ ≤ 1 := by simpa [κ, ρ, δ, J] using hκ1
  have hκBnonneg : 0 ≤ κB := by simpa [κB, ρ, δ, J] using hκB0
  have hκBcap : κB ≤ 1 := by simpa [κB, ρ, δ, J] using hκB1
  have hμRnonneg : 0 ≤ μR := by simpa [μR, A, B] using hμR0
  have hμRcap : μR ≤ 10 := by simpa [μR, A, B] using hμR1
  have hβ : (3683 / 2500 : ℝ) ≤ 3 / 2 := by norm_num
  have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hCge : 1 ≤ C := by
    dsimp [C, rawTraceOldFrameP20LocalClock]
    apply Real.one_le_rpow (by norm_num)
    have hs' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (show 1 ≤ s by omega)
    positivity
  have hfCapge : 1 ≤ fCap := by
    dsimp [fCap, rawTraceOldFrameP20FullResponseCap]
    have hpow : 1 ≤ (3 : ℝ) ^
        (2 * M.gamma * ((s + 1 : ℕ) : ℝ) + 2 * M.gamma * (s : ℝ)) := by
      apply Real.one_le_rpow (by norm_num)
      positivity
    have hfac : 1 ≤ 4 * ((2018618 : ℝ) / 1000000 + M.gamma *
        ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216)) := by
      have : (0 : ℝ) ≤ M.gamma *
          ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216) := by positivity
      nlinarith [this]
    have hfac0 : 0 ≤ 4 * ((2018618 : ℝ) / 1000000 + M.gamma *
        ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216)) := le_trans (by norm_num) hfac
    calc
      1 = 1 * 1 := by ring
      _ ≤ (4 * ((2018618 : ℝ) / 1000000 + M.gamma *
          ((32474 : ℝ) * ((s + 1 : ℕ) : ℝ) + 11483216))) *
          (3 : ℝ) ^ (2 * M.gamma * ((s + 1 : ℕ) : ℝ) + 2 * M.gamma * (s : ℝ)) :=
        mul_le_mul hfac hpow (by norm_num) hfac0
  have hC0 : 0 ≤ C := le_trans (by norm_num) hCge
  have hfCap0 : 0 ≤ fCap := le_trans (by norm_num) hfCapge
  have hv : 0 ≤ v := by
    dsimp [v]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  change v * ((78 + 76 * κ) * (C * (3683 / 2500 : ℝ)) +
      2 * κ * (C * (3683 / 2500 : ℝ)) * fCap +
      (μR + 38 * (κB ^ 2 + κ)) * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap) ≤
    428 * v * C ^ 2 * fCap
  have hterm1 : (78 + 76 * κ) * (C * (3683 / 2500 : ℝ)) ≤ 231 * C := by
    have hκ' : 78 + 76 * κ ≤ 154 := by nlinarith [hκcap]
    calc
      _ ≤ 154 * (C * (3683 / 2500 : ℝ)) :=
        mul_le_mul_of_nonneg_right hκ' (mul_nonneg hC0 (by norm_num))
      _ ≤ 154 * (C * (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hβ hC0) (by norm_num)
      _ = 231 * C := by ring
  have hterm2 : 2 * κ * (C * (3683 / 2500 : ℝ)) * fCap ≤ 3 * C * fCap := by
    have hκ' : 2 * κ ≤ 2 := by nlinarith [hκcap, hκnonneg]
    calc
      _ ≤ 2 * (C * (3683 / 2500 : ℝ)) * fCap :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hκ' (mul_nonneg hC0 (by norm_num))) hfCap0
      _ ≤ 2 * (C * (3 / 2 : ℝ)) * fCap :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hβ hC0) (by norm_num)) hfCap0
      _ = 3 * C * fCap := by ring
  have hterm3 : (μR + 38 * (κB ^ 2 + κ)) *
      (C * (3683 / 2500 : ℝ)) ^ 2 * fCap ≤ 194 * C ^ 2 * fCap := by
    have hinner : μR + 38 * (κB ^ 2 + κ) ≤ 86 := by
      nlinarith [hμRcap, hκcap, hκBcap, hκnonneg, hκBnonneg]
    have hCβ : C * (3683 / 2500 : ℝ) ≤ C * (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hβ hC0
    have hCβ0 : 0 ≤ C * (3683 / 2500 : ℝ) := by positivity
    have hCβ'0 : 0 ≤ C * (3 / 2 : ℝ) := by positivity
    have hsquare : (C * (3683 / 2500 : ℝ)) ^ 2 ≤
        (C * (3 / 2 : ℝ)) ^ 2 := (sq_le_sq₀ hCβ0 hCβ'0).mpr hCβ
    calc
      _ ≤ 86 * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hinner (sq_nonneg _)) hfCap0
      _ ≤ 86 * (C ^ 2 * (3 / 2 : ℝ) ^ 2) * fCap := by
        apply mul_le_mul_of_nonneg_right
        · calc
            86 * (C * (3683 / 2500 : ℝ)) ^ 2 ≤
                86 * (C * (3 / 2 : ℝ)) ^ 2 :=
              mul_le_mul_of_nonneg_left hsquare (by norm_num)
            _ = 86 * (C ^ 2 * (3 / 2 : ℝ) ^ 2) := by ring
        · exact hfCap0
      _ ≤ 194 * C ^ 2 * fCap := by
        have hconst : (86 : ℝ) * (3 / 2 : ℝ) ^ 2 ≤ 194 := by norm_num
        calc
          86 * (C ^ 2 * (3 / 2 : ℝ) ^ 2) * fCap =
              (86 * (3 / 2 : ℝ) ^ 2) * (C ^ 2 * fCap) := by ring
          _ ≤ 194 * (C ^ 2 * fCap) :=
            mul_le_mul_of_nonneg_right hconst (mul_nonneg (sq_nonneg _) hfCap0)
          _ = 194 * C ^ 2 * fCap := by ring
  have hinside : (78 + 76 * κ) * (C * (3683 / 2500 : ℝ)) +
      2 * κ * (C * (3683 / 2500 : ℝ)) * fCap +
      (μR + 38 * (κB ^ 2 + κ)) * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap ≤
      428 * C ^ 2 * fCap := by
    have hCsq : C ≤ C ^ 2 := by
      calc
        C = C * 1 := by ring
        _ ≤ C * C := mul_le_mul_of_nonneg_left hCge hC0
        _ = C ^ 2 := by ring
    have hCf : C * fCap ≤ C ^ 2 * fCap :=
      mul_le_mul_of_nonneg_right hCsq hfCap0
    have hCf1 : 1 ≤ C * fCap := by nlinarith [hCge, hfCapge]
    have hC : C ≤ C ^ 2 * fCap := by
      calc
        C = C * 1 := by ring
        _ ≤ C * (C * fCap) := mul_le_mul_of_nonneg_left hCf1 hC0
        _ = C ^ 2 * fCap := by ring
    nlinarith [hterm1, hterm2, hterm3]
  calc
    _ ≤ v * (428 * C ^ 2 * fCap) := mul_le_mul_of_nonneg_left hinside hv
    _ = 428 * v * C ^ 2 * fCap := by ring

/-- The local-clock squared times the full-response cap has the exact
affine-times-geometric depth form used in the discounted series. -/
theorem main_rawShell_old_frame_p20_clock_response_product
    (gamma : ℝ) (j : ℕ) :
    rawTraceOldFrameP20LocalClock gamma (6 + j) ^ 2 *
        rawTraceOldFrameP20FullResponseCap gamma (6 + j) =
      4 * ((2018618 : ℝ) / 1000000 + gamma *
        (32474 * ((j + 7 : ℕ) : ℝ) + 11483216)) *
        (3 : ℝ) ^ (46 * gamma) * ((3 : ℝ) ^ (8 * gamma)) ^ j := by
  have hs : ((6 + j : ℕ) : ℝ) = 6 + (j : ℝ) := by push_cast; ring
  have hs1 : ((6 + j + 1 : ℕ) : ℝ) = 7 + (j : ℝ) := by push_cast; ring
  have hs7 : ((j + 7 : ℕ) : ℝ) = (j : ℝ) + 7 := by push_cast; ring
  unfold rawTraceOldFrameP20LocalClock rawTraceOldFrameP20FullResponseCap
  rw [hs, hs1, hs7]
  conv_lhs => rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
  simp only [Nat.cast_ofNat]
  rw [show 2 * gamma * (6 + (j : ℝ) - 1) * 2 =
    2 * gamma * (5 + (j : ℝ)) * 2 by ring]
  have hexp :
      2 * gamma * (5 + (j : ℝ)) * 2 +
          (2 * gamma * (7 + (j : ℝ)) + 2 * gamma * (6 + (j : ℝ))) =
        46 * gamma + 8 * gamma * (j : ℝ) := by ring
  calc
    _ = 4 * ((2018618 : ℝ) / 1000000 + gamma *
          (32474 * ((j : ℝ) + 7) + 11483216)) *
        ((3 : ℝ) ^ (2 * gamma * (5 + (j : ℝ)) * 2) *
          (3 : ℝ) ^ (2 * gamma * (7 + (j : ℝ)) + 2 * gamma * (6 + (j : ℝ)))) := by
      ring
    _ = 4 * ((2018618 : ℝ) / 1000000 + gamma *
          (32474 * ((j : ℝ) + 7) + 11483216)) *
        (3 : ℝ) ^ (2 * gamma * (5 + (j : ℝ)) * 2 +
          (2 * gamma * (7 + (j : ℝ)) + 2 * gamma * (6 + (j : ℝ)))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    _ = 4 * ((2018618 : ℝ) / 1000000 + gamma *
          (32474 * ((j : ℝ) + 7) + 11483216)) *
        (3 : ℝ) ^ (46 * gamma) * (3 : ℝ) ^ (8 * gamma * (j : ℝ)) := by
      rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring
    _ = 4 * ((2018618 : ℝ) / 1000000 + gamma *
          (32474 * ((j : ℝ) + 7) + 11483216)) *
        (3 : ℝ) ^ (46 * gamma) * ((3 : ℝ) ^ (8 * gamma)) ^ j := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]

private theorem main_rawShell_fixed_discount_ratio_lt_one
    {gamma : ℝ} (hg : gamma ≤ gammaZero) :
    ‖Scalar.inverseHistoryDiscount * (3 : ℝ) ^ (8 * gamma)‖ < 1 := by
  have hg' : gamma ≤ 17 / 50000 := by simpa [gammaZero] using hg
  have hexp : 8 * gamma - 1 / 4 < 0 := by norm_num at hg'; nlinarith
  have hr0 : 0 ≤ Scalar.inverseHistoryDiscount * (3 : ℝ) ^ (8 * gamma) := by
    dsimp [Scalar.inverseHistoryDiscount]
    positivity
  have heq : Scalar.inverseHistoryDiscount * (3 : ℝ) ^ (8 * gamma) =
      (3 : ℝ) ^ (8 * gamma - 1 / 4) := by
    dsimp [Scalar.inverseHistoryDiscount]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [Real.norm_of_nonneg hr0, heq]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp

/-- The actual inserted shell at `m+1` has the normalized variance cap
needed by the OLD-history coefficient profile. -/
theorem main_rawShell_fixed_old_frame_p20_shell_variance_clock
    (M : ABKModel 2) (h : ℝ) (m q : ℤ) (s : ℕ)
    (hqs : q + (s : ℤ) = m + 1)
    (hstate : nativeInductionState M h m) :
    q3ModelAmplitude M h (q + (s : ℤ)) ^ 2 /
        (Annealed.sigmaBar M m : ℝ) ^ 2 ≤
      (9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma) := by
  simpa [hqs] using
    source_native_shell_variance_clock M h m (m + 1) hstate

/-- The fixed-frame producer's deterministic control is a nonnegative,
integrable constant profile on the insertion-time interval. -/
theorem main_rawShell_fixed_old_frame_p20_control_admissible
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (j : ℕ) :
    0 ≤ mainRawShellOldFrameP20Control M h m j ∧
      IntegrableOn (fun _ : ℝ => mainRawShellOldFrameP20Control M h m j)
        (Icc (0 : ℝ) 1) := by
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let s : ℕ := 6 + j
  let Q := originCube 2 q
  let J := q + (s : ℤ)
  let ρ := cubeScaleFactor Q / (q3ModelLength J).1
  let δ := diagMeshRadius Q (pureFluxBankSourceDepth s) /
    (q3ModelLength J).1
  let κ := rawTraceRemainderKappaF ρ δ
  let κB := rawTraceRemainderB ρ δ
  let A := rawTraceRemainderA (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let B := rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
    (pureFluxCovarianceDelta 0 (s - 1))
  let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0 A B
  let v := (q3ModelAmplitude M h J) ^ 2 / (Annealed.sigmaBar M m) ^ 2
  let C := rawTraceOldFrameP20LocalClock M.gamma s
  let fCap := rawTraceOldFrameP20FullResponseCap M.gamma s
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    exact div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
      (q3ModelLength J).2.le
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact div_nonneg (diagMeshRadius_pos Q (pureFluxBankSourceDepth s)).le
      (q3ModelLength J).2.le
  have hκ : 0 ≤ κ := by
    dsimp [κ]
    unfold rawTraceRemainderKappaF
    positivity
  have hκB : 0 ≤ κB := by
    dsimp [κB]
    unfold rawTraceRemainderB
    positivity
  have hρbank : 0 ≤ pureFluxCovarianceRho 0 (s - 1) :=
    (pureFlux_covariance_rho_pos 0 (s - 1)).le
  have hδbank : 0 ≤ pureFluxCovarianceDelta 0 (s - 1) :=
    (pureFlux_covariance_delta_bounds 0 (s - 1)).1
  have hA : 0 ≤ A := by
    dsimp [A]
    unfold rawTraceRemainderA
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    unfold rawTraceRemainderB
    positivity
  have hμR : 0 ≤ μR := by
    dsimp [μR]
    unfold rawTraceRemainderMu
    apply div_nonneg
    · have hH0 : 0 ≤ rawTraceRemainderH0 := by norm_num [rawTraceRemainderH0]
      have hD0 : 0 ≤ rawTraceRemainderD0 := by
        unfold rawTraceRemainderD0
        positivity
      positivity
    · norm_num
  have hv : 0 ≤ v := by
    dsimp [v]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hC : 0 ≤ C := by
    dsimp [C, rawTraceOldFrameP20LocalClock]
    positivity
  have hfCap : 0 ≤ fCap := by
    dsimp [fCap, rawTraceOldFrameP20FullResponseCap]
    positivity
  have hcontrol : 0 ≤ mainRawShellOldFrameP20Control M h m j := by
    dsimp only [mainRawShellOldFrameP20Control]
    dsimp only [q, s, Q, J, κ, κB, A, B, μR, v, C, fCap] at *
    positivity
  refine ⟨hcontrol, ?_⟩
  exact integrableOn_const (by rw [Real.volume_Icc]; norm_num)

/-- The fixed-OLD-frame producer discharges the depth-generator premise in
the weak-history profile assembly. The old-time L20 profile and its weighted
summability remain explicit inputs. -/
theorem main_rawWeakTraceHistory_lpNorm_le_of_fixed_old_frame_p20
    (M : ABKModel 2) (m : ℤ) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (B : ℕ → ℝ)
    (hT0 : ∀ j, MemLp
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) 0) 20
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hB : ∀ j, lpNorm
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) 0) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ B j)
    (hprofile : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      (B j + ∫ t in (0 : ℝ)..τ, mainRawShellOldFrameP20Control M h m j))) :
    ∃ hT : ∀ j : ℕ,
      MemLp (rawWeakTraceSequence M m (originCube 2 (m - 5)) τ · j) 2
        (Cutoff.cutoffSampleLaw M).toMeasure,
      ‖rawWeakTraceHistoryLp M m (originCube 2 (m - 5)) τ hT‖ ≤
        (1 - Scalar.inverseHistoryDiscount) *
          ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j *
            (B j + ∫ t in (0 : ℝ)..τ, mainRawShellOldFrameP20Control M h m j) := by
  let U : ℕ → ℝ → ℝ := fun j _ => mainRawShellOldFrameP20Control M h m j
  have hU0 : ∀ j t, t ∈ Icc (0 : ℝ) 1 → 0 ≤ U j t := by
    intro j t ht
    simpa only [U] using
      (main_rawShell_fixed_old_frame_p20_control_admissible M h m j).1
  have hUInt : ∀ j, IntegrableOn (U j) (Icc (0 : ℝ) 1) := by
    intro j
    simpa only [U] using
      (main_rawShell_fixed_old_frame_p20_control_admissible M h m j).2
  have hTτ : ∀ j, MemLp
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) τ) 20
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro j
    exact main_rawDepthFourLoadTrace_memLp_twenty_fixed_old_frame
      M h hM hg m hpast j τ ⟨hτ0, hτ1⟩
  have hGenerator : ∀ j t, t ∈ Ioo (0 : ℝ) 1 →
      deriv (modelTracePowerHeatAverage
        (m - ((5 + j : ℕ) : ℤ)) M m 20) t ≤
        20 * modelTracePowerHeatAverage
          (m - ((5 + j : ℕ) : ℤ)) M m 20 t ^ ((19 : ℝ) / 20) * U j t := by
    intro j t ht
    simpa only [U] using
      (main_rawShell_fixed_old_frame_p20_hGenerator M h hM hg m hpast j) t ht
  exact main_rawWeakTraceHistory_lpNorm_le_of_depth_generators
    M m h hM τ hτ0 hτ1 B U hU0 hUInt hT0 hTτ hB hGenerator hprofile

/-- The fixed-frame control has a summable inverse-history-discounted depth
profile throughout the source gamma interval. -/
theorem main_rawShell_fixed_old_frame_p20_control_discounted_summable
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (hg : M.gamma ≤ gammaZero) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      mainRawShellOldFrameP20Control M h m j) := by
  let gamma : ℝ := M.gamma
  let r : ℝ := Scalar.inverseHistoryDiscount * (3 : ℝ) ^ (8 * gamma)
  let a : ℝ := (2018618 : ℝ) / 1000000 + gamma *
    (32474 * 7 + 11483216)
  let b : ℝ := 32474 * gamma
  let v : ℝ := (q3ModelAmplitude M h (m + 1)) ^ 2 /
    (Annealed.sigmaBar M m : ℝ) ^ 2
  let K : ℝ := 1712 * v * (3 : ℝ) ^ (46 * gamma)
  have hrnorm : ‖r‖ < 1 := by
    simpa only [r, gamma] using main_rawShell_fixed_discount_ratio_lt_one hg
  have hgeo := hasSum_geometric_of_norm_lt_one hrnorm
  have hlin := hasSum_coe_mul_geometric_of_norm_lt_one hrnorm
  have hbase : Summable (fun j : ℕ => (a + b * (j : ℝ)) * r ^ j) := by
    have hpoint (j : ℕ) : (a + b * (j : ℝ)) * r ^ j =
        a * r ^ j + b * ((j : ℝ) * r ^ j) := by ring
    have heq : (fun j : ℕ => (a + b * (j : ℝ)) * r ^ j) =
        fun j : ℕ => a * r ^ j + b * ((j : ℝ) * r ^ j) := by
      funext j
      exact hpoint j
    rw [heq]
    exact (hgeo.summable.mul_left a).add (hlin.summable.mul_left b)
  have hmajor : Summable (fun j : ℕ => K * (a + b * (j : ℝ)) * r ^ j) := by
    have := hbase.mul_left K
    simpa only [mul_assoc] using this
  have hcoef (j : ℕ) :
      (2018618 : ℝ) / 1000000 + gamma *
        (32474 * ((j + 7 : ℕ) : ℝ) + 11483216) = a + b * (j : ℝ) := by
    dsimp [a, b]
    push_cast
    ring
  have hweight (j : ℕ) :
      Scalar.inverseHistoryDiscount ^ j *
          (428 * v * (rawTraceOldFrameP20LocalClock gamma (6 + j)) ^ 2 *
            rawTraceOldFrameP20FullResponseCap gamma (6 + j)) =
        K * (a + b * (j : ℝ)) * r ^ j := by
    calc
      _ = Scalar.inverseHistoryDiscount ^ j *
          (428 * v * ((rawTraceOldFrameP20LocalClock gamma (6 + j)) ^ 2 *
            rawTraceOldFrameP20FullResponseCap gamma (6 + j))) := by ring
      _ = K * (a + b * (j : ℝ)) * r ^ j := by
        rw [main_rawShell_old_frame_p20_clock_response_product, hcoef]
        dsimp [K, r]
        rw [mul_pow]
        ring
  have hnonneg (j : ℕ) : 0 ≤ Scalar.inverseHistoryDiscount ^ j *
      mainRawShellOldFrameP20Control M h m j := by
    have hcontrol := main_rawShell_fixed_old_frame_p20_control_admissible M h m j
    exact mul_nonneg
      (pow_nonneg Scalar.inverse_history_discount_range.1.le j) hcontrol.1
  have hbound (j : ℕ) : Scalar.inverseHistoryDiscount ^ j *
      mainRawShellOldFrameP20Control M h m j ≤ K * (a + b * (j : ℝ)) * r ^ j := by
    let q : ℤ := m - ((5 + j : ℕ) : ℤ)
    let s : ℕ := 6 + j
    let J := q + (s : ℤ)
    have hJ : J = m + 1 := by dsimp [J, q, s]; omega
    have hcoarse := main_rawShell_fixed_old_frame_p20_control_coarse_bound M h m j
    have hcoarse' : mainRawShellOldFrameP20Control M h m j ≤
        428 * v * (rawTraceOldFrameP20LocalClock gamma (6 + j)) ^ 2 *
          rawTraceOldFrameP20FullResponseCap gamma (6 + j) := by
      simpa only [mainRawShellOldFrameP20Control, v, gamma, q, s, J, hJ] using hcoarse
    calc
      _ ≤ Scalar.inverseHistoryDiscount ^ j *
          (428 * v * (rawTraceOldFrameP20LocalClock gamma (6 + j)) ^ 2 *
            rawTraceOldFrameP20FullResponseCap gamma (6 + j)) :=
        mul_le_mul_of_nonneg_left hcoarse'
          (pow_nonneg Scalar.inverse_history_discount_range.1.le j)
      _ = K * (a + b * (j : ℝ)) * r ^ j := hweight j
  exact Summable.of_nonneg_of_le hnonneg hbound hmajor

/-- At zero insertion, each source-depth four-load trace is the actual
cutoff trace at lag `5+j`; the frozen strong20 coordinate therefore supplies
its finite L20 moment. -/
theorem main_rawDepthFourLoadTrace_memLp_twenty_zero_of_strong20
    (M : ABKModel 2) (m : ℤ) (S : ℝ)
    (hstrong : strong20 M m ≤ ENNReal.ofReal S) (j : ℕ) :
    MemLp
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) 0)
      20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let Q := originCube 2 q
  have hcoeff (ω : Cutoff.CutoffSample 2) :
      Model.partialInsertedCoefficient M m 0 ω =
        Cutoff.coefficientCutoff M.nu m ω := by
    ext x i k
    change Cutoff.coefficientCutoff M.nu m ω x i k +
      Real.sqrt 0 * (ω.1 (m + 1)).forgetShell x i k = _
    rw [Real.sqrt_zero, zero_mul, add_zero]
  have hzero (ω : Cutoff.CutoffSample 2) :
      rawDepthFourLoadTrace M m q 0 ω = coldNativeCellTrace M m Q ω := by
    change traceDefect (cubeSet Q)
        (Model.partialInsertedCoefficient M m 0 ω).toFun
        (Annealed.sigmaBar M m : ℝ) =
      traceDefect (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun
        (Annealed.sigmaBar M m : ℝ)
    rw [hcoeff]
  change MemLp (rawDepthFourLoadTrace M m q 0) 20
    (Cutoff.cutoffSampleLaw M).toMeasure
  rw [show rawDepthFourLoadTrace M m q 0 = coldNativeCellTrace M m Q from
    funext hzero]
  apply (coldNativeCellTrace_memLp_iff M m Q 20).2
  dsimp [Q, q]
  exact cold_native_fine_memLp hstrong (5 + j)

/-- The actual zero-insertion depth trace has exactly the cutoff-trace L20
norm used by the frozen strong20 series. -/
theorem main_rawDepthFourLoadTrace_lpNorm_twenty_zero_eq_cutoff
    (M : ABKModel 2) (m : ℤ) (j : ℕ) :
    lpNorm
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) 0)
      20 (Cutoff.cutoffSampleLaw M).toMeasure =
    lpNorm (cutoffTraceDefect M m (m - ((5 + j : ℕ) : ℤ)))
      20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let Q := originCube 2 q
  have hcoeff (ω : Cutoff.CutoffSample 2) :
      Model.partialInsertedCoefficient M m 0 ω =
        Cutoff.coefficientCutoff M.nu m ω := by
    ext x i k
    change Cutoff.coefficientCutoff M.nu m ω x i k +
      Real.sqrt 0 * (ω.1 (m + 1)).forgetShell x i k = _
    rw [Real.sqrt_zero, zero_mul, add_zero]
  have hzero (ω : Cutoff.CutoffSample 2) :
      rawDepthFourLoadTrace M m q 0 ω = coldNativeCellTrace M m Q ω := by
    change traceDefect (cubeSet Q)
        (Model.partialInsertedCoefficient M m 0 ω).toFun
        (Annealed.sigmaBar M m : ℝ) =
      traceDefect (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun
        (Annealed.sigmaBar M m : ℝ)
    rw [hcoeff]
  change lpNorm (rawDepthFourLoadTrace M m q 0) 20
    (Cutoff.cutoffSampleLaw M).toMeasure = _
  rw [show rawDepthFourLoadTrace M m q 0 = coldNativeCellTrace M m Q from
    funext hzero]
  rw [coldNativeCellTrace_norm]
  rfl

/-- The discounted OLD depth profile at zero insertion is summable and its
normalized history sum is bounded by the strong20 source cap. -/
theorem main_rawDepthFourLoadTrace_old_profile_bound
    (M : ABKModel 2) (m : ℤ) (hγ : M.gamma ≤ gammaZero)
    (hstrong : strong20 M m ≤
      ENNReal.ofReal ((2379 / 2500 : ℝ) * theta M)) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      lpNorm (rawDepthFourLoadTrace M m
        (m - ((5 + j : ℕ) : ℤ)) 0) 20
        (Cutoff.cutoffSampleLaw M).toMeasure) ∧
    (1 - Scalar.inverseHistoryDiscount) *
      ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j *
        lpNorm (rawDepthFourLoadTrace M m
          (m - ((5 + j : ℕ) : ℤ)) 0) 20
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ mainH0 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B : ℕ → ℝ := fun j => lpNorm
    (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) 0) 20 μ
  have hθ : theta M ≤ 1 := cold_theta_le_one M hγ
  have hcap : strong20 M m ≤ ENNReal.ofReal (2379 / 2500 : ℝ) := by
    apply hstrong.trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have hstrongSum := cold_native_strong_sum (by norm_num : 0 ≤ (2379 / 2500 : ℝ)) hcap
  have hinj : Function.Injective (fun j : ℕ => j + 5) := by
    intro a b hab
    exact Nat.add_right_cancel hab
  have hshift : Summable (fun j : ℕ => coldNativeStrongRealTerm M m (j + 5)) :=
    hstrongSum.1.comp_injective hinj
  have hBnonneg (j : ℕ) : 0 ≤ B j := lpNorm_nonneg
  have hVeq (j : ℕ) : coldNativeStrongRealTerm M m (j + 5) =
      (1 - coldHistoryAlpha) * (coldHistoryBeta ^ (j + 5) * B j) := by
    rw [coldNativeStrongRealTerm]
    have he : m - ((j + 5 : ℕ) : ℤ) = m - ((5 + j : ℕ) : ℤ) := by
      omega
    rw [he]
    rw [← main_rawDepthFourLoadTrace_lpNorm_twenty_zero_eq_cutoff]
    dsimp [B]
    ring
  have hc : 0 < 1 - coldHistoryAlpha := sub_pos.mpr coldHistoryAlpha_lt_one
  have hprofile : Summable (fun j : ℕ => coldHistoryBeta ^ (j + 5) * B j) := by
    have hshift' : Summable (fun j : ℕ =>
        (1 - coldHistoryAlpha) * (coldHistoryBeta ^ (j + 5) * B j)) := by
      simpa only [hVeq] using hshift
    exact (summable_mul_left_iff hc.ne').mp hshift'
  have hαβ : coldHistoryAlpha ≤ coldHistoryBeta := by
    dsimp [coldHistoryAlpha, coldHistoryBeta]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by norm_num)
  let C : ℝ := (coldHistoryBeta ^ 5)⁻¹
  have hCpos : 0 < C := by
    dsimp [C]
    exact inv_pos.mpr (pow_pos coldHistoryBeta_pos 5)
  have hmajor : Summable (fun j : ℕ => C *
      (coldHistoryBeta ^ (j + 5) * B j)) := hprofile.mul_left C
  have hterm (j : ℕ) : coldHistoryAlpha ^ j * B j ≤
      C * (coldHistoryBeta ^ (j + 5) * B j) := by
    have hpow : coldHistoryAlpha ^ j ≤ coldHistoryBeta ^ j :=
      pow_le_pow_left₀ coldHistoryAlpha_pos.le hαβ j
    have hcancel : C * (coldHistoryBeta ^ (j + 5) * B j) =
        coldHistoryBeta ^ j * B j := by
      dsimp [C]
      rw [pow_add]
      field_simp [ne_of_gt coldHistoryBeta_pos]
    rw [hcancel]
    exact mul_le_mul_of_nonneg_right hpow (hBnonneg j)
  have halpha : Summable (fun j : ℕ => coldHistoryAlpha ^ j * B j) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (pow_nonneg coldHistoryAlpha_pos.le j) (hBnonneg j))
      hterm hmajor
  have halphaMajor := halpha.tsum_le_tsum hterm hmajor
  have halphaMajor' : (∑' j : ℕ, coldHistoryAlpha ^ j * B j) ≤
      C * (∑' j : ℕ, coldHistoryBeta ^ (j + 5) * B j) := by
    calc
      _ ≤ ∑' j : ℕ, C * (coldHistoryBeta ^ (j + 5) * B j) := halphaMajor
      _ = _ := by rw [tsum_mul_left]
  have hshiftLe : (1 - coldHistoryAlpha) *
      (∑' j : ℕ, coldHistoryBeta ^ (j + 5) * B j) ≤
        ∑' r : ℕ, coldNativeStrongRealTerm M m r := by
    have hsum := hstrongSum.1.sum_add_tsum_nat_add 5
    have hprefix : 0 ≤ ∑ r ∈ Finset.range 5, coldNativeStrongRealTerm M m r :=
      Finset.sum_nonneg (fun r _ => by
        simp only [coldNativeStrongRealTerm]
        exact mul_nonneg
          (mul_nonneg (sub_nonneg.mpr coldHistoryAlpha_le_one)
            (pow_nonneg coldHistoryBeta_pos.le r))
          lpNorm_nonneg)
    have htailEq : (∑' j : ℕ, coldNativeStrongRealTerm M m (j + 5)) =
        (1 - coldHistoryAlpha) *
          ∑' j : ℕ, coldHistoryBeta ^ (j + 5) * B j := by
      calc
        _ = ∑' j : ℕ,
            (1 - coldHistoryAlpha) * (coldHistoryBeta ^ (j + 5) * B j) := by
              apply tsum_congr
              exact hVeq
        _ = _ := by rw [tsum_mul_left]
    rw [← htailEq]
    linarith [hsum]
  have hbound : (1 - coldHistoryAlpha) *
      (∑' j : ℕ, coldHistoryAlpha ^ j * B j) ≤ mainH0 := by
    calc
      _ ≤ (1 - coldHistoryAlpha) *
          (C * ∑' j : ℕ, coldHistoryBeta ^ (j + 5) * B j) :=
        mul_le_mul_of_nonneg_left halphaMajor' hc.le
      _ = C * ((1 - coldHistoryAlpha) *
          ∑' j : ℕ, coldHistoryBeta ^ (j + 5) * B j) := by ring
      _ ≤ C * (∑' r : ℕ, coldNativeStrongRealTerm M m r) :=
        mul_le_mul_of_nonneg_left hshiftLe hCpos.le
      _ ≤ C * (2379 / 2500 : ℝ) :=
        mul_le_mul_of_nonneg_left hstrongSum.2 hCpos.le
      _ = mainH0 := by
        dsimp [C]
        have hbeta : coldHistoryBeta ^ 5 = (3 : ℝ) ^ (-(3 / 4 : ℝ)) := by
          rw [cold_native_beta_power]
          congr 1
          norm_num
        have hinv : (coldHistoryBeta ^ 5)⁻¹ = (3 : ℝ) ^ (3 / 4 : ℝ) := by
          rw [hbeta, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) (3 / 4 : ℝ)]
          simp
        rw [hinv, mainH0]
  constructor
  · simpa only [B, show Scalar.inverseHistoryDiscount = coldHistoryAlpha by rfl] using halpha
  · simpa only [B, show Scalar.inverseHistoryDiscount = coldHistoryAlpha by rfl] using hbound

/-- The fixed-frame generator and the native strong20 source cap give
an explicit state-level weak-history estimate. The remaining coefficient is
the inverse-discounted sum of the actual fixed-frame controls; the comparison
of this coefficient with `mainDeltaH` is a separate envelope step. -/
theorem main_rawWeakTraceHistory_lpNorm_le_of_fixed_old_frame_state_strong20
    (M : ABKModel 2) (m : ℤ) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hstrong : strong20 M m ≤
      ENNReal.ofReal ((2379 / 2500 : ℝ) * theta M)) :
    ∃ hT : ∀ j : ℕ,
      MemLp (rawWeakTraceSequence M m (originCube 2 (m - 5)) τ · j) 2
        (Cutoff.cutoffSampleLaw M).toMeasure,
      ‖rawWeakTraceHistoryLp M m (originCube 2 (m - 5)) τ hT‖ ≤
        mainH0 + τ * ((1 - Scalar.inverseHistoryDiscount) *
          ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j *
            mainRawShellOldFrameP20Control M h m j) := by
  let B : ℕ → ℝ := fun j => lpNorm
    (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) 0)
    20 (Cutoff.cutoffSampleLaw M).toMeasure
  let α : ℝ := Scalar.inverseHistoryDiscount
  have hzero := main_rawDepthFourLoadTrace_old_profile_bound M m hg hstrong
  have hcontrol := main_rawShell_fixed_old_frame_p20_control_discounted_summable
    M h m hg
  have hBsum : Summable (fun j : ℕ => α ^ j * B j) := by
    simpa only [α, B] using hzero.1
  have hCsum : Summable (fun j : ℕ => α ^ j *
      mainRawShellOldFrameP20Control M h m j) := by
    simpa only [α] using hcontrol
  have hCτsum : Summable (fun j : ℕ => α ^ j *
      (τ * mainRawShellOldFrameP20Control M h m j)) := by
    refine (hCsum.mul_left τ).congr ?_
    intro j
    ring
  have hIntegral (j : ℕ) :
      ∫ t in (0 : ℝ)..τ, mainRawShellOldFrameP20Control M h m j =
        τ * mainRawShellOldFrameP20Control M h m j := by
    simp [intervalIntegral.integral_const]
  have hprofile : Summable (fun j : ℕ => α ^ j *
      (B j + ∫ t in (0 : ℝ)..τ,
        mainRawShellOldFrameP20Control M h m j)) := by
    have hsum := hBsum.add hCτsum
    refine hsum.congr ?_
    intro j
    rw [hIntegral]
    ring
  have hT0 : ∀ j, MemLp
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) 0) 20
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro j
    exact main_rawDepthFourLoadTrace_memLp_twenty_zero_of_strong20
      M m _ hstrong j
  obtain ⟨hT, hbound⟩ :=
    main_rawWeakTraceHistory_lpNorm_le_of_fixed_old_frame_p20
      M m h hM hg hpast τ hτ0 hτ1 B hT0 (fun j => le_rfl) hprofile
  refine ⟨hT, ?_⟩
  have hsum :
      (∑' j : ℕ, α ^ j *
        (B j + ∫ t in (0 : ℝ)..τ,
          mainRawShellOldFrameP20Control M h m j)) =
        (∑' j : ℕ, α ^ j * B j) +
          τ * (∑' j : ℕ, α ^ j * mainRawShellOldFrameP20Control M h m j) := by
    calc
      _ = ∑' j : ℕ, (α ^ j * B j + α ^ j *
          (τ * mainRawShellOldFrameP20Control M h m j)) := by
        apply tsum_congr
        intro j
        rw [hIntegral]
        ring
      _ = _ := hBsum.tsum_add hCτsum
      _ = _ := by
        rw [show (fun j : ℕ => α ^ j *
            (τ * mainRawShellOldFrameP20Control M h m j)) =
          fun j : ℕ => τ * (α ^ j * mainRawShellOldFrameP20Control M h m j) by
            funext j
            ring]
        rw [tsum_mul_left]
  have hzeroBound : (1 - α) * (∑' j : ℕ, α ^ j * B j) ≤ mainH0 := by
    simpa only [α, B] using hzero.2
  calc
    _ ≤ (1 - α) *
        ∑' j : ℕ, α ^ j *
          (B j + ∫ t in (0 : ℝ)..τ,
            mainRawShellOldFrameP20Control M h m j) := hbound
    _ = (1 - α) * (∑' j : ℕ, α ^ j * B j) +
        τ * ((1 - α) *
          ∑' j : ℕ, α ^ j * mainRawShellOldFrameP20Control M h m j) := by
      rw [hsum]
      ring
    _ ≤ mainH0 + τ * ((1 - α) *
        ∑' j : ℕ, α ^ j * mainRawShellOldFrameP20Control M h m j) :=
      add_le_add_left hzeroBound _

end ASDExplicitGamma.Main

end

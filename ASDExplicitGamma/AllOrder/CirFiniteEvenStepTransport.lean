/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.CirFiniteEvenHeatBridge
public import ASDExplicitGamma.AllOrder.CirFiniteEvenResetTransport
public import ASDExplicitGamma.AllOrder.CirFiniteEvenTimeIntegrable
public import ASDExplicitGamma.AllOrder.CirMomentTransport

/-! # One-shell finite-even CIR transport from the reset producer -/

@[expose] public section

open Homogenization MeasureTheory Set
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Response
  ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

/-- Every depth-four response tile in a native frame is small enough for the
shell estimate once the inserted shell lies strictly above that frame. -/
theorem aoCir_native_child_shell_ratio {Q : TriadicCube 2} {frameLabel N : ℤ}
    (hscale : Q.scale = frameLabel) (hN : frameLabel + 1 ≤ N) :
    diagMeshRadius Q 4 / (q3ModelLength N).1 ≤ 1 / 243 := by
  have hratio : diagMeshRadius Q 4 / (q3ModelLength N).1 =
      (3 : ℝ) ^ (frameLabel - 4 - N) := by
    simp only [diagMeshRadius, cubeScaleFactor, hscale, q3ModelLength]
    change ((3 : ℝ) ^ frameLabel / (3 : ℝ) ^ (4 : ℤ)) / (3 : ℝ) ^ N = _
    rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0) frameLabel 4,
      ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0) (frameLabel - 4) N]
  rw [hratio]
  have hexp : frameLabel - 4 - N ≤ -5 := by omega
  have hpow : (3 : ℝ) ^ (frameLabel - 4 - N) ≤ (3 : ℝ) ^ (-5 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) hexp
  norm_num at hpow ⊢
  exact hpow

/-- One actual shell transports the finite weighted family of native
translated-square traces, using only the reset producer for its stochastic
moment and load inputs. The coefficient remains in the old true frame during
the insertion. -/
theorem aoCir_finite_even_shell_transport_of_reset
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2)
    (n ell frameLabel N : ℤ)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆
      closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (hscale : ∀ a ∈ s, (Q a).scale = frameLabel)
    (hN : frameLabel + 1 ≤ N) (hNhi : N ≤ frameLabel + 8)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1)
    {p : ℝ} (hp12 : 12 ≤ p) (hpP : p ≤ (smallGammaSeedP M.gamma : ℝ)) :
    let K := closure (cubeSet (originCube 2 n))
    let b := q3ModelAmplitude M h N
    let L := q3ModelLength N
    let k := fun a τ ω => cirSquareRestrictionCLM (Q a) (hQ a)
      (modelInsertedScalar K (N - 1) τ ω)
    let F := cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L k hw hsum
    Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure p
        (cirFamilyTrace F 1) -
      Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure p
        (cirFamilyTrace F 0) ≤
      (107 / 12 : ℝ) * p *
        (b ^ 2 / (Annealed.sigmaBar M frameLabel : ℝ) ^ 2) *
        ((2.2 : ℝ) ^ 2 * 50) := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  let b := q3ModelAmplitude M h N
  let L := q3ModelLength N
  let k : (a : ι) → ℝ → Cutoff.CutoffSample 2 →
      ResponseCoefficient (openCubeSet (Q a)) := fun a τ ω =>
    cirSquareRestrictionCLM (Q a) (hQ a) (modelInsertedScalar K (N - 1) τ ω)
  let F := cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L k hw hsum
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let vbar := b ^ 2 / (Annealed.sigmaBar M frameLabel : ℝ) ^ 2
  have hNle : frameLabel ≤ N := by omega
  have hratio : ∀ a ∈ s,
      diagMeshRadius (Q a) 4 / (q3ModelLength N).1 ≤ 1 / 243 := by
    intro a ha
    exact aoCir_native_child_shell_ratio (hscale a ha) hN
  have hfamily := aoCir_reset_square_family_memLp reset M h hM hγ hγsmall
    hstate s w Q n ell frameLabel N hQ hK hscale hNle hw hsum b L
  have hidx : N - 1 + 1 = N := by omega
  have hYmem : ∀ q, 1 < q → ∀ t ∈ Icc (0 : ℝ) 1,
      MemLp (cirFamilyTrace F t) (ENNReal.ofReal q) μ := by
    intro q hq t ht
    have hq1 : 1 ≤ q := by linarith
    simpa only [F, k] using (hfamily q hq1 t ht.1 ht.2).1
  have hLmem : ∀ q, 1 ≤ q → ∀ t ∈ Icc (0 : ℝ) 1,
      MemLp (cirFamilyHistoryLoad F t) (ENNReal.ofReal q) μ := by
    intro q hq t ht
    simpa only [F, k] using (hfamily q hq t ht.1 ht.2).2
  have hdata : ∀ q, 1 < q → ∀ ε, 0 < ε →
      Gaussian.P12RegularizedHeatData μ (cirFamilyTrace F)
        (cirFamilyGenerator F) (cirFamilyBracket F) q ε := by
    intro q hq ε hε
    simpa only [K, μ, F, k, hidx] using aoCir_weightedSquareTrace_shell_family_heat_data n M h hM frameLabel
      (N - 1) s w Q (fun _ => 4) hQ hw hsum hq hε
  have hvariationRaw := aoCir_weightedSquareTrace_first_variation n M h hM
    frameLabel (N - 1) s w Q (fun _ => 4) hQ hw hsum
  have hvariation := by simpa only [K, μ, F, k, hidx] using hvariationRaw
  have hG4 := aoCir_square_output s w Q (fun _ => 4) M frameLabel b L
    hw hsum hratio k
  have hgen : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ω, cirFamilyGenerator F t ω ≤
      19 * vbar * cirFamilyHistoryLoad F t ω := by
    intro t ht ω
    simpa [vbar] using hG4.generator_bound t ω
  have hbracket : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ω, cirFamilyBracket F t ω ≤
      16 * vbar * cirFamilyTrace F t ω * cirFamilyHistoryLoad F t ω := by
    intro t ht ω
    simpa [vbar] using hG4.bracket_bound t ω
  have hU := aoCir_reset_square_family_history_load_time_integrable reset
    M h hM hγ hγsmall hstate s w Q n ell frameLabel N
    hQ hK hscale hNle hNhi hw hsum b L p (by linarith : 1 ≤ p) hpP
  have hU' : IntegrableOn
      (fun t => (19 + 8 * (p - 1)) * vbar *
        Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t))
      (Icc (0 : ℝ) 1) := by
    simpa only [K, μ, F, k, vbar] using hU
  have htransport := aoCir_moment_transport_of_pathwise_bounds_on_unit_interval
    μ (cirFamilyTrace F) (cirFamilyGenerator F) (cirFamilyBracket F)
    (cirFamilyHistoryLoad F) (by linarith : 1 ≤ p) (by positivity : 0 ≤ vbar)
    (cirFamilyTrace_nonneg F) (cirFamilyHistoryLoad_nonneg F)
    hYmem hLmem hdata hgen hbracket hvariation.1 hvariation.2 hU
  have hmove := htransport 0 1 (by norm_num) (by norm_num) (by norm_num)
  have hcap (t : Set.Icc (0 : ℝ) 1) :
      eLpNorm (cirFamilyHistoryLoad F t.1) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 50) := by
    exact aoCir_reset_square_family_history_load_cap reset M h hM hγ hγsmall
      hstate s w Q n ell frameLabel N hQ hK hscale hNle hNhi
      hw hsum b L p hp12 hpP t.1 t.2.1 t.2.2
  have hloadnorm (t : Set.Icc (0 : ℝ) 1) :
      Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t.1) ≤
        (2.2 : ℝ) ^ 2 * 50 := by
    have hnormEq := Gaussian.positiveLpNorm_eq_eLpNorm_toReal μ
      (by linarith : 0 < p) (cirFamilyHistoryLoad F t.1)
      (cirFamilyHistoryLoad_nonneg F t.1)
      (hLmem p (by linarith) t.1 t.2)
    rw [hnormEq]
    calc
      (eLpNorm (cirFamilyHistoryLoad F t.1) (ENNReal.ofReal p) μ).toReal ≤
          (ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 50)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcap t)
      _ = (2.2 : ℝ) ^ 2 * 50 := by norm_num
  have hrate : 19 + 8 * (p - 1) ≤ (107 / 12 : ℝ) * p := by
    nlinarith
  have hvbar : 0 ≤ vbar := by positivity
  let coeff := (19 + 8 * (p - 1)) * vbar
  let bound := (107 / 12 : ℝ) * p * vbar * ((2.2 : ℝ) ^ 2 * 50)
  have hpoint (t : Set.Icc (0 : ℝ) 1) :
      coeff * Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t.1) ≤ bound := by
    dsimp [coeff, bound]
    calc
      _ ≤ (19 + 8 * (p - 1)) * vbar * ((2.2 : ℝ) ^ 2 * 50) :=
        mul_le_mul_of_nonneg_left (hloadnorm t)
          (mul_nonneg (by nlinarith [hp12]) hvbar)
      _ ≤ (107 / 12 : ℝ) * p * vbar * ((2.2 : ℝ) ^ 2 * 50) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hrate hvbar
  have hIntegral :
      (∫ t in (0 : ℝ)..1, coeff *
          Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t)) ≤ bound := by
    have hUu : IntegrableOn
        (fun t => coeff * Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t))
        (Set.uIcc (0 : ℝ) 1) volume := by
      simpa only [coeff, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hU'
    have hmono :
        (∫ t in (0 : ℝ)..1, coeff *
            Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t)) ≤
          (∫ _t in (0 : ℝ)..1, bound) := by
      apply intervalIntegral.integral_mono_on
        (by norm_num : (0 : ℝ) ≤ 1) hUu.intervalIntegrable intervalIntegrable_const
      intro t ht
      exact hpoint ⟨t, ht⟩
    simpa [bound, intervalIntegral.integral_const] using hmono
  have hIntegral' :
      (∫ t in (0 : ℝ)..1, (19 + 8 * (p - 1)) * vbar *
          Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t)) ≤ bound := by
    simpa only [coeff] using hIntegral
  calc
    _ ≤ ∫ t in (0 : ℝ)..1,
        (19 + 8 * (p - 1)) * vbar *
          Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t) := hmove
    _ ≤ bound := hIntegral'
    _ = (107 / 12 : ℝ) * p * vbar * ((2.2 : ℝ) ^ 2 * 50) := rfl

/-- One-shell P12 transport for an arbitrary terminal gap in the direct
order-depth window. The profile-derived load cap is 2.2²·3120. -/
private theorem aoCir_finite_even_shell_load_cap_of_reset_window
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2)
    (n ell frameLabel N : ℤ)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆
      closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (hscale : ∀ a ∈ s, (Q a).scale = frameLabel)
    (hN : frameLabel + 1 ≤ N)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1)
    (b : ℝ) (L : {l : ℝ // 0 < l})
    {p : ℝ} (hp : 1 ≤ p)
    (hpP : max 12 p ≤ (smallGammaSeedP M.gamma : ℝ))
    (hwindow : M.gamma * (max 12 p) *
      ((N - frameLabel : ℤ) + 2 : ℝ) ≤ 1 / 512)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm (cirFamilyHistoryLoad
      (cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L
        (fun a τ ω => cirSquareRestrictionCLM (Q a) (hQ a)
          (modelInsertedScalar (closure (cubeSet (originCube 2 n)))
            (N - 1) τ ω)) hw hsum) t)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 3120) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let pCap : ℝ := max 12 p
  let k : (a : ι) → ℝ → Cutoff.CutoffSample 2 →
      ResponseCoefficient (openCubeSet (Q a)) := fun a τ ω =>
    cirSquareRestrictionCLM (Q a) (hQ a) (modelInsertedScalar
      (closure (cubeSet (originCube 2 n))) (N - 1) τ ω)
  let F := cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L k hw hsum
  have hpCap12 : 12 ≤ pCap := by
    dsimp [pCap]
    exact le_max_left _ _
  have hpCapP : pCap ≤ (smallGammaSeedP M.gamma : ℝ) := by
    dsimp [pCap]
    exact hpP
  have hwindow' : M.gamma * pCap *
      ((N - frameLabel : ℤ) + 2 : ℝ) ≤ 1 / 512 := by
    simpa only [pCap] using hwindow
  have hcomponentsCap (a : ι) (ha : a ∈ s) :
      eLpNorm (fun ω =>
        pureFluxSourceTileHistory (Q a) 4
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M (Q a).scale : ℝ)
            (aoCirInsertedResponseCoefficient (Q a) n (hQ a) N t ω)) ^ 2 *
        rootTraceObservable M (Q a)
          (protectedOldLabel (Q a).scale (orderBand (2 * pCap)))
          N frameLabel (aoCirStepWeights N t) ω)
        (ENNReal.ofReal pCap) μ ≤ ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 3120) := by
    exact aoCir_step_history_load_component_cap_of_reset_window reset
      M h hM hγ hγsmall hstate (Q a) n ell frameLabel N (hQ a) hK
      (hscale a ha) (by omega) pCap hpCap12 hpCapP hwindow'
      t ht0 ht1
  have hCap := aoCir_reset_square_family_history_load_cap_of_component
    M s w Q n ell frameLabel N hQ hK hscale (by omega) hw hsum b L pCap
    ((2.2 : ℝ) ^ 2 * 3120) (by linarith) (by positivity)
    t ht0 ht1 hcomponentsCap
  have hmono : eLpNorm (cirFamilyHistoryLoad F t) (ENNReal.ofReal p) μ ≤
      eLpNorm (cirFamilyHistoryLoad F t) (ENNReal.ofReal pCap) μ :=
    eLpNorm_le_eLpNorm_of_exponent_le
      (ENNReal.ofReal_le_ofReal (le_max_right (12 : ℝ) p))
  simpa only [F, k, μ, pCap] using hmono.trans hCap

theorem aoCir_finite_even_shell_transport_of_reset_window
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2)
    (n ell frameLabel N : ℤ)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆
      closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (hscale : ∀ a ∈ s, (Q a).scale = frameLabel)
    (hN : frameLabel + 1 ≤ N)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1)
    {p : ℝ} (hp : 1 ≤ p)
    (hpP : max 12 p ≤ (smallGammaSeedP M.gamma : ℝ))
    (hwindow : M.gamma * (max 12 p) *
      ((N - frameLabel : ℤ) + 2 : ℝ) ≤ 1 / 512) :
    let K := closure (cubeSet (originCube 2 n))
    let b := q3ModelAmplitude M h N
    let L := q3ModelLength N
    let k := fun a τ ω => cirSquareRestrictionCLM (Q a) (hQ a)
      (modelInsertedScalar K (N - 1) τ ω)
    let F := cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L k hw hsum
    Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure p
        (cirFamilyTrace F 1) -
      Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure p
        (cirFamilyTrace F 0) ≤
      19 * p *
        (b ^ 2 / (Annealed.sigmaBar M frameLabel : ℝ) ^ 2) *
        ((2.2 : ℝ) ^ 2 * 3120) := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  let b := q3ModelAmplitude M h N
  let L := q3ModelLength N
  let k : (a : ι) → ℝ → Cutoff.CutoffSample 2 →
      ResponseCoefficient (openCubeSet (Q a)) := fun a τ ω =>
    cirSquareRestrictionCLM (Q a) (hQ a) (modelInsertedScalar K (N - 1) τ ω)
  let F := cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L k hw hsum
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let vbar := b ^ 2 / (Annealed.sigmaBar M frameLabel : ℝ) ^ 2
  have hratio : ∀ a ∈ s,
      diagMeshRadius (Q a) 4 / (q3ModelLength N).1 ≤ 1 / 243 := by
    intro a ha
    exact aoCir_native_child_shell_ratio (hscale a ha) hN
  have hfamily := aoCir_reset_square_family_memLp reset M h hM hγ hγsmall
    hstate s w Q n ell frameLabel N hQ hK hscale (by omega) hw hsum b L
  have hidx : N - 1 + 1 = N := by omega
  have hYmem : ∀ q, 1 < q → ∀ t ∈ Icc (0 : ℝ) 1,
      MemLp (cirFamilyTrace F t) (ENNReal.ofReal q) μ := by
    intro q hq t ht
    have hq1 : 1 ≤ q := by linarith
    simpa only [F, k] using (hfamily q hq1 t ht.1 ht.2).1
  have hLmem : ∀ q, 1 ≤ q → ∀ t ∈ Icc (0 : ℝ) 1,
      MemLp (cirFamilyHistoryLoad F t) (ENNReal.ofReal q) μ := by
    intro q hq t ht
    simpa only [F, k] using (hfamily q hq t ht.1 ht.2).2
  have hdata : ∀ q, 1 < q → ∀ ε, 0 < ε →
      Gaussian.P12RegularizedHeatData μ (cirFamilyTrace F)
        (cirFamilyGenerator F) (cirFamilyBracket F) q ε := by
    intro q hq ε hε
    simpa only [K, μ, F, k, hidx] using aoCir_weightedSquareTrace_shell_family_heat_data n M h hM frameLabel
      (N - 1) s w Q (fun _ => 4) hQ hw hsum hq hε
  have hvariationRaw := aoCir_weightedSquareTrace_first_variation n M h hM
    frameLabel (N - 1) s w Q (fun _ => 4) hQ hw hsum
  have hvariation := by simpa only [K, μ, F, k, hidx] using hvariationRaw
  have hG4 := aoCir_square_output s w Q (fun _ => 4) M frameLabel b L
    hw hsum hratio k
  have hgen : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ω, cirFamilyGenerator F t ω ≤
      19 * vbar * cirFamilyHistoryLoad F t ω := by
    intro t ht ω
    simpa [vbar] using hG4.generator_bound t ω
  have hbracket : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ω, cirFamilyBracket F t ω ≤
      16 * vbar * cirFamilyTrace F t ω * cirFamilyHistoryLoad F t ω := by
    intro t ht ω
    simpa [vbar] using hG4.bracket_bound t ω
  have hpP' : p ≤ (smallGammaSeedP M.gamma : ℝ) :=
    (le_max_right (12 : ℝ) p).trans hpP
  have hU := aoCir_reset_square_family_history_load_time_integrable_window reset
    M h hM hγ hγsmall hstate s w Q n ell frameLabel N
    hQ hK hscale (by omega) hw hsum b L p hp hpP' hwindow
  have hU' : IntegrableOn
      (fun t => (19 + 8 * (p - 1)) * vbar *
        Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t))
      (Icc (0 : ℝ) 1) := by
    simpa only [K, μ, F, k, vbar] using hU
  have hcap (t : Set.Icc (0 : ℝ) 1) :
      eLpNorm (cirFamilyHistoryLoad F t.1) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 3120) := by
    simpa only [F, k, K, μ] using
      aoCir_finite_even_shell_load_cap_of_reset_window reset M h hM hγ
        hγsmall hstate s w Q n ell frameLabel N hQ hK hscale (by omega)
        hw hsum b L hp hpP hwindow t.1 t.2.1 t.2.2
  have hloadnorm (t : Set.Icc (0 : ℝ) 1) :
      Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t.1) ≤
        (2.2 : ℝ) ^ 2 * 3120 := by
    have hnormEq := Gaussian.positiveLpNorm_eq_eLpNorm_toReal μ
      (by linarith : 0 < p) (cirFamilyHistoryLoad F t.1)
      (cirFamilyHistoryLoad_nonneg F t.1)
      (hLmem p (by linarith) t.1 t.2)
    rw [hnormEq]
    calc
      (eLpNorm (cirFamilyHistoryLoad F t.1) (ENNReal.ofReal p) μ).toReal ≤
          (ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 3120)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcap t)
      _ = (2.2 : ℝ) ^ 2 * 3120 := by norm_num
  have hrate : 19 + 8 * (p - 1) ≤ 19 * p := by nlinarith [hp]
  have hvbar : 0 ≤ vbar := by positivity
  have hpoint (t : Set.Icc (0 : ℝ) 1) :
      (19 + 8 * (p - 1)) * vbar *
        Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t.1) ≤
      19 * p * vbar * ((2.2 : ℝ) ^ 2 * 3120) := by
    calc
      _ ≤ (19 + 8 * (p - 1)) * vbar * ((2.2 : ℝ) ^ 2 * 3120) :=
        mul_le_mul_of_nonneg_left (hloadnorm t)
          (mul_nonneg (by nlinarith [hp]) hvbar)
      _ ≤ 19 * p * vbar * ((2.2 : ℝ) ^ 2 * 3120) := by
        have hcoeff := mul_le_mul_of_nonneg_right hrate hvbar
        exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
  have hIntegral :
      (∫ t in (0 : ℝ)..1, (19 + 8 * (p - 1)) * vbar *
          Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t)) ≤
        19 * p * vbar * ((2.2 : ℝ) ^ 2 * 3120) := by
    have hUu : IntegrableOn
        (fun t => (19 + 8 * (p - 1)) * vbar *
          Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t))
        (Set.uIcc (0 : ℝ) 1) volume := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hU'
    have hmono := intervalIntegral.integral_mono_on
      (by norm_num : (0 : ℝ) ≤ 1) hUu.intervalIntegrable intervalIntegrable_const
      (fun t ht => hpoint ⟨t, ht⟩)
    simpa [intervalIntegral.integral_const] using hmono
  have htransport := aoCir_moment_transport_of_pathwise_bounds_on_unit_interval
    μ (cirFamilyTrace F) (cirFamilyGenerator F) (cirFamilyBracket F)
    (cirFamilyHistoryLoad F) (by linarith : 1 ≤ p) (by positivity : 0 ≤ vbar)
    (cirFamilyTrace_nonneg F) (cirFamilyHistoryLoad_nonneg F)
    hYmem hLmem hdata hgen hbracket hvariation.1 hvariation.2 hU
  have hmove := htransport 0 1 (by norm_num) (by norm_num) (by norm_num)
  calc
    _ ≤ ∫ t in (0 : ℝ)..1,
        (19 + 8 * (p - 1)) * vbar *
          Gaussian.positiveLpNorm μ p (cirFamilyHistoryLoad F t) := hmove
    _ ≤ 19 * p * vbar * ((2.2 : ℝ) ^ 2 * 3120) := hIntegral
    _ = 19 * p * vbar * ((2.2 : ℝ) ^ 2 * 3120) := rfl

/-- The end of shell `N` is the beginning of shell `N+1` on the same
completed coefficient path. -/
theorem aoCir_modelInsertedScalar_succ_endpoint
    {K : Set (Vec 2)} [CompactSpace K]
    (M : ABKModel 2) (ell N : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (ω : Cutoff.CutoffSample 2) :
    modelInsertedScalar K (N - 1) 1 ω = modelInsertedScalar K N 0 ω := by
  ext x
  rw [Gaussian.modelInsertedScalar_apply K M ell (N - 1) hK 1 ω x,
    Gaussian.modelInsertedScalar_apply K M ell N hK 0 ω x]
  have hone : Model.partialInsertedCoefficient M (N - 1) 1 ω x 1 0 =
      Cutoff.coefficientCutoff M.nu N ω x 1 0 := by
    have h := congrArg (fun a : RegCoeffField 2 => a x 1 0)
      (Main.mainInsertion_coefficient_one M (N - 1) ω)
    simpa only [show N - 1 + 1 = N by omega] using h
  have hzero : Model.partialInsertedCoefficient M N 0 ω x 1 0 =
      Cutoff.coefficientCutoff M.nu N ω x 1 0 := by
    simp [Model.partialInsertedCoefficient]
  exact hone.trans hzero.symm

/-- The translated-square trace family agrees at adjacent completed-shell
endpoints; its frame remains fixed throughout the eight insertions. -/
@[irreducible] noncomputable def aoCirFiniteEvenFamilyAt
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2)
    (M : ABKModel 2) (h : ℝ) (n frameLabel : ℤ)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆
      closure (cubeSet (originCube 2 n)))
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1) :
    ℤ → CIRResponseFamily ι (Cutoff.CutoffSample 2) := by
  let K := closure (cubeSet (originCube 2 n))
  exact fun j =>
    cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel
      (q3ModelAmplitude M h j) (q3ModelLength j)
      (fun a t ω => cirSquareRestrictionCLM (Q a) (hQ a)
        (modelInsertedScalar K (j - 1) t ω)) hw hsum

theorem aoCirFiniteEvenFamilyAt_trace
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2)
    (M : ABKModel 2) (h : ℝ) (n frameLabel : ℤ)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆
      closure (cubeSet (originCube 2 n)))
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1)
    (j : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    cirFamilyTrace (aoCirFiniteEvenFamilyAt s w Q M h n frameLabel hQ hw hsum j) t ω =
      ∑ a ∈ s, w a * Gaussian.squareTrace (Q a) M.nu
        (Annealed.sigmaBar M frameLabel)
        (cirSquareRestrictionCLM (Q a) (hQ a)
          (modelInsertedScalar (closure (cubeSet (originCube 2 n))) (j - 1) t ω)) := by
  classical
  simp only [aoCirFiniteEvenFamilyAt, cirFamilyTrace, cirSquareResponseFamily]

theorem aoCir_finite_even_family_succ_endpoint
    {ι : Type*} (FamilyAt : ℤ → CIRResponseFamily ι (Cutoff.CutoffSample 2))
    (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2)
    (M : ABKModel 2) (h : ℝ) (n ell frameLabel N : ℤ)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆
      closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1)
    (htrace : ∀ j t ω, cirFamilyTrace (FamilyAt j) t ω =
      ∑ a ∈ s, w a * Gaussian.squareTrace (Q a) M.nu
        (Annealed.sigmaBar M frameLabel)
        (cirSquareRestrictionCLM (Q a) (hQ a)
          (modelInsertedScalar (closure (cubeSet (originCube 2 n)))
            (j - 1) t ω))) :
    cirFamilyTrace (FamilyAt N) 1 = cirFamilyTrace (FamilyAt (N + 1)) 0 := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  funext ω
  rw [htrace N 1 ω, htrace (N + 1) 0 ω]
  have hindex : N + 1 - 1 = N := by omega
  simp only [hindex]
  apply Finset.sum_congr rfl
  intro a ha
  rw [aoCir_modelInsertedScalar_succ_endpoint M ell N hK ω]

/-- Eight consecutive actual shell transports, with the largest true-frame
variance clock paid once for each shell. This is the transport input to the
finite-even induction; it uses no reset data beyond the single producer. -/
theorem aoCir_finite_even_eight_shell_transport_of_reset
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2)
    (n ell frameLabel : ℤ)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆
      closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (hscale : ∀ a ∈ s, (Q a).scale = frameLabel)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1)
    {p : ℝ} (hp12 : 12 ≤ p) (hpP : p ≤ (smallGammaSeedP M.gamma : ℝ)) :
    let FamilyAt := aoCirFiniteEvenFamilyAt s w Q M h n frameLabel hQ hw hsum
    Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure p
        (cirFamilyTrace (FamilyAt (frameLabel + 8)) 1) -
      Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure p
        (cirFamilyTrace (FamilyAt (frameLabel + 1)) 0) ≤
      8 * (107 / 12 : ℝ) * p * (9 / 2 : ℝ) * M.gamma *
        (3 : ℝ) ^ (16 * M.gamma) * ((2.2 : ℝ) ^ 2 * 50) := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  let FamilyAt := aoCirFiniteEvenFamilyAt s w Q M h n frameLabel hQ hw hsum
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let C := (107 / 12 : ℝ) * p * (9 / 2 : ℝ) * M.gamma *
    (3 : ℝ) ^ (16 * M.gamma) * ((2.2 : ℝ) ^ 2 * 50)
  have htrace (j : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
      cirFamilyTrace (FamilyAt j) t ω =
        ∑ a ∈ s, w a * Gaussian.squareTrace (Q a) M.nu
          (Annealed.sigmaBar M frameLabel)
          (cirSquareRestrictionCLM (Q a) (hQ a)
            (modelInsertedScalar K (j - 1) t ω)) := by
    simpa [K] using
      aoCirFiniteEvenFamilyAt_trace s w Q M h n frameLabel hQ hw hsum j t ω
  have hendpoint (N : ℤ) :
      cirFamilyTrace (FamilyAt N) 1 = cirFamilyTrace (FamilyAt (N + 1)) 0 := by
    exact aoCir_finite_even_family_succ_endpoint FamilyAt s w Q M h n ell
      frameLabel N hQ hK hw hsum htrace
  have hstep (i : Fin 8) :
      Gaussian.positiveLpNorm μ p
          (cirFamilyTrace (FamilyAt (frameLabel + (i.val : ℤ) + 1)) 1) -
        Gaussian.positiveLpNorm μ p
          (cirFamilyTrace (FamilyAt (frameLabel + (i.val : ℤ) + 1)) 0) ≤ C := by
    let N := frameLabel + (i.val : ℤ) + 1
    have hN : frameLabel + 1 ≤ N := by dsimp [N]; omega
    have hNhi : N ≤ frameLabel + 8 := by
      dsimp [N]
      have hi := i.isLt
      omega
    have htransport := aoCir_finite_even_shell_transport_of_reset reset
      M h hM hγ hγsmall hstate s w Q n ell frameLabel N hQ hK hscale
      hN hNhi hw hsum hp12 hpP
    have hclock := aoCir_native_eight_shell_clock M h frameLabel N hNhi
      (hstate frameLabel)
    have hrate :
        (107 / 12 : ℝ) * p *
          (q3ModelAmplitude M h N ^ 2 /
            (Annealed.sigmaBar M frameLabel : ℝ) ^ 2) *
            ((2.2 : ℝ) ^ 2 * 50) ≤ C := by
      dsimp [C]
      have hpcoef0 : 0 ≤ (107 / 12 : ℝ) * p := by nlinarith [hp12]
      have hcap0 : 0 ≤ (2.2 : ℝ) ^ 2 * 50 := by positivity
      calc
        _ ≤ ((107 / 12 : ℝ) * p) *
            ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (16 * M.gamma)) *
            ((2.2 : ℝ) ^ 2 * 50) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hclock hpcoef0) hcap0
        _ = (107 / 12 : ℝ) * p * (9 / 2 : ℝ) * M.gamma *
            (3 : ℝ) ^ (16 * M.gamma) * ((2.2 : ℝ) ^ 2 * 50) := by ring
    simpa only [N, μ, FamilyAt, aoCirFiniteEvenFamilyAt] using
      htransport.trans hrate
  let A : ℕ → ℝ := fun i =>
    if i = 8 then
      Gaussian.positiveLpNorm μ p
        (cirFamilyTrace (FamilyAt (frameLabel + 8)) 1)
    else Gaussian.positiveLpNorm μ p
      (cirFamilyTrace (FamilyAt (frameLabel + (i : ℤ) + 1)) 0)
  have hincrement (i : Fin 8) :
      A (i.val + 1) - A i.val ≤ C := by
    let N := frameLabel + (i.val : ℤ) + 1
    have hstart : A i.val =
        Gaussian.positiveLpNorm μ p (cirFamilyTrace (FamilyAt N) 0) := by
      simpa only [A, if_neg (ne_of_lt i.isLt), N]
    have hend : A (i.val + 1) =
        Gaussian.positiveLpNorm μ p (cirFamilyTrace (FamilyAt N) 1) := by
      dsimp [A]
      by_cases hi : i.val + 1 = 8
      · rw [if_pos hi]
        have hN : N = frameLabel + 8 := by dsimp [N]; omega
        rw [hN]
      · rw [if_neg hi]
        have hindex : frameLabel + ((i.val : ℤ) + 1) + 1 = N + 1 := by
          dsimp [N]
          omega
        rw [hindex]
        have h := congrArg (Gaussian.positiveLpNorm μ p) (hendpoint N)
        exact h.symm
    rw [hend, hstart]
    exact hstep i
  have htel (j : ℕ) :
      Finset.sum (Finset.range j) (fun i => A (i + 1) - A i) = A j - A 0 := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      ring
  have hsumSteps : Finset.sum (Finset.range 8)
      (fun i => A (i + 1) - A i) ≤
      Finset.sum (Finset.range 8) (fun _i => C) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hincrement ⟨i, Finset.mem_range.mp hi⟩
  have htel8 := htel 8
  have hsumC : Finset.sum (Finset.range 8) (fun _i => C) = 8 * C := by simp
  rw [htel8, hsumC] at hsumSteps
  have hA8 : A 8 = Gaussian.positiveLpNorm μ p
      (cirFamilyTrace (FamilyAt (frameLabel + 8)) 1) := by
    simp [A]
  have hA0 : A 0 = Gaussian.positiveLpNorm μ p
      (cirFamilyTrace (FamilyAt (frameLabel + 1)) 0) := by
    simp [A]
  have hsumBoundary : Gaussian.positiveLpNorm μ p
      (cirFamilyTrace (FamilyAt (frameLabel + 8)) 1) ≤
      8 * C + Gaussian.positiveLpNorm μ p
        (cirFamilyTrace (FamilyAt (frameLabel + 1)) 0) := by
    rw [← hA8, ← hA0]
    linarith [hsumSteps]
  have hcoef : 8 * C = 8 * (107 / 12 : ℝ) * p * (9 / 2 : ℝ) *
      M.gamma * (3 : ℝ) ^ (16 * M.gamma) * ((2.2 : ℝ) ^ 2 * 50) := by
    dsimp [C]
    ring
  have hsumDirect : Gaussian.positiveLpNorm μ p
      (cirFamilyTrace (aoCirFiniteEvenFamilyAt s w Q M h n frameLabel
        hQ hw hsum (frameLabel + 8)) 1) ≤
      8 * (107 / 12 : ℝ) * p * (9 / 2 : ℝ) * M.gamma *
        (3 : ℝ) ^ (16 * M.gamma) * ((2.2 : ℝ) ^ 2 * 50) +
      Gaussian.positiveLpNorm μ p
        (cirFamilyTrace (aoCirFiniteEvenFamilyAt s w Q M h n frameLabel
          hQ hw hsum (frameLabel + 1)) 0) := by
    rw [hcoef] at hsumBoundary
    simpa [FamilyAt, μ] using hsumBoundary
  dsimp [μ, FamilyAt] at hsumDirect
  linarith

end ASDExplicitGamma.AllOrder

/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.CirResetTileHistoryLp
public import ASDExplicitGamma.AllOrder.CirResetProfiles
public import ASDExplicitGamma.AllOrder.CirMomentTransport
public import ASDExplicitGamma.AllOrder.CirFamilyHeatData

/-! # Reset-derived moment integrability for CIR heat loads -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

/-- The actual full trace on a one-shell insertion path has every reset-
derived moment of order at least two. -/
theorem aoCir_step_root_trace_memLp_of_reset
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    (Q : TriadicCube 2) (N K₀ : ℤ) (hN : Q.scale ≤ N)
    (p : ℝ) (hp2 : 2 ≤ p) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MemLp (rootTraceObservable M Q
      (protectedOldLabel Q.scale (orderBand p)) N K₀
      (aoCirStepWeights N t)) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := rootTraceObservable M Q
    (protectedOldLabel Q.scale (orderBand p)) N K₀
    (aoCirStepWeights N t)
  have hprofile := aoCir_step_profile_of_reset reset M h hM hγ hstate
    Q N K₀ hN p hp2 t ht0 ht1
  have hfinite : eLpNorm X (ENNReal.ofReal p) μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hprofile.1
  exact lt_top_iff_ne_top.mpr hfinite

/-- A single source history-load summand is integrable at every order q≥1.
The history uses the four-level fine grid, so its reset profile is evaluated
at order 48+4q and depth offset five; the full trace is evaluated at 2+2q.
-/
theorem aoCir_step_history_load_component_memLp_of_reset
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    (Q : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (N : ℤ) (hN : Q.scale ≤ N) (q : ℝ) (hq : 1 ≤ q)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MemLp (fun ω =>
      pureFluxSourceTileHistory Q 4
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M Q.scale : ℝ)
          (aoCirInsertedResponseCoefficient Q n hQ N t ω)) ^ 2 *
      rootTraceObservable M Q
        (protectedOldLabel Q.scale (orderBand (2 + 2 * q)))
        N Q.scale (aoCirStepWeights N t) ω)
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B := fun ω => pureFluxSourceTileHistory Q 4
    (responseFramePlanarCoefficientField M.nu
      (Annealed.sigmaBar M Q.scale : ℝ)
      (aoCirInsertedResponseCoefficient Q n hQ N t ω))
  let T := rootTraceObservable M Q
    (protectedOldLabel Q.scale (orderBand (2 + 2 * q)))
    N Q.scale (aoCirStepWeights N t)
  let qB : ℝ := 48 + 4 * q
  let qT : ℝ := 2 + 2 * q
  have hqB48 : 48 ≤ qB := by dsimp [qB]; linarith
  have hqT2 : 2 ≤ qT := by dsimp [qT]; linarith
  have hB := aoCir_reset_tile_history_memLp reset M h hM hγ hγsmall
    hstate Q n ell hQ hK N hN qB hqB48 t ht0 ht1
  have hT := aoCir_step_root_trace_memLp_of_reset reset M h hM hγ hstate
    Q N Q.scale hN qT hqT2 t ht0 ht1
  have hB4 : MemLp B (ENNReal.ofReal (4 * q)) μ := by
    apply hB.1.mono_exponent
    apply ENNReal.ofReal_le_ofReal
    dsimp [qB]
    linarith
  have hT2 : MemLp T (ENNReal.ofReal (2 * q)) μ := by
    apply hT.mono_exponent
    apply ENNReal.ofReal_le_ofReal
    dsimp [qT]
    linarith
  have hholderSq : Real.HolderTriple (4 * q) (4 * q) (2 * q) := by
    refine ⟨?_, by positivity, by positivity⟩
    field_simp
    ring
  have hholderOut : Real.HolderTriple (2 * q) (2 * q) q := by
    refine ⟨?_, by positivity, by positivity⟩
    field_simp
    ring
  letI := hholderSq.ennrealOfReal
  have hBsq : MemLp (fun ω => B ω * B ω) (ENNReal.ofReal (2 * q)) μ :=
    hB4.mul hB4
  letI := hholderOut.ennrealOfReal
  have hproduct : MemLp (fun ω => (B ω * B ω) * T ω)
      (ENNReal.ofReal q) μ := hBsq.mul hT2
  simpa only [B, T, pow_two] using hproduct

/-- Every finite actual translated-square family in one parent cube has the
all-orders trace and CIR history-load moments required by P12. The only
stochastic input is the single reset producer; the summands use the same
one-shell insertion path and the common completed true frame. -/
theorem aoCir_reset_square_family_memLp
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
    (hN : frameLabel ≤ N)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1)
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (q : ℝ) (hq1 : 1 ≤ q)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MemLp (cirFamilyTrace
      (cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L
        (fun a τ ω => cirSquareRestrictionCLM (Q a) (hQ a)
          (modelInsertedScalar (closure (cubeSet (originCube 2 n))) (N - 1) τ ω))
        hw hsum) t) (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    MemLp (cirFamilyHistoryLoad
      (cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L
        (fun a τ ω => cirSquareRestrictionCLM (Q a) (hQ a)
          (modelInsertedScalar (closure (cubeSet (originCube 2 n))) (N - 1) τ ω))
        hw hsum) t) (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  let k : (a : ι) → ℝ → Cutoff.CutoffSample 2 →
      ResponseCoefficient (openCubeSet (Q a)) := fun a τ ω =>
    cirSquareRestrictionCLM (Q a) (hQ a)
      (modelInsertedScalar K (N - 1) τ ω)
  let F := cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L k hw hsum
  have hQscale (a : ι) (ha : a ∈ s) : (Q a).scale ≤ N := by
    rw [hscale a ha]
    exact hN
  have hTraceEq (a : ι) (ha : a ∈ s) (p : ℝ) (ω : Cutoff.CutoffSample 2) :
      rootTraceObservable M (Q a)
        (protectedOldLabel (Q a).scale (orderBand p)) N frameLabel
        (aoCirStepWeights N t) ω = F.trace a t ω + 4 := by
    have hOld : protectedOldLabel (Q a).scale (orderBand p) < N := by
      have hscale' := hscale a ha
      dsimp [protectedOldLabel]
      omega
    have hEq := aoCir_step_trace_eq_squareTrace M (Q a) n ell
      (hQ a) hK (protectedOldLabel (Q a).scale (orderBand p))
      N frameLabel hOld t ω
    simpa [F, cirSquareResponseFamily, k, K, hscale a ha] using hEq
  have hTraceTerm (a : ι) (ha : a ∈ s) :
      MemLp (fun ω => w a * F.trace a t ω) (ENNReal.ofReal q)
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    let qRoot := max 2 q
    have hqRoot2 : 2 ≤ qRoot := le_max_left _ _
    have hqle : q ≤ qRoot := le_max_right _ _
    have hRoot := aoCir_step_root_trace_memLp_of_reset reset M h hM hγ hstate
      (Q a) N frameLabel (hQscale a ha) qRoot hqRoot2 t ht0 ht1
    have hRootq : MemLp (rootTraceObservable M (Q a)
        (protectedOldLabel (Q a).scale (orderBand qRoot)) N frameLabel
        (aoCirStepWeights N t)) (ENNReal.ofReal q)
        (Cutoff.cutoffSampleLaw M).toMeasure := by
      apply hRoot.mono_exponent
      exact ENNReal.ofReal_le_ofReal hqle
    have hLocal : MemLp (fun ω => F.trace a t ω) (ENNReal.ofReal q)
        (Cutoff.cutoffSampleLaw M).toMeasure := by
      have hSub := hRootq.sub (memLp_const (4 : ℝ))
      have hEq : (fun ω => rootTraceObservable M (Q a)
          (protectedOldLabel (Q a).scale (orderBand qRoot)) N frameLabel
          (aoCirStepWeights N t) ω - 4) = fun ω => F.trace a t ω := by
        funext ω
        have heq := hTraceEq a ha qRoot ω
        dsimp [F, cirSquareResponseFamily] at heq ⊢
        linarith
      exact (memLp_congr_ae (Filter.Eventually.of_forall fun ω => congrFun hEq ω)).mp hSub
    simpa [F] using hLocal.const_mul (w a)
  have hLoadTerm (a : ι) (ha : a ∈ s) :
      MemLp (fun ω => w a * F.inverseHistory a t ω ^ 2 *
          (F.trace a t ω + 4)) (ENNReal.ofReal q)
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    have hcomponent := aoCir_step_history_load_component_memLp_of_reset reset
      M h hM hγ hγsmall hstate (Q a) n ell (hQ a) hK N
      (hQscale a ha) q hq1 t ht0 ht1
    have hrewrite : (fun ω => w a * (pureFluxSourceTileHistory (Q a) 4
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M (Q a).scale : ℝ)
            (aoCirInsertedResponseCoefficient (Q a) n (hQ a) N t ω)) ^ 2 *
          rootTraceObservable M (Q a)
            (protectedOldLabel (Q a).scale (orderBand (2 + 2 * q)))
            N (Q a).scale (aoCirStepWeights N t) ω)) =
        fun ω => w a * F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4) := by
      funext ω
      have heq := hTraceEq a ha (2 + 2 * q) ω
      dsimp [F, cirSquareResponseFamily, k, aoCirInsertedResponseCoefficient] at heq ⊢
      rw [hscale a ha]
      rw [hscale a ha] at heq
      rw [← heq]
      ac_rfl
    have hrewriteMem : MemLp (fun ω => w a * (pureFluxSourceTileHistory (Q a) 4
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M (Q a).scale : ℝ)
            (aoCirInsertedResponseCoefficient (Q a) n (hQ a) N t ω)) ^ 2 *
          rootTraceObservable M (Q a)
            (protectedOldLabel (Q a).scale (orderBand (2 + 2 * q)))
            N (Q a).scale (aoCirStepWeights N t) ω))
        (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure :=
      hcomponent.const_mul (w a)
    have hrewriteMem' := (memLp_congr_ae
      (Filter.Eventually.of_forall fun ω => congrFun hrewrite ω)).mp hrewriteMem
    simpa [F] using hrewriteMem'
  have hTraceSum : MemLp (fun ω => ∑ a ∈ s, w a * F.trace a t ω)
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure :=
    memLp_finsetSum s (fun a ha => hTraceTerm a ha)
  have hLoadSum : MemLp (fun ω => ∑ a ∈ s,
      w a * F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure :=
    memLp_finsetSum s (fun a ha => hLoadTerm a ha)
  constructor
  · change MemLp (cirFamilyTrace F t) (ENNReal.ofReal q)
      (Cutoff.cutoffSampleLaw M).toMeasure
    exact hTraceSum
  · change MemLp (cirFamilyHistoryLoad F t) (ENNReal.ofReal q)
      (Cutoff.cutoffSampleLaw M).toMeasure
    exact hLoadSum

/-- On the finite-even source band, the actual one-cell CIR load has the
uniform profile-derived moment cap: tile-history order `4q` at 2.2 and
trace order `2q` at 50. -/
theorem aoCir_step_history_load_component_cap_of_reset
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    (Q : TriadicCube 2) (n ell frameLabel N : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (hscale : Q.scale = frameLabel) (hN : frameLabel ≤ N)
    (hNhi : N ≤ frameLabel + 8)
    (q : ℝ) (hq12 : 12 ≤ q) (hqP : q ≤ (smallGammaSeedP M.gamma : ℝ))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm (fun ω =>
      pureFluxSourceTileHistory Q 4
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M Q.scale : ℝ)
          (aoCirInsertedResponseCoefficient Q n hQ N t ω)) ^ 2 *
      rootTraceObservable M Q
        (protectedOldLabel Q.scale (orderBand (2 * q)))
        N frameLabel (aoCirStepWeights N t) ω)
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 50) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B := fun ω => pureFluxSourceTileHistory Q 4
    (responseFramePlanarCoefficientField M.nu
      (Annealed.sigmaBar M Q.scale : ℝ)
      (aoCirInsertedResponseCoefficient Q n hQ N t ω))
  let T := rootTraceObservable M Q
    (protectedOldLabel Q.scale (orderBand (2 * q)))
    N frameLabel (aoCirStepWeights N t)
  let qT : ℝ := 2 * q
  let qI : ℝ := 4 * q
  have hqT : 2 ≤ qT := by dsimp [qT]; linarith
  have hqI48 : 48 ≤ qI := by dsimp [qI]; linarith
  have hqTband : qT ≤ 4 * (smallGammaSeedP M.gamma : ℝ) := by
    dsimp [qT]
    nlinarith [hqP]
  have hqIband : qI ≤ 4 * (smallGammaSeedP M.gamma : ℝ) := by
    dsimp [qI]
    nlinarith [hqP]
  have hB := aoCir_reset_tile_history_memLp reset M h hM hγ hγsmall
    hstate Q n ell hQ hK N (by rw [hscale]; exact hN) qI hqI48 t ht0 ht1
  have hTmem := aoCir_step_root_trace_memLp_of_reset reset M h hM hγ hstate
    Q N frameLabel (by rw [hscale]; exact hN) qT hqT t ht0 ht1
  have hcaps := aoCir_step_small_gamma_profile_caps_of_reset reset M h hM hγ hγsmall
    hstate Q Q N (by rw [hscale]; exact hN) (by rw [hscale]; exact hNhi)
    (by rw [hscale]; exact hN) frameLabel frameLabel
    (by rw [hscale]; norm_num) (by rw [hscale]; norm_num)
    qT qI hqT hqTband hqI48 hqIband t ht0 ht1
  have hheight : 0 ≤
      (Inverse.heightEntrance (Inverse.orderBand qI) : ℝ) := by positivity
  have hband := aoCir_small_gamma_profile_band_bounds M.shellPrefix.gamma_pos hγsmall
    (show 2 ≤ qI by linarith) hqIband
  have hprofile :
      Inverse.orderInverseProfile (153 / 100) M.gamma qI 5 ≤
        (153 / 100 : ℝ) * (3 : ℝ) ^
          (2 * M.gamma *
            ((Inverse.heightEntrance (Inverse.orderBand qI) : ℝ) + 20) +
            2 * M.gamma * 5) := by rfl
  have hscalar := aoCir_small_gamma_inverse_profile_cap
    (γ := M.gamma) (hγ := M.shellPrefix.gamma_pos.le) (hh := hheight)
    (hγsmall := hγsmall) (hshift := hband.1.le)
    (hf0 := by norm_num) (hf := by norm_num) (hq := hqI48)
    (R := Inverse.orderInverseProfile (153 / 100) M.gamma qI 5) hprofile
  have hpow : Real.rpow 9 (4 / qI) = (3 : ℝ) ^ (8 / qI) := by
    rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num]
    calc
      _ = (3 : ℝ) ^ ((2 : ℝ) * (4 / qI)) :=
        (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 3) 2 (4 / qI)).symm
      _ = (3 : ℝ) ^ (8 / qI) := by
        congr 1
        dsimp [qI]
        field_simp
        ring
  have hscalar' : aoCirInverseHistoryFactor M.gamma * Real.rpow 9 (4 / qI) *
      Inverse.orderInverseProfile (153 / 100) M.gamma qI 5 < 2.2 := by
    rw [hpow]
    exact hscalar
  have hBcap : eLpNorm B (ENNReal.ofReal qI) μ ≤ ENNReal.ofReal 2.2 := by
    calc
      _ ≤ ENNReal.ofReal (aoCirInverseHistoryFactor M.gamma *
          Real.rpow 9 (4 / qI) *
            Inverse.orderInverseProfile (153 / 100) M.gamma qI 5) := hB.2
      _ ≤ ENNReal.ofReal 2.2 := ENNReal.ofReal_le_ofReal hscalar'.le
  have hTcap : eLpNorm T (ENNReal.ofReal qT) μ ≤ ENNReal.ofReal 50 := by
    simpa [T, qT] using hcaps.1
  have hB0 (ω : Cutoff.CutoffSample 2) : 0 ≤ B ω :=
    pureFlux_source_tile_history_nonneg Q 4 _
  have hBpow : eLpNorm (fun ω => B ω * B ω) (ENNReal.ofReal (2 * q)) μ =
      eLpNorm B (ENNReal.ofReal (4 * q)) μ ^ 2 := by
    have h := eLpNorm_norm_rpow (p := ENNReal.ofReal (2 * q)) (f := B)
      hB.1.aestronglyMeasurable (by norm_num : (0 : ℝ) < 2)
    have hfun : (fun ω => B ω * B ω) = fun ω => ‖B ω‖ ^ (2 : ℝ) := by
      funext ω
      simp [Real.norm_of_nonneg (hB0 ω), Real.rpow_natCast, pow_two]
    have hexponent : ENNReal.ofReal (2 * q) * ENNReal.ofReal (2 : ℝ) =
        ENNReal.ofReal (4 * q) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * q)]
      congr 1
      ring
    rw [hexponent] at h
    rw [hfun]
    exact h.trans (ENNReal.rpow_natCast _ 2)
  letI := (show Real.HolderTriple (4 * q) (4 * q) (2 * q) from by
    refine ⟨?_, by positivity, by positivity⟩
    field_simp
    ring).ennrealOfReal
  have hBsq : MemLp (fun ω => B ω * B ω) (ENNReal.ofReal (2 * q)) μ :=
    hB.1.mul hB.1
  letI := (show Real.HolderTriple (2 * q) (2 * q) q from by
    refine ⟨?_, by positivity, by positivity⟩
    field_simp
    ring).ennrealOfReal
  have hproductMem : MemLp (fun ω => (B ω * B ω) * T ω)
      (ENNReal.ofReal q) μ := hBsq.mul hTmem
  have hproductHolder := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
    (p := ENNReal.ofReal (2 * q)) (q := ENNReal.ofReal (2 * q))
    (r := ENNReal.ofReal q) (b := fun x y : ℝ => x * y) (c := 1)
    (f := fun ω => B ω * B ω) (g := T)
    (by fun_prop) hBsq.aestronglyMeasurable hTmem.aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => by simp)
  have hBsqCap : eLpNorm (fun ω => B ω * B ω) (ENNReal.ofReal (2 * q)) μ ≤
      ENNReal.ofReal ((2.2 : ℝ) ^ 2) := by
    rw [hBpow]
    calc
      _ ≤ ENNReal.ofReal 2.2 ^ 2 := by gcongr
      _ = ENNReal.ofReal ((2.2 : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_pow]
        norm_num
  have hproductCap : eLpNorm (fun ω => (B ω * B ω) * T ω)
      (ENNReal.ofReal q) μ ≤ ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 50) := by
    calc
      _ ≤ eLpNorm (fun ω => B ω * B ω) (ENNReal.ofReal (2 * q)) μ *
          eLpNorm T (ENNReal.ofReal (2 * q)) μ := by simpa using hproductHolder
      _ ≤ ENNReal.ofReal ((2.2 : ℝ) ^ 2) * ENNReal.ofReal 50 := by gcongr
      _ = ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 50) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2.2 : ℝ) ^ 2)]
  simpa [B, T, pow_two] using hproductCap

/-- Arbitrary-depth variant of the CIR load cap. The trace profile is capped
at 3120 by the direct order-depth gate; the complete four-level inverse
history remains capped at 2.2 from the same reset profile. -/
theorem aoCir_step_history_load_component_cap_of_reset_window
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    (Q : TriadicCube 2) (n ell frameLabel N : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (hscale : Q.scale = frameLabel) (hN : frameLabel ≤ N)
    (q : ℝ) (hq12 : 12 ≤ q) (hqP : q ≤ (smallGammaSeedP M.gamma : ℝ))
    (hwindow : M.gamma * q * ((N - frameLabel : ℤ) + 2 : ℝ) ≤ 1 / 512)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm (fun ω =>
      pureFluxSourceTileHistory Q 4
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M Q.scale : ℝ)
          (aoCirInsertedResponseCoefficient Q n hQ N t ω)) ^ 2 *
      rootTraceObservable M Q
        (protectedOldLabel Q.scale (orderBand (2 * q)))
        N frameLabel (aoCirStepWeights N t) ω)
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 3120) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B := fun ω => pureFluxSourceTileHistory Q 4
    (responseFramePlanarCoefficientField M.nu
      (Annealed.sigmaBar M Q.scale : ℝ)
      (aoCirInsertedResponseCoefficient Q n hQ N t ω))
  let T := rootTraceObservable M Q
    (protectedOldLabel Q.scale (orderBand (2 * q)))
    N frameLabel (aoCirStepWeights N t)
  let qT : ℝ := 2 * q
  let qI : ℝ := 4 * q
  have hqT : 2 ≤ qT := by dsimp [qT]; linarith
  have hqI48 : 48 ≤ qI := by dsimp [qI]; linarith
  have hqTband : qT ≤ 4 * (smallGammaSeedP M.gamma : ℝ) := by
    dsimp [qT]
    nlinarith [hqP]
  have hqIband : qI ≤ 4 * (smallGammaSeedP M.gamma : ℝ) := by
    dsimp [qI]
    nlinarith [hqP]
  have hB := aoCir_reset_tile_history_memLp reset M h hM hγ hγsmall
    hstate Q n ell hQ hK N (by rw [hscale]; exact hN) qI hqI48 t ht0 ht1
  have hTmem := aoCir_step_root_trace_memLp_of_reset reset M h hM hγ hstate
    Q N frameLabel (by rw [hscale]; exact hN) qT hqT t ht0 ht1
  have hprof := aoCir_step_profile_of_reset reset M h hM hγ hstate
    Q N frameLabel (by rw [hscale]; exact hN) qT hqT t ht0 ht1
  have hband := aoCir_small_gamma_profile_band_bounds M.shellPrefix.gamma_pos hγsmall
    hqT hqTband
  have hheight : 0 ≤
      (Inverse.heightEntrance (Inverse.orderBand qT) : ℝ) := by positivity
  have hD0 : 0 ≤ ((N - frameLabel + 1 : ℤ) : ℝ) := by
    have hgap : 0 ≤ ((N - frameLabel : ℤ) : ℝ) := by
      exact_mod_cast (show 0 ≤ N - frameLabel by omega)
    have hcast : ((N - frameLabel + 1 : ℤ) : ℝ) =
        ((N - frameLabel : ℤ) : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith
  have hDgate : M.gamma * qT * (((N - frameLabel + 1 : ℤ) : ℝ) + 1) ≤ 1 / 256 := by
    have hgap : ((N - frameLabel + 1 : ℤ) : ℝ) + 1 =
        ((N - frameLabel : ℤ) + 2 : ℝ) := by push_cast; ring
    rw [hgap]
    dsimp [qT]
    nlinarith [hwindow]
  have htraceProfile :
      Inverse.orderTraceProfile M.gamma qT
          ((N - frameLabel + 1 : ℤ) : ℝ) 1 ≤ 3120 := by
    apply le_of_lt (aoCir_depth_trace_profile_cap
      (γ := M.gamma) (h := (Inverse.heightEntrance (Inverse.orderBand qT) : ℝ))
      (p := qT) (D := ((N - frameLabel + 1 : ℤ) : ℝ)) (f := 1)
      (T := Inverse.orderTraceProfile M.gamma qT
        ((N - frameLabel + 1 : ℤ) : ℝ) 1)
      M.shellPrefix.gamma_pos.le (by norm_num at hγ ⊢; linarith)
      hheight hqT hD0 hDgate (by norm_num) (by norm_num) (by linarith [hband.1]) (by rfl))
  have hTcap : eLpNorm T (ENNReal.ofReal qT) μ ≤ ENNReal.ofReal 3120 := by
    have hprofile : eLpNorm T (ENNReal.ofReal qT) μ ≤
        ENNReal.ofReal (Inverse.orderTraceProfile M.gamma qT
          ((N - frameLabel + 1 : ℤ) : ℝ) 1) := by
      simpa [T, qT, hscale] using hprof.1
    exact hprofile.trans (ENNReal.ofReal_le_ofReal htraceProfile)
  have hheightI : 0 ≤
      (Inverse.heightEntrance (Inverse.orderBand qI) : ℝ) := by positivity
  have hbandI := aoCir_small_gamma_profile_band_bounds M.shellPrefix.gamma_pos hγsmall
    (show 2 ≤ qI by linarith) hqIband
  have hprofileI : Inverse.orderInverseProfile (153 / 100) M.gamma qI 5 ≤
      (153 / 100 : ℝ) * (3 : ℝ) ^
        (2 * M.gamma * ((Inverse.heightEntrance (Inverse.orderBand qI) : ℝ) + 20) +
          2 * M.gamma * 5) := by rfl
  have hscalar := aoCir_small_gamma_inverse_profile_cap
    (γ := M.gamma) (h := (Inverse.heightEntrance (Inverse.orderBand qI) : ℝ))
    (f := 5) (q := qI) (R := Inverse.orderInverseProfile (153 / 100) M.gamma qI 5)
    M.shellPrefix.gamma_pos.le hheightI hγsmall hbandI.1.le
    (by norm_num) (by norm_num) hqI48 hprofileI
  have hpow : Real.rpow 9 (4 / qI) = (3 : ℝ) ^ (8 / qI) := by
    rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num]
    calc
      _ = (3 : ℝ) ^ ((2 : ℝ) * (4 / qI)) :=
        (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 3) 2 (4 / qI)).symm
      _ = (3 : ℝ) ^ (8 / qI) := by congr 1; dsimp [qI]; field_simp; ring
  have hscalar' : aoCirInverseHistoryFactor M.gamma * Real.rpow 9 (4 / qI) *
      Inverse.orderInverseProfile (153 / 100) M.gamma qI 5 < 2.2 := by
    rw [hpow]
    exact hscalar
  have hBcap : eLpNorm B (ENNReal.ofReal qI) μ ≤ ENNReal.ofReal 2.2 := by
    calc
      _ ≤ ENNReal.ofReal (aoCirInverseHistoryFactor M.gamma *
          Real.rpow 9 (4 / qI) *
            Inverse.orderInverseProfile (153 / 100) M.gamma qI 5) := hB.2
      _ ≤ ENNReal.ofReal 2.2 := ENNReal.ofReal_le_ofReal hscalar'.le
  have hB0 (ω : Cutoff.CutoffSample 2) : 0 ≤ B ω :=
    pureFlux_source_tile_history_nonneg Q 4 _
  have hBpow : eLpNorm (fun ω => B ω * B ω) (ENNReal.ofReal (2 * q)) μ =
      eLpNorm B (ENNReal.ofReal (4 * q)) μ ^ 2 := by
    have h := eLpNorm_norm_rpow (p := ENNReal.ofReal (2 * q)) (f := B)
      hB.1.aestronglyMeasurable (by norm_num : (0 : ℝ) < 2)
    have hfun : (fun ω => B ω * B ω) = fun ω => ‖B ω‖ ^ (2 : ℝ) := by
      funext ω
      simp [Real.norm_of_nonneg (hB0 ω), Real.rpow_natCast, pow_two]
    have hexponent : ENNReal.ofReal (2 * q) * ENNReal.ofReal (2 : ℝ) =
        ENNReal.ofReal (4 * q) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * q)]
      congr 1
      ring
    rw [hexponent] at h
    rw [hfun]
    exact h.trans (ENNReal.rpow_natCast _ 2)
  letI := (show Real.HolderTriple (4 * q) (4 * q) (2 * q) from by
    refine ⟨?_, by positivity, by positivity⟩
    field_simp
    ring).ennrealOfReal
  have hBsq : MemLp (fun ω => B ω * B ω) (ENNReal.ofReal (2 * q)) μ :=
    hB.1.mul hB.1
  letI := (show Real.HolderTriple (2 * q) (2 * q) q from by
    refine ⟨?_, by positivity, by positivity⟩
    field_simp
    ring).ennrealOfReal
  have hproductMem : MemLp (fun ω => (B ω * B ω) * T ω)
      (ENNReal.ofReal q) μ := hBsq.mul hTmem
  have hproductHolder := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
    (p := ENNReal.ofReal (2 * q)) (q := ENNReal.ofReal (2 * q))
    (r := ENNReal.ofReal q) (b := fun x y : ℝ => x * y) (c := 1)
    (f := fun ω => B ω * B ω) (g := T)
    (by fun_prop) hBsq.aestronglyMeasurable hTmem.aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => by simp)
  have hBsqCap : eLpNorm (fun ω => B ω * B ω) (ENNReal.ofReal (2 * q)) μ ≤
      ENNReal.ofReal ((2.2 : ℝ) ^ 2) := by
    rw [hBpow]
    calc
      _ ≤ ENNReal.ofReal 2.2 ^ 2 := by gcongr
      _ = ENNReal.ofReal ((2.2 : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_pow]
        norm_num
  have hproductCap : eLpNorm (fun ω => (B ω * B ω) * T ω)
      (ENNReal.ofReal q) μ ≤ ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 3120) := by
    calc
      _ ≤ eLpNorm (fun ω => B ω * B ω) (ENNReal.ofReal (2 * q)) μ *
          eLpNorm T (ENNReal.ofReal (2 * q)) μ := by simpa using hproductHolder
      _ ≤ ENNReal.ofReal ((2.2 : ℝ) ^ 2) * ENNReal.ofReal 3120 := by gcongr
      _ = ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 3120) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2.2 : ℝ) ^ 2)]
  simpa [B, T, pow_two] using hproductCap

/-- A finite probability-weighted family inherits the same 2.2²·50 load cap
from the reset-derived one-cell estimate. The weights sum to one, so Minkowski
does not introduce a population factor. -/
theorem aoCir_reset_square_family_history_load_cap
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
    (hN : frameLabel ≤ N) (hNhi : N ≤ frameLabel + 8)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1)
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (q : ℝ) (hq12 : 12 ≤ q)
    (hqP : q ≤ (smallGammaSeedP M.gamma : ℝ))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm
      (cirFamilyHistoryLoad
        (cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L
          (fun a τ ω => cirSquareRestrictionCLM (Q a) (hQ a)
            (modelInsertedScalar (closure (cubeSet (originCube 2 n))) (N - 1) τ ω))
          hw hsum) t)
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 50) := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  let k : (a : ι) → ℝ → Cutoff.CutoffSample 2 →
      ResponseCoefficient (openCubeSet (Q a)) := fun a τ ω =>
    cirSquareRestrictionCLM (Q a) (hQ a) (modelInsertedScalar K (N - 1) τ ω)
  let F := cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L k hw hsum
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hScaleN (a : ι) (ha : a ∈ s) : (Q a).scale ≤ N := by
    rw [hscale a ha]
    exact hN
  have hTraceEq (a : ι) (ha : a ∈ s) (p : ℝ)
      (ω : Cutoff.CutoffSample 2) :
      rootTraceObservable M (Q a)
        (protectedOldLabel (Q a).scale (orderBand p)) N frameLabel
        (aoCirStepWeights N t) ω = F.trace a t ω + 4 := by
    have hOld : protectedOldLabel (Q a).scale (orderBand p) < N := by
      have hscale' := hscale a ha
      dsimp [protectedOldLabel]
      omega
    have hEq := aoCir_step_trace_eq_squareTrace M (Q a) n ell
      (hQ a) hK (protectedOldLabel (Q a).scale (orderBand p))
      N frameLabel hOld t ω
    simpa [F, cirSquareResponseFamily, k, K, hscale a ha] using hEq
  have htermCap (a : ι) (ha : a ∈ s) :
      eLpNorm (fun ω => w a * F.inverseHistory a t ω ^ 2 *
          (F.trace a t ω + 4)) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (w a * ((2.2 : ℝ) ^ 2 * 50)) := by
    have hcomponent := aoCir_step_history_load_component_cap_of_reset reset
      M h hM hγ hγsmall hstate (Q a) n ell frameLabel N (hQ a) hK
      (hscale a ha) hN hNhi
      q hq12 hqP t ht0 ht1
    let B := fun ω => pureFluxSourceTileHistory (Q a) 4
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M (Q a).scale : ℝ)
        (aoCirInsertedResponseCoefficient (Q a) n (hQ a) N t ω))
    have hrewrite :
        (fun ω => F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4)) =
        fun ω => B ω ^ 2 * rootTraceObservable M (Q a)
          (protectedOldLabel (Q a).scale (orderBand (2 * q)))
          N frameLabel (aoCirStepWeights N t) ω := by
      funext ω
      have hte := hTraceEq a ha (2 * q) ω
      have hB : F.inverseHistory a t ω = B ω := by
        simp [B, F, cirSquareResponseFamily, k,
          K, aoCirInsertedResponseCoefficient, hscale a ha]
      calc
        _ = B ω ^ 2 * (F.trace a t ω + 4) := by rw [hB]
        _ = B ω ^ 2 * rootTraceObservable M (Q a)
            (protectedOldLabel (Q a).scale (orderBand (2 * q)))
            N frameLabel (aoCirStepWeights N t) ω := by rw [← hte]
    have hscalar :
        (fun ω => w a * F.inverseHistory a t ω ^ 2 *
            (F.trace a t ω + 4)) =
          w a • (fun ω => B ω ^ 2 *
            rootTraceObservable M (Q a)
              (protectedOldLabel (Q a).scale (orderBand (2 * q)))
              N frameLabel (aoCirStepWeights N t) ω) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      calc
        _ = w a * (F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4)) := by ring
        _ = w a * (B ω ^ 2 * rootTraceObservable M (Q a)
            (protectedOldLabel (Q a).scale (orderBand (2 * q)))
            N frameLabel (aoCirStepWeights N t) ω) :=
          congrArg (fun x : ℝ => w a * x) (congrFun hrewrite ω)
    rw [hscalar, eLpNorm_const_smul, Real.enorm_eq_ofReal (hw a ha),
      ENNReal.ofReal_mul (hw a ha)]
    exact mul_le_mul_of_nonneg_left hcomponent (zero_le : (0 : ℝ≥0∞) ≤ _)
  have hsumEq : cirFamilyHistoryLoad F t =
      fun ω => ∑ a ∈ s, w a * F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4) := by
    funext ω
    simp [cirFamilyHistoryLoad, F, cirSquareResponseFamily]
  have hpENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q :=
    ENNReal.one_le_ofReal.mpr (by linarith)
  calc
    _ = eLpNorm (fun ω => ∑ a ∈ s,
          w a * F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4))
        (ENNReal.ofReal q) μ := by rw [hsumEq]
    _ ≤ ∑ a ∈ s, eLpNorm (fun ω =>
          w a * F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4))
        (ENNReal.ofReal q) μ := by
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (μ := μ)
          (f := fun a ω => w a * F.inverseHistory a t ω ^ 2 *
            (F.trace a t ω + 4)) (s := s) hpENN)
    _ ≤ ∑ a ∈ s,
          ENNReal.ofReal (w a * ((2.2 : ℝ) ^ 2 * 50)) :=
      Finset.sum_le_sum fun a ha => htermCap a ha
    _ = ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 50) := by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun a ha => mul_nonneg (hw a ha) (by positivity))]
      rw [← Finset.sum_mul, hsum, one_mul]

/-- Minkowski lifts a uniform one-cell CIR load cap to any finite
probability-weighted translated-square family. -/
theorem aoCir_reset_square_family_history_load_cap_of_component
    (M : ABKModel 2) {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (Q : ι → TriadicCube 2)
    (n ell frameLabel N : ℤ)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆
      closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (hscale : ∀ a ∈ s, (Q a).scale = frameLabel)
    (hN : frameLabel ≤ N)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1)
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (q C : ℝ) (hq1 : 1 ≤ q) (hC : 0 ≤ C)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hcomponent : ∀ a ∈ s,
      eLpNorm (fun ω =>
        pureFluxSourceTileHistory (Q a) 4
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M (Q a).scale : ℝ)
            (aoCirInsertedResponseCoefficient (Q a) n (hQ a) N t ω)) ^ 2 *
        rootTraceObservable M (Q a)
          (protectedOldLabel (Q a).scale (orderBand (2 * q)))
          N frameLabel (aoCirStepWeights N t) ω)
        (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal C) :
    eLpNorm
      (cirFamilyHistoryLoad
        (cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L
          (fun a τ ω => cirSquareRestrictionCLM (Q a) (hQ a)
            (modelInsertedScalar (closure (cubeSet (originCube 2 n))) (N - 1) τ ω))
          hw hsum) t)
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  let k : (a : ι) → ℝ → Cutoff.CutoffSample 2 →
      ResponseCoefficient (openCubeSet (Q a)) := fun a τ ω =>
    cirSquareRestrictionCLM (Q a) (hQ a) (modelInsertedScalar K (N - 1) τ ω)
  let F := cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L k hw hsum
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hTraceEq (a : ι) (ha : a ∈ s) (p : ℝ)
      (ω : Cutoff.CutoffSample 2) :
      rootTraceObservable M (Q a)
        (protectedOldLabel (Q a).scale (orderBand p)) N frameLabel
        (aoCirStepWeights N t) ω = F.trace a t ω + 4 := by
    have hOld : protectedOldLabel (Q a).scale (orderBand p) < N := by
      have hscale' := hscale a ha
      dsimp [protectedOldLabel]
      omega
    have hEq := aoCir_step_trace_eq_squareTrace M (Q a) n ell
      (hQ a) hK (protectedOldLabel (Q a).scale (orderBand p))
      N frameLabel hOld t ω
    simpa [F, cirSquareResponseFamily, k, K, hscale a ha] using hEq
  have htermCap (a : ι) (ha : a ∈ s) :
      eLpNorm (fun ω => w a * F.inverseHistory a t ω ^ 2 *
          (F.trace a t ω + 4)) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (w a * C) := by
    have hcomp := hcomponent a ha
    let B := fun ω => pureFluxSourceTileHistory (Q a) 4
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M (Q a).scale : ℝ)
        (aoCirInsertedResponseCoefficient (Q a) n (hQ a) N t ω))
    have hrewrite :
        (fun ω => F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4)) =
        fun ω => B ω ^ 2 * rootTraceObservable M (Q a)
          (protectedOldLabel (Q a).scale (orderBand (2 * q)))
          N frameLabel (aoCirStepWeights N t) ω := by
      funext ω
      have hte := hTraceEq a ha (2 * q) ω
      have hB : F.inverseHistory a t ω = B ω := by
        simp [B, F, cirSquareResponseFamily, k, K,
          aoCirInsertedResponseCoefficient, hscale a ha]
      calc
        _ = B ω ^ 2 * (F.trace a t ω + 4) := by rw [hB]
        _ = B ω ^ 2 * rootTraceObservable M (Q a)
            (protectedOldLabel (Q a).scale (orderBand (2 * q)))
            N frameLabel (aoCirStepWeights N t) ω := by rw [← hte]
    have hscalar :
        (fun ω => w a * F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4)) =
          w a • (fun ω => B ω ^ 2 *
            rootTraceObservable M (Q a)
              (protectedOldLabel (Q a).scale (orderBand (2 * q)))
              N frameLabel (aoCirStepWeights N t) ω) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      calc
        _ = w a * (F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4)) := by ring
        _ = w a * (B ω ^ 2 * rootTraceObservable M (Q a)
            (protectedOldLabel (Q a).scale (orderBand (2 * q)))
            N frameLabel (aoCirStepWeights N t) ω) :=
          congrArg (fun x : ℝ => w a * x) (congrFun hrewrite ω)
    rw [hscalar, eLpNorm_const_smul, Real.enorm_eq_ofReal (hw a ha),
      ENNReal.ofReal_mul (hw a ha)]
    exact mul_le_mul_of_nonneg_left hcomp (zero_le : (0 : ℝ≥0∞) ≤ _)
  have hsumEq : cirFamilyHistoryLoad F t =
      fun ω => ∑ a ∈ s, w a * F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4) := by
    funext ω
    simp [cirFamilyHistoryLoad, F, cirSquareResponseFamily]
  have hpENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.mpr hq1
  calc
    _ = eLpNorm (fun ω => ∑ a ∈ s,
          w a * F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4))
        (ENNReal.ofReal q) μ := by rw [hsumEq]
    _ ≤ ∑ a ∈ s, eLpNorm (fun ω =>
          w a * F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4))
        (ENNReal.ofReal q) μ := by
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (μ := μ)
          (f := fun a ω => w a * F.inverseHistory a t ω ^ 2 *
            (F.trace a t ω + 4)) (s := s) hpENN)
    _ ≤ ∑ a ∈ s, ENNReal.ofReal (w a * C) :=
      Finset.sum_le_sum fun a ha => htermCap a ha
    _ = ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a ha => mul_nonneg (hw a ha) hC)]
      rw [← Finset.sum_mul, hsum, one_mul]

end ASDExplicitGamma.AllOrder

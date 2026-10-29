/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.CirFiniteEvenJointMeasurable
public import ASDExplicitGamma.Gaussian.GaussMomentHolder
public import ASDExplicitGamma.AllOrder.SmallGammaSeed

/-! # Time integrability for finite-even CIR insertion paths -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Response
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

/-- Joint measurability and pointwise MemLp make the all-order norm along a
sample path measurable. -/
private theorem aoCir_path_eLpNorm_measurable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {p : ℝ} (hp : 1 ≤ p)
    (f : Set.Icc (0 : ℝ) 1 → Ω → ℝ)
    (hf : Measurable (Function.uncurry f))
    (hmem : ∀ t, MemLp (f t) (ENNReal.ofReal p) μ) :
    Measurable (fun t => eLpNorm (f t) (ENNReal.ofReal p) μ) := by
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpNonneg : 0 ≤ p := by linarith
  have hpow : Measurable (fun z : Set.Icc (0 : ℝ) 1 × Ω =>
      ‖f z.1 z.2‖ₑ ^ (ENNReal.ofReal p).toReal) :=
    ENNReal.continuous_rpow_const.measurable.comp
      (measurable_enorm.comp hf)
  have hlintegral : Measurable (fun t : Set.Icc (0 : ℝ) 1 =>
      ∫⁻ ω, ‖f t ω‖ₑ ^ (ENNReal.ofReal p).toReal ∂μ) :=
    hpow.lintegral_prod_right'
  have hformula (t : Set.Icc (0 : ℝ) 1) :
      eLpNorm (f t) (ENNReal.ofReal p) μ =
        (∫⁻ ω, ‖f t ω‖ₑ ^ p ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop
      (hmem t).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal hpNonneg]
  have heq : (fun t : Set.Icc (0 : ℝ) 1 =>
      eLpNorm (f t) (ENNReal.ofReal p) μ) =
      fun t => (∫⁻ ω, ‖f t ω‖ₑ ^ (ENNReal.ofReal p).toReal ∂μ) ^ (1 / p) := by
    funext t
    rw [hformula t]
    simp only [ENNReal.toReal_ofReal hpNonneg]
  rw [heq]
  exact ENNReal.continuous_rpow_const.measurable.comp hlintegral

/-- A measurable path of moments with a uniform higher-order cap gives an
integrable P12 norm along the compact insertion interval. -/
private theorem aoCir_path_norm_integrable_of_uniform_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    [IsProbabilityMeasure μ]
    {p q c C : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hc : 0 ≤ c) (hC : 0 ≤ C)
    (f : ℝ → Ω → ℝ)
    (hf : Measurable (fun z : Set.Icc (0 : ℝ) 1 × Ω => f z.1.1 z.2))
    (hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ω, 0 ≤ f t ω)
    (hmemQ : ∀ t : Set.Icc (0 : ℝ) 1,
      MemLp (f t.1) (ENNReal.ofReal q) μ)
    (hcapQ : ∀ t : Set.Icc (0 : ℝ) 1,
      eLpNorm (f t.1) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C) :
    IntegrableOn (fun t : ℝ => c * Gaussian.positiveLpNorm μ p (f t))
      (Set.Icc 0 1) volume := by
  have hmemP (t : Set.Icc (0 : ℝ) 1) :
      MemLp (f t.1) (ENNReal.ofReal p) μ := by
    apply (hmemQ t).mono_exponent
    exact ENNReal.ofReal_le_ofReal hpq
  have hnormMeas : Measurable (fun t : Set.Icc (0 : ℝ) 1 =>
      eLpNorm (f t.1) (ENNReal.ofReal p) μ) :=
    aoCir_path_eLpNorm_measurable μ hp (fun t => f t.1) hf hmemP
  have hnormEq (t : Set.Icc (0 : ℝ) 1) :
      Gaussian.positiveLpNorm μ p (f t.1) =
        (eLpNorm (f t.1) (ENNReal.ofReal p) μ).toReal := by
    rw [Gaussian.positiveLpNorm_eq_eLpNorm_toReal μ (by linarith) (f t.1)
      (hnonneg t.1 t.2) (hmemP t)]
  have hnormMeas' : Measurable (fun t : Set.Icc (0 : ℝ) 1 =>
      Gaussian.positiveLpNorm μ p (f t.1)) := by
    have heq : (fun t : Set.Icc (0 : ℝ) 1 =>
        Gaussian.positiveLpNorm μ p (f t.1)) =
      fun t => (eLpNorm (f t.1) (ENNReal.ofReal p) μ).toReal := by
      funext t
      exact hnormEq t
    rw [heq]
    exact ENNReal.measurable_toReal.comp hnormMeas
  have hnormBound (t : Set.Icc (0 : ℝ) 1) :
      Gaussian.positiveLpNorm μ p (f t.1) ≤ C := by
    rw [hnormEq t]
    have hpCap : eLpNorm (f t.1) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C := by
      calc
        _ ≤ eLpNorm (f t.1) (ENNReal.ofReal q) μ :=
          eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)
        _ ≤ ENNReal.ofReal C := hcapQ t
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hpCap).trans_eq
      (ENNReal.toReal_ofReal hC)
  let integrand : Set.Icc (0 : ℝ) 1 → ℝ := fun t =>
    c * Gaussian.positiveLpNorm μ p (f t.1)
  have hintegrandMeas : Measurable integrand :=
    measurable_const.mul hnormMeas'
  have hintegrandBound (t : Set.Icc (0 : ℝ) 1) : ‖integrand t‖ ≤ c * C := by
    have hval0 : 0 ≤ integrand t := mul_nonneg hc (by
      rw [hnormEq t]
      exact ENNReal.toReal_nonneg)
    rw [Real.norm_of_nonneg hval0]
    dsimp [integrand]
    exact mul_le_mul_of_nonneg_left (hnormBound t) hc
  have hintegrableSubtype : Integrable integrand
      ((volume : Measure ℝ).comap (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ)) := by
    apply integrableOn_univ.mp
    apply Measure.integrableOn_of_bounded
      (μ := (volume : Measure ℝ).comap
        (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ)) (s := Set.univ)
    · calc
        ((volume : Measure ℝ).comap
            (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ)) Set.univ =
            volume (Set.Icc (0 : ℝ) 1) := by
          rw [comap_subtype_coe_apply measurableSet_Icc,
            Set.image_univ, Subtype.range_coe]
        _ ≠ ∞ := isCompact_Icc.measure_lt_top.ne
    · exact hintegrandMeas.aestronglyMeasurable
    · filter_upwards with t
      exact hintegrandBound t
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Icc]
  change Integrable (fun t : Set.Icc (0 : ℝ) 1 =>
    c * Gaussian.positiveLpNorm μ p (f t.1))
    ((volume : Measure ℝ).comap (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ))
  exact hintegrableSubtype

/-- The reset cap controls the actual P12 time integrand uniformly on the
insertion interval, so the pathwise moment-transport theorem needs no
integrability premise. -/
theorem aoCir_reset_square_family_history_load_time_integrable
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2)
    (n ell frameLabel N : ℤ)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆
      closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆
      openCubeSet (originCube 2 ell))
    (hscale : ∀ a ∈ s, (Q a).scale = frameLabel)
    (hN : frameLabel ≤ N) (hNhi : N ≤ frameLabel + 8)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1)
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (p : ℝ) (hp : 1 ≤ p) (hpP : p ≤ (smallGammaSeedP M.gamma : ℝ)) :
    IntegrableOn
      (fun t => (19 + 8 * (p - 1)) *
        (b ^ 2 / (Annealed.sigmaBar M frameLabel : ℝ) ^ 2) *
        Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure p
          (cirFamilyHistoryLoad
            (cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L
              (fun a τ ω => cirSquareRestrictionCLM (Q a) (hQ a)
                (modelInsertedScalar (closure (cubeSet (originCube 2 n)))
                  (N - 1) τ ω)) hw hsum) t))
      (Set.Icc 0 1) := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  let k : (a : ι) → ℝ → Cutoff.CutoffSample 2 →
      ResponseCoefficient (openCubeSet (Q a)) := fun a τ ω =>
    cirSquareRestrictionCLM (Q a) (hQ a) (modelInsertedScalar K (N - 1) τ ω)
  let F := cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L k hw hsum
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let P := (smallGammaSeedP M.gamma : ℝ)
  let q : ℝ := max 12 p
  let load : ℝ → Cutoff.CutoffSample 2 → ℝ := fun τ ω =>
    cirFamilyHistoryLoad F τ ω
  have hP20 : (20 : ℝ) ≤ P := by
    dsimp [P, smallGammaSeedP]
    exact_mod_cast (Nat.le_max_left 20 _)
  have hq12 : 12 ≤ q := le_max_left _ _
  have hqP : q ≤ P := max_le (by linarith) hpP
  have hq1 : 1 ≤ q := by linarith
  have hQscale (a : ι) (ha : a ∈ s) : (Q a).scale ≤ N := by
    rw [hscale a ha]
    exact hN
  have hloadMeas : Measurable (fun z : CIRPathSample => load z.1.1 z.2) := by
    simpa only [load, F, k, K] using
      aoCir_reset_square_family_load_joint_measurable
        M frameLabel n ell N s w Q hQ hK hscale hN hw hsum b L
  have hmemQ (t : Set.Icc (0 : ℝ) 1) : MemLp (load t.1) (ENNReal.ofReal q) μ := by
    have h := aoCir_reset_square_family_memLp reset M h hM hγ hγsmall hstate
      s w Q n ell frameLabel N hQ hK hscale hN hw hsum b L q hq1 t.1 t.2.1 t.2.2
    exact h.2
  have hmemP (t : Set.Icc (0 : ℝ) 1) : MemLp (load t.1) (ENNReal.ofReal p) μ := by
    apply (hmemQ t).mono_exponent
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hnormMeas : Measurable (fun t : Set.Icc (0 : ℝ) 1 =>
      eLpNorm (load t.1) (ENNReal.ofReal p) μ) := by
    apply aoCir_path_eLpNorm_measurable μ hp
    · change Measurable (fun z : CIRPathSample => load z.1.1 z.2)
      exact hloadMeas
    · exact hmemP
  have hloadNonneg (t : ℝ) (ω : Cutoff.CutoffSample 2) : 0 ≤ load t ω := by
    exact cirFamilyHistoryLoad_nonneg F t ω
  have hnormEq (t : Set.Icc (0 : ℝ) 1) :
      Gaussian.positiveLpNorm μ p (load t.1) =
        (eLpNorm (load t.1) (ENNReal.ofReal p) μ).toReal :=
    Gaussian.positiveLpNorm_eq_eLpNorm_toReal μ (by linarith) (load t.1)
      (hloadNonneg t.1) (hmemP t)
  have hnormRealMeas : Measurable (fun t : Set.Icc (0 : ℝ) 1 =>
      Gaussian.positiveLpNorm μ p (load t.1)) := by
    have heq : (fun t : Set.Icc (0 : ℝ) 1 =>
        Gaussian.positiveLpNorm μ p (load t.1)) =
        fun t => (eLpNorm (load t.1) (ENNReal.ofReal p) μ).toReal := by
      funext t
      exact hnormEq t
    rw [heq]
    exact ENNReal.measurable_toReal.comp hnormMeas
  have hcoef0 : 0 ≤ (19 + 8 * (p - 1)) *
      (b ^ 2 / (Annealed.sigmaBar M frameLabel : ℝ) ^ 2) := by
    have hσ : 0 < (Annealed.sigmaBar M frameLabel : ℝ) :=
      (Annealed.sigmaBar_characterization M frameLabel).1
    positivity
  have hcapQ (t : Set.Icc (0 : ℝ) 1) :
      eLpNorm (load t.1) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 50) := by
    exact aoCir_reset_square_family_history_load_cap reset M h hM hγ hγsmall
      hstate s w Q n ell frameLabel N hQ hK hscale hN hNhi hw hsum b L q hq12 hqP
      t.1 t.2.1 t.2.2
  have hcapP (t : Set.Icc (0 : ℝ) 1) :
      eLpNorm (load t.1) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 50) := by
    calc
      _ ≤ eLpNorm (load t.1) (ENNReal.ofReal q) μ :=
        eLpNorm_le_eLpNorm_of_exponent_le
          (ENNReal.ofReal_le_ofReal (le_max_right _ _))
      _ ≤ ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 50) := hcapQ t
  have hnormBound (t : Set.Icc (0 : ℝ) 1) :
      Gaussian.positiveLpNorm μ p (load t.1) ≤ (2.2 : ℝ) ^ 2 * 50 := by
    rw [hnormEq t]
    calc
      (eLpNorm (load t.1) (ENNReal.ofReal p) μ).toReal ≤
          (ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 50)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcapP t)
      _ = (2.2 : ℝ) ^ 2 * 50 := by norm_num
  let coeff : ℝ := (19 + 8 * (p - 1)) *
    (b ^ 2 / (Annealed.sigmaBar M frameLabel : ℝ) ^ 2)
  let integrand : Set.Icc (0 : ℝ) 1 → ℝ := fun t =>
    coeff * Gaussian.positiveLpNorm μ p (load t.1)
  have hintegrandMeas : Measurable integrand := by
    exact (measurable_const.mul hnormRealMeas)
  have hintegrandBound (t : Set.Icc (0 : ℝ) 1) :
      ‖integrand t‖ ≤ coeff * ((2.2 : ℝ) ^ 2 * 50) := by
    have hval0 : 0 ≤ integrand t := by
      exact mul_nonneg (by dsimp [coeff]; exact hcoef0)
        (by rw [hnormEq t]; exact ENNReal.toReal_nonneg)
    rw [Real.norm_of_nonneg hval0]
    dsimp [integrand]
    exact mul_le_mul_of_nonneg_left (hnormBound t) (by dsimp [coeff]; exact hcoef0)
  have hintegrableSubtype : Integrable integrand
      ((volume : Measure ℝ).comap (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ)) := by
    apply integrableOn_univ.mp
    apply Measure.integrableOn_of_bounded
      (μ := (volume : Measure ℝ).comap
        (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ))
      (s := Set.univ)
    · calc
        ((volume : Measure ℝ).comap
            (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ)) Set.univ =
            volume (Set.Icc (0 : ℝ) 1) := by
          rw [comap_subtype_coe_apply measurableSet_Icc,
            Set.image_univ, Subtype.range_coe]
        _ ≠ ∞ := isCompact_Icc.measure_lt_top.ne
    · exact hintegrandMeas.aestronglyMeasurable
    · filter_upwards with t
      exact hintegrandBound t
  change IntegrableOn (fun t : ℝ => coeff *
      Gaussian.positiveLpNorm μ p (load t)) (Set.Icc 0 1)
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Icc]
  change Integrable (fun t : Set.Icc (0 : ℝ) 1 =>
    coeff * Gaussian.positiveLpNorm μ p (load t.1))
    ((volume : Measure ℝ).comap (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ))
  exact hintegrableSubtype

/-- Arbitrary-depth P12 time integrability from the reset-derived direct
window load cap. -/
theorem aoCir_reset_square_family_history_load_time_integrable_window
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2)
    (n ell frameLabel N : ℤ)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆
      closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆
      openCubeSet (originCube 2 ell))
    (hscale : ∀ a ∈ s, (Q a).scale = frameLabel)
    (hN : frameLabel ≤ N)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1)
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (p : ℝ) (hp : 1 ≤ p) (hpP : p ≤ (smallGammaSeedP M.gamma : ℝ))
    (hwindow : M.gamma * (max 12 p) * ((N - frameLabel : ℤ) + 2 : ℝ) ≤ 1 / 512) :
    IntegrableOn
      (fun t => (19 + 8 * (p - 1)) *
        (b ^ 2 / (Annealed.sigmaBar M frameLabel : ℝ) ^ 2) *
        Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure p
          (cirFamilyHistoryLoad
            (cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L
              (fun a τ ω => cirSquareRestrictionCLM (Q a) (hQ a)
                (modelInsertedScalar (closure (cubeSet (originCube 2 n)))
                  (N - 1) τ ω)) hw hsum) t))
      (Set.Icc 0 1) := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  let k : (a : ι) → ℝ → Cutoff.CutoffSample 2 →
      ResponseCoefficient (openCubeSet (Q a)) := fun a τ ω =>
    cirSquareRestrictionCLM (Q a) (hQ a) (modelInsertedScalar K (N - 1) τ ω)
  let F := cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L k hw hsum
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let q : ℝ := max 12 p
  let load : ℝ → Cutoff.CutoffSample 2 → ℝ := fun τ ω => cirFamilyHistoryLoad F τ ω
  have hP20 : 20 ≤ smallGammaSeedP M.gamma := by
    dsimp [smallGammaSeedP]
    exact le_max_left _ _
  have hP12 : (12 : ℝ) ≤ (smallGammaSeedP M.gamma : ℝ) := by
    exact_mod_cast (show 12 ≤ smallGammaSeedP M.gamma by omega)
  have hq12 : 12 ≤ q := le_max_left _ _
  have hqP : q ≤ (smallGammaSeedP M.gamma : ℝ) := max_le hP12 hpP
  have hq1 : 1 ≤ q := by linarith
  have hQscale (a : ι) (ha : a ∈ s) : (Q a).scale ≤ N := by
    rw [hscale a ha]
    exact hN
  have hloadMeas : Measurable (fun z : CIRPathSample => load z.1.1 z.2) := by
    simpa only [load, F, k, K] using
      aoCir_reset_square_family_load_joint_measurable
        M frameLabel n ell N s w Q hQ hK hscale hN hw hsum b L
  have hmemQ (t : Set.Icc (0 : ℝ) 1) : MemLp (load t.1) (ENNReal.ofReal q) μ := by
    have h := aoCir_reset_square_family_memLp reset M h hM hγ hγsmall hstate
      s w Q n ell frameLabel N hQ hK hscale hN hw hsum b L q hq1
      t.1 t.2.1 t.2.2
    exact h.2
  have hnonneg (t : Set.Icc (0 : ℝ) 1) (ω : Cutoff.CutoffSample 2) :
      0 ≤ load t.1 ω := cirFamilyHistoryLoad_nonneg F t.1 ω
  have hcapQ (t : Set.Icc (0 : ℝ) 1) :
      eLpNorm (load t.1) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 3120) := by
    have hcomponents (a : ι) (ha : a ∈ s) :
        eLpNorm (fun ω =>
          pureFluxSourceTileHistory (Q a) 4
            (responseFramePlanarCoefficientField M.nu
              (Annealed.sigmaBar M (Q a).scale : ℝ)
              (aoCirInsertedResponseCoefficient (Q a) n (hQ a) N t.1 ω)) ^ 2 *
          rootTraceObservable M (Q a)
            (protectedOldLabel (Q a).scale (orderBand (2 * q)))
            N frameLabel (aoCirStepWeights N t.1) ω)
          (ENNReal.ofReal q) μ ≤ ENNReal.ofReal ((2.2 : ℝ) ^ 2 * 3120) := by
      exact aoCir_step_history_load_component_cap_of_reset_window reset
        M h hM hγ hγsmall hstate (Q a) n ell frameLabel N (hQ a) hK
        (hscale a ha) hN q hq12 hqP (by simpa [q] using hwindow)
        t.1 t.2.1 t.2.2
    have h := aoCir_reset_square_family_history_load_cap_of_component
      M s w Q n ell frameLabel N hQ hK hscale hN hw hsum b L q
      ((2.2 : ℝ) ^ 2 * 3120) hq1 (by positivity) t.1 t.2.1 t.2.2 hcomponents
    simpa only [load, F, k, K, μ] using h
  have hcoef : 0 ≤ (19 + 8 * (p - 1)) *
      (b ^ 2 / (Annealed.sigmaBar M frameLabel : ℝ) ^ 2) := by
    have hσ : 0 < (Annealed.sigmaBar M frameLabel : ℝ) :=
      (Annealed.sigmaBar_characterization M frameLabel).1
    positivity
  let c : ℝ := (19 + 8 * (p - 1)) *
    (b ^ 2 / (Annealed.sigmaBar M frameLabel : ℝ) ^ 2)
  have hgeneric := aoCir_path_norm_integrable_of_uniform_cap μ hp
    (le_max_right 12 p) hcoef (by positivity) load
    (by simpa [Function.uncurry, load, F, k, K] using hloadMeas)
    (by intro t ht ω; exact hnonneg ⟨t, ht⟩ ω) hmemQ hcapQ
  have hroute :
      (fun t => (19 + 8 * (p - 1)) *
        (b ^ 2 / (Annealed.sigmaBar M frameLabel : ℝ) ^ 2) *
        Gaussian.positiveLpNorm μ p (load t)) =
      (fun t => c * Gaussian.positiveLpNorm μ p (load t)) := by
    funext t
    simp [c]
  rw [hroute]
  simpa only [load, F, k, K, μ] using hgeneric

end ASDExplicitGamma.AllOrder

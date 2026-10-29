module

public import ASDExplicitGamma.Native.HeatPowerGeneratorAllDegrees
public import ASDExplicitGamma.Native.GenericSourceBandMoments
public import ASDExplicitGamma.Native.GenericSourceBandGenerator
public import ASDExplicitGamma.Native.HeatCooperativeSourceStart
public import ASDExplicitGamma.Inverse.SourceQ3PowerIdentity

/-! Actual all-degree source-band moment curves for the cooperative heat
system.  This file records the derivative and start data of the curve itself;
it does not add a premise for the configured generator row. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Main
open ASDExplicitGamma.Variational ASDExplicitGamma.Response
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal
noncomputable section

/-- The actual simultaneous source-band moment of integer degree `k`. -/
def nativeSourceBandMomentK (M : ABKModel 2) (n : ℤ) (height k : ℕ) (t : ℝ) : ℝ :=
  nativeSourceBandAverage M n height
    (fun x => modelTraceObservable n M.nu (Annealed.sigmaBar M n) x ^ (k : ℝ)) t

/-- The canonical q3 covariance contraction is exactly the power generator
for every integer degree at least two. -/
theorem source_q3_covariance_power_identity_nat
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l}) (k : ℕ) (hk : 2 ≤ k)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    (1 / 2 : ℝ) * modelCovarianceTrace
        (fun y => modelTraceObservable n ν σ y ^ (k : ℝ))
        (pureFluxMainCubeQ3Directions n b L) x =
      modelPowerHeatGenerator (modelTraceObservable n ν σ)
        (pureFluxMainCubeQ3Directions n b L) (k : ℝ) x := by
  exact @modelCovarianceTrace_rpow (MainCubeH3 n b L)
    (C(closure (cubeSet (originCube 2 n)), ℝ))
    inferInstance (mainCubeH3InnerProductSpace n b L) inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (mainCubeQ3Directions n b L) (mainCubeQ3Directions_summable n b L)
    (mainCubeH3Value n b L) (modelTraceObservable n ν σ)
    (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n ν σ hν hσ)
    (modelTraceObservable_nonneg n ν σ hν hσ) (k : ℝ) (by exact_mod_cast hk) x

/-- Each finite-band integer-power generator is integrable on the actual
cutoff law.  The proof uses the actual Gaussian realization and polynomial
integrability, independently of any signed row estimate. -/
theorem native_source_band_power_generatorK_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height k : ℕ) (hheight : 1 ≤ height) (hk : 2 ≤ k) (t : ℝ) :
    Integrable (nativeSourceBandPowerGeneratorK M h n height t k)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let Φ := modelTraceObservable n M.nu (Annealed.sigmaBar M n)
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
  have hΦ0 := modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1
  have hpower := hasPolynomiallyBoundedC2Derivatives_rpow hΦ hΦ0
    (by exact_mod_cast hk : (2 : ℝ) ≤ (k : ℝ))
  unfold nativeSourceBandPowerGeneratorK
  apply integrable_finsetSum Finset.univ
  intro i _
  let b := q3ModelAmplitude M h (n + ((i.val + 1 : ℕ) : ℤ))
  let L := q3ModelLength (n + ((i.val + 1 : ℕ) : ℤ))
  let H := pureFluxMainCubeQ3Directions n b L
  have htest := source_q3_covariance_trace_regular n b L
    (fun x => Φ x ^ (k : ℝ)) hpower
  have hmem := native_source_band_test_memLp M h hM n height hheight
    (modelCovarianceTrace (fun x => Φ x ^ (k : ℝ)) H)
    htest.1 htest.2 t 2 (by norm_num)
  have hi := hmem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 : ℝ))
  have he :
      (fun ω : Cutoff.CutoffSample 2 =>
        modelPowerHeatGenerator Φ H (k : ℝ) (nativeSourceBandScalar n height t ω)) =
      (fun ω => (1 / 2 : ℝ) *
        modelCovarianceTrace (fun x => Φ x ^ (k : ℝ)) H
          (nativeSourceBandScalar n height t ω)) := by
    funext ω
    exact (source_q3_covariance_power_identity_nat n M.nu
      (Annealed.sigmaBar M n) b M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 L k hk _).symm
  rw [he]
  exact hi.const_mul (1 / 2 : ℝ)

/-- Every actual source-band power moment has the complete finite shell
generator as its derivative on positive times. -/
theorem native_source_band_momentK_heat
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height k : ℕ) (hheight : 1 ≤ height) (hk : 2 ≤ k) :
    ContinuousOn (nativeSourceBandMomentK M n height k) (Set.Ici 0) ∧
    ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt (nativeSourceBandMomentK M n height k)
      (∫ ω : Cutoff.CutoffSample 2,
        nativeSourceBandPowerGeneratorK M h n height t k ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  let Φ := modelTraceObservable n M.nu (Annealed.sigmaBar M n)
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
  have hΦ0 := modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1
  have hpower := hasPolynomiallyBoundedC2Derivatives_rpow hΦ hΦ0
    (by exact_mod_cast hk : (2 : ℝ) ≤ (k : ℝ))
  have hh := native_source_band_average_shell_heat M h hM n height hheight
    (fun x => Φ x ^ (k : ℝ)) hpower
  refine ⟨?_, ?_⟩
  · change ContinuousOn (fun s => nativeSourceBandAverage M n height
      (fun x => Φ x ^ (k : ℝ)) s) (Set.Ici 0)
    exact hh.1
  · intro t ht
    change HasDerivAt (fun s => nativeSourceBandAverage M n height
      (fun x => Φ x ^ (k : ℝ)) s) _ t
    have hd := hh.2 t ht
    have he :
        (1 / 2 : ℝ) * (∫ ω : Cutoff.CutoffSample 2,
          ∑ i : Fin height, modelCovarianceTrace (fun x => Φ x ^ (k : ℝ))
            (pureFluxMainCubeQ3Directions n
              (q3ModelAmplitude M h (n + ((i.val + 1 : ℕ) : ℤ)))
              (q3ModelLength (n + ((i.val + 1 : ℕ) : ℤ))))
            (nativeSourceBandScalar n height t ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        ∫ ω : Cutoff.CutoffSample 2,
          nativeSourceBandPowerGeneratorK M h n height t k ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact source_q3_covariance_power_identity_nat n M.nu
        (Annealed.sigmaBar M n)
        (q3ModelAmplitude M h (n + ((i.val + 1 : ℕ) : ℤ)))
        M.nu_pos (Annealed.sigmaBar_characterization M n).1
        (q3ModelLength (n + ((i.val + 1 : ℕ) : ℤ))) k hk _
    rw [he] at hd
    exact hd

/-- The actual simultaneous-band generator has its degree-specific signed
row. The row keeps the exact `k` dependence instead of replacing it by the
degree-20 maximum. -/
theorem native_source_band_power_generatorK_exact_ae_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j)
    (hstate : nativeInductionState M h n)
    (t : ℝ) (ht1 : t ≤ 1) (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let X := nativeSourceBandScalar n height t ω
      let T := modelTraceObservable n M.nu (Annealed.sigmaBar M n) X
      let F := T + 4
      let P := (nativeSourceBandHistory M n height t ω).toReal
      let D := bankInverseTraceObservable n M.nu (Annealed.sigmaBar M n)
        M.nu_pos (Annealed.sigmaBar_characterization M n).1 X
      nativeSourceBandPowerGeneratorK M h n height t k ω ≤
        (k : ℝ) * T ^ ((k : ℝ) - 1) *
          (nativeSourceRawShellVarianceCap M.gamma height *
            (((2 * (k : ℝ) - 1) * (height : ℝ) +
                2 * ((k : ℝ) - 1) * (521 / 1000 : ℝ)) * D +
              2 * (521 / 1000 : ℝ) * (P * F) +
              ((1975 / 1000 : ℝ) +
                2 * ((k : ℝ) - 1) * (1565 / 1000 : ℝ)) * (P ^ 2 * F))) := by
  have hall : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ i : Fin height,
      let Q := originCube 2 n
      let af := responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M n : ℝ)
        (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))
      max (lemmaVTileHistory Q (pureFluxBankSourceDepth (i.val + 1)) af)
        (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth (i.val + 1)) af) ≤
          (nativeSourceBandHistory M n height t ω).toReal :=
    ae_all_iff.mpr fun i => native_source_band_source_history_ae_le
      M h hM hg n height hpast i.val t ht1
  filter_upwards [hall] with ω hsource
  let X := nativeSourceBandScalar n height t ω
  let σ : ℝ := Annealed.sigmaBar M n
  let T := modelTraceObservable n M.nu σ X
  let F := T + 4
  let P := (nativeSourceBandHistory M n height t ω).toReal
  let D := bankInverseTraceObservable n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 X
  let e := nativeSourceRawShellVarianceCap M.gamma height
  let κ := (521 / 1000 : ℝ)
  let μc := (1975 / 1000 : ℝ)
  let qc := (1565 / 1000 : ℝ)
  let v := fun i : ℕ =>
    (q3ModelAmplitude M h (n + ((i + 1 : ℕ) : ℤ))) ^ 2 / σ ^ 2
  let c := fun i : ℕ =>
    v i * ((2 * (k : ℝ) - 1 + 2 * ((k : ℝ) - 1) * nativeSourceShellK i) * D +
      2 * nativeSourceShellK i * (P * F) +
      (nativeSourceShellMu i +
        2 * ((k : ℝ) - 1) * nativeSourceShellQ i) * (P ^ 2 * F))
  have hT : 0 ≤ T := modelTraceObservable_nonneg n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 X
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hP : 0 ≤ P := ENNReal.toReal_nonneg
  have hD : 0 ≤ D := native_source_model_inverse_trace_nonneg n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 X
  have hg0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have he : 0 ≤ e := by dsimp [e, nativeSourceRawShellVarianceCap]; positivity
  have hscale : 0 ≤ (k : ℝ) * T ^ ((k : ℝ) - 1) := by
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hT _)
  have hcoef (i : Fin height) :
      modelPowerHeatGenerator (modelTraceObservable n M.nu σ)
          (pureFluxMainCubeQ3Directions n
            (q3ModelAmplitude M h (n + ((i.val + 1 : ℕ) : ℤ)))
            (q3ModelLength (n + ((i.val + 1 : ℕ) : ℤ)))) (k : ℝ) X ≤
        (k : ℝ) * T ^ ((k : ℝ) - 1) * c i.val := by
    let s : ℕ := i.val + 1
    let b := q3ModelAmplitude M h (n + (s : ℤ))
    let L := q3ModelLength (n + (s : ℤ))
    let af := responseFramePlanarCoefficientField M.nu σ
      (pureFluxOpenResponseRestriction n X)
    let B := max (lemmaVTileHistory (originCube 2 n)
        (pureFluxBankSourceDepth s) af)
      (pureFluxSourceTileHistory (originCube 2 n)
        (pureFluxBankSourceDepth s) af)
    have hB : B ≤ P := by
      simpa [B, af, s, P] using hsource i
    have hB0 : 0 ≤ B := le_max_of_le_left
      (lemmaVTileHistory_nonneg (originCube 2 n)
        (pureFluxBankSourceDepth s) af)
    have hB2 : B ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ hB0 hB 2
    have hc := native_source_shell_coefficients_nonneg i.val
    have hcoeffK : 0 ≤ nativeSourceShellK i.val := hc.1
    have hkR2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hkR1 : (1 : ℝ) ≤ (k : ℝ) := le_trans (by norm_num) hkR2
    have hcoeffQ : 0 ≤ nativeSourceShellMu i.val +
        2 * ((k : ℝ) - 1) * nativeSourceShellQ i.val :=
      add_nonneg hc.2.2
        (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hkR1)) hc.2.1)
    have hK := hc.1
    have hQ := hc.2.1
    have hμ := hc.2.2
    have hv : 0 ≤ b ^ 2 / σ ^ 2 := by positivity
    have htwo : 2 * b ^ 2 / σ ^ 2 = 2 * (b ^ 2 / σ ^ 2) := by ring
    have hfour : 4 * b ^ 2 / σ ^ 2 = 4 * (b ^ 2 / σ ^ 2) := by ring
    have hrow := nativeHeat_sourceTracePowerGenerator_le_profile
      n s (by dsimp [s]; omega) M.nu σ b (k : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (by exact_mod_cast hk2)
      (nativeSourceBandScalar n height t ω)
    have hpow : T ^ ((k : ℝ) - 2) * T = T ^ ((k : ℝ) - 1) := by
      have hk2cast : (k : ℝ) - 2 = ((k - 2 : ℕ) : ℝ) := by
        have hk2nat : k = (k - 2) + 2 := by omega
        have hk2real : (k : ℝ) = ((k - 2 : ℕ) : ℝ) + 2 := by
          exact_mod_cast hk2nat
        linarith
      have hk1cast : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by
        have hk1nat : k = (k - 1) + 1 := by omega
        have hk1real : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
          exact_mod_cast hk1nat
        linarith
      rw [hk2cast, hk1cast, Real.rpow_natCast, Real.rpow_natCast]
      have hindex : k - 1 = (k - 2) + 1 := by omega
      rw [hindex, pow_succ]
    have hrow' :
        modelPowerHeatGenerator (modelTraceObservable n M.nu σ)
          (pureFluxMainCubeQ3Directions n b L) (k : ℝ) X ≤
        (k : ℝ) * T ^ ((k : ℝ) - 1) *
          (b ^ 2 / σ ^ 2 *
            ((2 * (k : ℝ) - 1 + 2 * ((k : ℝ) - 1) * nativeSourceShellK i.val) * D +
              2 * nativeSourceShellK i.val * B * F +
              (nativeSourceShellMu i.val +
                2 * ((k : ℝ) - 1) * nativeSourceShellQ i.val) * B ^ 2 * F)) := by
      have hpowFactor :
          T ^ ((k : ℝ) - 2) *
              (4 * b ^ 2 / σ ^ 2 * T *
                ((1 + nativeSourceShellK i.val) * D +
                  nativeSourceShellQ i.val * B ^ 2 * F)) =
            4 * b ^ 2 / σ ^ 2 * T ^ ((k : ℝ) - 1) *
              ((1 + nativeSourceShellK i.val) * D +
                nativeSourceShellQ i.val * B ^ 2 * F) := by
        calc
          _ = (4 * b ^ 2 / σ ^ 2) * (T ^ ((k : ℝ) - 2) * T) *
              ((1 + nativeSourceShellK i.val) * D +
                nativeSourceShellQ i.val * B ^ 2 * F) := by ring
          _ = _ := by rw [hpow]
      have hrow'' :
          modelPowerHeatGenerator (modelTraceObservable n M.nu σ)
            (pureFluxMainCubeQ3Directions n b L) (k : ℝ) X ≤
          (k : ℝ) * T ^ ((k : ℝ) - 1) *
              (b ^ 2 / σ ^ 2 * D +
                (2 * b ^ 2 / σ ^ 2 * nativeSourceShellK i.val * B +
                  b ^ 2 / σ ^ 2 * nativeSourceShellMu i.val * B ^ 2) * F) +
            ((k : ℝ) * ((k : ℝ) - 1) / 2) * T ^ ((k : ℝ) - 2) *
              (4 * b ^ 2 / σ ^ 2 * T *
                ((1 + nativeSourceShellK i.val) * D +
                  nativeSourceShellQ i.val * B ^ 2 * F)) := by
        simpa only [X, T, F, D, B, af, s, b, L,
          pureFlux_bank_source_rho n (i.val + 1) (by omega),
          pureFlux_bank_source_delta n (i.val + 1) (by omega),
          source_lemmaV_B_eq_covariance_B,
          ← native_source_model_inverse_trace_eq_frame_trace n M.nu σ
            M.nu_pos (Annealed.sigmaBar_characterization M n).1 X,
          nativeSourceShellK, nativeSourceShellQ, nativeSourceShellMu,
          Nat.add_sub_cancel, htwo, hfour] using hrow
      have hsecond :
          ((k : ℝ) * ((k : ℝ) - 1) / 2) * T ^ ((k : ℝ) - 2) *
              (4 * b ^ 2 / σ ^ 2 * T *
                ((1 + nativeSourceShellK i.val) * D +
                  nativeSourceShellQ i.val * B ^ 2 * F)) =
            ((k : ℝ) * ((k : ℝ) - 1) / 2) *
              (4 * b ^ 2 / σ ^ 2) * T ^ ((k : ℝ) - 1) *
                ((1 + nativeSourceShellK i.val) * D +
                  nativeSourceShellQ i.val * B ^ 2 * F) := by
        calc
          _ = ((k : ℝ) * ((k : ℝ) - 1) / 2) *
              (T ^ ((k : ℝ) - 2) *
                (4 * b ^ 2 / σ ^ 2 * T *
                  ((1 + nativeSourceShellK i.val) * D +
                    nativeSourceShellQ i.val * B ^ 2 * F))) := by ring
          _ = ((k : ℝ) * ((k : ℝ) - 1) / 2) *
              (4 * b ^ 2 / σ ^ 2 * T ^ ((k : ℝ) - 1) *
                ((1 + nativeSourceShellK i.val) * D +
                  nativeSourceShellQ i.val * B ^ 2 * F)) := by rw [hpowFactor]
          _ = _ := by ring
      have hfactor :
          (k : ℝ) * T ^ ((k : ℝ) - 1) *
              (b ^ 2 / σ ^ 2 * D +
                (2 * b ^ 2 / σ ^ 2 * nativeSourceShellK i.val * B +
                  b ^ 2 / σ ^ 2 * nativeSourceShellMu i.val * B ^ 2) * F) +
            ((k : ℝ) * ((k : ℝ) - 1) / 2) * T ^ ((k : ℝ) - 2) *
              (4 * b ^ 2 / σ ^ 2 * T *
                ((1 + nativeSourceShellK i.val) * D +
                  nativeSourceShellQ i.val * B ^ 2 * F)) =
          (k : ℝ) * T ^ ((k : ℝ) - 1) *
            (b ^ 2 / σ ^ 2 *
              ((2 * (k : ℝ) - 1 + 2 * ((k : ℝ) - 1) * nativeSourceShellK i.val) * D +
                2 * nativeSourceShellK i.val * B * F +
                (nativeSourceShellMu i.val +
                  2 * ((k : ℝ) - 1) * nativeSourceShellQ i.val) * B ^ 2 * F)) := by
        rw [hsecond]
        ring
      calc
        _ ≤ _ := hrow''
        _ = _ := hfactor
    have hinner :
        (2 * (k : ℝ) - 1 + 2 * ((k : ℝ) - 1) * nativeSourceShellK i.val) * D +
          2 * nativeSourceShellK i.val * B * F +
          (nativeSourceShellMu i.val +
            2 * ((k : ℝ) - 1) * nativeSourceShellQ i.val) * B ^ 2 * F ≤
        (2 * (k : ℝ) - 1 + 2 * ((k : ℝ) - 1) * nativeSourceShellK i.val) * D +
          2 * nativeSourceShellK i.val * (P * F) +
          (nativeSourceShellMu i.val +
            2 * ((k : ℝ) - 1) * nativeSourceShellQ i.val) * (P ^ 2 * F) := by
      have hpf := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hB
          (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hcoeffK)) hF
      have hqf := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hB2 hcoeffQ) hF
      nlinarith [hpf, hqf]
    have hrowbound :
        b ^ 2 / σ ^ 2 *
          ((2 * (k : ℝ) - 1 + 2 * ((k : ℝ) - 1) * nativeSourceShellK i.val) * D +
            2 * nativeSourceShellK i.val * (P * F) +
            (nativeSourceShellMu i.val +
              2 * ((k : ℝ) - 1) * nativeSourceShellQ i.val) * (P ^ 2 * F)) = c i.val := by
      dsimp [c, v, b, s] <;> ring
    have hscaled' :
        (k : ℝ) * T ^ ((k : ℝ) - 1) *
            (b ^ 2 / σ ^ 2 *
              ((2 * (k : ℝ) - 1 + 2 * ((k : ℝ) - 1) * nativeSourceShellK i.val) * D +
                2 * nativeSourceShellK i.val * B * F +
                (nativeSourceShellMu i.val +
                  2 * ((k : ℝ) - 1) * nativeSourceShellQ i.val) * B ^ 2 * F)) ≤
          (k : ℝ) * T ^ ((k : ℝ) - 1) * c i.val := by
      calc
        _ = (k : ℝ) * T ^ ((k : ℝ) - 1) *
            (b ^ 2 / σ ^ 2 *
              ((2 * (k : ℝ) - 1 + 2 * ((k : ℝ) - 1) * nativeSourceShellK i.val) * D +
                2 * nativeSourceShellK i.val * B * F +
                (nativeSourceShellMu i.val +
                  2 * ((k : ℝ) - 1) * nativeSourceShellQ i.val) * B ^ 2 * F)) := by ring
        _ ≤ (k : ℝ) * T ^ ((k : ℝ) - 1) *
            (b ^ 2 / σ ^ 2 *
              ((2 * (k : ℝ) - 1 + 2 * ((k : ℝ) - 1) * nativeSourceShellK i.val) * D +
                2 * nativeSourceShellK i.val * (P * F) +
                (nativeSourceShellMu i.val +
                  2 * ((k : ℝ) - 1) * nativeSourceShellQ i.val) * (P ^ 2 * F))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinner hv) hscale
        _ = (k : ℝ) * T ^ ((k : ℝ) - 1) * c i.val := by rw [← hrowbound]
    exact hrow'.trans hscaled'
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoef i)
  rw [← Finset.mul_sum] at hsum
  let vv : ℕ → ℝ := fun i =>
    (q3ModelAmplitude M h (n + ((i + 1 : ℕ) : ℤ))) ^ 2 / σ ^ 2
  have heq : nativeSourceShellClock M.gamma height = e := by
    dsimp [nativeSourceShellClock, e, nativeSourceRawShellVarianceCap]
    congr 2
    ring
  have hv (i : ℕ) (hi : i ∈ Finset.range height) :
      vv i ≤ e := by
    dsimp [vv]
    rw [← heq]
    exact native_source_shell_variance_le_clock M h n height (i + 1)
      hstate (by have := Finset.mem_range.mp hi; omega)
  have hsums := source_covariance_weighted_partial_sums (Finset.range height)
    vv e he (by
      intro i hi
      simpa [vv, e, heq] using hv i hi)
  have hcostsum :
      (∑ i : Fin height, c i.val) ≤
        e * (((2 * (k : ℝ) - 1) * (height : ℝ) +
              2 * ((k : ℝ) - 1) * κ) * D +
            2 * κ * (P * F) +
            (μc + 2 * ((k : ℝ) - 1) * qc) * (P ^ 2 * F)) := by
    rw [Fin.sum_univ_eq_sum_range]
    let A := (2 * (k : ℝ) - 1) * D
    let Bc := 2 * ((k : ℝ) - 1) * D + 2 * (P * F)
    let C := P ^ 2 * F
    let E := 2 * ((k : ℝ) - 1) * C
    have hkR2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hkR1 : (1 : ℝ) ≤ (k : ℝ) := le_trans (by norm_num) hkR2
    have hkm1 : 0 ≤ (k : ℝ) - 1 := sub_nonneg.mpr hkR1
    have h2km1 : 0 ≤ 2 * (k : ℝ) - 1 := by linarith
    have hA : 0 ≤ A := by dsimp [A]; exact mul_nonneg h2km1 hD
    have hBc : 0 ≤ Bc := by
      dsimp [Bc]
      exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hkm1) hD)
        (mul_nonneg (by norm_num) (mul_nonneg hP hF))
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hE : 0 ≤ E := by dsimp [E]; exact mul_nonneg (mul_nonneg (by norm_num) hkm1) hC
    have hpoint (i : ℕ) :
        c i = A * vv i + Bc * (vv i * nativeSourceShellK i) +
          C * (vv i * nativeSourceShellMu i) +
          E * (vv i * nativeSourceShellQ i) := by
      dsimp [c, v, vv, A, Bc, C, E]
      ring
    have hsumRewrite :
        (∑ i ∈ Finset.range height, c i) =
          A * (∑ i ∈ Finset.range height, vv i) +
            Bc * (∑ i ∈ Finset.range height, vv i * nativeSourceShellK i) +
            C * (∑ i ∈ Finset.range height, vv i * nativeSourceShellMu i) +
            E * (∑ i ∈ Finset.range height, vv i * nativeSourceShellQ i) := by
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum] <;> ring
    rw [hsumRewrite]
    have hV : (∑ i ∈ Finset.range height, vv i) ≤ (height : ℝ) * e := by
      calc
        _ ≤ ∑ i ∈ Finset.range height, e :=
          Finset.sum_le_sum fun i hi => hv i hi
        _ = (height : ℝ) * e := by simp
    have hK := hsums.1
    have hM := hsums.2.1
    have hQ := hsums.2.2
    have hV' := mul_le_mul_of_nonneg_left hV hA
    have hK' := mul_le_mul_of_nonneg_left hK hBc
    have hM' := mul_le_mul_of_nonneg_left hM hC
    have hQ' := mul_le_mul_of_nonneg_left hQ hE
    have hsumCap :
        A * (∑ i ∈ Finset.range height, vv i) +
          Bc * (∑ i ∈ Finset.range height, vv i * nativeSourceShellK i) +
          C * (∑ i ∈ Finset.range height, vv i * nativeSourceShellMu i) +
          E * (∑ i ∈ Finset.range height, vv i * nativeSourceShellQ i) ≤
        A * ((height : ℝ) * e) + Bc * (κ * e) + C * (μc * e) + E * (qc * e) := by
      calc
        _ = (A * (∑ i ∈ Finset.range height, vv i) +
              Bc * (∑ i ∈ Finset.range height, vv i * nativeSourceShellK i)) +
            (C * (∑ i ∈ Finset.range height, vv i * nativeSourceShellMu i) +
              E * (∑ i ∈ Finset.range height, vv i * nativeSourceShellQ i)) := by ring
        _ ≤ (A * ((height : ℝ) * e) + Bc * (κ * e)) +
              (C * (μc * e) + E * (qc * e)) :=
          add_le_add (add_le_add hV' hK') (add_le_add hM' hQ')
        _ = A * ((height : ℝ) * e) + Bc * (κ * e) + C * (μc * e) + E * (qc * e) := by ring
    calc
      _ ≤ _ := hsumCap
      _ = _ := by dsimp [A, Bc, C, E]; ring
  have hmain :
      nativeSourceBandPowerGeneratorK M h n height t k ω =
        ∑ i : Fin height,
          modelPowerHeatGenerator (modelTraceObservable n M.nu σ)
            (pureFluxMainCubeQ3Directions n
              (q3ModelAmplitude M h (n + ((i.val + 1 : ℕ) : ℤ)))
              (q3ModelLength (n + ((i.val + 1 : ℕ) : ℤ)))) (k : ℝ) X := rfl
  rw [hmain]
  calc
    _ ≤ (k : ℝ) * T ^ ((k : ℝ) - 1) * (∑ i : Fin height, c i.val) := hsum
    _ ≤ (k : ℝ) * T ^ ((k : ℝ) - 1) * _ :=
      mul_le_mul_of_nonneg_left hcostsum hscale
    _ = _ := by
      dsimp [T, F, P, D, e, κ, μc, qc] <;> ring

/-- The actual integer-power source moments inherit the exact NATIVE_START
profile at time zero from the native state. -/
theorem native_source_band_momentK_start_le_profile
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (height k : ℕ)
    (hgamma : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h n)
    (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    nativeSourceBandMomentK M n height k 0 ≤
      (3 / 50 : ℝ)^k *
        (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(k - 1) := by
  simpa [nativeSourceBandMomentK] using
    nativeSourceBand_startMoment_le_profile M h n height k hgamma hstate hk1 hk20

end
end ASDExplicitGamma.Native

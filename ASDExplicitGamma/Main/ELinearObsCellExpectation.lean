module

public import ASDExplicitGamma.Main.ELinearObsSplit
public import ASDExplicitGamma.Main.ELinearCellExpectation

/-! Observer-root actual-law integrable majorant of one leading cell term. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- The deterministic bound of one cell's actual-law expectation. -/
def mainELinearObsLCellBound
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t b : ℝ) (L : {l : ℝ // 0 < l})
    (Q U : TriadicCube 2) : ℝ :=
  let xi := mainEnvelopeXi
    ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
    M.gamma mainSourceInversePrefix (theta M) t
  let H := mainEnvelopeH (theta M) M.gamma t
  2 * Real.sqrt (xi / 2) * oldSignedFlatMeanSize Q U b L true *
      oldSignedFlatOscillationSize Q U b L true +
    mainBeta * oldSignedFlatOscillationSize Q U b L true ^ 2 +
    2 * Real.sqrt (2 * (mainD * mainM0 H * H)) *
      (oldSignedFlatL2Size Q U b L false * oldSignedFlatOscillationSize Q U b L false) +
    mainM0 H * oldSignedFlatOscillationSize Q U b L false ^ 2 +
    2 * Real.sqrt 2 * mainKd (b ^ 2) *
      (Real.sqrt (xi / 2) * oldSignedFlatMeanSize Q U b L false +
        (mainBm H + 1) * oldSignedFlatOscillationSize Q U b L false)

/-- Actual-law integrable majorant of one cell term, with the exact
expectation bound. -/
theorem main_e_linear_obs_L_cell_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (Q : TriadicCube 2) (d : ℕ) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q d)
    (hscale : U.scale = m - 5)
    (hκ : oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 ≤ mainKd (b ^ 2)) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    ∃ A : CutoffSample 2 → ℝ, Integrable A μ ∧ 0 ≤ᵐ[μ] A ∧
      (∀ᵐ ω ∂μ, mainELinearObsLCellTerm M m t b L Q U ω ≤ A ω) ∧
      (∫ ω, A ω ∂μ) ≤ mainELinearObsLCellBound M h m t b L Q U := by
  intro μ
  have hpast' : ∀ n ≤ m, nativeInductionState M h n :=
    fun n hn => hpast n (lt_of_le_of_lt hn hm)
  let xi := mainEnvelopeXi
    ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
    M.gamma mainSourceInversePrefix (theta M) t
  let H := mainEnvelopeH (theta M) M.gamma t
  let Ωp := oldSignedFlatOscillationSize Q U b L true
  let Ωm := oldSignedFlatOscillationSize Q U b L false
  let ℓ := oldSignedFlatL2Size Q U b L false
  have hΩp : 0 ≤ Ωp := Real.sqrt_nonneg _
  have hΩm : 0 ≤ Ωm := Real.sqrt_nonneg _
  have hℓ : 0 ≤ ℓ := Real.sqrt_nonneg _
  have hkd : 0 ≤ mainKd (b ^ 2) := mainKd_nonneg _
  obtain ⟨pPi, -, pPs, pPb⟩ := main_e_linear_obs_mean_proxy_payment M h hM hγ N hpast m hm t ht
    Q d U hU hscale b L true
  obtain ⟨pMi, -, pMs, pMb⟩ := main_e_linear_obs_mean_proxy_payment M h hM hγ N hpast m hm t ht
    Q d U hU hscale b L false
  obtain ⟨B, Mu, hB0, hMu0, hBmem, hBcap, hMumem, hMucap, hprod, hae⟩ :=
    main_e_linear_obs_history_carriers M h hM hγ m hpast' t ht U hscale
  obtain ⟨C, hCint, hC0, hCle, hCae⟩ :=
    main_e_linear_obs_corrector_majorant M h hM hγ m hpast' t ht U hscale
  have hBint : Integrable B μ := hBmem.integrable (by norm_num)
  have hMuint : Integrable Mu μ := hMumem.integrable (by norm_num)
  have hBMint : Integrable (fun ω => B ω * Mu ω) μ := hBmem.integrable_mul hMumem
  have hBM0 : 0 ≤ᵐ[μ] (fun ω => B ω * Mu ω) := by
    filter_upwards [hMu0] with ω hω
    exact mul_nonneg (hB0 ω) hω
  have h2C : Integrable (fun ω => 2 * C ω) μ := hCint.const_mul 2
  have h2C0 : 0 ≤ᵐ[μ] (fun ω => 2 * C ω) := by
    filter_upwards [hC0] with ω hω
    exact mul_nonneg (by norm_num) hω
  obtain ⟨sCi, sCb⟩ := main_sqrt_expectation_ae μ _ h2C h2C0
  obtain ⟨sBMi, sBMb⟩ := main_sqrt_expectation_ae μ _ hBMint hBM0
  let g1 : CutoffSample 2 → ℝ := fun ω =>
    2 * Real.sqrt (mainELinearObsMeanProxy M m t Q U b L true ω) * Ωp
  let g2 : CutoffSample 2 → ℝ := fun ω => B ω * Ωp ^ 2
  let g3 : CutoffSample 2 → ℝ := fun ω => 2 * Real.sqrt (2 * C ω) * (ℓ * Ωm)
  let g4 : CutoffSample 2 → ℝ := fun ω => Mu ω * Ωm ^ 2
  let g5 : CutoffSample 2 → ℝ := fun ω =>
    2 * Real.sqrt 2 * mainKd (b ^ 2) *
      (Real.sqrt (mainELinearObsMeanProxy M m t Q U b L false ω) +
        (Real.sqrt (B ω * Mu ω) + 1) * Ωm)
  have i1 : Integrable g1 μ := (pPs.const_mul 2).mul_const Ωp
  have i2 : Integrable g2 μ := hBint.mul_const _
  have i3 : Integrable g3 μ := (sCi.const_mul 2).mul_const _
  have i4 : Integrable g4 μ := hMuint.mul_const _
  have i5 : Integrable g5 μ :=
    (pMs.add ((sBMi.add (integrable_const (1 : ℝ))).mul_const Ωm)).const_mul _
  refine ⟨fun ω => g1 ω + g2 ω + g3 ω + g4 ω + g5 ω, ?_, ?_, ?_, ?_⟩
  · exact (((i1.add i2).add i3).add i4).add i5
  · filter_upwards [hMu0] with ω hω
    have a1 : 0 ≤ g1 ω := mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hΩp
    have a2 : 0 ≤ g2 ω := mul_nonneg (hB0 ω) (sq_nonneg _)
    have a3 : 0 ≤ g3 ω := mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg hℓ hΩm)
    have a4 : 0 ≤ g4 ω := mul_nonneg hω (sq_nonneg _)
    have a5 : 0 ≤ g5 ω := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hkd)
      (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (add_nonneg (Real.sqrt_nonneg _) zero_le_one) hΩm))
    positivity
  · filter_upwards [hae, hCae] with ω hω hC
    obtain ⟨hinv, hresp⟩ := hω
    have hq : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) := by
      apply Real.one_lt_rpow (by norm_num) (by norm_num)
    have hinv0 : 0 ≤ oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) :=
      ASDExplicitGamma.Variational.lemmaVInverseHistory_nonneg U _ hq
    have hresp0 : 0 ≤ oldSignedResponseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) :=
      ENNReal.toReal_nonneg
    have hcorr0 : 0 ≤ oldSignedCorrectorHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) := by
      unfold oldSignedCorrectorHistory
      have hα := inverse_history_discount_range
      exact mul_nonneg (mul_nonneg (by linarith [hα.1]) hresp0) ENNReal.toReal_nonneg
    simp only [mainELinearObsLCellTerm]
    show _ ≤ g1 ω + g2 ω + g3 ω + g4 ω + g5 ω
    have e2 : oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) * Ωp ^ 2 ≤
        g2 ω := mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
    have e3 : 2 * Real.sqrt (2 * oldSignedCorrectorHistory U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω))) * (ℓ * Ωm) ≤ g3 ω :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by linarith)) (by norm_num)) (mul_nonneg hℓ hΩm)
    have e4 : oldSignedResponseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) * Ωm ^ 2 =
        g4 ω := by rw [hresp]
    have hBM : oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) *
        oldSignedResponseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) ≤ B ω * Mu ω := by
      rw [hresp]
      exact mul_le_mul_of_nonneg_right hinv (hresp ▸ hresp0)
    have hin : 0 ≤ Real.sqrt (mainELinearObsMeanProxy M m t Q U b L false ω) +
        (Real.sqrt (oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) *
          oldSignedResponseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω))) + 1) * Ωm :=
      add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (add_nonneg (Real.sqrt_nonneg _) zero_le_one) hΩm)
    have e5 : 2 * Real.sqrt 2 * oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 *
        (Real.sqrt (mainELinearObsMeanProxy M m t Q U b L false ω) +
          (Real.sqrt (oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) *
            oldSignedResponseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω))) + 1) * Ωm) ≤
        g5 ω := by
      calc _ ≤ 2 * Real.sqrt 2 * mainKd (b ^ 2) *
          (Real.sqrt (mainELinearObsMeanProxy M m t Q U b L false ω) +
            (Real.sqrt (oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) *
              oldSignedResponseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω))) + 1) * Ωm) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hκ (by positivity)) hin
        _ ≤ g5 ω := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := Real.sqrt_le_sqrt hBM
          nlinarith [mul_le_mul_of_nonneg_right this hΩm]
    linarith [e2, e3, e4, e5]
  · have hsum : (∫ ω, (g1 ω + g2 ω + g3 ω + g4 ω + g5 ω) ∂μ) =
        (∫ ω, g1 ω ∂μ) + (∫ ω, g2 ω ∂μ) + (∫ ω, g3 ω ∂μ) + (∫ ω, g4 ω ∂μ) +
          (∫ ω, g5 ω ∂μ) := by
      have j12 : Integrable (fun ω => g1 ω + g2 ω) μ := i1.add i2
      have j123 : Integrable (fun ω => g1 ω + g2 ω + g3 ω) μ := j12.add i3
      have j1234 : Integrable (fun ω => g1 ω + g2 ω + g3 ω + g4 ω) μ := j123.add i4
      rw [integral_add j1234 i5, integral_add j123 i4, integral_add j12 i3, integral_add i1 i2]
    have hBint' : (∫ ω, B ω ∂μ) ≤ mainBeta :=
      (main_integral_le_lpNorm_two μ B hBmem).trans hBcap
    have hMint' : (∫ ω, Mu ω ∂μ) ≤ mainM0 H :=
      (main_integral_le_lpNorm_two μ Mu hMumem).trans hMucap
    have hC' : (∫ ω, 2 * C ω ∂μ) ≤ 2 * (mainD * mainM0 H * H) := by
      rw [integral_const_mul]
      linarith
    have hsC : (∫ ω, Real.sqrt (2 * C ω) ∂μ) ≤ Real.sqrt (2 * (mainD * mainM0 H * H)) :=
      sCb.trans (Real.sqrt_le_sqrt hC')
    have hsBM : (∫ ω, Real.sqrt (B ω * Mu ω) ∂μ) ≤ mainBm H :=
      sBMb.trans (Real.sqrt_le_sqrt hprod)
    have e1 : (∫ ω, g1 ω ∂μ) ≤ 2 * (Real.sqrt (xi / 2) * oldSignedFlatMeanSize Q U b L true) *
        Ωp := by
      have : (∫ ω, g1 ω ∂μ) = 2 * (∫ ω, Real.sqrt (mainELinearObsMeanProxy M m t Q U b L true ω) ∂μ) *
          Ωp := by
        simp only [g1]
        rw [integral_mul_const, integral_const_mul]
      rw [this]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pPb (by norm_num)) hΩp
    have e2 : (∫ ω, g2 ω ∂μ) ≤ mainBeta * Ωp ^ 2 := by
      have : (∫ ω, g2 ω ∂μ) = (∫ ω, B ω ∂μ) * Ωp ^ 2 := by
        simp only [g2]
        rw [integral_mul_const]
      rw [this]
      exact mul_le_mul_of_nonneg_right hBint' (sq_nonneg _)
    have e3 : (∫ ω, g3 ω ∂μ) ≤ 2 * Real.sqrt (2 * (mainD * mainM0 H * H)) * (ℓ * Ωm) := by
      have : (∫ ω, g3 ω ∂μ) = 2 * (∫ ω, Real.sqrt (2 * C ω) ∂μ) * (ℓ * Ωm) := by
        simp only [g3]
        rw [integral_mul_const, integral_const_mul]
      rw [this]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsC (by norm_num))
        (mul_nonneg hℓ hΩm)
    have e4 : (∫ ω, g4 ω ∂μ) ≤ mainM0 H * Ωm ^ 2 := by
      have : (∫ ω, g4 ω ∂μ) = (∫ ω, Mu ω ∂μ) * Ωm ^ 2 := by
        simp only [g4]
        rw [integral_mul_const]
      rw [this]
      exact mul_le_mul_of_nonneg_right hMint' (sq_nonneg _)
    have e5 : (∫ ω, g5 ω ∂μ) ≤ 2 * Real.sqrt 2 * mainKd (b ^ 2) *
        (Real.sqrt (xi / 2) * oldSignedFlatMeanSize Q U b L false + (mainBm H + 1) * Ωm) := by
      have : (∫ ω, g5 ω ∂μ) = 2 * Real.sqrt 2 * mainKd (b ^ 2) *
          ((∫ ω, Real.sqrt (mainELinearObsMeanProxy M m t Q U b L false ω) ∂μ) +
            ((∫ ω, Real.sqrt (B ω * Mu ω) ∂μ) + 1) * Ωm) := by
        simp only [g5]
        have k1 : Integrable (fun ω => Real.sqrt (B ω * Mu ω) + 1) μ :=
          sBMi.add (integrable_const (1 : ℝ))
        have k2 : Integrable (fun ω => (Real.sqrt (B ω * Mu ω) + 1) * Ωm) μ := k1.mul_const Ωm
        rw [integral_const_mul, integral_add pMs k2, integral_mul_const, integral_add sBMi
          (integrable_const (1 : ℝ))]
        have h1 : ∫ _ω, (1 : ℝ) ∂μ = 1 := by simp
        rw [h1]
      rw [this]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := mul_le_mul_of_nonneg_right (add_le_add hsBM le_rfl : (∫ ω, Real.sqrt (B ω * Mu ω) ∂μ) + 1 ≤ mainBm H + 1) hΩm
      linarith
    rw [hsum]
    simp only [mainELinearObsLCellBound]
    linarith [e1, e2, e3, e4, e5]

end

end ASDExplicitGamma.Main

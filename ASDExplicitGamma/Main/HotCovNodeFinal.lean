module

public import ASDExplicitGamma.Main.HotCovExpectG
public import ASDExplicitGamma.Main.HotCovTrial
public import ASDExplicitGamma.Main.AffineFlatBoundary
public import ASDExplicitGamma.Main.ErrorCoefficients

/-! MA-E-COVARIANCE (hot-patched trial, observer root): the theorem, with the residual
factor `sqrt (v + B0/4)` that the actual flat means carry. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

theorem hotCov_alg_ecov (xi S R : ℝ) (hxi : 0 ≤ xi) (hS : 0 ≤ S) :
    2 * R * Real.sqrt (xi / 2 * S) = Real.sqrt 2 * Real.sqrt xi * R * Real.sqrt S := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]
  field_simp
  rw [h2]
  ring

/-- MA-E-COVARIANCE for the HOT-patched trial at the observer root `originCube 2 (m + hobs)`,
`hobs ∈ [1, 40]`: the affine (non-flat source cross with the affine reciprocal receiver) carrier
is dominated pathwise by an integrable majorant, the hot trial's mixed cross splits exactly into
this carrier plus the oscillatory carrier, and the expectation of the majorant is at most
`(v/2) R₁² + 2 (κ_rem R₁ + k_d t₀) t₀ √(v + B₀/4) + √2 t₀ R₁ e_cov`, `B₀ = v q`. -/
theorem main_e_covariance_node
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    let xi := mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t
    let R1 := mainR1 (inSourceMeanActual M m 5 t) (modelTraceHeatAverage (m + hobs) M m t)
      (mainEnvelopeH (theta M) M.gamma t)
    ∃ G : Cutoff.CutoffSample 2 → ℝ,
      Integrable G μ ∧
      (∀ ω, hotCovAffCarrier (originCube 2 (m + hobs)) (hobs + 5) M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
        (hotCovObsCoef M m hobs t ω) b (q3ModelLength (m + 1)) ≤ G ω) ∧
      (∀ (ω : Cutoff.CutoffSample 2) (n : whiteBasisIndex),
        2 * (hotPatchTrialTerms (originCube 2 (m + hobs)) (hobs + 5) M.nu
            (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
            (hotCovObsCoef M m hobs t ω) b (q3ModelLength (m + 1))).mixedPlus n -
          2 * (hotPatchTrialTerms (originCube 2 (m + hobs)) (hobs + 5) M.nu
            (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
            (hotCovObsCoef M m hobs t ω) b (q3ModelLength (m + 1))).mixedMinus n =
          oldSignedCellAverage (originCube 2 (m + hobs)) (hobs + 5)
            (hotCovAffMode (originCube 2 (m + hobs)) (hobs + 5) M.nu
              (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
              (hotCovObsCoef M m hobs t ω) b (q3ModelLength (m + 1)) n) +
          oldSignedCellAverage (originCube 2 (m + hobs)) (hobs + 5)
            (hotCovOscMode (originCube 2 (m + hobs)) (hobs + 5) M.nu
              (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
              (hotCovObsCoef M m hobs t ω) b (q3ModelLength (m + 1)) n)) ∧
      (∫ ω, G ω ∂μ) ≤
        (b ^ 2 / 2) * R1 ^ 2 +
        2 * (mainKrem (b ^ 2) * R1 + mainKd (b ^ 2) * mainT0 xi) * mainT0 xi *
          Real.sqrt (b ^ 2 + b ^ 2 * q / 4) +
        Real.sqrt 2 * mainT0 xi * R1 * mainEcov (b ^ 2) q := by
  intro μ b q xi R1
  have hcap := main_affine_flat_boundary_cap M h hM m hobs h1 h40
  obtain ⟨hX0, hGint, hGle⟩ := hotCov_expect_G M h hM hγ N hpast m hm hobs h1 h40 t ht b
    (b ^ 2 * q) hcap
  refine ⟨hotCovGObs M m hobs t b, hGint,
    fun ω => hotCov_pathwise_obs M m hobs h40 t ht b ω,
    fun ω n => hotCov_trial_mixed_split _ _ _ _ _ _ _ _ _ n, ?_⟩
  have hxi : 0 ≤ xi := hotCov_xi_nonneg M h hγ m t ht
  have hS : 0 ≤ mainFlatBoundaryEPlus (b ^ 2) (b ^ 2 * q) ^ 2 +
      mainFlatBoundaryEMinus (b ^ 2) (b ^ 2 * q) ^ 2 := by positivity
  have hR1 : R1 ^ 2 = mainBeta * (inSourceMeanActual M m 5 t -
      modelTraceHeatAverage (m + hobs) M m t) +
      mainEpsNew * (mainEnvelopeH (theta M) M.gamma t / (1 - mainAlpha)) :=
    Real.sq_sqrt hX0
  have hR1' : R1 = Real.sqrt (mainBeta * (inSourceMeanActual M m 5 t -
      modelTraceHeatAverage (m + hobs) M m t) +
      mainEpsNew * (mainEnvelopeH (theta M) M.gamma t / (1 - mainAlpha))) := rfl
  have e2 := hotCov_alg_ecov xi (mainFlatBoundaryEPlus (b ^ 2) (b ^ 2 * q) ^ 2 +
      mainFlatBoundaryEMinus (b ^ 2) (b ^ 2 * q) ^ 2) R1 hxi hS
  have hecov : mainEcov (b ^ 2) q = Real.sqrt (mainFlatBoundaryEPlus (b ^ 2) (b ^ 2 * q) ^ 2 +
      mainFlatBoundaryEMinus (b ^ 2) (b ^ 2 * q) ^ 2) :=
    mainEcov_eq_flat_boundary_errors (b ^ 2) q
  have e3 : Real.sqrt (xi / 2 * (2 * b ^ 2 + b ^ 2 * q / 2)) =
      mainT0 xi * Real.sqrt (b ^ 2 + b ^ 2 * q / 4) := by
    rw [show xi / 2 * (2 * b ^ 2 + b ^ 2 * q / 2) = xi * (b ^ 2 + b ^ 2 * q / 4) by ring,
      Real.sqrt_mul hxi]
    rfl
  have hG2 : (∫ ω, hotCovGObs M m hobs t b ω ∂μ) ≤
      b ^ 2 / 2 * R1 ^ 2 +
      2 * R1 * Real.sqrt (xi / 2 * (mainFlatBoundaryEPlus (b ^ 2) (b ^ 2 * q) ^ 2 +
        mainFlatBoundaryEMinus (b ^ 2) (b ^ 2 * q) ^ 2)) +
      2 * (mainKrem (b ^ 2) * R1 + mainKd (b ^ 2) * Real.sqrt xi) *
        Real.sqrt (xi / 2 * (2 * b ^ 2 + b ^ 2 * q / 2)) := by
    refine hGle.trans (le_of_eq ?_)
    rw [hR1]
    rfl
  rw [e2, ← hecov, e3] at hG2
  have hT0 : mainT0 xi = Real.sqrt xi := rfl
  rw [hT0] at hG2 ⊢
  refine hG2.trans (le_of_eq ?_)
  ring

end

end ASDExplicitGamma.Main

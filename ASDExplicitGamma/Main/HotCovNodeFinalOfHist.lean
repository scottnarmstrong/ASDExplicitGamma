module

public import ASDExplicitGamma.Main.HotCovNodeFinal
public import ASDExplicitGamma.Main.HotCovExpectGOfHist

/-! Successors of `HotCovNodeFinal` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Successor of `main_e_covariance_node` with the history envelope `Hfun`. -/
theorem main_e_covariance_node_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    let xi := mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t
    let R1 := mainR1 (inSourceMeanActual M m 5 t) (modelTraceHeatAverage (m + hobs) M m t)
      (Hfun t)
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
  obtain ⟨hX0, hGint, hGle⟩ := hotCov_expect_G_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ N hpast m hm hobs h1 h40 t ht b
    (b ^ 2 * q) hcap
  refine ⟨hotCovGObs M m hobs t b, hGint,
    fun ω => hotCov_pathwise_obs M m hobs h40 t ht b ω,
    fun ω n => hotCov_trial_mixed_split _ _ _ _ _ _ _ _ _ n, ?_⟩
  have hxi : 0 ≤ xi := hotCov_xi_nonneg M h hγ m t ht
  have hS : 0 ≤ mainFlatBoundaryEPlus (b ^ 2) (b ^ 2 * q) ^ 2 +
      mainFlatBoundaryEMinus (b ^ 2) (b ^ 2 * q) ^ 2 := by positivity
  have hR1 : R1 ^ 2 = mainBeta * (inSourceMeanActual M m 5 t -
      modelTraceHeatAverage (m + hobs) M m t) +
      mainEpsNew * (Hfun t / (1 - mainAlpha)) :=
    Real.sq_sqrt hX0
  have hR1' : R1 = Real.sqrt (mainBeta * (inSourceMeanActual M m 5 t -
      modelTraceHeatAverage (m + hobs) M m t) +
      mainEpsNew * (Hfun t / (1 - mainAlpha))) := rfl
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
end

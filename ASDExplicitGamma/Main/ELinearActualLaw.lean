module

public import ASDExplicitGamma.Main.ELinearObsGPart
public import ASDExplicitGamma.Main.EBottomCovarianceActualLaw

/-! MA-E-LINEAR and the MA-E-FOURLOAD-AGGREGATE row at the observer
root. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- MA-E-LINEAR for the hot trial at the observer root. -/
theorem main_e_linear_actual_law
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ) (hobs_pos : 1 ≤ hobs) (hobs40 : hobs ≤ 40) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let L := q3ModelLength (m + 1)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    ∃ Lg : CutoffSample 2 → ℝ, Integrable Lg μ ∧
      (∀ᵐ ω ∂μ, mainELinearObsGroup M (originCube 2 (m + (hobs : ℤ))) (5 + hobs) m t b L ω ≤ Lg ω) ∧
      (∫ ω, Lg ω ∂μ) ≤
        mainLinearError (b ^ 2) (mainEnvelopeH (theta M) M.gamma t)
          (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) q +
        (mainFourLoadAG (b ^ 2) (mainEnvelopeH (theta M) M.gamma t)
          (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) q -
          2 * mainBe (b ^ 2) q) *
          mainG (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) := by
  intro μ b L q
  obtain ⟨Lbar, hLi, hL0, hLle, hLint⟩ :=
    main_e_linear_obs_L_part_expectation M h hM hγ N hpast m hm t ht hobs hobs_pos hobs40
  obtain ⟨Gbar, hGi, hG0, hGle, hGint⟩ :=
    main_e_linear_obs_G_part_expectation M h hM hγ N hpast m hm t ht hobs hobs_pos hobs40
  refine ⟨fun ω => Lbar ω + Gbar ω, hLi.add hGi, ?_, ?_⟩
  · filter_upwards [hLle, hGle] with ω h1 h2
    exact (main_e_linear_obs_group_split M (originCube 2 (m + (hobs : ℤ))) (5 + hobs) m t b L ω).trans
      (add_le_add h1 h2)
  · rw [integral_add hLi hGi]
    linarith

/-- MA-E-FOURLOAD-AGGREGATE row at the observer root: the bottom covariance of
the hot trial (with its baseline trace term moved to the left) plus the
`G`-weighted half-gain feedback, bounded by `mainFourLoadAG * G`. -/
theorem main_e_fourload_aggregate_actual_law
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ) (hobs_pos : 1 ≤ hobs) (hobs40 : hobs ≤ 40) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let L := q3ModelLength (m + 1)
    let Q := originCube 2 (m + (hobs : ℤ))
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    ∃ Ag : CutoffSample 2 → ℝ, Integrable Ag μ ∧
      (∀ᵐ ω ∂μ, mainEHotBottomCovarianceGroup M Q (5 + hobs) m t b L ω +
          b ^ 2 * (Matrix.trace (coarseBlockMatrix (openCubeSet Q)
            (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
              (mainELinearObsCoefficient Q m t ω))).lowerRight - 2) +
          mainELinearObsGAverageTerm M Q (5 + hobs) m t b L ω ≤ Ag ω) ∧
      (∫ ω, Ag ω ∂μ) ≤
        mainFourLoadAG (b ^ 2) (mainEnvelopeH (theta M) M.gamma t)
          (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) q *
          mainG (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) := by
  intro μ b L Q q
  obtain ⟨Gb, hGbi, hGble, hGbint⟩ :=
    main_e_bottom_covariance_actual_law M h hM hγ N hpast m hm t ht hobs hobs_pos hobs40
  obtain ⟨Gbar, hGi, hG0, hGle, hGint⟩ :=
    main_e_linear_obs_G_part_expectation M h hM hγ N hpast m hm t ht hobs hobs_pos hobs40
  refine ⟨fun ω => Gb ω + Gbar ω, hGbi.add hGi, ?_, ?_⟩
  · filter_upwards [hGle] with ω h2
    have h1 := hGble ω
    linarith
  · rw [integral_add hGbi hGi]
    have e : mainFourLoadAG (b ^ 2) (mainEnvelopeH (theta M) M.gamma t)
          (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) q *
          mainG (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) =
        2 * mainBe (b ^ 2) q *
          Real.sqrt (2 * mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) +
        (mainFourLoadAG (b ^ 2) (mainEnvelopeH (theta M) M.gamma t)
          (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) q -
          2 * mainBe (b ^ 2) q) *
          mainG (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) := by
      unfold mainG
      ring
    rw [e]
    linarith

end
end ASDExplicitGamma.Main

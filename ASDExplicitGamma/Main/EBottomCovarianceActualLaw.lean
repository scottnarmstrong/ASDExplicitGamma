module

public import ASDExplicitGamma.Main.HotBottomCovariancePathwise
public import ASDExplicitGamma.Main.ObserverGapRow

/-! Bottom covariance of the hot trial at the observer root: integrable majorant
with mean at most `2 mainBe(b^2, q) sqrt(2 xi)`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

theorem main_e_bottom_covariance_actual_law
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
    ∃ G : CutoffSample 2 → ℝ, Integrable G μ ∧
      (∀ ω, mainEHotBottomCovarianceGroup M Q (5 + hobs) m t b L ω ≤
        -b ^ 2 * (Matrix.trace (coarseBlockMatrix (openCubeSet Q)
          (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
            (mainELinearObsCoefficient Q m t ω))).lowerRight - 2) + G ω) ∧
      (∫ ω, G ω ∂μ) ≤ 2 * mainBe (b ^ 2) q *
        Real.sqrt (2 * mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) /
          (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma mainSourceInversePrefix (theta M) t) := by
  intro μ b L Q q
  obtain ⟨Gbar, hGint, hG0, hGle, -, hGmean⟩ :=
    observer_parent_gap_G_row M h hM hγ N hpast m hm t ht hobs hobs40
  have hBe0 : 0 ≤ mainBe (b ^ 2) q := by
    have hq0 := mainAffineFlatBoundaryCapQ_nonneg (hobs - 1)
    unfold mainBe
    positivity
  refine ⟨fun ω => 2 * mainBe (b ^ 2) q * Gbar ω, hGint.const_mul _, ?_, ?_⟩
  · intro ω
    have hp := main_e_hot_bottom_covariance_pathwise M h hM m t hobs hobs_pos hobs40 ω
    have := mul_le_mul_of_nonneg_left (hGle ω) (by positivity : 0 ≤ 2 * mainBe (b ^ 2) q)
    simp only at hp ⊢
    linarith
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hGmean (by positivity)

end
end ASDExplicitGamma.Main

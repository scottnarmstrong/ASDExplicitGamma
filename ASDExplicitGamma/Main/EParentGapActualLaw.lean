module

public import ASDExplicitGamma.Main.HotTopCovariancePathwise
public import ASDExplicitGamma.Main.ObserverParentGapExpectation

/-! MA-E-PARENT-GAP at the observer root: the hot top covariance group has an
integrable majorant with mean at most `2 mainBe(b^2, q) mainV(xi, f)`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

theorem main_e_parent_gap_actual_law
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
      (∀ ω, |mainEHotTopCovarianceGroup M Q (5 + hobs) m t b L ω| ≤ G ω) ∧
      (∫ ω, G ω ∂μ) ≤ 2 * mainBe (b ^ 2) q *
        mainV (mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) /
          (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma mainSourceInversePrefix (theta M) t)
          (modelTraceHeatAverage (m + hobs) M m t) := by
  intro μ b L Q q
  obtain ⟨Vbar, hVint, hV0, hVle, hVmean⟩ :=
    observer_parent_gap_row M h hM hγ N hpast m hm t ht hobs hobs40
  have hq0 := mainAffineFlatBoundaryCapQ_nonneg (hobs - 1)
  have hBe0 : 0 ≤ mainBe (b ^ 2) q := by
    unfold mainBe
    positivity
  refine ⟨fun ω => 2 * mainBe (b ^ 2) q * Vbar ω, hVint.const_mul _, ?_, ?_⟩
  · intro ω
    refine (main_e_hot_top_covariance_pathwise M h hM m t hobs hobs_pos hobs40 ω).trans ?_
    exact mul_le_mul_of_nonneg_left (hVle ω) (by positivity)
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hVmean (by positivity)

end
end ASDExplicitGamma.Main

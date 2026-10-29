module

public import ASDExplicitGamma.Main.HotCovarianceBetaCapFlag
public import ASDExplicitGamma.Native.OldSignedBottomCovarianceBill
public import ASDExplicitGamma.Main.HotTopCovariancePathwise

/-! Bottom flat covariance of the hot-patched trial at the observer root. The
bottom covariance family does not involve the source `H`, so it is the old one. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- The bottom flat covariance group of the hot-patched trial at an observer root. -/
def mainEHotBottomCovarianceGroup (M : ABKModel 2) (Q : TriadicCube 2) (d : ℕ) (m : ℤ)
    (t b : ℝ) (L : {l : ℝ // 0 < l}) (ω : CutoffSample 2) : ℝ :=
  let σ : ℝ := Annealed.sigmaBar M m
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let k := mainELinearObsCoefficient Q m t ω
  let T := hotPatchTrialTerms Q d M.nu σ M.nu_pos hσ k b L
  ∑' n, T.covarianceBottom n

/-- Pathwise bottom covariance bill of the hot trial. -/
theorem main_e_hot_bottom_covariance_pathwise
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ) (t : ℝ)
    (hobs : ℕ) (hobs_pos : 1 ≤ hobs) (hobs40 : hobs ≤ 40) (ω : CutoffSample 2) :
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let L := q3ModelLength (m + 1)
    let Q := originCube 2 (m + (hobs : ℤ))
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
      (mainELinearObsCoefficient Q m t ω)
    mainEHotBottomCovarianceGroup M Q (5 + hobs) m t b L ω ≤
      -b ^ 2 * (Matrix.trace (coarseBlockMatrix (openCubeSet Q) a).lowerRight - 2) +
      2 * mainBe (b ^ 2) q * Real.sqrt (descendantsAverage Q (5 + hobs) (fun U =>
        oldSignedReciprocalErrorSize Q U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1
          (mainELinearObsCoefficient Q m t ω) ^ 2)) := by
  intro b L Q q a
  have hq := main_affine_flat_boundary_cap M h hM m hobs hobs_pos hobs40
  have hq0 := mainAffineFlatBoundaryCapQ_nonneg (hobs - 1)
  have hr : cubeScaleFactor Q / (3 : ℝ) ^ (5 + hobs) ≤ (3 : ℝ) ^ (-6 : ℤ) * L.1 := by
    unfold cubeScaleFactor
    change (3 : ℝ) ^ (m + (hobs : ℤ)) / (3 : ℝ) ^ (5 + hobs) ≤
      (3 : ℝ) ^ (-6 : ℤ) * (3 : ℝ) ^ (m + 1)
    rw [← zpow_add₀ (by norm_num)]
    have : (3 : ℝ) ^ (m + (hobs : ℤ)) / (3 : ℝ) ^ (5 + hobs) = (3 : ℝ) ^ (m - 5) := by
      rw [← zpow_natCast, ← zpow_sub₀ (by norm_num)]
      congr 1
      push_cast
      ring
    rw [this]
    exact le_of_eq (by congr 1; omega)
  have hbill := old_signed_actual_bottom_covariance_bill Q (5 + hobs) M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (mainELinearObsCoefficient Q m t ω) b L
  have hcap := main_covariance_beta_weighted_le_flag false Q (5 + hobs) b L q hq hq0 hr
    (fun U => oldSignedReciprocalErrorSize Q U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 (mainELinearObsCoefficient Q m t ω))
  unfold mainEHotBottomCovarianceGroup
  refine hbill.2.trans ?_
  have := mul_le_mul_of_nonneg_left hcap (by norm_num : (0 : ℝ) ≤ 2)
  linarith

end
end ASDExplicitGamma.Main

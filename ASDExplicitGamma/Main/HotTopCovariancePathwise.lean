module

public import ASDExplicitGamma.Main.HotCovarianceBetaCap
public import ASDExplicitGamma.Native.HotTopCovarianceBill
public import ASDExplicitGamma.Main.ELinearObsPathwise
public import ASDExplicitGamma.Main.AffineFlatBoundary

/-! Pathwise MA-E-PARENT-GAP for the hot trial at the observer root: the top
flat covariance group is at most `2 mainBe(b², q_{hobs-1})` times the
root-mean-square of the actual parent primal error sizes of the depth-`5+hobs`
cells. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- The exact grid and tail values of the observer boundary cap are nonnegative. -/
theorem mainAffineFlatBoundaryCapQ_nonneg (d : ℕ) :
    0 ≤ mainAffineFlatBoundaryCapQ d := by
  unfold mainAffineFlatBoundaryCapQ
  split_ifs
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have hq : (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) = 1 / (3 : ℝ) ^ d := by
      simp [ASDExplicitGamma.Numerics.Model.q3ModeLength]
    rw [hq]
    have h0 : 0 < 1 / (3 : ℝ) ^ d := by positivity
    have h1 : 1 / (3 : ℝ) ^ d ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    nlinarith

/-- The top flat covariance group of the hot-patched trial at an observer root. -/
def mainEHotTopCovarianceGroup (M : ABKModel 2) (Q : TriadicCube 2) (d : ℕ) (m : ℤ)
    (t b : ℝ) (L : {l : ℝ // 0 < l}) (ω : CutoffSample 2) : ℝ :=
  let σ : ℝ := Annealed.sigmaBar M m
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let k := mainELinearObsCoefficient Q m t ω
  let T := hotPatchTrialTerms Q d M.nu σ M.nu_pos hσ k b L
  ∑' n, T.covarianceTop n

/-- Pathwise parent-gap bill of the hot top covariance. -/
theorem main_e_hot_top_covariance_pathwise
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ) (t : ℝ)
    (hobs : ℕ) (hobs_pos : 1 ≤ hobs) (hobs40 : hobs ≤ 40) (ω : CutoffSample 2) :
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let L := q3ModelLength (m + 1)
    let Q := originCube 2 (m + (hobs : ℤ))
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    |mainEHotTopCovarianceGroup M Q (5 + hobs) m t b L ω| ≤
      2 * mainBe (b ^ 2) q * Real.sqrt (descendantsAverage Q (5 + hobs) (fun U =>
        oldSignedPrimalErrorSize Q U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1 (mainELinearObsCoefficient Q m t ω) ^ 2)) := by
  intro b L Q q
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
  have hbill := hot_top_covariance_bill Q (5 + hobs) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (mainELinearObsCoefficient Q m t ω) b L
  have hcap := main_covariance_beta_weighted_le Q (5 + hobs) b L q hq hq0 hr
    (fun U => oldSignedPrimalErrorSize Q U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 (mainELinearObsCoefficient Q m t ω))
  unfold mainEHotTopCovarianceGroup
  refine hbill.2.trans ?_
  have := mul_le_mul_of_nonneg_left hcap (by norm_num : (0 : ℝ) ≤ 2)
  linarith

end

end ASDExplicitGamma.Main

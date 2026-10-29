module

public import ASDExplicitGamma.Inverse.BankHistoryPhysical

/-! A complete extended bank history identified directly from its actual
framed descendant matrices. Only the normalized coefficient needs an
ellipticity witness; no extra physical-law premise is introduced. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- Exact history identification from the actual descendant frame matrices.
This retains the complete positive series as an ENNReal equality. -/
theorem source_bank_history_eq_of_framed_matrices
    (Q : TriadicCube 2) (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (af : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) af)
    (hMatrix : ∀ (R : TriadicCube 2) (d : ℕ), R ∈ descendantsAtDepth Q d →
      coarseBlockMatrix (cubeSet R) af = frameMatrix (Annealed.sigmaBar M m:ℝ)
        (coarseBlockMatrix (cubeSet R) (attenuatedCoefficient M m J weights ω))) :
    bankRootInverseHistory Q M m J weights ω = ENNReal.ofReal
      (lemmaVInverseHistory Q af ((3:ℝ)^(1/4:ℝ))) := by
  let q := (3:ℝ)^(1/4:ℝ)
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hs := (Annealed.sigmaBar_characterization M m).1
  have hdepth (j : ℕ) : bankFiniteRootResponseMax (descendantsAtDepth Q j) M m J weights ω =
      ENNReal.ofReal (lemmaVInverseDepthMax Q af j) := by
    have hmax := bank_finite_max_ofReal (descendantsAtDepth Q j) (descendantsAtDepth_nonempty Q j)
      (fun R => rootInverseResponse M R m J weights ω)
    change bankFiniteRootResponseMax (descendantsAtDepth Q j) M m J weights ω = _ at hmax
    rw [hmax]
    congr 1
    unfold lemmaVInverseDepthMax
    apply Book.Ch02.finsetSupReal_congr
    intro R hR
    rw [Scalar.inverse_history_lowerRight R af (hEll.mono (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR)),hMatrix R j hR]
    simp only [frameMatrix]
    rw [Scalar.inverse_history_matrixNorm_smul _ _ hs.le]
    rfl
  have hi : q⁻¹=(3:ℝ)^(-(1/4:ℝ)) := (Real.rpow_neg (by norm_num : (0:ℝ)≤3) (1/4:ℝ)).symm
  have hw : 0 ≤ q⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hq).le
  have hw1 : q⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hq)).mpr hq
  have hsum := lemmaVInverseHistory_summable Q hEll hq
  unfold bankRootInverseHistory
  simp_rw [hdepth]
  unfold bankHistoryPrefactor bankHistoryAlpha
  rw [←hi]
  simp_rw [←ENNReal.ofReal_pow hw,←ENNReal.ofReal_mul (pow_nonneg hw _)]
  rw [←ENNReal.ofReal_tsum_of_nonneg
    (fun j => mul_nonneg (pow_nonneg hw j) (lemmaVInverseDepthMax_nonneg Q af j)) hsum]
  rw [←ENNReal.ofReal_mul (sub_nonneg.mpr hw1.le)]
  rfl

end
end ASDExplicitGamma.Inverse

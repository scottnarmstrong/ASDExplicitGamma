module

public import ASDExplicitGamma.Cold.ScalarCoefficient

/-! # Literal coefficient normalization realizes the true-frame coarse matrix -/

@[expose] public section
noncomputable section
open Homogenization
namespace ASDExplicitGamma.Cold

/-- The square-root parameter in the existing rescaling API is the ordinary positive amplitude. -/
theorem cold_coarseMatrixRescale_sqrt {c : ℝ} (hc : 0 < c) (A : BlockMat 2) :
    Variational.coarseMatrixRescale (Real.sqrt c) A =
      { upperLeft := c • A.upperLeft
        upperRight := A.upperRight
        lowerLeft := A.lowerLeft
        lowerRight := c⁻¹ • A.lowerRight } := by
  unfold Variational.coarseMatrixRescale
  simp only [Real.sq_sqrt hc.le,zpow_neg,zpow_ofNat]

/-- Positive amplitude rescaling of a coefficient with unit lower ellipticity. -/
theorem cold_coarse_smul_unit {Q : TriadicCube 2} {a : CoeffField 2} {Λ c : ℝ}
    (hEll : IsEllipticFieldOn 1 Λ (cubeSet Q) a) (hc : 0 < c) :
    coarseBlockMatrix (cubeSet Q) (c • a) =
      { upperLeft := c • (coarseBlockMatrix (cubeSet Q) a).upperLeft
        upperRight := (coarseBlockMatrix (cubeSet Q) a).upperRight
        lowerLeft := (coarseBlockMatrix (cubeSet Q) a).lowerLeft
        lowerRight := c⁻¹ • (coarseBlockMatrix (cubeSet Q) a).lowerRight } := by
  have hs := Real.sqrt_pos.mpr hc
  have he : (Real.sqrt c)^2 • a = c • a := by rw [Real.sq_sqrt hc.le]
  rw [← he,Variational.coarseBlockMatrix_sq_smul_triCube hEll hs,cold_coarseMatrixRescale_sqrt hc]

/-- Normalizing the literal field by any positive frame realizes exactly frameMatrix.
No replacement of the true frame by the molecular parameter occurs. -/
theorem cold_coarse_frame {Q : TriadicCube 2} {a : CoeffField 2} {lam Λ σ : ℝ}
    (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Λ (cubeSet Q) a) (hσ : 0 < σ) :
    coarseBlockMatrix (cubeSet Q) (σ⁻¹ • a) =
      Variational.frameMatrix σ (coarseBlockMatrix (cubeSet Q) a) := by
  let a0 : CoeffField 2 := lam⁻¹ • a
  have hEll0 : IsEllipticFieldOn 1 (lam⁻¹*Λ) (cubeSet Q) a0 := by
    simpa only [inv_mul_cancel₀ hlam.ne'] using cold_isEllipticFieldOn_smul (inv_pos.mpr hlam) hEll
  have ha : lam • a0 = a := by
    dsimp only [a0]
    rw [smul_smul,mul_inv_cancel₀ hlam.ne',one_smul]
  have hb : (σ⁻¹*lam) • a0 = σ⁻¹ • a := by rw [mul_smul,ha]
  have hA := cold_coarse_smul_unit hEll0 hlam
  have hB := cold_coarse_smul_unit hEll0 (mul_pos (inv_pos.mpr hσ) hlam)
  rw [ha] at hA
  rw [hb] at hB
  rw [hB,hA]
  apply blockMat_ext
  · ext i j
    simp only [Variational.frameMatrix,Matrix.smul_apply,smul_eq_mul]
    ring
  · rfl
  · rfl
  · ext i j
    simp only [Variational.frameMatrix,Matrix.smul_apply,smul_eq_mul,mul_inv_rev,inv_inv]
    ring

end ASDExplicitGamma.Cold

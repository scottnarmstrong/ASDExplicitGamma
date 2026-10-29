module

public import ASDExplicitGamma.Variational.TrueFrame
public import ASDExplicitGamma.Inverse.HistoryTrace

/-! SC-TRUE-FRAME-NORMALIZATION. The annealed matrix inequality and pathwise
trace inequality have distinct proofs. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Homogenization.Book Algsuperdiff.Section3

/-- The physical mean on every triadic square dominates the true homogenized matrix. -/
theorem annealed_cube_true_frame_lower (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    BlockMatLoewnerLE
      (Ch02.blockDiag ((Annealed.sigmaBar M m : ℝ) • (1 : Mat 2))
        ((Annealed.sigmaBar M m : ℝ)⁻¹ • (1 : Mat 2)))
      (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m) (cubeSet Q)) := by
  rw [cubeSet_eq_translateSet_originCube_of_triadicCube Q]
  exact Variational.annealedBlockMatrix_trueFrame_lower M m Q.scale _

/-- Exact scalar-frame congruence gives the normalized full-block identity floor. -/
theorem normalized_mean_identity_lower (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    BlockMatLoewnerLE (Ch02.blockIdentity 2)
      (Variational.frameMatrix (Annealed.sigmaBar M m : ℝ)
        (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m) (cubeSet Q))) := by
  rw [cubeSet_eq_translateSet_originCube_of_triadicCube Q]
  exact Variational.trueFrame_mean_lower M m Q.scale _

/-- The expected directional physical inverse response at an actual source cube. -/
noncomputable def physicalInverseResponse (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (e : Vec 2) : ℝ :=
  vecDot e (matVecMul (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m)
    (cubeSet Q)).lowerRight e)

/-- sigmaBar times the physical inverse response is at least one for unit loads. -/
theorem sigmaBar_mul_physicalInverseResponse_ge_one (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (e : Vec 2) (he : vecDot e e = 1) :
    1 ≤ (Annealed.sigmaBar M m : ℝ)*physicalInverseResponse M m Q e := by
  have h := annealed_cube_true_frame_lower M m Q (0,e)
  have hs := (Annealed.sigmaBar_characterization M m).1
  have hid (x : Vec 2) : matVecMul (1 : Mat 2) x = x := Matrix.one_mulVec x
  have hz (x : Vec 2) : matVecMul (0 : Mat 2) x = 0 := by
    ext i
    simp only [matVecMul,Pi.zero_apply,Matrix.zero_apply,zero_mul,Finset.sum_const_zero]
  simp only [Ch02.blockDiag,blockMatVecMul,blockVecDot,matVecMul_zero,hz,
    zero_add,add_zero,vecDot_zero_left,smul_matVecMul,hid,vecDot_smul_right,he] at h
  have hi : (Annealed.sigmaBar M m : ℝ)⁻¹ ≤ physicalInverseResponse M m Q e := by
    dsimp only [physicalInverseResponse]
    linarith only [h]
  have hm := mul_le_mul_of_nonneg_left hi hs.le
  simpa only [mul_inv_cancel₀ hs.ne'] using hm

/-- Every normalized mean quadratic excess is nonnegative, including B_old. -/
theorem true_frame_mean_excess_nonneg (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (P : BlockVec 2) :
    0 ≤ blockVecDot P (blockMatVecMul
      (Variational.frameMatrix (Annealed.sigmaBar M m : ℝ)
        (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m) (cubeSet Q))) P)-
      blockVecDot P P := by
  have h := normalized_mean_identity_lower M m Q P
  have hid : blockMatVecMul (Ch02.blockIdentity 2) P = P := by
    rcases P with ⟨p,q⟩
    have hi (x : Vec 2) : matVecMul (1 : Mat 2) x = x := Matrix.one_mulVec x
    have hz (x : Vec 2) : matVecMul (0 : Mat 2) x = 0 := by
      ext i
      simp only [matVecMul,Pi.zero_apply,Matrix.zero_apply,zero_mul,Finset.sum_const_zero]
    simp only [Ch02.blockIdentity,Ch02.blockDiag,blockMatVecMul,
      hi,hz,add_zero,zero_add]
  rw [hid] at h
  linarith only [h]

end ASDExplicitGamma.Scalar

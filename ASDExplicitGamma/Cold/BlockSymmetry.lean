module

public import ASDExplicitGamma.Variational.TrueFrame

/-! # Expected cold response blocks in the true frame -/

@[expose] public section

namespace ASDExplicitGamma.Cold

open Homogenization Homogenization.Book
open Algsuperdiff.Section3 MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- CO-EXPECTED-BLOCK-SYMMETRY: at a fixed scale the two expected centered
blocks are scalar and nonnegative, and do not depend on the translated cell. -/
theorem exists_centered_mean_scalar_blocks (M : ABKModel 2) (m n : ℤ) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧
      ∀ z : Vec 2,
        toFullBlockMat (Variational.frameMatrix (Annealed.sigmaBar M m : ℝ)
          (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m)
            (translateSet z (cubeSet (originCube 2 n))))) - 1 =
          toFullBlockMat (Ch02.blockDiag (u • (1 : Mat 2)) (v • (1 : Mat 2))) := by
  obtain ⟨alpha, beta, ha, hb, hmean⟩ := Variational.exists_trueFrame_mean_scalars M m n
  refine ⟨alpha - 1, beta - 1, sub_nonneg.mpr ha, sub_nonneg.mpr hb, ?_⟩
  intro z
  rw [hmean z]
  ext i j
  cases i <;> cases j <;>
    simp [toFullBlockMat, Ch02.blockDiag, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply] <;> split_ifs <;> simp only [sub_self]

/-- The centered expected response on every triadic square has the source
block form. Both the child and parent scales can be instantiated independently. -/
theorem exists_centered_cube_mean_scalar_blocks (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧
      (∫ a : RegCoeffField 2,
        toFullBlockMat (Variational.frameMatrix (Annealed.sigmaBar M m : ℝ)
          (coarseBlockMatrix (cubeSet Q) a.toFun))
        ∂(Cutoff.coefficientCutoffLaw M m)) - 1 =
          toFullBlockMat (Ch02.blockDiag (u • (1 : Mat 2)) (v • (1 : Mat 2))) := by
  obtain ⟨u, v, hu, hv, hmean⟩ := exists_centered_mean_scalar_blocks M m Q.scale
  refine ⟨u, v, hu, hv, ?_⟩
  rw [Variational.integral_frameMatrix]
  have h := hmean (triadicCubeShift Q)
  rw [← cubeSet_eq_translateSet_originCube_of_triadicCube Q] at h
  exact h

end ASDExplicitGamma.Cold

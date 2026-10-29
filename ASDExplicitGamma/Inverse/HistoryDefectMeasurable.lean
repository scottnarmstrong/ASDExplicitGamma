module

public import ASDExplicitGamma.Inverse.HistoryDefectSource
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-! Measurability of the genuine reflected operator defect on the cutoff sample space. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3

/-- Every full coarse entry is a finite linear combination of measurable Mu evaluations. -/
theorem history_full_coarse_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      toFullBlockMat (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun)) := by
  classical
  let X : Cutoff.CutoffSample 2 → RegCoeffField 2 := Cutoff.coefficientCutoff M.nu n
  have hX : Measurable X := Cutoff.measurable_coefficientCutoff M.nu n
  have hEll : ∀ ω, Book.Ch04.AELocallyUniformlyEllipticField (X ω) :=
    fun ω => Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M n ω
  have hmu (P : BlockVec 2) :=
    Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_Mu_cubeSet hX hEll Q P
  have he (α β : BlockCoord 2) : Measurable (fun ω => coarseBlockEntry (cubeSet Q) (X ω).toFun α β) := by
    by_cases h : α = β
    · simpa only [coarseBlockEntry,dite_eq_left h] using (hmu (blockBasis α)).const_mul 2
    · simp only [coarseBlockEntry,dite_eq_right h]
      convert ((hmu (blockBasis α+blockBasis β)).sub (hmu (blockBasis α))).sub
        (hmu (blockBasis β)) using 1
  apply measurable_pi_iff.mpr
  intro α
  apply measurable_pi_iff.mpr
  intro β
  cases α <;> cases β <;> simpa only [toFullBlockMat,coarseBlockMatrix,X] using he _ _

/-- No measurable representative or surrogate for the source matrix is introduced. -/
theorem history_operator_defect_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) :
    Measurable (historyOperatorDefect M n Q) := by
  let C (ω : Cutoff.CutoffSample 2) := Variational.frameMatrix (Annealed.sigmaBar M n : ℝ)
    (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun)
  let D := Variational.frameDiagonal (Annealed.sigmaBar M n : ℝ)
  have hC : Measurable (fun ω => toFullBlockMat (C ω)) := by
    have he : (fun ω => toFullBlockMat (C ω)) =
        (fun ω => D*toFullBlockMat (coarseBlockMatrix (cubeSet Q)
          (Cutoff.coefficientCutoff M.nu n ω).toFun)*D) := by
      funext ω
      exact Variational.toFullBlockMat_frameMatrix_eq_diagonal_congruence _ _
        (Annealed.sigmaBar_characterization M n).1
    rw [he]
    apply Measurable.of_eval_matrix
    intro i j
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ (fun k _ =>
      (Finset.measurable_sum _ (fun l _ =>
        ((history_full_coarse_measurable M n Q).eval_matrix (i := l) (j := k)).const_mul (D i l))).mul_const (D k j))
  have hR : Measurable (fun ω => toFullBlockMat (blockReflect (C ω))) := by
    have he : (fun ω => toFullBlockMat (blockReflect (C ω))) =
        (fun ω α β => toFullBlockMat (C ω) (Sum.swap α) (Sum.swap β)) := by
      funext ω α β
      cases α <;> cases β <;> rfl
    rw [he]
    exact measurable_pi_iff.mpr (fun α => measurable_pi_iff.mpr
      (fun β => (measurable_pi_iff.mp (measurable_pi_iff.mp hC (Sum.swap α))) (Sum.swap β)))
  have hH : Measurable (fun ω => historyDefectMatrix (C ω)) := by
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun ω => (1/2:ℝ)*(toFullBlockMat (C ω) i j+
      toFullBlockMat (blockReflect (C ω)) i j)-(1 : FullBlockMat 2) i j)
    exact ((hC.eval_matrix.add hR.eval_matrix).const_mul (1/2:ℝ)).sub measurable_const
  let L : FullBlockMat 2 →ₗ[ℝ]
      (EuclideanSpace ℝ (BlockCoord 2) →L[ℝ] EuclideanSpace ℝ (BlockCoord 2)) :=
    { toFun := fun A => Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A
      map_add' := fun A B => map_add (Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)) A B
      map_smul' := fun r A => map_smul (Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)) r A }
  have hL : Continuous L := L.continuous_of_finiteDimensional
  exact hL.norm.measurable.comp hH

end ASDExplicitGamma.Inverse

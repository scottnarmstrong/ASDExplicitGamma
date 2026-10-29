module

public import ASDExplicitGamma.Scalar.UpperCellEnergySensitivityPayment
public import Homogenization.Ambient.BlockMatrix

/-! Entrywise independence contracts a random quadratic to its annealed matrix. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory
noncomputable section

/-- Finite quadratic expectation with integrability proved from L1 matrix
entries, L2 load coordinates, and OLD/fresh independence. -/
theorem upper_cell_independent_quadratic_expectation
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (A : Ω → I → I → ℝ) (Y : Ω → I → ℝ)
    (hA : ∀ i j, Integrable (fun ω => A ω i j) μ)
    (hY : ∀ i, MemLp (fun ω => Y ω i) 2 μ)
    (hi : ∀ i j, IndepFun (fun ω => A ω i j) (fun ω => Y ω i*Y ω j) μ) :
    Integrable (fun ω => ∑ i, ∑ j, A ω i j*(Y ω i*Y ω j)) μ ∧
      (∫ ω, (∑ i, ∑ j, A ω i j*(Y ω i*Y ω j)) ∂μ) =
      ∫ ω, (∑ i, ∑ j, (∫ ω', A ω' i j ∂μ)*(Y ω i*Y ω j)) ∂μ := by
  have hYY (i j) : Integrable (fun ω => Y ω i*Y ω j) μ := (hY i).integrable_mul (hY j)
  have hp (i j) : Integrable (fun ω => A ω i j*(Y ω i*Y ω j)) μ :=
    (hi i j).integrable_mul (hA i j) (hYY i j)
  have hm (i j) : Integrable (fun ω => (∫ ω', A ω' i j ∂μ)*(Y ω i*Y ω j)) μ :=
    (hYY i j).const_mul _
  refine ⟨integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hp i j)), ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finset_sum _ (fun j _ => hp i j)),
    integral_finsetSum _ (fun i _ => integrable_finset_sum _ (fun j _ => hm i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hp i j), integral_finsetSum _ (fun j _ => hm i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  exact (hi i j).integral_mul_eq_mul_integral (hA i j).aestronglyMeasurable
    (hYY i j).aestronglyMeasurable

/-- The full-coordinate expansion is the original block quadratic. -/
theorem upper_cell_block_quadratic_sum (A : BlockMat 2) (P : BlockVec 2) :
    blockVecDot P (blockMatVecMul A P) =
      ∑ i : BlockCoord 2, ∑ j : BlockCoord 2,
        toFullBlockMat A i j*(toFullBlockVec P i*toFullBlockVec P j) := by
  rw [←dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end ASDExplicitGamma.Scalar

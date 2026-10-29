module

public import ASDExplicitGamma.Inverse.ClippedMatrixResponseEnergy
public import ASDExplicitGamma.Inverse.ClippedMatrixQuadraticNorm

/-! Sharp old response quadratic cap from the actual reflected defect. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization

/-- Exact reflected-energy sum, in the source block-reflection convention. -/
theorem clipped_block_history_energy_sum (C : BlockMat 2) (P : BlockVec 2) :
    blockVecDot P (blockMatVecMul C P)+blockVecDot (P.2,P.1) (blockMatVecMul C (P.2,P.1)) =
      2*(dotProduct (toFullBlockVec P) ((historyDefectMatrix C).mulVec (toFullBlockVec P))+blockVecDot P P) := by
  have he (D : BlockMat 2) : dotProduct (toFullBlockVec P)
      ((toFullBlockMat D).mulVec (toFullBlockVec P))=blockVecDot P (blockMatVecMul D P) := by
    rw [← toFullBlockVec_blockMatVecMul,dotProduct_toFullBlockVec]
  simp only [historyDefectMatrix,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.add_mulVec,
    Matrix.one_mulVec,dotProduct_sub,dotProduct_smul,dotProduct_add,he,dotProduct_toFullBlockVec,
    blockVecDot_blockMatVecMul_blockReflect,smul_eq_mul]
  ring

/-- The literal g(t) cap follows directly from variational pair inequalities
and a defect operator-norm cap. No inverse or coarse self-duality is a premise. -/
theorem clipped_block_response_quadratic_bound (C : BlockMat 2)
    (hp : ∀ p q : Vec 2, 2*vecDot p q ≤ blockVecDot (p,q) (blockMatVecMul C (p,q)))
    (hn : ∀ p q : Vec 2, -2*vecDot p q ≤ blockVecDot (p,q) (blockMatVecMul C (p,q)))
    (t : ℝ) (ht : 0 ≤ t)
    (hH : ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (historyDefectMatrix C)‖ ≤ t)
    (P : BlockVec 2) :
    blockVecDot P (blockMatVecMul C P) ≤ (1+t+Real.sqrt (t*(t+2)))*blockVecDot P P := by
  have hS := blockVecDot_nonneg P
  have hA : 0 ≤ blockVecDot P (blockMatVecMul C P) := by
    have hp' := hp P.1 P.2
    have hn' := hn P.1 P.2
    change _ ≤ blockVecDot P (blockMatVecMul C P) at hp' hn'
    linarith only [hp',hn']
  apply clipped_response_scalar_bound _ _ _ t hS ht hA (clipped_block_energy_product C hp hn P)
  have hq := clipped_quadratic_abs_le_norm (historyDefectMatrix C) (toFullBlockVec P)
  rw [dotProduct_toFullBlockVec] at hq
  have hupper := ((le_abs_self _).trans hq).trans (mul_le_mul_of_nonneg_right hH hS)
  rw [clipped_block_history_energy_sum]
  linarith only [hupper]

end ASDExplicitGamma.Inverse
